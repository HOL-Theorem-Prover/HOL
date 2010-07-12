open HolKernel Parse boolLib bossLib;

(*
quietdec := true;
loadPath := (concat [Globals.HOLDIR, "/examples/separationLogic/src"]) ::
            !loadPath;

map load ["finite_mapTheory", "relationTheory", "congLib", "sortingTheory",
   "rich_listTheory", "generalHelpersTheory", "latticeTheory", "separationLogicTheory",
   "bagSimps", "ConseqConv", "quantHeuristicsLib"];
show_assums := true;
*)

open generalHelpersTheory finite_mapTheory pred_setTheory
   listTheory rich_listTheory arithmeticTheory separationLogicTheory
   bagTheory bagSimps containerTheory relationTheory operatorTheory optionTheory;
open ConseqConv boolSimps quantHeuristicsLib quantHeuristicsArgsLib Sanity


(*
quietdec := false;
open Sanity
*)

val _ = new_theory "vars_as_resource";

val MP_CANON = SIMP_RULE std_ss [AND_IMP_INTRO,
    GSYM RIGHT_FORALL_IMP_THM]

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



val IS_PERMISSION_STRUCTURE_def = Define `
   IS_PERMISSION_STRUCTURE (f:'a option -> 'a option -> 'a option, total_perm:'a) =
      ASSOC f /\
      COMM f /\
      OPTION_IS_LEFT_CANCELLATIVE f /\
      (!C. f NONE C = NONE) /\
      (!c. ?c1 c2. f (SOME c1) (SOME c2) = (SOME c)) /\
      (!c. f (SOME total_perm) (SOME c) = NONE) /\
      (!c1 c2. ~(f (SOME c1) (SOME c2) = (SOME c1)))`



val IS_PERMISSION_STRUCTURE_THM = store_thm ("IS_PERMISSION_STRUCTURE_THM",
``IS_PERMISSION_STRUCTURE (f, total_perm) =
      ASSOC f /\
      COMM f /\
      OPTION_IS_LEFT_CANCELLATIVE f /\
      OPTION_IS_RIGHT_CANCELLATIVE f /\
      (!C. f NONE C = NONE) /\
      (!C. f C NONE = NONE) /\
      (!c. ?c1 c2. f (SOME c1) (SOME c2) = (SOME c)) /\
      (!p. f (SOME total_perm) p = NONE) /\
      (!p. f p (SOME total_perm) = NONE) /\
      (!c1 p. ~(f (SOME c1) p = (SOME c1))) /\
      (!c1 p. ~(f p (SOME c1) = (SOME c1)))``,

SIMP_TAC std_ss [IS_PERMISSION_STRUCTURE_def] THEN
EQ_TAC THEN SIMP_TAC std_ss [] THEN
REPEAT STRIP_TAC THENL [
   FULL_SIMP_TAC std_ss [OPTION_IS_LEFT_CANCELLATIVE_def,
                         OPTION_IS_RIGHT_CANCELLATIVE_def] THEN
   METIS_TAC[COMM_DEF],

   METIS_TAC[COMM_DEF],
   Cases_on `p` THEN METIS_TAC[COMM_DEF],
   Cases_on `p` THEN METIS_TAC[COMM_DEF],
   Cases_on `p` THEN METIS_TAC[COMM_DEF],
   Cases_on `p` THEN METIS_TAC[COMM_DEF]
]);



val IS_EQ_SPLIT_PERMISSION_STRUCTURE_def = Define `
   IS_EQ_SPLIT_PERMISSION_STRUCTURE (f:'a option -> 'a option -> 'a option, total_perm:'a, split_perm) =
      ASSOC f /\
      COMM f /\
      OPTION_IS_LEFT_CANCELLATIVE f /\
      (!C. f NONE C = NONE) /\
      (!c. f (SOME (split_perm c)) (SOME (split_perm c)) = (SOME c)) /\
      (!c. f (SOME total_perm) (SOME c) = NONE) /\
      (!c1 c2. ~(f (SOME c1) (SOME c2) = (SOME c1)))`



val IS_EQ_SPLIT_PERMISSION_STRUCTURE_THM = store_thm ("IS_EQ_SPLIT_PERMISSION_STRUCTURE_THM",
``
    IS_EQ_SPLIT_PERMISSION_STRUCTURE (f, total_perm, perm_split) =
    (IS_PERMISSION_STRUCTURE (f, total_perm) /\
    (!c. f (SOME (perm_split c)) (SOME (perm_split c)) = SOME c) /\
    (!c. ~((perm_split c) = total_perm)))``,

SIMP_TAC std_ss [IS_EQ_SPLIT_PERMISSION_STRUCTURE_def,
   IS_PERMISSION_STRUCTURE_def] THEN
EQ_TAC THEN SIMP_TAC std_ss [] THEN
METIS_TAC[]);


(*Define one concrete permission structure*)

local
   open realLib;

val var_res_permission_TY_DEF = new_type_definition("var_res_permission", prove
(``?x:real. (\x. (0:real < x) /\ (x <= 1:real)) x``,
EXISTS_TAC ``1:real`` THEN
SIMP_TAC realLib.real_ss []));

val var_res_permission_ISO_DEF =
define_new_type_bijections
{name = "var_res_permission_ISO_DEF",
   ABS  = "var_res_permission_ABS",
   REP  = "var_res_permission_REP",
   tyax = var_res_permission_TY_DEF};

val rep_fn_onto_THM = SIMP_RULE std_ss [] (prove_rep_fn_onto var_res_permission_ISO_DEF);
val abs_fn_one_one_thm = SIMP_RULE std_ss [] (prove_abs_fn_one_one var_res_permission_ISO_DEF);
val rep_fn_one_one_thm = SIMP_RULE std_ss [] (prove_rep_fn_one_one var_res_permission_ISO_DEF);

val var_res_permission_ISO_IMP =
prove (``
   !r. (0 < r /\ r <= 1) ==>
            (var_res_permission_REP (var_res_permission_ABS r) = r)``,
METIS_TAC[var_res_permission_ISO_DEF])

val rep_fn_onto_IMP_THM =
   prove (``!p.  (0 < var_res_permission_REP p) /\ (var_res_permission_REP p <= 1)``,
      METIS_TAC [prove_rep_fn_onto var_res_permission_ISO_DEF]);


val var_res_permission_THM_exists =
   prove (``?var_res_permission_combine var_res_permission_split var_res_write_permission:var_res_permission.
      IS_EQ_SPLIT_PERMISSION_STRUCTURE (var_res_permission_combine, var_res_write_permission, var_res_permission_split)``,

   Q.EXISTS_TAC `\po1 po2.
      if (po1 = NONE) \/ (po2 = NONE) then NONE else
      let p1 = THE po1 in
      let p2 = THE po2 in
      let r1 = var_res_permission_REP p1 in
      let r2 = var_res_permission_REP p2 in
      if (r1 + r2 <= 1) then SOME (var_res_permission_ABS (r1+r2)) else NONE` THEN
   Q.EXISTS_TAC `\c. var_res_permission_ABS ((var_res_permission_REP c)/2)` THEN
   Q.EXISTS_TAC `var_res_permission_ABS 1` THEN

   SIMP_TAC std_ss [IS_EQ_SPLIT_PERMISSION_STRUCTURE_def] THEN
   REPEAT STRIP_TAC THENL [
      SIMP_TAC std_ss [ASSOC_DEF, LET_THM] THEN
      Cases_on `po1` THEN SIMP_TAC std_ss [] THEN
      Cases_on `po2` THEN SIMP_TAC std_ss [] THEN
      Cases_on `po2'` THEN SIMP_TAC std_ss [] THEN
      SIMP_TAC std_ss [COND_RAND, COND_RATOR] THEN
      Q.ABBREV_TAC `r1 = var_res_permission_REP x` THEN
      Q.ABBREV_TAC `r2 = var_res_permission_REP x'` THEN
      Q.ABBREV_TAC `r3 = var_res_permission_REP x''` THEN


      `(0 < r1) /\ (r1 <= 1) /\ (0 < r2) /\ (r2 <= 1) /\ (0 < r3) /\ (r3 <= 1)` by
         PROVE_TAC[rep_fn_onto_IMP_THM] THEN
      `(0 < (r1 + r2)) /\ (0 < (r2 + r3))` by ALL_TAC THEN1 (
         REPEAT (POP_ASSUM MP_TAC) THEN
         realLib.REAL_ARITH_TAC
      ) THEN
      Cases_on `r1 + r2 <= 1` THENL [
         ASM_SIMP_TAC std_ss [var_res_permission_ISO_IMP] THEN
         Cases_on `r1 + r2 + r3 <= 1` THENL [
            `(r2 + r3) <= 1` by ALL_TAC THEN1 (
               POP_ASSUM MP_TAC THEN
               Q.PAT_ASSUM `0 < r1` MP_TAC THEN
               realLib.REAL_ARITH_TAC
            ) THEN
            ASM_SIMP_TAC std_ss [var_res_permission_ISO_IMP,
               realTheory.REAL_ADD_ASSOC],


            ASM_SIMP_TAC std_ss [] THEN
            Cases_on `r2 + r3 <= 1` THEN (
               ASM_SIMP_TAC std_ss [var_res_permission_ISO_IMP,
                  realTheory.REAL_ADD_ASSOC]
            )
         ],


         ASM_SIMP_TAC std_ss [] THEN
         Cases_on `r2 + r3 <= 1` THEN (
            ASM_SIMP_TAC std_ss [var_res_permission_ISO_IMP,
               realTheory.REAL_ADD_ASSOC]
         ) THEN
         Q.PAT_ASSUM `~(r1 + r2 <= 1)` MP_TAC THEN
         Q.PAT_ASSUM `0 < r3` MP_TAC THEN
         realLib.REAL_ARITH_TAC
      ],



      SIMP_TAC std_ss [COMM_DEF] THEN
      Cases_on `po1` THEN1 REWRITE_TAC [] THEN
      Cases_on `po2` THEN1 REWRITE_TAC [] THEN
      SIMP_TAC std_ss [LET_THM] THEN
      METIS_TAC[realTheory.REAL_ADD_SYM],



      SIMP_TAC std_ss [OPTION_IS_LEFT_CANCELLATIVE_def] THEN
      Cases_on `po1` THEN1 SIMP_TAC std_ss [] THEN
      Cases_on `po2` THEN1 SIMP_TAC std_ss [] THEN
      Cases_on `po2'` THEN1 SIMP_TAC std_ss [] THEN
      SIMP_TAC std_ss [LET_THM] THEN
      SIMP_TAC std_ss [COND_RAND, COND_RATOR] THEN
      Q.ABBREV_TAC `r1 = var_res_permission_REP x` THEN
      Q.ABBREV_TAC `r2 = var_res_permission_REP x'` THEN
      Q.ABBREV_TAC `r3 = var_res_permission_REP x''` THEN
      Tactical.REVERSE (Cases_on `r1 + r3 <= 1`) THEN1 (
         ASM_SIMP_TAC std_ss [] THEN
         PROVE_TAC[]
      ) THEN
      ASM_REWRITE_TAC[] THEN
      STRIP_TAC THEN
      Q.PAT_ASSUM `var_res_permission_ABS X = Y`MP_TAC THEN
      `(0 < r1) /\ (r1 <= 1) /\ (0 < r2) /\ (r2 <= 1) /\ (0 < r3) /\ (r3 <= 1)` by
         PROVE_TAC[rep_fn_onto_IMP_THM] THEN
      `(0 < (r1 + r2)) /\ (0 < (r1 + r3))` by ALL_TAC THEN1 (
         REPEAT (POP_ASSUM MP_TAC) THEN
         realLib.REAL_ARITH_TAC
      ) THEN
      ASM_SIMP_TAC std_ss [abs_fn_one_one_thm, realTheory.REAL_EQ_LADD] THEN
      UNABBREV_ALL_TAC THEN
      REWRITE_TAC[rep_fn_one_one_thm],



      SIMP_TAC std_ss [LET_THM] THEN

      Q.ABBREV_TAC `r = var_res_permission_REP c` THEN
      `(0 < r) /\ (r <= 1)` by PROVE_TAC[rep_fn_onto_IMP_THM] THEN
      `(0 < r / 2) /\ (r / 2 <= 1)` by ALL_TAC THEN1 (
         ASM_REWRITE_TAC [realTheory.REAL_LT_HALF1] THEN
         `(r / 2) < r` by PROVE_TAC [realTheory.REAL_LT_HALF2] THEN
         NTAC 2 (POP_ASSUM MP_TAC) THEN
         realLib.REAL_ARITH_TAC
      ) THEN
      ASM_SIMP_TAC std_ss [var_res_permission_ISO_IMP,
         realTheory.REAL_HALF_DOUBLE] THEN
      UNABBREV_ALL_TAC THEN
      SIMP_TAC std_ss [var_res_permission_ISO_DEF],



      SIMP_TAC std_ss [LET_THM, COND_RAND, COND_RATOR] THEN
      `(0 < 1) /\ (1 <= 1)` by realLib.REAL_ARITH_TAC THEN
      ASM_SIMP_TAC std_ss [var_res_permission_ISO_IMP] THEN
      `(0 < var_res_permission_REP c)` by PROVE_TAC[rep_fn_onto_IMP_THM] THEN
      POP_ASSUM MP_TAC THEN
      realLib.REAL_ARITH_TAC,



      POP_ASSUM MP_TAC THEN
      SIMP_TAC std_ss [LET_THM, COND_RAND, COND_RATOR] THEN
      Q.ABBREV_TAC `r1 = var_res_permission_REP c1` THEN
      Q.ABBREV_TAC `r2 = var_res_permission_REP c2` THEN
      Cases_on `r1 + r2 <= 1` THEN (
         ASM_SIMP_TAC std_ss []
      ) THEN
      ONCE_REWRITE_TAC [GSYM rep_fn_one_one_thm] THEN
      `(0 < r1) /\ (r1 <= 1) /\ (0 < r2) /\ (r2 <= 1)` by
         PROVE_TAC[rep_fn_onto_IMP_THM] THEN
      `0 < (r1 + r2)` by ALL_TAC THEN1 (
         REPEAT (POP_ASSUM MP_TAC) THEN
         realLib.REAL_ARITH_TAC
      ) THEN
      ASM_SIMP_TAC std_ss [var_res_permission_ISO_IMP] THEN
      Q.PAT_ASSUM `0 < r2` MP_TAC THEN
      realLib.REAL_ARITH_TAC
   ]);

in

val var_res_permission_THM = new_specification
  ("var_res_permission_THM", ["var_res_permission_combine", "var_res_permission_split", "var_res_write_permission"],
  var_res_permission_THM_exists);

val var_res_permission_THM2 = save_thm ("var_res_permission_THM2",
   REWRITE_RULE [IS_PERMISSION_STRUCTURE_THM,
      IS_EQ_SPLIT_PERMISSION_STRUCTURE_THM] var_res_permission_THM)


val var_res_read_permission_THM = new_specification
  ("var_res_read_permission_THM", ["var_res_read_permission"],
   prove (``?var_res_read_permission:var_res_permission.
                 ~(var_res_read_permission = var_res_write_permission)``,
            METIS_TAC[var_res_permission_THM2]));


end;


(*--------------------------------------------------------------------------------------------------*)



val _ = type_abbrev("var_res_state",
   Type `:('pvars |-> ('data # var_res_permission))`);



val VAR_RES_STACK_IS_SEPARATE_def = Define `
   VAR_RES_STACK_IS_SEPARATE s1 s2 =
   !x.    ((x IN (FDOM s1)) /\ (x IN (FDOM s2))) ==>
      ((FST (s1 ' x) = FST (s2 ' x)) /\
                 (IS_SOME (var_res_permission_combine (SOME (SND (s1 ' x))) (SOME (SND (s2 ' x))))))`;











val VAR_RES_STACK_IS_SEPARATE___SYM = store_thm ("VAR_RES_STACK_IS_SEPARATE___SYM",
   ``!s1 s2. VAR_RES_STACK_IS_SEPARATE s1 s2 = VAR_RES_STACK_IS_SEPARATE s2 s1``,

SIMP_TAC std_ss [VAR_RES_STACK_IS_SEPARATE_def] THEN
REPEAT STRIP_TAC THEN
`COMM var_res_permission_combine` by REWRITE_TAC[var_res_permission_THM2] THEN
FULL_SIMP_TAC std_ss [COMM_DEF] THEN
METIS_TAC[]);


val VAR_RES_STACK_IS_SEPARATE___FEMPTY = store_thm ("VAR_RES_STACK_IS_SEPARATE___FEMPTY",
   ``(!s. VAR_RES_STACK_IS_SEPARATE s FEMPTY) /\
      (!s. VAR_RES_STACK_IS_SEPARATE FEMPTY s)``,

SIMP_TAC std_ss [VAR_RES_STACK_IS_SEPARATE_def,
   FDOM_FEMPTY, NOT_IN_EMPTY]);


val VAR_RES_STACK_COMBINE___MERGE_FUNC_def = Define `
VAR_RES_STACK_COMBINE___MERGE_FUNC = \e1 e2.
         (* (e1 = (v1, p1)), (e2 = (v2, p2)),
            (v1 = v2) and (p1 compatible p2) because of separateness*)
         (FST e1, THE (var_res_permission_combine (SOME (SND e1)) (SOME (SND e2))))`

val VAR_RES_STACK_COMBINE_def = Define `
   VAR_RES_STACK_COMBINE =
      BIN_OPTION_MAP (FMERGE VAR_RES_STACK_COMBINE___MERGE_FUNC)
         VAR_RES_STACK_IS_SEPARATE`;


val VAR_RES_STACK_COMBINE_REWRITE = store_thm ("VAR_RES_STACK_COMBINE_REWRITE",
`` (!s. VAR_RES_STACK_COMBINE NONE s = NONE) /\
   (!s. VAR_RES_STACK_COMBINE s NONE = NONE) /\
   (!s. VAR_RES_STACK_COMBINE s (SOME FEMPTY) = s) /\
   (!s. VAR_RES_STACK_COMBINE (SOME FEMPTY) s = s) /\

   (!s1 s2. (VAR_RES_STACK_COMBINE (SOME s1) (SOME s2) = (SOME s1)) =
           (s2 = FEMPTY)) /\

   (!s1 s2. (VAR_RES_STACK_COMBINE (SOME s1) (SOME s2) = (SOME s2)) =
           (s1 = FEMPTY)) /\


   (!s1 s2. IS_SOME (VAR_RES_STACK_COMBINE (SOME s1) (SOME s2)) =
         VAR_RES_STACK_IS_SEPARATE s1 s2) /\
   (!s1 s2. ~(VAR_RES_STACK_IS_SEPARATE s1 s2) ==>
         (VAR_RES_STACK_COMBINE (SOME s1) (SOME s2) = NONE)) /\

   (!s1 s2 s. (VAR_RES_STACK_COMBINE (SOME s1) (SOME s2) = (SOME s)) ==>
         (VAR_RES_STACK_IS_SEPARATE s1 s2 /\ (FDOM s = FDOM s1 UNION FDOM s2))) /\

   (!s1 s2 s x. ((VAR_RES_STACK_COMBINE (SOME s1) (SOME s2) = (SOME s)) /\
            (x IN FDOM s1) /\ ~(x IN FDOM s2)) ==>
            (s ' x = s1 ' x)) /\

   (!s1 s2 s x. ((VAR_RES_STACK_COMBINE (SOME s1) (SOME s2) = (SOME s)) /\
            ~(x IN FDOM s1) /\ (x IN FDOM s2)) ==>
            (s ' x = s2 ' x)) /\

   (!s1 s2 s x.
            ((VAR_RES_STACK_COMBINE (SOME s1) (SOME s2) = (SOME s)) /\
            (x IN FDOM s1) /\ (x IN FDOM s2)) ==>

            (((FST (s1 ' x)) = (FST (s ' x))) /\ ((FST (s2 ' x)) = (FST (s ' x))) /\
                            (var_res_permission_combine (SOME (SND (s1 ' x))) (SOME (SND (s2 ' x))) =
                                                        (SOME (SND (s ' x))))))``,


SIMP_TAC std_ss [VAR_RES_STACK_COMBINE_def, BIN_OPTION_MAP_THM, FMERGE_DEF,
       VAR_RES_STACK_COMBINE___MERGE_FUNC_def] THEN
SIMP_TAC std_ss [COND_RAND, COND_RATOR] THEN
REPEAT CONJ_TAC THEN REPEAT GEN_TAC THENL [
   Cases_on `s` THEN SIMP_TAC std_ss [BIN_OPTION_MAP_THM] THEN
   SIMP_TAC std_ss [FMERGE_FEMPTY, VAR_RES_STACK_IS_SEPARATE___FEMPTY],

   Cases_on `s` THEN SIMP_TAC std_ss [BIN_OPTION_MAP_THM] THEN
   SIMP_TAC std_ss [FMERGE_FEMPTY, VAR_RES_STACK_IS_SEPARATE___FEMPTY],

   SIMP_TAC std_ss [FMERGE_NO_CHANGE] THEN
   Tactical.REVERSE EQ_TAC THEN1 (
      SIMP_TAC std_ss [VAR_RES_STACK_IS_SEPARATE___FEMPTY, FDOM_FEMPTY, NOT_IN_EMPTY]
   ) THEN
   REPEAT STRIP_TAC THEN
   CCONTR_TAC THEN
   `?x. x IN FDOM s2` by ALL_TAC THEN1 (
      CCONTR_TAC THEN
      FULL_SIMP_TAC std_ss [GSYM fmap_EQ_THM, FDOM_FEMPTY, EXTENSION, NOT_IN_EMPTY]
   ) THEN
   RES_TAC THEN
   FULL_SIMP_TAC std_ss [VAR_RES_STACK_IS_SEPARATE_def] THEN
   RES_TAC THEN
   Cases_on `s1 ' x` THEN
   FULL_SIMP_TAC std_ss [] THEN
   METIS_TAC[option_CLAUSES, var_res_permission_THM2],


   SIMP_TAC std_ss [FMERGE_NO_CHANGE] THEN
   Tactical.REVERSE EQ_TAC THEN1 (
      SIMP_TAC std_ss [VAR_RES_STACK_IS_SEPARATE___FEMPTY, FDOM_FEMPTY, NOT_IN_EMPTY]
   ) THEN
   REPEAT STRIP_TAC THEN
   CCONTR_TAC THEN
   `?x. x IN FDOM s1` by ALL_TAC THEN1 (
      CCONTR_TAC THEN
      FULL_SIMP_TAC std_ss [GSYM fmap_EQ_THM, FDOM_FEMPTY, EXTENSION, NOT_IN_EMPTY]
   ) THEN
   RES_TAC THEN
   FULL_SIMP_TAC std_ss [VAR_RES_STACK_IS_SEPARATE_def] THEN
   RES_TAC THEN
   Cases_on `s2 ' x` THEN
   FULL_SIMP_TAC std_ss [] THEN
   METIS_TAC[option_CLAUSES, var_res_permission_THM2],

   FULL_SIMP_TAC std_ss [VAR_RES_STACK_IS_SEPARATE_def, SOME_THE_EQ]
]);


val SOME___VAR_RES_STACK_COMBINE = store_thm ("SOME___VAR_RES_STACK_COMBINE",
  ``(VAR_RES_STACK_COMBINE (SOME s1) (SOME s2) = SOME s) =
    (VAR_RES_STACK_IS_SEPARATE s1 s2 /\ (s = FMERGE VAR_RES_STACK_COMBINE___MERGE_FUNC
       s1 s2))``,

SIMP_TAC std_ss [VAR_RES_STACK_COMBINE_def, BIN_OPTION_MAP_THM, COND_RATOR, COND_RAND] THEN
PROVE_TAC[]);



val VAR_RES_STACK_COMBINE_EXPAND = store_thm ("VAR_RES_STACK_COMBINE_EXPAND",
  ``(VAR_RES_STACK_IS_SEPARATE s1 s2 ==>
    (VAR_RES_STACK_COMBINE (SOME s1) (SOME s2) = SOME (FMERGE VAR_RES_STACK_COMBINE___MERGE_FUNC
       s1 s2))) /\

    (~(VAR_RES_STACK_IS_SEPARATE s1 s2) ==>
    (VAR_RES_STACK_COMBINE (SOME s1) (SOME s2) = NONE))``,

SIMP_TAC std_ss [VAR_RES_STACK_COMBINE_def, BIN_OPTION_MAP_THM, COND_RATOR, COND_RAND]);



val VAR_RES_STACK_COMBINE___EQ___FEMPTY = store_thm
("VAR_RES_STACK_COMBINE___EQ___FEMPTY",
``(VAR_RES_STACK_COMBINE X Y = SOME FEMPTY) =
((X = SOME FEMPTY) /\ (Y = SOME FEMPTY))``,

Cases_on `X` THEN Cases_on `Y` THEN
SIMP_TAC std_ss [SOME___VAR_RES_STACK_COMBINE,
       VAR_RES_STACK_COMBINE_REWRITE,
       FMERGE_EQ_FEMPTY] THEN
METIS_TAC[VAR_RES_STACK_IS_SEPARATE___FEMPTY]);



val IS_VAR_RES_SUBPERMISSION_def = Define `
   IS_VAR_RES_SUBPERMISSION p1 p2 =
      (p1 = p2) \/ (?p. var_res_permission_combine (SOME p1) (SOME p) = (SOME p2))`

val IS_VAR_RES_SUBPERMISSION_THM = store_thm ("IS_VAR_RES_SUBPERMISSION_THM",
   ``(IS_VAR_RES_SUBPERMISSION var_res_write_permission p =
       (p = var_res_write_permission)) /\
      ((IS_VAR_RES_SUBPERMISSION p1 p2 /\ IS_VAR_RES_SUBPERMISSION p2 p1) = (p1 = p2)) /\
      ((IS_VAR_RES_SUBPERMISSION p1 p2 /\ IS_VAR_RES_SUBPERMISSION p2 p3) ==>
       (IS_VAR_RES_SUBPERMISSION p1 p3)) /\
      (IS_VAR_RES_SUBPERMISSION p p) /\
      (IS_VAR_RES_SUBPERMISSION (var_res_permission_split p) p) /\
      ~(IS_VAR_RES_SUBPERMISSION p (var_res_permission_split p))``,

   SIMP_TAC std_ss [IS_VAR_RES_SUBPERMISSION_def] THEN
   REPEAT STRIP_TAC THENL [
      SIMP_TAC std_ss [var_res_permission_THM2] THEN
      PROVE_TAC[],

      Cases_on `p1 = p2` THEN ASM_SIMP_TAC std_ss [] THEN
      CCONTR_TAC THEN
      FULL_SIMP_TAC std_ss [] THEN
      Q.PAT_ASSUM `X = SOME p2` (ASSUME_TAC o GSYM) THEN
      Q.PAT_ASSUM `X = SOME p1` MP_TAC THEN
      ASM_SIMP_TAC std_ss [] THEN
      `ASSOC var_res_permission_combine` by PROVE_TAC[var_res_permission_THM2] THEN
      FULL_SIMP_TAC std_ss [ASSOC_SYM] THEN
      SIMP_TAC std_ss [var_res_permission_THM2],


      ASM_REWRITE_TAC[],
      METIS_TAC[],
      METIS_TAC[],

      Q.PAT_ASSUM `X = SOME p2` (ASSUME_TAC o GSYM) THEN
      `ASSOC var_res_permission_combine` by PROVE_TAC[var_res_permission_THM2] THEN
      FULL_SIMP_TAC std_ss [ASSOC_SYM] THEN
      Cases_on `var_res_permission_combine (SOME p) (SOME p')` THENL [
         FULL_SIMP_TAC std_ss [var_res_permission_THM2],
         METIS_TAC[]
      ],

      METIS_TAC[var_res_permission_THM2],
      METIS_TAC[var_res_permission_THM2],

      `(SOME p = var_res_permission_combine (SOME (var_res_permission_split p)) (SOME (var_res_permission_split p))) /\ (ASSOC var_res_permission_combine)` by
      METIS_TAC[var_res_permission_THM2] THEN
      FULL_SIMP_TAC std_ss [ASSOC_SYM] THEN
      METIS_TAC[var_res_permission_THM2]
   ]
);



val VAR_RES_STACK_COMBINE___SEPARATE_TO_BOTH = store_thm ("VAR_RES_STACK_COMBINE___SEPARATE_TO_BOTH",

``!s1 s2 s3 s12. (VAR_RES_STACK_COMBINE (SOME s1) (SOME s2) = SOME s12) /\
VAR_RES_STACK_IS_SEPARATE s12 s3 ==>
(VAR_RES_STACK_IS_SEPARATE s1 s3 /\ VAR_RES_STACK_IS_SEPARATE s2 s3)``,


SIMP_TAC std_ss [VAR_RES_STACK_COMBINE_def, BIN_OPTION_MAP_THM,
   COND_RAND, COND_RATOR, VAR_RES_STACK_COMBINE___MERGE_FUNC_def] THEN
SIMP_TAC std_ss [VAR_RES_STACK_IS_SEPARATE_def, FMERGE_DEF, IN_UNION,
   GSYM FORALL_AND_THM] THEN
REPEAT GEN_TAC THEN
HO_MATCH_MP_TAC (prove (``(!x. (P x ==> Q x)) ==> ((!x. P x) ==> (!x. Q x))``, METIS_TAC[])) THEN
GEN_TAC THEN STRIP_TAC THEN
REPEAT GEN_TAC THEN STRIP_TAC THEN STRIP_TAC THENL [
   `?v3 p3. s2 ' x = (v3, p3)` by METIS_TAC[pairTheory.PAIR] THEN
   FULL_SIMP_TAC std_ss [FORALL_AND_THM] THEN
   Cases_on `x IN FDOM s2` THEN FULL_SIMP_TAC std_ss [] THEN
   METIS_TAC[option_CLAUSES, ASSOC_DEF, COMM_DEF,
      var_res_permission_THM2],

   `?v3 p3. s1 ' x = (v3, p3)` by METIS_TAC[pairTheory.PAIR] THEN
   FULL_SIMP_TAC std_ss [FORALL_AND_THM] THEN
   Cases_on `x IN FDOM s1` THEN FULL_SIMP_TAC std_ss [] THEN
   METIS_TAC[option_CLAUSES, ASSOC_DEF, COMM_DEF,
      var_res_permission_THM2]
]);





val VAR_RES_STACK_COMBINE___IS_SEPARATION_ALGEBRA =
   store_thm ("VAR_RES_STACK_COMBINE___IS_SEPARATION_ALGEBRA",

   ``IS_SEPARATION_ALGEBRA VAR_RES_STACK_COMBINE FEMPTY``,


SIMP_TAC std_ss [IS_SEPARATION_ALGEBRA_def] THEN
REPEAT STRIP_TAC THENL [
   REWRITE_TAC [VAR_RES_STACK_COMBINE_REWRITE],
   REWRITE_TAC [VAR_RES_STACK_COMBINE_REWRITE],


   ASM_SIMP_TAC std_ss [VAR_RES_STACK_COMBINE_def,
      BIN_OPTION_MAP_THM] THEN
   REPEAT STRIP_TAC THENL [
      SIMP_TAC std_ss [COMM_DEF, VAR_RES_STACK_IS_SEPARATE___SYM],

      SIMP_TAC std_ss [GSYM fmap_EQ_THM, FMERGE_DEF, VAR_RES_STACK_COMBINE___MERGE_FUNC_def] THEN
      REPEAT STRIP_TAC THENL [
         PROVE_TAC [UNION_COMM],

         Cases_on `x IN FDOM x1` THEN Cases_on `x IN FDOM x2` THEN (
            FULL_SIMP_TAC std_ss [IN_UNION]
         ) THEN
         `?v1 p1. x1 ' x = (v1, p1)` by PROVE_TAC[pairTheory.PAIR] THEN
         `?v2 p2. x2 ' x = (v2, p2)` by PROVE_TAC[pairTheory.PAIR] THEN
         FULL_SIMP_TAC std_ss [VAR_RES_STACK_IS_SEPARATE_def] THEN
         RES_TAC THEN
         `COMM var_res_permission_combine` by REWRITE_TAC[var_res_permission_THM2] THEN
          FULL_SIMP_TAC std_ss [IS_SOME_EXISTS, COMM_DEF]
      ]
   ],


   SIMP_TAC std_ss [VAR_RES_STACK_COMBINE_def, BIN_OPTION_MAP_THM,
          VAR_RES_STACK_COMBINE___MERGE_FUNC_def] THEN
   SIMP_TAC std_ss [VAR_RES_STACK_IS_SEPARATE_def,
      FMERGE_DEF, IN_UNION] THEN
   REPEAT STRIP_TAC THENL [
      HO_MATCH_MP_TAC (prove (``(!x. (((P1 x) /\ (P2 x)) = ((P3 x) /\ (P4 x)))) ==>
         (((!x. P1 x) /\ (!x. P2 x)) = ((!x. P3 x) /\ (!x. P4 x)))``, METIS_TAC[])) THEN
      GEN_TAC THEN
      `?v1 p1. x1 ' x = (v1, p1)` by METIS_TAC[pairTheory.PAIR] THEN
      `?v2 p2. x2 ' x = (v2, p2)` by METIS_TAC[pairTheory.PAIR] THEN
      `?v3 p3. x3 ' x = (v3, p3)` by METIS_TAC[pairTheory.PAIR] THEN
      ASM_SIMP_TAC std_ss [] THEN

      Cases_on `x IN FDOM x1` THEN Cases_on `x IN FDOM x2` THEN Cases_on `x IN FDOM x3` THEN (
         ASM_SIMP_TAC std_ss [IN_UNION]
      ) THEN
      Cases_on `v2 = v1` THEN ASM_SIMP_TAC std_ss [] THEN
      Cases_on `v3 = v1` THEN ASM_SIMP_TAC std_ss [] THEN
      REPEAT (POP_ASSUM (K ALL_TAC)) THEN

      ASSUME_TAC var_res_permission_THM2 THEN
      FULL_SIMP_TAC std_ss [ASSOC_DEF, COMM_DEF] THEN

      Cases_on `var_res_permission_combine (SOME p1) (SOME p2)` THEN
      Cases_on `var_res_permission_combine (SOME p2) (SOME p3)` THEN
      ASM_SIMP_TAC std_ss [IS_SOME_EXISTS] THEN
      METIS_TAC[optionTheory.option_CLAUSES],



      SIMP_TAC std_ss [GSYM fmap_EQ_THM, FMERGE_DEF, UNION_ASSOC] THEN
      GEN_TAC THEN
      STRIP_TAC THEN
      REPEAT (Q.PAT_ASSUM `!x. X x` (
         MP_TAC o Q.SPECL [`x`])) THEN
      `?v1 p1. x1 ' x = (v1, p1)` by METIS_TAC[pairTheory.PAIR] THEN
      `?v2 p2. x2 ' x = (v2, p2)` by METIS_TAC[pairTheory.PAIR] THEN
      `?v3 p3. x3 ' x = (v3, p3)` by METIS_TAC[pairTheory.PAIR] THEN
      ASM_SIMP_TAC std_ss [] THEN
      Cases_on `x IN FDOM x1` THEN
      Cases_on `x IN FDOM x2` THEN
      Cases_on `x IN FDOM x3` THEN
      FULL_SIMP_TAC std_ss [IN_UNION] THEN

      Cases_on `v2 = v1` THEN ASM_SIMP_TAC std_ss [] THEN
      Cases_on `v3 = v1` THEN ASM_SIMP_TAC std_ss [] THEN
      REPEAT (POP_ASSUM (K ALL_TAC)) THEN

      ASSUME_TAC var_res_permission_THM2 THEN
      FULL_SIMP_TAC std_ss [ASSOC_DEF, COMM_DEF] THEN
      ASM_SIMP_TAC std_ss [IS_SOME_EXISTS, GSYM LEFT_FORALL_IMP_THM] THEN
      METIS_TAC[optionTheory.option_CLAUSES]
   ],



   SIMP_TAC std_ss [VAR_RES_STACK_COMBINE_def, BIN_OPTION_MAP_THM,
          VAR_RES_STACK_COMBINE___MERGE_FUNC_def] THEN
   SIMP_TAC std_ss [GSYM fmap_EQ_THM, FMERGE_DEF] THEN
   REPEAT GEN_TAC THEN
   STRIP_TAC THEN
   FULL_SIMP_TAC std_ss [EXTENSION, IN_UNION, GSYM FORALL_AND_THM] THEN
   GEN_TAC THEN
   REPEAT (Q.PAT_ASSUM `!x. X x` (
      MP_TAC o Q.SPECL [`x`])) THEN
   `?v1 p1. x1 ' x = (v1, p1)` by METIS_TAC[pairTheory.PAIR] THEN
   `?v2 p2. x2 ' x = (v2, p2)` by METIS_TAC[pairTheory.PAIR] THEN
   `?v3 p3. x3 ' x = (v3, p3)` by METIS_TAC[pairTheory.PAIR] THEN
   ASM_SIMP_TAC std_ss [] THEN
   Cases_on `x IN FDOM x1` THEN
   Cases_on `x IN FDOM x2` THEN
   Cases_on `x IN FDOM x3` THEN
   FULL_SIMP_TAC std_ss [] THEN (
      REPEAT (Q.PAT_ASSUM `VAR_RES_STACK_IS_SEPARATE X Y` (MP_TAC o
         Q.SPEC `x` o REWRITE_RULE [VAR_RES_STACK_IS_SEPARATE_def])) THEN
      ASM_SIMP_TAC std_ss [IS_SOME_EXISTS, GSYM LEFT_EXISTS_AND_THM,
         GSYM RIGHT_EXISTS_AND_THM, GSYM LEFT_FORALL_IMP_THM] THEN
      METIS_TAC[var_res_permission_THM2, OPTION_IS_LEFT_CANCELLATIVE_def, option_CLAUSES]
   )
]);



val VAR_RES_STACK_COMBINE___IS_SEPARATION_COMBINATOR =
   store_thm ("VAR_RES_STACK_COMBINE___IS_SEPARATION_COMBINATOR",

   ``IS_SEPARATION_COMBINATOR VAR_RES_STACK_COMBINE``,

MATCH_MP_TAC IS_SEPARATION_ALGEBRA___IS_COMBINATOR THEN
Q.EXISTS_TAC `FEMPTY` THEN
REWRITE_TAC[VAR_RES_STACK_COMBINE___IS_SEPARATION_ALGEBRA]);



val VAR_RES_STACK_COMBINE___COMM = store_thm ("VAR_RES_STACK_COMBINE___COMM",
   ``!X Y. VAR_RES_STACK_COMBINE X Y = VAR_RES_STACK_COMBINE Y X``,
METIS_TAC[VAR_RES_STACK_COMBINE___IS_SEPARATION_ALGEBRA,
          IS_SEPARATION_ALGEBRA_def, COMM_DEF]);






val asl_emp___VAR_RES_STACK_COMBINE = store_thm ("asl_emp___VAR_RES_STACK_COMBINE",
``asl_emp VAR_RES_STACK_COMBINE = {FEMPTY}``,

SIMP_TAC std_ss [asl_emp_def, EXTENSION, IN_ABS, IN_SING,
   VAR_RES_STACK_COMBINE_REWRITE])





val var_res_sl___star_def = Define `var_res_sl___star = asl_star VAR_RES_STACK_COMBINE`

val var_res_sl___value_perm_of_def = Define `
   var_res_sl___value_perm_of pvar (value,perm:var_res_permission) =  {FEMPTY |+ (pvar, (value, perm))}`;

val var_res_sl___value_of_def = Define `
   var_res_sl___value_of pvar value = asl_exists perm. var_res_sl___value_perm_of pvar (value, perm)`;

val var_res_sl___own_def = Define `
   var_res_sl___own perm pvar = asl_exists v. var_res_sl___value_perm_of pvar (v, perm)`;



val var_res_sl___value_perm_of___asl_star = store_thm ("var_res_sl___value_perm_of___asl_star",
``!pvar v1 p1 v2 p2.
(var_res_sl___star (var_res_sl___value_perm_of pvar (v1,p1)) (var_res_sl___value_perm_of pvar (v2,p2))) =
if ((v1 = v2) /\ IS_SOME (var_res_permission_combine (SOME p1) (SOME p2))) then
(var_res_sl___value_perm_of pvar (v1, THE (var_res_permission_combine (SOME p1) (SOME p2)))) else asl_false``,

SIMP_TAC std_ss [EXTENSION, var_res_sl___star_def,
   asl_star_def, IN_ABS,
   var_res_sl___value_perm_of_def,
   IN_SING, SOME___VAR_RES_STACK_COMBINE] THEN
SIMP_TAC std_ss [
   VAR_RES_STACK_IS_SEPARATE_def, FDOM_FUPDATE, FDOM_FEMPTY,
   IN_SING, FAPPLY_FUPDATE_THM] THEN
REPEAT GEN_TAC THEN
Tactical.REVERSE (Cases_on `v1 = v2`) THEN1 (
   ASM_SIMP_TAC std_ss [asl_false_def, NOT_IN_EMPTY]
) THEN
Cases_on `var_res_permission_combine (SOME p1) (SOME p2)` THEN1 (
   ASM_SIMP_TAC std_ss [asl_false_def, NOT_IN_EMPTY]
) THEN
ASM_SIMP_TAC std_ss [IN_ABS, GSYM fmap_EQ_THM, IN_SING] THEN
SIMP_TAC std_ss [FDOM_FEMPTY, FDOM_FUPDATE, FMERGE_DEF,
   IN_SING, UNION_IDEMPOT] THEN
Cases_on `FDOM x = {pvar}` THEN ASM_REWRITE_TAC[] THEN
ASM_SIMP_TAC std_ss [IN_SING, FAPPLY_FUPDATE_THM, IS_SOME_EXISTS,
   VAR_RES_STACK_COMBINE___MERGE_FUNC_def]);





val var_res_sl___value_of___asl_star = store_thm ("var_res_sl___value_of___asl_star",
``!pvar v1 v2.
(var_res_sl___star ((var_res_sl___value_of pvar v1)) (var_res_sl___value_of pvar v2)) =
if (v1 = v2) then
(var_res_sl___value_of pvar v1) else asl_false``,


SIMP_TAC std_ss [EXTENSION, var_res_sl___star_def,
   var_res_sl___value_of_def,
   GSYM asl_exists___asl_star_THM] THEN
SIMP_TAC std_ss [var_res_sl___value_perm_of___asl_star,
   GSYM var_res_sl___star_def] THEN
REPEAT STRIP_TAC THEN
Cases_on `v1 = v2` THENL [
   ASM_SIMP_TAC std_ss [asl_exists_def, IN_ABS,
      COND_RAND, COND_RATOR, asl_false_def,
      NOT_IN_EMPTY] THEN
   METIS_TAC[var_res_permission_THM2, option_CLAUSES],

   ASM_SIMP_TAC std_ss [asl_exists_def, IN_ABS]
]);





val var_res_sl___own___asl_star = store_thm ("var_res_sl___own___asl_star",
``!pvar p1 p2.
(var_res_sl___star ((var_res_sl___own p1 pvar)) (var_res_sl___own p2 pvar)) =
if (IS_SOME (var_res_permission_combine (SOME p1) (SOME p2))) then
(var_res_sl___own (THE ((var_res_permission_combine (SOME p1) (SOME p2)))) pvar) else asl_false``,


SIMP_TAC std_ss [EXTENSION, var_res_sl___star_def,
   var_res_sl___own_def,
   GSYM asl_exists___asl_star_THM] THEN
SIMP_TAC std_ss [var_res_sl___value_perm_of___asl_star,
   GSYM var_res_sl___star_def] THEN
REPEAT STRIP_TAC THEN
Cases_on `IS_SOME (var_res_permission_combine (SOME p1) (SOME p2))` THENL [
   ASM_SIMP_TAC std_ss [asl_exists_def, IN_ABS,
      COND_RAND, COND_RATOR, asl_false_def,
      NOT_IN_EMPTY],

   ASM_SIMP_TAC std_ss [asl_exists_def, IN_ABS]
]);



val var_res_sl___read_def = Define `
   var_res_sl___read v s =
   if ~(v IN FDOM s) then NONE else
      SOME (s ' v)`

val var_res_sl___read_val_def = Define `
   var_res_sl___read_val v s =
   if ~(v IN FDOM s) then NONE else
      SOME (FST (s ' v))`


val var_res_sl___has_read_permission_def = Define `
   var_res_sl___has_read_permission v s =
   v IN FDOM s`

val var_res_sl___has_write_permission_def = Define `
   var_res_sl___has_write_permission v s =
   (v IN FDOM s) /\ (SND (s ' v) = var_res_write_permission)`



val var_res_sl___has_read_write_permission___read =
store_thm ("var_res_sl___has_read_write_permission___read",
``(var_res_sl___has_read_permission v s =
   IS_SOME (var_res_sl___read v s)) /\

  (var_res_sl___has_write_permission v s =
  (?x. (var_res_sl___read v s = SOME (x, var_res_write_permission))))``,

SIMP_TAC std_ss [var_res_sl___has_write_permission_def,
var_res_sl___has_read_permission_def, var_res_sl___read_def,
   COND_NONE_SOME_REWRITES] THEN
Cases_on `s ' v` THEN
SIMP_TAC std_ss []);




val var_res_sl___has_read_permission_THM = store_thm ("var_res_sl___has_read_permission_THM",
``var_res_sl___has_read_permission v = var_res_sl___star (asl_exists p. var_res_sl___own p v) asl_true``,

SIMP_TAC std_ss [FUN_EQ_THM, var_res_sl___star_def,
   asl_star_def, asl_exists_def, IN_ABS, var_res_sl___own_def,
   var_res_sl___value_perm_of_def, IN_SING, asl_true_def, IN_UNIV,
   GSYM RIGHT_EXISTS_AND_THM, var_res_sl___has_read_permission_def] THEN
GEN_TAC THEN
Cases_on `v IN FDOM x` THENL [
   ASM_SIMP_TAC std_ss [] THEN
   `?X. x ' v = X` by METIS_TAC[] THEN
   Cases_on `X` THEN
   Q.EXISTS_TAC `x \\ v` THEN
   Q.EXISTS_TAC `r` THEN
   Q.EXISTS_TAC `q` THEN
   SIMP_TAC std_ss [VAR_RES_STACK_COMBINE_def, BIN_OPTION_MAP_THM,
      VAR_RES_STACK_IS_SEPARATE_def, FDOM_FUPDATE,
      IN_INSERT, FDOM_FEMPTY, NOT_IN_EMPTY, FDOM_DOMSUB, IN_DELETE,
      GSYM fmap_EQ_THM, FMERGE_DEF,
      EXTENSION, IN_UNION, DOMSUB_FAPPLY_NEQ, FAPPLY_FUPDATE_THM] THEN
   METIS_TAC[],

   ASM_SIMP_TAC std_ss [VAR_RES_STACK_COMBINE_def,
      BIN_OPTION_MAP_THM, GSYM fmap_EQ_THM, FMERGE_DEF,
      FDOM_FUPDATE, FDOM_FEMPTY, IN_SING] THEN
   REPEAT STRIP_TAC THEN
   MATCH_MP_TAC (prove (``(~B) ==> (~A \/ ~B \/ C)``, METIS_TAC[])) THEN
   CCONTR_TAC THEN
   POP_ASSUM (ASSUME_TAC o GSYM) THEN
   FULL_SIMP_TAC std_ss [IN_UNION, IN_SING]
]);



val var_res_sl___has_write_permission_THM = store_thm ("var_res_sl___has_write_permission_THM",
``var_res_sl___has_write_permission v = var_res_sl___star (var_res_sl___own var_res_write_permission v) asl_true``,

SIMP_TAC std_ss [FUN_EQ_THM, var_res_sl___star_def,
   asl_star_def, asl_exists_def, IN_ABS, var_res_sl___own_def,
   var_res_sl___value_perm_of_def, IN_SING, asl_true_def, IN_UNIV,
   GSYM RIGHT_EXISTS_AND_THM, var_res_sl___has_write_permission_def] THEN
GEN_TAC THEN
Cases_on `v IN FDOM x` THENL [
   Cases_on `x ' v` THEN
   ASM_SIMP_TAC std_ss [] THEN
   SIMP_TAC std_ss [VAR_RES_STACK_COMBINE_def, BIN_OPTION_MAP_THM,
      VAR_RES_STACK_IS_SEPARATE_def, FDOM_FUPDATE, COND_RAND, COND_RATOR] THEN
   SIMP_TAC std_ss [IN_INSERT, NOT_IN_EMPTY, FDOM_FEMPTY, FAPPLY_FUPDATE_THM,
      var_res_permission_THM2] THEN
   SIMP_TAC std_ss [GSYM fmap_EQ_THM, FMERGE_DEF, FDOM_FUPDATE,
      FDOM_FEMPTY, IN_INSERT, NOT_IN_EMPTY, FAPPLY_FUPDATE_THM,
      var_res_permission_THM2] THEN
   EQ_TAC THENL [
      STRIP_TAC THEN
      Q.EXISTS_TAC `x \\ v` THEN
      Q.EXISTS_TAC `q` THEN
      ASM_SIMP_TAC std_ss [FDOM_DOMSUB, IN_UNION, IN_DELETE, IN_SING,
         DOMSUB_FAPPLY_NEQ, EXTENSION] THEN
      METIS_TAC[],

      STRIP_TAC THEN
      Q.PAT_ASSUM `!x''. X` (MP_TAC o Q.SPEC `v`) THEN
      ASM_SIMP_TAC std_ss [IN_UNION, IN_SING]
   ],

   ASM_SIMP_TAC std_ss [VAR_RES_STACK_COMBINE_def,
      BIN_OPTION_MAP_THM, COND_RAND, COND_RATOR] THEN
   ASM_SIMP_TAC std_ss [GSYM fmap_EQ_THM, FMERGE_DEF,
      FDOM_FUPDATE, FDOM_FEMPTY, IN_SING] THEN
   REPEAT STRIP_TAC THEN
   MATCH_MP_TAC (prove (``(~B) ==> (~A \/ ~B \/ C)``, METIS_TAC[])) THEN
   CCONTR_TAC THEN
   POP_ASSUM (ASSUME_TAC o GSYM) THEN
   FULL_SIMP_TAC std_ss [IN_UNION, IN_SING]
]);






val VAR_RES_STACK_IS_SUBSTATE_def = Define `
    VAR_RES_STACK_IS_SUBSTATE = ASL_IS_SUBSTATE VAR_RES_STACK_COMBINE`


val VAR_RES_STACK_IS_SUBSTATE_REWRITE = store_thm ("VAR_RES_STACK_IS_SUBSTATE_REWRITE",
``VAR_RES_STACK_IS_SUBSTATE st1 st2 =

  ((FDOM st1 SUBSET FDOM st2) /\
  (!v. v IN FDOM st1 ==>
       (FST (st1 ' v) = FST (st2 ' v)) /\
       (IS_VAR_RES_SUBPERMISSION (SND (st1 ' v)) (SND (st2 ' v)))))``,


SIMP_TAC std_ss [VAR_RES_STACK_IS_SUBSTATE_def,
       ASL_IS_SUBSTATE_def,
       SOME___VAR_RES_STACK_COMBINE,
       IS_VAR_RES_SUBPERMISSION_def,
       VAR_RES_STACK_IS_SEPARATE_def] THEN
REPEAT STRIP_TAC THEN EQ_TAC THEN STRIP_TAC THENL [
    ASM_SIMP_TAC std_ss [FMERGE_DEF, SUBSET_UNION] THEN
    GEN_TAC THEN STRIP_TAC THEN
    Cases_on `v IN FDOM s1` THEN ASM_REWRITE_TAC[] THEN
    FULL_SIMP_TAC std_ss [VAR_RES_STACK_COMBINE___MERGE_FUNC_def,
           VAR_RES_STACK_IS_SEPARATE_def] THEN
    METIS_TAC[option_CLAUSES],


    Q.ABBREV_TAC `s1dom = \x. ((x IN (FDOM st2)) /\
          (~(x IN FDOM st1) \/ ~(SND (st1 ' x) = SND (st2 ' x))))` THEN
    Q.ABBREV_TAC `s1def = \x. if ~(x IN FDOM st1) then st2 ' x else (FST (st1 ' x),
                         (@p. var_res_permission_combine (SOME (SND (st1 ' x))) (SOME p) =
                             SOME (SND (st2 ' x))))` THEN
    Q.EXISTS_TAC `FUN_FMAP s1def s1dom` THEN
    `FINITE s1dom` by ALL_TAC THEN1 (
       `s1dom SUBSET FDOM st2` by (UNABBREV_ALL_TAC THEN SIMP_TAC std_ss [SUBSET_DEF, IN_ABS]) THEN
       METIS_TAC[SUBSET_FINITE, FDOM_FINITE]
    ) THEN
    ASM_SIMP_TAC std_ss [GSYM fmap_EQ_THM, FUN_FMAP_DEF,
          FMERGE_DEF] THEN
    REPEAT STRIP_TAC THENL [
       UNABBREV_ALL_TAC THEN
       ASM_SIMP_TAC std_ss [],


       UNABBREV_ALL_TAC THEN
       ASM_SIMP_TAC std_ss [] THEN
       SELECT_ELIM_TAC THEN
       SIMP_TAC std_ss [] THEN
       FULL_SIMP_TAC std_ss [IN_ABS] THEN
       METIS_TAC[],


       UNABBREV_ALL_TAC THEN
       FULL_SIMP_TAC std_ss [EXTENSION, IN_ABS, IN_UNION, SUBSET_DEF] THEN
       METIS_TAC[],


       Cases_on `st1 ' x` THEN
       Cases_on `st2 ' x` THEN
       Q.PAT_ASSUM `!v. v IN FDOM st1 ==> X v` (MP_TAC o Q.SPEC `x`) THEN
       UNABBREV_ALL_TAC THEN
       ASM_SIMP_TAC std_ss [IN_ABS, FUN_FMAP_DEF] THEN
       SIMP_TAC std_ss [COND_RATOR, COND_RAND] THEN
       Cases_on `x IN FDOM st1` THEN ASM_REWRITE_TAC[] THEN
       Cases_on `r = r'` THEN ASM_REWRITE_TAC[] THEN
       STRIP_TAC THEN
       SELECT_ELIM_TAC THEN
       SIMP_TAC std_ss [VAR_RES_STACK_COMBINE___MERGE_FUNC_def] THEN
       METIS_TAC[]
   ]
]);



val VAR_RES_STACK_IS_SUBSTATE_INTRO = store_thm ("VAR_RES_STACK_IS_SUBSTATE_INTRO",
``!x1 x2 x.
   (VAR_RES_STACK_COMBINE (SOME x1) (SOME x2) = SOME x) ==>
   (VAR_RES_STACK_IS_SUBSTATE x1 x /\
    VAR_RES_STACK_IS_SUBSTATE x2 x)``,

SIMP_TAC std_ss [VAR_RES_STACK_IS_SUBSTATE_def,
       ASL_IS_SUBSTATE_def] THEN
ASSUME_TAC VAR_RES_STACK_COMBINE___IS_SEPARATION_COMBINATOR THEN
FULL_SIMP_TAC std_ss [IS_SEPARATION_COMBINATOR_def, COMM_DEF] THEN
METIS_TAC[]);






val VAR_RES_STACK_IS_SUBSTATE___IS_PREORDER = store_thm ("VAR_RES_STACK_IS_SUBSTATE___IS_PREORDER",
``PreOrder VAR_RES_STACK_IS_SUBSTATE``,

SIMP_TAC std_ss [VAR_RES_STACK_IS_SUBSTATE_def, ASL_IS_SUBSTATE___IS_PREORDER,
       VAR_RES_STACK_COMBINE___IS_SEPARATION_COMBINATOR]);



val VAR_RES_STACK_IS_SUBSTATE___TRANS = save_thm ("VAR_RES_STACK_IS_SUBSTATE___TRANS",
CONJUNCT2 (
REWRITE_RULE [PreOrder, transitive_def] VAR_RES_STACK_IS_SUBSTATE___IS_PREORDER));


val VAR_RES_STACK_IS_SUBSTATE___REFL = save_thm ("VAR_RES_STACK_IS_SUBSTATE___REFL",
CONJUNCT1 (
REWRITE_RULE [PreOrder, reflexive_def] VAR_RES_STACK_IS_SUBSTATE___IS_PREORDER));



val VAR_RES_STACK_IS_SUBSTATE___ANTISYM = store_thm ("VAR_RES_STACK_IS_SUBSTATE___ANTISYM",
``
(VAR_RES_STACK_IS_SUBSTATE st1 st2 /\
VAR_RES_STACK_IS_SUBSTATE st2 st1) ==>

(st1 = st2)``,

SIMP_TAC std_ss [VAR_RES_STACK_IS_SUBSTATE_REWRITE] THEN
REPEAT STRIP_TAC THEN
`FDOM st2 = FDOM st1` by PROVE_TAC[SUBSET_ANTISYM] THEN
ASM_SIMP_TAC std_ss [GSYM fmap_EQ_THM] THEN
REPEAT STRIP_TAC THEN
ONCE_REWRITE_TAC[GSYM pairTheory.PAIR] THEN
SIMP_TAC std_ss [] THEN
`x IN FDOM st2` by PROVE_TAC[] THEN
RES_TAC THEN
METIS_TAC[IS_VAR_RES_SUBPERMISSION_THM]);





val VAR_RES_STACK_SPLIT_def = Define `
   VAR_RES_STACK_SPLIT wp1 wp2 st =
   FUN_FMAP (\var. let (v,p) = st ' var in
                        if (var IN wp1) then (v, p) else
                           (v, var_res_permission_split p)) (FDOM st DIFF wp2)`



val VAR_RES_STACK_SPLIT1_def = Define `
        VAR_RES_STACK_SPLIT1 wp st =
        FUN_FMAP (\var. let (v,p) = st ' var in
                        if (var IN wp) then (v, p) else
                           (v, var_res_permission_split p)) (FDOM st)`


val VAR_RES_STACK_SPLIT2_def = Define `
        VAR_RES_STACK_SPLIT2 wp st =
        FUN_FMAP (\var. let (v,p) = st ' var in
                        (v, var_res_permission_split p)) (FDOM st DIFF wp)`


val VAR_RES_STACK_SPLIT12___DEF = store_thm (
 "VAR_RES_STACK_SPLIT12___DEF",
``(VAR_RES_STACK_SPLIT1 wp st =
  VAR_RES_STACK_SPLIT wp {} st) /\

(VAR_RES_STACK_SPLIT2 wp st =
  VAR_RES_STACK_SPLIT {} wp st)``,

SIMP_TAC std_ss [VAR_RES_STACK_SPLIT1_def, VAR_RES_STACK_SPLIT2_def,
       VAR_RES_STACK_SPLIT_def, DIFF_EMPTY,
       NOT_IN_EMPTY]);



val VAR_RES_STACK_SPLIT___REWRITES = store_thm ("VAR_RES_STACK_SPLIT___REWRITES",
``(!wp1 wp2 st. (FDOM (VAR_RES_STACK_SPLIT wp1 wp2 st) =  FDOM st DIFF wp2)) /\
  (!wp1 wp2 st v. (v IN FDOM st) /\ ~(v IN wp2) ==>
         ((VAR_RES_STACK_SPLIT wp1 wp2 st) ' v =  (FST (st ' v),
                                                  (if (v IN wp1) then SND (st ' v) else
                    (var_res_permission_split (SND (st ' v)))))))``,


SIMP_TAC std_ss [VAR_RES_STACK_SPLIT_def, FUN_FMAP_DEF, FDOM_FINITE, FINITE_DIFF, IN_DIFF,
       LET_THM, GSYM PAIR_BETA_THM, COND_RATOR, COND_RAND]);


val VAR_RES_STACK_SPLIT12___REWRITES = store_thm ("VAR_RES_STACK_SPLIT12___REWRITES",
``(!wp st. (FDOM (VAR_RES_STACK_SPLIT1 wp st) =  FDOM st)) /\
  (!wp st. (FDOM (VAR_RES_STACK_SPLIT2 wp st) =  FDOM st DIFF wp)) /\
  (!wp st v. (v IN FDOM st)  ==>
         ((VAR_RES_STACK_SPLIT1 wp st) ' v =  (FST (st ' v),
                                                  (if (v IN wp) then SND (st ' v) else
                    (var_res_permission_split (SND (st ' v))))))) /\
  (!wp st v. (v IN FDOM st) /\ ~(v IN wp) ==>
         ((VAR_RES_STACK_SPLIT2 wp st) ' v =  (FST (st ' v),
                                              (var_res_permission_split (SND (st ' v))))))``,

SIMP_TAC std_ss [VAR_RES_STACK_SPLIT12___DEF, VAR_RES_STACK_SPLIT___REWRITES,
       NOT_IN_EMPTY, DIFF_EMPTY]);



val VAR_RES_STACK_IS_SEPARATE___VAR_RES_STACK_SPLIT =
store_thm ("VAR_RES_STACK_IS_SEPARATE___VAR_RES_STACK_SPLIT",
``VAR_RES_STACK_IS_SEPARATE (VAR_RES_STACK_SPLIT wp1 wp2 s) (VAR_RES_STACK_SPLIT wp2 wp1 s)``,

SIMP_TAC std_ss [VAR_RES_STACK_IS_SEPARATE_def,
                 VAR_RES_STACK_SPLIT___REWRITES, IN_DIFF,
       var_res_permission_THM2]);




val VAR_RES_STACK_IS_SEPARATE___VAR_RES_STACK_SPLIT12 =
store_thm ("VAR_RES_STACK_IS_SEPARATE___VAR_RES_STACK_SPLIT12",
``VAR_RES_STACK_IS_SEPARATE (VAR_RES_STACK_SPLIT1 wp s) (VAR_RES_STACK_SPLIT2 wp s)``,

SIMP_TAC std_ss [VAR_RES_STACK_SPLIT12___DEF,
       VAR_RES_STACK_IS_SEPARATE___VAR_RES_STACK_SPLIT]);





val VAR_RES_STACK_COMBINE___VAR_RES_STACK_SPLIT =
store_thm ("VAR_RES_STACK_COMBINE___VAR_RES_STACK_SPLIT",
``!s wp1 wp2. VAR_RES_STACK_COMBINE (SOME (VAR_RES_STACK_SPLIT wp1 wp2 s))
                        (SOME (VAR_RES_STACK_SPLIT wp2 wp1 s)) =
              SOME (DRESTRICT s (COMPL (wp1 INTER wp2)))``,

SIMP_TAC std_ss [SOME___VAR_RES_STACK_COMBINE,
   VAR_RES_STACK_IS_SEPARATE___VAR_RES_STACK_SPLIT,
   GSYM fmap_EQ_THM, FMERGE_DEF, FDOM_DRESTRICT, EXTENSION,
   IN_INTER, VAR_RES_STACK_SPLIT___REWRITES, IN_COMPL, IN_INTER, IN_DIFF,
   IN_UNION, VAR_RES_STACK_COMBINE___MERGE_FUNC_def,
   var_res_permission_THM2, DRESTRICT_DEF] THEN
SIMP_TAC std_ss [COND_RAND, COND_RATOR, COND_ABS,
       LEFT_AND_OVER_OR, DISJ_IMP_THM, VAR_RES_STACK_SPLIT___REWRITES] THEN
METIS_TAC[]);




val VAR_RES_STACK_COMBINE___VAR_RES_STACK_SPLIT12 =
store_thm ("VAR_RES_STACK_COMBINE___VAR_RES_STACK_SPLIT12",

``!s wp. VAR_RES_STACK_COMBINE (SOME (VAR_RES_STACK_SPLIT1 wp s))
                        (SOME (VAR_RES_STACK_SPLIT2 wp s)) =
              SOME s``,

SIMP_TAC std_ss [VAR_RES_STACK_SPLIT12___DEF,
       VAR_RES_STACK_COMBINE___VAR_RES_STACK_SPLIT,
       INTER_EMPTY, COMPL_EMPTY, DRESTRICT_UNIV]);






val VAR_RES_STACK_SPLIT___read_writes = store_thm (
"VAR_RES_STACK_SPLIT___read_writes",

``(~(v IN wp2) ==>
(var_res_sl___read_val v (VAR_RES_STACK_SPLIT wp1 wp2 s) =
 var_res_sl___read_val v s)) /\

(((v IN wp1) /\ ~(v IN wp2)) ==>
(var_res_sl___read v (VAR_RES_STACK_SPLIT wp1 wp2 s) =
 var_res_sl___read v s)) /\


(var_res_sl___has_read_permission v (VAR_RES_STACK_SPLIT wp1 wp2 s) =
var_res_sl___has_read_permission v s /\ ~(v IN wp2)) /\

(var_res_sl___has_write_permission v (VAR_RES_STACK_SPLIT wp1 wp2 s) =
var_res_sl___has_write_permission v s /\ (v IN wp1) /\ ~(v IN wp2))``,


SIMP_TAC std_ss [var_res_sl___has_write_permission_def,
       var_res_sl___has_read_permission_def,
       VAR_RES_STACK_SPLIT___REWRITES, IN_DIFF,
       var_res_sl___read_def,
       var_res_sl___read_val_def] THEN
Cases_on `v IN FDOM s` THEN ASM_REWRITE_TAC[] THEN
Cases_on `v IN wp2` THEN ASM_REWRITE_TAC[] THEN
ASM_SIMP_TAC std_ss [VAR_RES_STACK_SPLIT___REWRITES, COND_RATOR, COND_RAND,
           var_res_permission_THM2] THEN
Cases_on `s ' v` THEN
SIMP_TAC std_ss [] THEN
PROVE_TAC[])





val VAR_RES_STACK_SPLIT12___read_writes = store_thm (
"VAR_RES_STACK_SPLIT12___read_writes",

``(var_res_sl___read_val v (VAR_RES_STACK_SPLIT1 wp s) =
 var_res_sl___read_val v s) /\

((v IN wp) ==>
(var_res_sl___read v (VAR_RES_STACK_SPLIT1 wp s) =
 var_res_sl___read v s)) /\

(~(v IN wp) ==>
(var_res_sl___read_val v (VAR_RES_STACK_SPLIT2 wp s) =
 var_res_sl___read_val v s)) /\

(var_res_sl___has_read_permission v (VAR_RES_STACK_SPLIT1 wp s) =
var_res_sl___has_read_permission v s) /\
(var_res_sl___has_read_permission v (VAR_RES_STACK_SPLIT2 wp s) =
var_res_sl___has_read_permission v s /\ ~(v IN wp)) /\

(var_res_sl___has_write_permission v (VAR_RES_STACK_SPLIT1 wp s) =
var_res_sl___has_write_permission v s /\ (v IN wp)) /\
(~(var_res_sl___has_write_permission v (VAR_RES_STACK_SPLIT2 wp s)))``,


SIMP_TAC std_ss [VAR_RES_STACK_SPLIT12___DEF,
       VAR_RES_STACK_SPLIT___read_writes,
       NOT_IN_EMPTY]);



val VAR_RES_STACK___IS_SUBSTATE_UPTO_PERMISSIONS_def = Define `
    VAR_RES_STACK___IS_SUBSTATE_UPTO_PERMISSIONS exS st1 st2 =

    ((FDOM st1) SUBSET (FDOM st2)) /\ (!v. v IN FDOM st1 ==>
                   (FST (st1 ' v) = FST (st2 ' v))) /\
                             (!v. (v IN (FDOM st1) /\ v IN exS) ==>
                                  (IS_VAR_RES_SUBPERMISSION (SND (st1 ' v)) (SND (st2 ' v))))`;


val VAR_RES_STACK___IS_EQUAL_UPTO_PERMISSIONS_def = Define `
    VAR_RES_STACK___IS_EQUAL_UPTO_PERMISSIONS exS (st1:('a, 'b) var_res_state) st2 =
    (FDOM st1 = FDOM st2) /\ (!v. v IN FDOM st1 ==>
                   (FST (st1 ' v) = FST (st2 ' v))) /\
                             (!v. (v IN (FDOM st1) /\ v IN exS) ==>
                                  ((st1 ' v) = (st2 ' v)))`;

val VAR_RES_STACK___IS_SUBSTATE_UPTO_PERMISSIONS___UNIV =
store_thm ("VAR_RES_STACK___IS_SUBSTATE_UPTO_PERMISSIONS___UNIV",
``
VAR_RES_STACK___IS_SUBSTATE_UPTO_PERMISSIONS UNIV st1 st2 =
VAR_RES_STACK_IS_SUBSTATE st1 st2``,

SIMP_TAC std_ss [VAR_RES_STACK_IS_SUBSTATE_REWRITE,
       VAR_RES_STACK___IS_SUBSTATE_UPTO_PERMISSIONS_def,
       IN_UNIV] THEN
EQ_TAC THEN SIMP_TAC std_ss []);



val VAR_RES_STACK___IS_EQUAL_UPTO_PERMISSIONS___UNIV =
store_thm ("VAR_RES_STACK___IS_EQUAL_UPTO_PERMISSIONS___UNIV",
``
VAR_RES_STACK___IS_EQUAL_UPTO_PERMISSIONS UNIV st1 st2 =
(st1 = st2)``,

SIMP_TAC std_ss [VAR_RES_STACK___IS_EQUAL_UPTO_PERMISSIONS_def,
       IN_UNIV] THEN
EQ_TAC THEN
SIMP_TAC std_ss [GSYM fmap_EQ_THM]);



val VAR_RES_STACK___IS_EQUAL_UPTO_PERMISSIONS___ALTERNATIVE_DEF =
store_thm ("VAR_RES_STACK___IS_EQUAL_UPTO_PERMISSIONS___ALTERNATIVE_DEF",
``!exS st1 st2.
VAR_RES_STACK___IS_EQUAL_UPTO_PERMISSIONS exS st1 st2 =
(VAR_RES_STACK___IS_SUBSTATE_UPTO_PERMISSIONS exS st1 st2 /\
VAR_RES_STACK___IS_SUBSTATE_UPTO_PERMISSIONS exS st2 st1)``,


SIMP_TAC std_ss [VAR_RES_STACK___IS_SUBSTATE_UPTO_PERMISSIONS_def,
       VAR_RES_STACK___IS_EQUAL_UPTO_PERMISSIONS_def] THEN
REPEAT STRIP_TAC THEN EQ_TAC THEN STRIP_TAC THENL [
   ASM_SIMP_TAC std_ss [SUBSET_REFL, IS_VAR_RES_SUBPERMISSION_THM],

   ASM_SIMP_TAC std_ss [SUBSET_ANTISYM] THEN
   REPEAT STRIP_TAC THEN
   RES_TAC THEN
   `v IN FDOM st2` by PROVE_TAC[SUBSET_DEF] THEN
   Cases_on `st1 ' v` THEN
   Cases_on `st2 ' v` THEN
   FULL_SIMP_TAC std_ss [] THEN
   METIS_TAC[IS_VAR_RES_SUBPERMISSION_THM]
]);




val VAR_RES_STACK___UPDATE_PERMISSION_def = Define `
    VAR_RES_STACK___UPDATE_PERMISSION v p st =
    if (v IN FDOM st) then st |+ (v, FST (st ' v), p) else st`


val VAR_RES_STACK___UPDATE_PERMISSION_ALL_def = Define `
    VAR_RES_STACK___UPDATE_PERMISSION_ALL f st =
    FUN_FMAP (\v. if IS_SOME (f v) then (FST (st ' v), THE (f v)) else st ' v)
             (FDOM st)`;

val VAR_RES_STACK___UPDATE_PERMISSION___ALTERNATIVE_DEF = store_thm
 ("VAR_RES_STACK___UPDATE_PERMISSION___ALTERNATIVE_DEF",
``  VAR_RES_STACK___UPDATE_PERMISSION v p st =
  VAR_RES_STACK___UPDATE_PERMISSION_ALL
      (\x. if (x = v) then (SOME p) else NONE) st``,

SIMP_TAC std_ss [GSYM fmap_EQ_THM, EXTENSION,
       VAR_RES_STACK___UPDATE_PERMISSION_ALL_def,
       VAR_RES_STACK___UPDATE_PERMISSION_def,
       FUN_FMAP_DEF, COND_NONE_SOME_REWRITES,
       FDOM_FINITE] THEN
Cases_on `v IN FDOM st` THENL [
   ASM_SIMP_TAC std_ss [FDOM_FUPDATE, IN_INSERT, FAPPLY_FUPDATE_THM,
              FUN_FMAP_DEF] THEN
   REPEAT STRIP_TAC THENL [
      PROVE_TAC[],
      ASM_SIMP_TAC std_ss [FUN_FMAP_DEF, FDOM_FINITE],
      ASM_SIMP_TAC std_ss [FUN_FMAP_DEF, FDOM_FINITE]
   ],


   ASM_SIMP_TAC std_ss [FUN_FMAP_DEF, FDOM_FINITE] THEN
   PROVE_TAC[]
]);



val VAR_RES_STACK___IS_EQUAL_UPTO_PERMISSIONS_THM = store_thm (
"VAR_RES_STACK___IS_EQUAL_UPTO_PERMISSIONS_THM",
``
COMM (VAR_RES_STACK___IS_EQUAL_UPTO_PERMISSIONS exS) /\
(VAR_RES_STACK___IS_EQUAL_UPTO_PERMISSIONS exS st st) /\

(~(v IN exS) ==>
(VAR_RES_STACK___IS_EQUAL_UPTO_PERMISSIONS exS st
(VAR_RES_STACK___UPDATE_PERMISSION v p st))) /\

((!v. v IN exS ==> IS_NONE (f v)) ==>
(VAR_RES_STACK___IS_EQUAL_UPTO_PERMISSIONS exS st
(VAR_RES_STACK___UPDATE_PERMISSION_ALL f st))) /\

(?p. VAR_RES_STACK___UPDATE_PERMISSION v p st = st)
``,


SIMP_TAC std_ss [VAR_RES_STACK___UPDATE_PERMISSION_def,
       VAR_RES_STACK___IS_EQUAL_UPTO_PERMISSIONS_def,
       COMM_DEF, VAR_RES_STACK___UPDATE_PERMISSION_ALL_def,
       FUN_FMAP_DEF, FDOM_FINITE, COND_RATOR, COND_RAND] THEN
Cases_on `v IN FDOM st` THENL [
   Cases_on `st ' v` THEN
   ASM_SIMP_TAC std_ss [FDOM_FUPDATE, IN_INSERT, FAPPLY_FUPDATE_THM,
         COND_RATOR, COND_RAND, EXTENSION,
              GSYM fmap_EQ_THM] THEN
   METIS_TAC[],

   ASM_SIMP_TAC std_ss [] THEN
   METIS_TAC[]
]);





val VAR_RES_STACK___IS_SUBSTATE_UPTO_PERMISSIONS___COMBINE_EXISTS1 =
store_thm ("VAR_RES_STACK___IS_SUBSTATE_UPTO_PERMISSIONS___COMBINE_EXISTS1",
``
!st1 st2 st st' exS.
((VAR_RES_STACK_COMBINE (SOME st1) (SOME st2) = SOME st) /\
(VAR_RES_STACK___IS_SUBSTATE_UPTO_PERMISSIONS exS st st')) ==>

(?st1' st2'.
(VAR_RES_STACK_COMBINE (SOME st1') (SOME st2') = SOME st') /\
(VAR_RES_STACK___IS_EQUAL_UPTO_PERMISSIONS exS st1 st1') /\
(VAR_RES_STACK___IS_SUBSTATE_UPTO_PERMISSIONS exS st2 st2'))``,


SIMP_TAC std_ss [SOME___VAR_RES_STACK_COMBINE,
       VAR_RES_STACK___IS_SUBSTATE_UPTO_PERMISSIONS_def,
       VAR_RES_STACK___IS_EQUAL_UPTO_PERMISSIONS_def,
       FMERGE_DEF, SUBSET_DEF, VAR_RES_STACK_IS_SEPARATE_def] THEN
REPEAT STRIP_TAC THEN


`?pf. !v. ((v IN FDOM st1) /\ (v IN exS)) ==>
          (((var_res_permission_combine (SOME (SND (st1 ' v))) (SOME (pf v)) = SOME (SND (st' ' v))) \/
           (~(v IN FDOM st2) /\ (st1 ' v = st' ' v))) /\
           (v IN FDOM st2 ==> IS_VAR_RES_SUBPERMISSION (SND (st2 ' v)) (pf v)))` by ALL_TAC THEN1 (

   Q.EXISTS_TAC `\v. if ~(v IN FDOM st1) \/ ~(v IN exS) then ARB else
                        @p. ((var_res_permission_combine (SOME (SND (st1 ' v))) (SOME p) =
                             SOME (SND (st' ' v))) \/ (~(v IN FDOM st2) /\ (st1 ' v = st' ' v))) /\
                     (v IN FDOM st2 ==> IS_VAR_RES_SUBPERMISSION (SND (st2 ' v)) p)` THEN
   GEN_TAC THEN BETA_TAC THEN
   REPEAT (Q.PAT_ASSUM `!x. X x` (ASSUME_TAC o Q.SPEC `v`)) THEN
   STRIP_TAC THEN
   ASM_REWRITE_TAC[] THEN
   SELECT_ELIM_TAC THEN
   SIMP_TAC std_ss [] THEN
   Cases_on `v IN FDOM st2` THENL [
      FULL_SIMP_TAC std_ss [IN_UNION, IS_SOME_EXISTS, VAR_RES_STACK_COMBINE___MERGE_FUNC_def] THEN
      FULL_SIMP_TAC std_ss [IS_VAR_RES_SUBPERMISSION_def] THENL [
         METIS_TAC[],

    Q.EXISTS_TAC `THE (var_res_permission_combine (SOME (SND (st2 ' v))) (SOME p))` THEN
         Q.PAT_ASSUM `X = SOME y` (ASSUME_TAC o GSYM) THEN
         FULL_SIMP_TAC std_ss [] THEN
         `var_res_permission_combine
            (var_res_permission_combine (SOME (SND (st1 ' v)))
               (SOME (SND (st2 ' v)))) (SOME p) =
          var_res_permission_combine
            (SOME (SND (st1 ' v))) (var_res_permission_combine
               (SOME (SND (st2 ' v))) (SOME p))` by ALL_TAC THEN1 (
       METIS_TAC[var_res_permission_THM2, ASSOC_DEF, COMM_DEF]
    ) THEN
         Cases_on `var_res_permission_combine (SOME (SND (st2 ' v))) (SOME p)` THEN (
            FULL_SIMP_TAC std_ss [var_res_permission_THM2]
    ) THEN
         PROVE_TAC[]
      ],


      FULL_SIMP_TAC std_ss [IN_UNION, IS_VAR_RES_SUBPERMISSION_def] THENL [
         ONCE_REWRITE_TAC[GSYM pairTheory.PAIR] THEN
         ASM_SIMP_TAC std_ss [],

    METIS_TAC[]
      ]
  ]
) THEN


Q.ABBREV_TAC `resS = \v. ~(v IN exS) \/ ~(v IN FDOM st1) \/ (v IN FDOM st2) \/ ~(st' ' v = st1 ' v)` THEN
Q.EXISTS_TAC `VAR_RES_STACK___UPDATE_PERMISSION_ALL (\v. if (v IN exS) then NONE else
                      SOME (var_res_permission_split  (SND (st' ' v)))
                                                          ) st1` THEN
Q.EXISTS_TAC `VAR_RES_STACK___UPDATE_PERMISSION_ALL (\v. if (v IN exS) /\ (v IN FDOM st1) then
                          SOME (pf  v) else
                      SOME (if (v IN FDOM st1) then
                                 var_res_permission_split  (SND (st' ' v))
                                                               else SND (st' ' v)
                                                          )) (DRESTRICT st' resS)` THEN
FULL_SIMP_TAC std_ss [VAR_RES_STACK___UPDATE_PERMISSION_ALL_def,
            FDOM_FINITE, FUN_FMAP_DEF, COND_REWRITES,
            IN_UNION, GSYM fmap_EQ_THM, FMERGE_DEF] THEN
`(FDOM st1 UNION FDOM (DRESTRICT st' resS)) = (FDOM st')` by ALL_TAC THEN1 (
   UNABBREV_ALL_TAC THEN
   SIMP_TAC std_ss [EXTENSION, IN_UNION, IN_INTER, IN_ABS, DRESTRICT_DEF] THEN
   METIS_TAC[]
) THEN
ONCE_ASM_REWRITE_TAC[] THEN POP_ASSUM (K ALL_TAC) THEN
ASM_SIMP_TAC std_ss [GSYM FORALL_AND_THM] THEN
GEN_TAC THEN

REPEAT (Q.PAT_ASSUM `!x. X x` (ASSUME_TAC o Q.SPEC `v`)) THEN
Tactical.REVERSE (Cases_on `v IN FDOM st'`) THEN1 (
   `~(v IN FDOM st2)` by METIS_TAC[] THEN
   `~(v IN FDOM st1)` by METIS_TAC[] THEN
   ASM_SIMP_TAC std_ss []
) THEN
Tactical.REVERSE (Cases_on `v IN resS`) THEN1 (
   UNABBREV_ALL_TAC THEN
   FULL_SIMP_TAC std_ss [IN_ABS, DRESTRICT_DEF, IN_INTER]
) THEN
ASM_SIMP_TAC std_ss [DRESTRICT_DEF, FUN_FMAP_DEF, FDOM_FINITE, FINITE_INTER,
           IN_INTER] THEN
Cases_on `v IN FDOM st2` THEN Cases_on `v IN FDOM st1` THEN Cases_on `v IN exS` THEN (
   FULL_SIMP_TAC std_ss [VAR_RES_STACK_COMBINE___MERGE_FUNC_def,
          IS_VAR_RES_SUBPERMISSION_THM,
          var_res_permission_THM2]
) THEN
UNABBREV_ALL_TAC THEN
FULL_SIMP_TAC std_ss [IN_ABS]);



val VAR_RES_STACK___IS_SUBSTATE_UPTO_PERMISSIONS___COMBINE_EXISTS2 =
store_thm ("VAR_RES_STACK___IS_SUBSTATE_UPTO_PERMISSIONS___COMBINE_EXISTS2",
``
!st1:('a,'b) var_res_state st2 st st' exS.
((VAR_RES_STACK_COMBINE (SOME st1) (SOME st2) = SOME st) /\
(VAR_RES_STACK___IS_SUBSTATE_UPTO_PERMISSIONS exS st st')) ==>

(?st1' st2'.
(VAR_RES_STACK_COMBINE (SOME st1') (SOME st2') = SOME st') /\
(VAR_RES_STACK___IS_SUBSTATE_UPTO_PERMISSIONS exS st1 st1') /\
(VAR_RES_STACK___IS_EQUAL_UPTO_PERMISSIONS exS st2 st2'))``,


`!(st1:('a,'b) var_res_state) st2. VAR_RES_STACK_COMBINE (SOME st1) (SOME st2) =
                                  VAR_RES_STACK_COMBINE (SOME st2) (SOME st1)` by
   METIS_TAC[VAR_RES_STACK_COMBINE___IS_SEPARATION_COMBINATOR, IS_SEPARATION_COMBINATOR_def,
     COMM_DEF] THEN
METIS_TAC[VAR_RES_STACK___IS_SUBSTATE_UPTO_PERMISSIONS___COMBINE_EXISTS1]);



val VAR_RES_STACK___IS_EQUAL_UPTO_PERMISSIONS___COMBINE_EXISTS =
store_thm ("VAR_RES_STACK___IS_EQUAL_UPTO_PERMISSIONS___COMBINE_EXISTS",
``
!st1 st2 st st' exS.
((VAR_RES_STACK_COMBINE (SOME st1) (SOME st2) = SOME st) /\
(VAR_RES_STACK___IS_EQUAL_UPTO_PERMISSIONS exS st st')) ==>

(?st1' st2'.
(VAR_RES_STACK_COMBINE (SOME st1') (SOME st2') = SOME st') /\
(VAR_RES_STACK___IS_EQUAL_UPTO_PERMISSIONS exS st1 st1') /\
(VAR_RES_STACK___IS_EQUAL_UPTO_PERMISSIONS exS st2 st2'))``,


SIMP_TAC std_ss [SOME___VAR_RES_STACK_COMBINE,
       VAR_RES_STACK___IS_EQUAL_UPTO_PERMISSIONS_def,
       FMERGE_DEF, SUBSET_DEF, VAR_RES_STACK_IS_SEPARATE_def] THEN
REPEAT STRIP_TAC THEN
Q.EXISTS_TAC `VAR_RES_STACK___UPDATE_PERMISSION_ALL (\v. if (v IN exS) then NONE else
                      SOME (if (v IN FDOM st2) then
                                 var_res_permission_split  (SND (st' ' v))
                                                               else SND (st' ' v)
                                                          )) st1` THEN
Q.EXISTS_TAC `VAR_RES_STACK___UPDATE_PERMISSION_ALL (\v. if (v IN exS) then NONE else
                      SOME (if (v IN FDOM st1) then
                                 var_res_permission_split  (SND (st' ' v))
                                                               else SND (st' ' v)
                                                          )) st2` THEN

`!x. (x IN FDOM st' /\ ~(x IN FDOM st1)) ==> x IN FDOM st2` by METIS_TAC[EXTENSION, IN_UNION] THEN
FULL_SIMP_TAC std_ss [VAR_RES_STACK___UPDATE_PERMISSION_ALL_def,
            FDOM_FINITE, FUN_FMAP_DEF, COND_REWRITES,
            IN_UNION, GSYM fmap_EQ_THM, FMERGE_DEF, GSYM FORALL_AND_THM] THEN
GEN_TAC THEN
REPEAT (Q.PAT_ASSUM `!x. X x` (ASSUME_TAC o Q.SPEC `x`)) THEN
Cases_on `x IN FDOM st2` THEN Cases_on `x IN FDOM st1` THEN Cases_on `x IN exS` THEN (
   FULL_SIMP_TAC std_ss [VAR_RES_STACK_COMBINE___MERGE_FUNC_def,
          IS_VAR_RES_SUBPERMISSION_THM,
          var_res_permission_THM2]
));






val VAR_RES_STACK___IS_SUBSTATE_UPTO_PERMISSIONS___FEMPTY = store_thm (
"VAR_RES_STACK___IS_SUBSTATE_UPTO_PERMISSIONS___FEMPTY",
``(VAR_RES_STACK___IS_SUBSTATE_UPTO_PERMISSIONS exS FEMPTY X) /\
  (VAR_RES_STACK___IS_SUBSTATE_UPTO_PERMISSIONS exS X FEMPTY = (X = FEMPTY))``,

SIMP_TAC std_ss [VAR_RES_STACK___IS_SUBSTATE_UPTO_PERMISSIONS_def,
       FDOM_FEMPTY, NOT_IN_EMPTY, EMPTY_SUBSET, SUBSET_DEF,
       GSYM fmap_EQ_THM, EXTENSION] THEN
METIS_TAC[]);




val VAR_RES_STACK___IS_EQUAL_UPTO_PERMISSIONS___FEMPTY = store_thm (
"VAR_RES_STACK___IS_EQUAL_UPTO_PERMISSIONS___FEMPTY",
``(VAR_RES_STACK___IS_EQUAL_UPTO_PERMISSIONS exS FEMPTY X = (X = FEMPTY)) /\
  (VAR_RES_STACK___IS_EQUAL_UPTO_PERMISSIONS exS X FEMPTY = (X = FEMPTY))``,

SIMP_TAC std_ss [VAR_RES_STACK___IS_EQUAL_UPTO_PERMISSIONS___ALTERNATIVE_DEF,
                 VAR_RES_STACK___IS_SUBSTATE_UPTO_PERMISSIONS___FEMPTY]);




val VAR_RES_STACK___IS_SUBSTATE_UPTO_PERMISSIONS___SUBSET = store_thm (
"VAR_RES_STACK___IS_SUBSTATE_UPTO_PERMISSIONS___SUBSET",
``(VAR_RES_STACK___IS_SUBSTATE_UPTO_PERMISSIONS exS1 st1 st2 /\
(exS2 SUBSET exS1)) ==>
(VAR_RES_STACK___IS_SUBSTATE_UPTO_PERMISSIONS exS2 st1 st2)``,


SIMP_TAC std_ss [VAR_RES_STACK___IS_SUBSTATE_UPTO_PERMISSIONS_def, SUBSET_DEF]);



val VAR_RES_STACK___IS_EQUAL_UPTO_PERMISSIONS___SUBSET = store_thm (
"VAR_RES_STACK___IS_EQUAL_UPTO_PERMISSIONS___SUBSET",
``(VAR_RES_STACK___IS_EQUAL_UPTO_PERMISSIONS exS1 st1 st2 /\
(exS2 SUBSET exS1)) ==>
(VAR_RES_STACK___IS_EQUAL_UPTO_PERMISSIONS exS2 st1 st2)``,


SIMP_TAC std_ss [VAR_RES_STACK___IS_EQUAL_UPTO_PERMISSIONS_def, SUBSET_DEF]);





val VAR_RES_STACK___IS_SUBSTATE_UPTO_PERMISSIONS___UNION = store_thm (
"VAR_RES_STACK___IS_SUBSTATE_UPTO_PERMISSIONS___UNION",
``VAR_RES_STACK___IS_SUBSTATE_UPTO_PERMISSIONS (exS1 UNION exS2) st1 st2 =
(VAR_RES_STACK___IS_SUBSTATE_UPTO_PERMISSIONS exS1 st1 st2 /\
 VAR_RES_STACK___IS_SUBSTATE_UPTO_PERMISSIONS exS2 st1 st2)``,


SIMP_TAC std_ss [VAR_RES_STACK___IS_SUBSTATE_UPTO_PERMISSIONS_def, IN_UNION] THEN
METIS_TAC[]);




val VAR_RES_STACK___IS_EQUAL_UPTO_PERMISSIONS___UNION = store_thm (
"VAR_RES_STACK___IS_EQUAL_UPTO_PERMISSIONS___UNION",
``VAR_RES_STACK___IS_EQUAL_UPTO_PERMISSIONS (exS1 UNION exS2) st1 st2 =
(VAR_RES_STACK___IS_EQUAL_UPTO_PERMISSIONS exS1 st1 st2 /\
 VAR_RES_STACK___IS_EQUAL_UPTO_PERMISSIONS exS2 st1 st2)``,


SIMP_TAC std_ss [VAR_RES_STACK___IS_EQUAL_UPTO_PERMISSIONS_def, IN_UNION] THEN
METIS_TAC[]);



val VAR_RES_STACK___IS_EQUAL_UPTO_PERMISSIONS___VAR_RES_STACK_SPLIT =
store_thm ("VAR_RES_STACK___IS_EQUAL_UPTO_PERMISSIONS___VAR_RES_STACK_SPLIT",
``
(VAR_RES_STACK___IS_EQUAL_UPTO_PERMISSIONS {} (VAR_RES_STACK_SPLIT1 wp p) p) /\
(VAR_RES_STACK___IS_EQUAL_UPTO_PERMISSIONS {} (VAR_RES_STACK_SPLIT2 {} p) p) /\
(VAR_RES_STACK___IS_EQUAL_UPTO_PERMISSIONS {} (VAR_RES_STACK_SPLIT wp {} p) p)``,


SIMP_TAC std_ss [VAR_RES_STACK___IS_EQUAL_UPTO_PERMISSIONS_def,
       VAR_RES_STACK_SPLIT12___REWRITES,
       VAR_RES_STACK_SPLIT___REWRITES,
       DIFF_EMPTY, NOT_IN_EMPTY]);





val VAR_RES_STACK_IS_SEPARATE___DRESTRICT =
   store_thm ("VAR_RES_STACK_IS_SEPARATE___DRESTRICT",

``(!st1:('a, 'b) var_res_state st2 vs1 vs2.
             VAR_RES_STACK_IS_SEPARATE st1 st2 ==>
             (VAR_RES_STACK_IS_SEPARATE (DRESTRICT st1 vs1) (DRESTRICT st2 vs2))) /\

  (!st1:('a, 'b) var_res_state st2 vs.
             VAR_RES_STACK_IS_SEPARATE st1 st2 ==>
             (VAR_RES_STACK_IS_SEPARATE (DRESTRICT st1 vs) st2)) /\

  (!st1:('a, 'b) var_res_state st2 vs.
             VAR_RES_STACK_IS_SEPARATE st1 st2 ==>
             (VAR_RES_STACK_IS_SEPARATE st1 (DRESTRICT st2 vs)))``,


MATCH_MP_TAC (prove (``((A ==> (B /\ C)) /\ A) ==> (A /\ B /\ C)``, PROVE_TAC[])) THEN
CONJ_TAC THEN1 (
   METIS_TAC [DRESTRICT_UNIV]
) THEN
SIMP_TAC std_ss [VAR_RES_STACK_IS_SEPARATE_def, DRESTRICT_DEF, IN_INTER] THEN
METIS_TAC[]);



val VAR_RES_STACK_IS_SEPARATE___write_perm = store_thm ( "VAR_RES_STACK_IS_SEPARATE___write_perm",
``!st1 st2 s.
VAR_RES_STACK_IS_SEPARATE st1 st2 /\
var_res_sl___has_write_permission s st1 ==>
~(var_res_sl___has_read_permission s st2)``,

SIMP_TAC std_ss [var_res_sl___has_read_permission_def, var_res_sl___has_write_permission_def] THEN
REPEAT STRIP_TAC THEN
Q.PAT_ASSUM `VAR_RES_STACK_IS_SEPARATE st1 st2` MP_TAC THEN
SIMP_TAC std_ss [VAR_RES_STACK_IS_SEPARATE_def] THEN
Q.EXISTS_TAC `s` THEN
ASM_SIMP_TAC std_ss [var_res_permission_THM2]);



val VAR_RES_STACK_IS_SEPARATE___UPDATE = store_thm ("VAR_RES_STACK_IS_SEPARATE___UPDATE",
``!st1 st2 s v.
VAR_RES_STACK_IS_SEPARATE st1 st2 /\
var_res_sl___has_write_permission s st1 ==>

VAR_RES_STACK_IS_SEPARATE
      (st1 |+(s,v,var_res_write_permission)) st2``,

REPEAT STRIP_TAC THEN
IMP_RES_TAC VAR_RES_STACK_IS_SEPARATE___write_perm THEN
FULL_SIMP_TAC std_ss [VAR_RES_STACK_IS_SEPARATE_def,
   var_res_sl___has_write_permission_def,
   var_res_sl___has_read_permission_def,
   FDOM_FUPDATE] THEN
REPEAT GEN_TAC THEN STRIP_TAC THEN
`~(x = s)` by PROVE_TAC[] THEN
FULL_SIMP_TAC std_ss [FAPPLY_FUPDATE_THM, IN_INSERT] THEN
METIS_TAC[]);



val VAR_RES_STACK_IS_SEPARATE___COMBINE_UPDATE = store_thm ("VAR_RES_STACK_IS_SEPARATE___COMBINE_UPDATE",
``!st1 st2 s v.
VAR_RES_STACK_IS_SEPARATE st1 st2 /\
var_res_sl___has_write_permission s st1 ==>

((THE (VAR_RES_STACK_COMBINE (SOME st1) (SOME st2))) |+ (s,v,var_res_write_permission) =
(THE (VAR_RES_STACK_COMBINE (SOME (st1 |+ (s,v,var_res_write_permission))) (SOME st2))))``,


REPEAT GEN_TAC THEN STRIP_TAC THEN
IMP_RES_TAC VAR_RES_STACK_IS_SEPARATE___UPDATE THEN
IMP_RES_TAC VAR_RES_STACK_IS_SEPARATE___write_perm THEN
ASM_SIMP_TAC std_ss [VAR_RES_STACK_COMBINE_def, BIN_OPTION_MAP_THM] THEN
SIMP_TAC std_ss [GSYM fmap_EQ_THM, FMERGE_DEF, FDOM_FUPDATE] THEN
CONJ_TAC THEN1 (
   SIMP_TAC std_ss [EXTENSION, IN_UNION, IN_INSERT] THEN
   PROVE_TAC[]
) THEN
REPEAT STRIP_TAC THEN
Cases_on `x = s` THEN1 (
   `~(s IN FDOM st2)` by PROVE_TAC [var_res_sl___has_read_permission_def] THEN
   FULL_SIMP_TAC std_ss [IN_INSERT, FAPPLY_FUPDATE_THM]
) THEN
ASM_SIMP_TAC std_ss [FAPPLY_FUPDATE_THM, FMERGE_DEF, IN_INSERT]);






val VAR_RES_STACK___IS_EQUAL_UPTO_VALUES_def = Define `
 VAR_RES_STACK___IS_EQUAL_UPTO_VALUES (st1:('a, 'b) var_res_state) (st2:('a, 'b) var_res_state) =
((!x. ((x IN FDOM st1) /\ (x IN FDOM st2)) ==> (SND (st1 ' x) = SND (st2 ' x))) /\
 (!x. ((x IN FDOM st1) /\ ~(x IN FDOM st2)) ==> (SND (st1 ' x) = var_res_write_permission)) /\
 (!x. (~(x IN FDOM st1) /\ (x IN FDOM st2)) ==> (SND (st2 ' x) = var_res_write_permission)))
`;


val VAR_RES_STACK___IS_EQUAL_UPTO_VALUES___TRANS =
store_thm ("VAR_RES_STACK___IS_EQUAL_UPTO_VALUES___TRANS",
``!st1 st2 st3.
(VAR_RES_STACK___IS_EQUAL_UPTO_VALUES st1 st2 /\
VAR_RES_STACK___IS_EQUAL_UPTO_VALUES st2 st3) ==>
VAR_RES_STACK___IS_EQUAL_UPTO_VALUES st1 st3``,

SIMP_TAC std_ss [VAR_RES_STACK___IS_EQUAL_UPTO_VALUES_def,
       GSYM FORALL_AND_THM] THEN
REPEAT GEN_TAC THEN
HO_MATCH_MP_TAC (prove (``(!x. (X x ==> Y x)) ==> ((!x. X x) ==> (!x. Y x))``,
                    METIS_TAC[])) THEN
GEN_TAC THEN
Cases_on `x IN FDOM st1` THEN
Cases_on `x IN FDOM st2` THEN
Cases_on `x IN FDOM st3` THEN
ASM_SIMP_TAC (std_ss++CONJ_ss) []);



val VAR_RES_STACK___IS_EQUAL_UPTO_VALUES___REFL =
store_thm ("VAR_RES_STACK___IS_EQUAL_UPTO_VALUES___REFL",
``!st. VAR_RES_STACK___IS_EQUAL_UPTO_VALUES st st``,

SIMP_TAC (std_ss++CONJ_ss) [VAR_RES_STACK___IS_EQUAL_UPTO_VALUES_def]);


val VAR_RES_STACK___IS_EQUAL_UPTO_VALUES___SYM =
store_thm ("VAR_RES_STACK___IS_EQUAL_UPTO_VALUES___SYM",
``!st1 st2. VAR_RES_STACK___IS_EQUAL_UPTO_VALUES st1 st2 =
            VAR_RES_STACK___IS_EQUAL_UPTO_VALUES st2 st1``,

SIMP_TAC std_ss [VAR_RES_STACK___IS_EQUAL_UPTO_VALUES_def] THEN
METIS_TAC[]);






(******************************************************
 Extended Separation Combinators
 ******************************************************)

val _ = type_abbrev("var_res_ext_state", Type `:('a, 'b) var_res_state # 'c`);

val VAR_RES_COMBINATOR_def = Define `
   VAR_RES_COMBINATOR f =
   PRODUCT_SEPARATION_COMBINATOR VAR_RES_STACK_COMBINE f`


val IS_SEPARATION_ALGEBRA___VAR_RES_COMBINATOR =
   store_thm ("IS_SEPARATION_ALGEBRA___VAR_RES_COMBINATOR",
``!f u. IS_SEPARATION_ALGEBRA f u ==>
        IS_SEPARATION_ALGEBRA (VAR_RES_COMBINATOR f) (FEMPTY, u)``,
REWRITE_TAC [VAR_RES_COMBINATOR_def] THEN
REPEAT STRIP_TAC THEN
MATCH_MP_TAC PRODUCT_SEPARATION_COMBINATOR___ALGEBRA_THM THEN
ASM_REWRITE_TAC[VAR_RES_STACK_COMBINE___IS_SEPARATION_ALGEBRA]);



val IS_SEPARATION_COMBINATOR___VAR_RES_COMBINATOR =
   store_thm ("IS_SEPARATION_COMBINATOR___VAR_RES_COMBINATOR",
``!f. IS_SEPARATION_COMBINATOR f ==>
      IS_SEPARATION_COMBINATOR (VAR_RES_COMBINATOR f)``,
REWRITE_TAC [VAR_RES_COMBINATOR_def] THEN
REPEAT STRIP_TAC THEN
MATCH_MP_TAC PRODUCT_SEPARATION_COMBINATOR_THM THEN
ASM_REWRITE_TAC[VAR_RES_STACK_COMBINE___IS_SEPARATION_COMBINATOR]);


val asl_emp___VAR_RES_COMBINATOR = store_thm (
"asl_emp___VAR_RES_COMBINATOR",
``!f. (asl_emp (VAR_RES_COMBINATOR f) =
        \s. (FST s = FEMPTY) /\ (SND s IN asl_emp f))``,
SIMP_TAC std_ss [VAR_RES_COMBINATOR_def,
   PRODUCT_SEPARATION_COMBINATOR___asl_emp,
   asl_emp___VAR_RES_STACK_COMBINE, IN_SING]);



val VAR_RES_COMBINATOR_REWRITE = save_thm ("VAR_RES_COMBINATOR_REWRITE",
let
   val thm0 = Q.GEN `f1` PRODUCT_SEPARATION_COMBINATOR_REWRITE
   val thm1 = ISPEC ``VAR_RES_STACK_COMBINE:('c, 'a) var_res_state bin_option_function`` thm0
   val thm2 = REWRITE_RULE [GSYM VAR_RES_COMBINATOR_def] thm1
in
   thm2
end);


val IS_VAR_RES_COMBINATOR_def = Define `
IS_VAR_RES_COMBINATOR f =
?f'. (f = VAR_RES_COMBINATOR f') /\ IS_SEPARATION_COMBINATOR f'`


val IS_SEPARATION_COMBINATOR___IS_VAR_RES_COMBINATOR =
store_thm ("IS_SEPARATION_COMBINATOR___IS_VAR_RES_COMBINATOR",
``!f. IS_VAR_RES_COMBINATOR f ==> IS_SEPARATION_COMBINATOR f``,
SIMP_TAC std_ss [IS_VAR_RES_COMBINATOR_def,
  GSYM LEFT_FORALL_IMP_THM, IS_SEPARATION_COMBINATOR___VAR_RES_COMBINATOR]);



val VAR_RES_COMBINATOR_WEAK_11 = store_thm ("VAR_RES_COMBINATOR_WEAK_11",
``!f f'.
 ((VAR_RES_COMBINATOR f = VAR_RES_COMBINATOR f') =
  !x1 x2. (f (SOME x1) (SOME x2) = f' (SOME x1) (SOME x2)))``,

REPEAT STRIP_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THENL [
   FULL_SIMP_TAC std_ss [VAR_RES_COMBINATOR_def,
      PRODUCT_SEPARATION_COMBINATOR_def] THEN
   `PRODUCT_SEPARATION_COMBINATOR VAR_RES_STACK_COMBINE f (SOME (FEMPTY, x1)) (SOME (FEMPTY, x2))=
    PRODUCT_SEPARATION_COMBINATOR VAR_RES_STACK_COMBINE f' (SOME (FEMPTY, x1)) (SOME (FEMPTY, x2))` by PROVE_TAC[] THEN
   FULL_SIMP_TAC std_ss [PRODUCT_SEPARATION_COMBINATOR_REWRITE,
      LET_THM, VAR_RES_STACK_COMBINE_REWRITE] THEN
   Cases_on `f (SOME x1) (SOME x2)` THEN
   Cases_on `f' (SOME x1) (SOME x2)` THEN
   FULL_SIMP_TAC std_ss [],


   FULL_SIMP_TAC std_ss [FUN_EQ_THM] THEN
   Cases_on `x` THEN SIMP_TAC std_ss [VAR_RES_COMBINATOR_REWRITE] THEN
   Cases_on `x''` THEN SIMP_TAC std_ss [VAR_RES_COMBINATOR_REWRITE] THEN
   ASM_SIMP_TAC std_ss [LET_THM]
]);



val VAR_RES_COMBINATOR_11 = store_thm ("VAR_RES_COMBINATOR_11",
``!f f'.
 IS_SEPARATION_COMBINATOR f /\ IS_SEPARATION_COMBINATOR f' ==>
 ((VAR_RES_COMBINATOR f = VAR_RES_COMBINATOR f') =
  (f = f'))``,

REWRITE_TAC[VAR_RES_COMBINATOR_WEAK_11] THEN
REPEAT STRIP_TAC THEN
EQ_TAC THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
SIMP_TAC std_ss [FUN_EQ_THM] THEN
Cases_on `x` THEN1 (
  FULL_SIMP_TAC std_ss [IS_SEPARATION_COMBINATOR_EXPAND_THM]
) THEN
Cases_on `x''` THEN1 (
  FULL_SIMP_TAC std_ss [IS_SEPARATION_COMBINATOR_EXPAND_THM]
) THEN
ASM_REWRITE_TAC[]);



val GET_VAR_RES_COMBINATOR_def = Define `
GET_VAR_RES_COMBINATOR f =
@f'. (IS_SEPARATION_COMBINATOR f') /\ (f = VAR_RES_COMBINATOR f')`


val GET_VAR_RES_COMBINATOR_THM = store_thm (
"GET_VAR_RES_COMBINATOR_THM",
``!f. IS_SEPARATION_COMBINATOR f ==>
  (GET_VAR_RES_COMBINATOR (VAR_RES_COMBINATOR f) = f)``,

SIMP_TAC std_ss [GET_VAR_RES_COMBINATOR_def] THEN
REPEAT STRIP_TAC THEN
SELECT_ELIM_TAC THEN
METIS_TAC[VAR_RES_COMBINATOR_11]);



val GET_VAR_RES_COMBINATOR_THM2 = store_thm ("GET_VAR_RES_COMBINATOR_THM2",
``!f f'. (IS_VAR_RES_COMBINATOR f /\ (GET_VAR_RES_COMBINATOR f = f')) ==>
  (IS_SEPARATION_COMBINATOR f') /\ (f = VAR_RES_COMBINATOR f')``,
SIMP_TAC std_ss [IS_VAR_RES_COMBINATOR_def,
  GSYM LEFT_FORALL_IMP_THM, GET_VAR_RES_COMBINATOR_THM]);



val VAR_RES_WRITE_PERM___SUBSTATE = store_thm (
"VAR_RES_WRITE_PERM___SUBSTATE",
``!f s1 s2 v.
             ASL_IS_SUBSTATE (VAR_RES_COMBINATOR f) s1 s2 /\
             var_res_sl___has_write_permission v (FST s1) ==>
             var_res_sl___has_write_permission v (FST s2)``,

REPEAT STRIP_TAC THEN
Cases_on `s1` THEN Cases_on `s2` THEN
FULL_SIMP_TAC std_ss [var_res_sl___has_write_permission_def,
                      ASL_IS_SUBSTATE_def, VAR_RES_COMBINATOR_def] THEN
FULL_SIMP_TAC std_ss [PRODUCT_SEPARATION_COMBINATOR_REWRITE,
                      SOME___VAR_RES_STACK_COMBINE,
                      FMERGE_DEF, IN_UNION, VAR_RES_STACK_IS_SEPARATE_def] THEN
FULL_SIMP_TAC std_ss [VAR_RES_STACK_COMBINE___MERGE_FUNC_def,
                      COND_RAND, COND_RATOR] THEN
Cases_on `v IN FDOM (FST s1)` THEN ASM_REWRITE_TAC[] THEN
Q.PAT_ASSUM `!x. P x` (MP_TAC o Q.SPEC `v`) THEN
ASM_SIMP_TAC std_ss [var_res_permission_THM2]);



val VAR_RES_READ_PERM___SUBSTATE = store_thm (
"VAR_RES_READ_PERM___SUBSTATE",
``!f s1 s2 v. (ASL_IS_SUBSTATE (VAR_RES_COMBINATOR f) s1 s2 /\
               var_res_sl___has_read_permission v (FST s1)) ==>
              var_res_sl___has_read_permission v (FST s2)``,

SIMP_TAC std_ss [var_res_sl___has_read_permission_def,
                 ASL_IS_SUBSTATE_def, VAR_RES_COMBINATOR_def] THEN
SIMP_TAC std_ss [PRODUCT_SEPARATION_COMBINATOR_REWRITE,
                 SOME___VAR_RES_STACK_COMBINE, GSYM LEFT_EXISTS_AND_THM,
                 GSYM LEFT_FORALL_IMP_THM, FMERGE_DEF, IN_UNION]);



(******************************************************
 Expressions
 ******************************************************)

val _ = type_abbrev("var_res_expression", Type `:('a, 'b) var_res_state -> 'c option`);

val var_res_exp_var_def = Define `var_res_exp_var var = (\stack:('a, 'b) var_res_state.
(if (var IN FDOM stack) then SOME (FST (stack ' var)) else NONE))`;

val var_res_exp_const_def = Define `var_res_exp_const c = (K (SOME c)):('a, 'b,'c) var_res_expression`;

val var_res_exp_const_EVAL = store_thm ("var_res_exp_const_EVAL",
``var_res_exp_const c s = SOME c``,
SIMP_TAC std_ss [var_res_exp_const_def]);


val var_res_exp_op_def = Define `
  ((var_res_exp_op f (el:('a, 'b,'c) var_res_expression list)):('a, 'b,'c) var_res_expression) =
   (\s. let el' = MAP (\e. e s) el in
        if EVERY IS_SOME el' then SOME (f (MAP THE el')) else NONE)`


val var_res_exp_binop_def = Define `
  var_res_exp_binop bop e1 e2 = var_res_exp_op (\l. bop (EL 0 l) (EL 1 l)) [e1;e2]`

val var_res_exp_binop_const_def = Define `
   var_res_exp_binop_const bop e n =
   var_res_exp_binop bop e (var_res_exp_const n)`


val var_res_exp_binop___const_eval = store_thm ("var_res_exp_binop___const_eval",
``var_res_exp_binop bop (var_res_exp_const c1) (var_res_exp_const c2) =
  var_res_exp_const (bop c1 c2)``,
  SIMP_TAC list_ss [var_res_exp_binop_def, var_res_exp_const_def,
                    var_res_exp_op_def, LET_THM, combinTheory.K_DEF]);


val var_res_exp_binop_REWRITE = store_thm ("var_res_exp_binop_REWRITE",
``var_res_exp_binop bop e1 e2 = \s. if (IS_SOME (e1 s) /\ IS_SOME (e2 s)) then
   SOME (bop (THE (e1 s)) (THE (e2 s))) else NONE``,
  SIMP_TAC list_ss [var_res_exp_binop_def, var_res_exp_const_def,
                    var_res_exp_op_def, LET_THM, combinTheory.K_DEF]);


val var_res_exp_binop_const___ALTERNATIVE_DEF = store_thm ("var_res_exp_binop_const___ALTERNATIVE_DEF",
``var_res_exp_binop_const bop e n = 
  var_res_exp_op (\l. bop (EL 0 l) n) [e]``,
SIMP_TAC list_ss [var_res_exp_op_def, var_res_exp_binop_def,
   var_res_exp_binop_const_def, LET_THM, var_res_exp_const_EVAL]);


val var_res_exp_binop_const_REWRITE = store_thm ("var_res_exp_binop_const_REWRITE",
``var_res_exp_binop_const bop e n = \s. if (IS_SOME (e s)) then
   SOME (bop (THE (e s)) n) else NONE``,
  SIMP_TAC list_ss [var_res_exp_binop_const___ALTERNATIVE_DEF, 
                    var_res_exp_const_def,
                    var_res_exp_op_def, LET_THM, combinTheory.K_DEF]);


val var_res_exp_op_NIL = store_thm ("var_res_exp_op_NIL",
``!f. var_res_exp_op f [] = var_res_exp_const (f [])``,
SIMP_TAC list_ss [var_res_exp_op_def, var_res_exp_const_def,
                  LET_THM, combinTheory.K_DEF]);


val var_res_exp_op_CONS = store_thm ("var_res_exp_op_CONS",
``!f e L. var_res_exp_op f (e::L) =
   \s. if (e s = NONE) then NONE else
       var_res_exp_op (\L'. f ((THE (e s))::L')) L s``,

SIMP_TAC list_ss [var_res_exp_op_def, LET_THM, FUN_EQ_THM] THEN
REPEAT GEN_TAC THEN
Cases_on `e s` THEN SIMP_TAC std_ss []);


val var_res_exp_op_CONS_CONST = store_thm ("var_res_exp_op_CONS_CONST",
``!f c L. var_res_exp_op f ((var_res_exp_const c)::L) =
          var_res_exp_op (\L'. f (c::L')) L``,
SIMP_TAC list_ss [var_res_exp_op_CONS, var_res_exp_const_def, FUN_EQ_THM]);


val var_res_exp_eq_THM = store_thm ("var_res_exp_eq_THM",
  ``((var_res_exp_var v1 = var_res_exp_var v2) = (v1 = v2)) /\
    ((var_res_exp_const c1 = var_res_exp_const c2) = (c1 = c2)) /\
    (~(var_res_exp_const c = var_res_exp_var v))``,

SIMP_TAC std_ss [FUN_EQ_THM,
                 var_res_exp_var_def, var_res_exp_const_def] THEN
CONJ_TAC THENL [
   EQ_TAC THEN SIMP_TAC std_ss [] THEN STRIP_TAC THEN CCONTR_TAC THEN
   Q.PAT_ASSUM `!x. P x` (MP_TAC o Q.SPEC `FEMPTY |+ (v1,ARB)`) THEN
   ASM_SIMP_TAC std_ss [FDOM_FEMPTY, FDOM_FUPDATE, IN_SING],

   Q.EXISTS_TAC `FEMPTY` THEN
   SIMP_TAC std_ss [FDOM_FEMPTY, NOT_IN_EMPTY]
]);


val SOME___var_res_exp_const = store_thm ("SOME___var_res_exp_const",
``!c c1 X. (var_res_exp_const c X = SOME c1) = (c = c1)``,
SIMP_TAC std_ss [var_res_exp_const_def]);

val var_res_exp_is_const_def = Define `
    var_res_exp_is_const e = ?n. e = var_res_exp_const n`;



val var_res_exp_add_def = Define `
   var_res_exp_add = var_res_exp_binop_const (($+):num -> num -> num)`
val var_res_exp_sub_def = Define `
   var_res_exp_sub = var_res_exp_binop_const (($-):num -> num -> num)`

val var_res_exp_add_sub_REWRITES = store_thm ("var_res_exp_add_sub_REWRITES",
``(var_res_exp_add e 0 = e) /\ (var_res_exp_sub e 0 = e) /\
  (var_res_exp_add (var_res_exp_const n1) n2 = (var_res_exp_const (n1 + n2))) /\
  (var_res_exp_sub (var_res_exp_const n1) n2 = (var_res_exp_const (n1 - n2))) /\

  (var_res_exp_add (var_res_exp_add e n1) n2 = (var_res_exp_add e (n1 + n2))) /\
  (var_res_exp_sub (var_res_exp_sub e n1) n2 = (var_res_exp_sub e (n1 + n2))) /\

  (n2 <= n1 ==>
     (var_res_exp_sub (var_res_exp_add e n1) n2 = (var_res_exp_add e (n1 - n2)))) /\
  (n1 < n2 ==>
     (var_res_exp_sub (var_res_exp_add e n1) n2 = (var_res_exp_sub e (n2 - n1))))``,
SIMP_TAC (list_ss++CONJ_ss) [var_res_exp_add_def, var_res_exp_sub_def,
   var_res_exp_binop_const_REWRITE, COND_NONE_SOME_REWRITES,
   var_res_exp_const_EVAL, FUN_EQ_THM] THEN
METIS_TAC[optionTheory.option_CLAUSES]);


fun var_res_exp_add_sub___INST_THM thm =
  let
     val thm1 = REWRITE_RULE [GSYM var_res_exp_add_def] (ISPEC ``($+):num->num->num`` thm)
     val thm2 = REWRITE_RULE [GSYM var_res_exp_sub_def] (ISPEC ``($-):num->num->num`` thm)
  in
     CONJ thm1 thm2
  end;



(******************************************************
 Propositions
 ******************************************************)

val _ = type_abbrev("var_res_proposition", Type `:('a,'b,'c) var_res_ext_state -> bool`);

val var_res_exp_is_cond_defined_def = Define `
  var_res_exp_is_cond_defined P (e:('a,'b,'c) var_res_expression) =
  (!s. (P s ==> IS_SOME (e (FST s))))`;


val var_res_exp_is_list_cond_defined_def = Define `
  var_res_exp_is_list_cond_defined P L =
    ((FST P):bool, \s. s IN (SND P) /\
    EVERY (\e:('a,'b,'c) var_res_expression. IS_SOME ((e (FST s)))) L)`


val var_res_prop_implies_readperms_def = Define `
  var_res_prop_implies_readperms (P:('a,'b,'c) var_res_proposition) vs =
  (!s. P s ==> vs SUBSET FDOM (FST s))`;


val var_res_prop_implies_writeperm_def = Define `
  var_res_prop_implies_writeperm (P:('a,'b,'c) var_res_proposition) v =
  (!s. P s ==> var_res_sl___has_write_permission v (FST s))`;


val var_res_stack_proposition_def = Define `
   var_res_stack_proposition f emp sp =
   \state:('a, 'b, 'c) var_res_ext_state.
     ((SND state) IN asl_emp f \/ ~emp) /\ ((sp (FST state)))`;

val var_res_exp_is_defined_def = Define `
  var_res_exp_is_defined f (e:('a,'b,'c) var_res_expression) =
  var_res_stack_proposition f T (\st. IS_SOME (e st))`

val var_res_exp_prop_def = Define `
   var_res_exp_prop (e:('a,'b,'c) var_res_expression) P =
   \state. let e_opt = e (FST state) in
           (IS_SOME e_opt) /\ (P (THE e_opt) state)`

val var_res_exp_prop___CONST = store_thm ("var_res_exp_prop___CONST",
``var_res_exp_prop (var_res_exp_const c) P = P c``,
SIMP_TAC std_ss [var_res_exp_prop_def, LET_THM, var_res_exp_const_EVAL, 
  FUN_EQ_THM])

val var_res_exp_is_defined_REWRITE = save_thm (
"var_res_exp_is_defined_REWRITE",
SIMP_RULE std_ss [var_res_stack_proposition_def]
   var_res_exp_is_defined_def);

val var_res_exp_weak_is_defined_def = Define `
  var_res_exp_weak_is_defined (e:('a,'b,'c) var_res_expression) =
  var_res_stack_proposition ARB F (\st. IS_SOME (e st))`

val var_res_exp_weak_is_defined_REWRITE = save_thm (
"var_res_exp_weak_is_defined_REWRITE",
SIMP_RULE std_ss [var_res_stack_proposition_def]
   var_res_exp_weak_is_defined_def);


val var_res_prop_expression_def = Define `
  var_res_prop_expression f emp p el =
  var_res_stack_proposition f emp (\s:('a,'b) var_res_state.
      (let el' = MAP (\e. e s) el in
      ((EVERY IS_SOME el') /\ (p (MAP THE el')))))`;

val var_res_prop_binexpression_def = Define `
  var_res_prop_binexpression f emp p e1 e2 =
  var_res_stack_proposition f emp (\s:('a,'b) var_res_state.
      let (no1:'c option) = e1 s in
      let (no2:'c option) = e2 s in
      ((IS_SOME no1) /\ (IS_SOME no2) /\ (p (THE no1) (THE no2))))`

val var_res_prop_binexpression___ALTERNATIVE_DEF = store_thm (
  "var_res_prop_binexpression___ALTERNATIVE_DEF",
``var_res_prop_binexpression f emp p e1 e2 =
  var_res_prop_expression f emp (\l. p (HD l) (HD (TL l))) [e1;e2]``,
SIMP_TAC list_ss [var_res_prop_expression_def, var_res_prop_binexpression_def,
  LET_THM] THEN
REWRITE_TAC[CONJ_ASSOC]);

val var_res_prop_expression_REWRITE = save_thm (
"var_res_prop_expression_REWRITE",
SIMP_RULE std_ss [var_res_stack_proposition_def]
   var_res_prop_expression_def);

val var_res_prop_binexpression_REWRITE = save_thm (
"var_res_prop_binexpression_REWRITE",
SIMP_RULE std_ss [var_res_stack_proposition_def]
   var_res_prop_binexpression_def);

val var_res_prop_weak_expression_def = Define `
  var_res_prop_weak_expression p el =
  var_res_prop_expression ARB F p el`

val var_res_prop_weak_binexpression_def = Define `
  var_res_prop_weak_binexpression p e1 e2 =
  var_res_prop_binexpression ARB F p e1 e2`

val var_res_prop_weak_binexpression_REWRITE = save_thm (
"var_res_prop_weak_binexpression_REWRITE",
SIMP_RULE std_ss [var_res_prop_binexpression_def,
                  var_res_stack_proposition_def]
   var_res_prop_weak_binexpression_def);

val var_res_prop_weak_binexpression___ALTERNATIVE_DEF = store_thm (
"var_res_prop_weak_binexpression___ALTERNATIVE_DEF",
``var_res_prop_weak_binexpression p e1 e2 =
  var_res_prop_weak_expression (\l. p (HD l) (HD (TL l))) [e1;e2]``,
SIMP_TAC std_ss [var_res_prop_weak_binexpression_def,
                 var_res_prop_weak_expression_def,
                 var_res_prop_binexpression___ALTERNATIVE_DEF]);

val var_res_prop_equal_def = Define `
  var_res_prop_equal f p1 p2 =
  var_res_prop_binexpression f T $= p1 p2`;

val var_res_prop_unequal_def = Define `
  var_res_prop_unequal f p1 p2 =
  var_res_prop_binexpression f T (\n1 n2. ~(n1 = n2)) p1 p2`;

val var_res_prop_weak_equal_def = Define `
  var_res_prop_weak_equal = var_res_prop_weak_binexpression $=`;

val var_res_prop_weak_unequal_def = Define `
  var_res_prop_weak_unequal = var_res_prop_weak_binexpression (\n1 n2. ~(n1 = n2))`;


val var_res_ext_state_proposition_def = Define `
   var_res_ext_state_proposition emp p =
   \state:('a, 'b, 'c) var_res_ext_state.
     (((FST state) = FEMPTY) \/ ~emp) /\ ((p (SND state)))`;


val var_res_bool_proposition_def = Define `
  var_res_bool_proposition f c =
  var_res_stack_proposition f T (\s. c)`

val var_res_bool_proposition_REWRITE = save_thm (
"var_res_bool_proposition_REWRITE",
SIMP_RULE std_ss [var_res_stack_proposition_def]
   var_res_bool_proposition_def);

val var_res_prop_stack_true_def = Define `
   var_res_prop_stack_true f = var_res_bool_proposition f T`

val var_res_prop_stack_true_REWRITE = save_thm (
"var_res_prop_stack_true_REWRITE",
SIMP_RULE std_ss [var_res_bool_proposition_REWRITE]
   var_res_prop_stack_true_def);

val var_res_exp_is_defined___const = store_thm (
"var_res_exp_is_defined___const",
``!f c. var_res_exp_is_defined f (var_res_exp_const c) =
        var_res_prop_stack_true f``,
SIMP_TAC std_ss [var_res_exp_is_defined_def,
  var_res_exp_const_def, var_res_prop_stack_true_def,
  var_res_bool_proposition_def]);

val var_res_bool_proposition_TF = store_thm ("var_res_bool_proposition_TF",
``(!f. (var_res_bool_proposition f T = var_res_prop_stack_true f)) /\
  (!f. (var_res_bool_proposition f F = asl_false))``,

SIMP_TAC std_ss [var_res_bool_proposition_REWRITE, EMPTY_DEF,
                 var_res_prop_stack_true_REWRITE, asl_false_def]);

val asl_and___var_res_bool_proposition = store_thm (
   "asl_and___var_res_bool_proposition",
``((asl_and (K c1) (var_res_bool_proposition f c2)) =
   var_res_bool_proposition f (c1 /\ c2)) /\

  ((asl_and (var_res_bool_proposition f c1) (K c2)) =
    var_res_bool_proposition f (c1 /\ c2)) /\

  ((asl_and (var_res_prop_stack_true f) (var_res_prop_stack_true f) =
   var_res_prop_stack_true f)) /\

  ((asl_and (var_res_bool_proposition f c) (var_res_prop_stack_true f) =
   var_res_bool_proposition f c)) /\

  ((asl_and (var_res_prop_stack_true f) (var_res_bool_proposition f c)) =
   var_res_bool_proposition f c) /\

  ((asl_and (var_res_bool_proposition f c1) (var_res_bool_proposition f c2)) =
   var_res_bool_proposition f (c1 /\ c2))``,

SIMP_TAC (std_ss++EQUIV_EXTRACT_ss) [EXTENSION, asl_bool_EVAL,
   var_res_prop_stack_true_def, IN_ABS,
   var_res_bool_proposition_REWRITE]);


val asl_star___var_res_bool_proposition = store_thm (
   "asl_star___var_res_bool_proposition",
   ``!f b1 b2. IS_SEPARATION_COMBINATOR f ==>
     (asl_star (VAR_RES_COMBINATOR f)
       (var_res_bool_proposition f b1) (var_res_bool_proposition f b2) =
        var_res_bool_proposition f (b1 /\ b2))``,

   SIMP_TAC std_ss [asl_star_def, var_res_bool_proposition_REWRITE,
      IN_ABS, VAR_RES_COMBINATOR_REWRITE, FUN_EQ_THM] THEN
   REPEAT STRIP_TAC THEN
   IMP_RES_TAC IS_SEPARATION_COMBINATOR_NEUTRAL_ELEMENT_FUNCTION_IMP THEN
   FULL_SIMP_TAC std_ss [IS_SEPARATION_COMBINATOR_NEUTRAL_ELEMENT_FUNCTION___WITH_COMBINATOR_THM,
     asl_emp_def, IN_ABS, GSYM RIGHT_EXISTS_AND_THM, GSYM LEFT_EXISTS_AND_THM,
     PAIR_EXISTS_THM] THEN
   QUANT_INSTANTIATE_TAC [] THEN
   EQ_TAC THEN1 METIS_TAC[] THEN
   STRIP_TAC THEN
   Q.EXISTS_TAC `FEMPTY` THEN
   ASM_SIMP_TAC std_ss [VAR_RES_STACK_COMBINE_REWRITE] THEN
   METIS_TAC[]
);


val var_res_prop_expression___NIL = store_thm (
"var_res_prop_expression___NIL",
``var_res_prop_expression f emp p [] =
  if emp then var_res_bool_proposition f (p []) else (K (p []))``,
SIMP_TAC list_ss [var_res_prop_expression_def, LET_THM,
  var_res_stack_proposition_def, var_res_bool_proposition_def] THEN
Cases_on `emp` THEN SIMP_TAC std_ss [combinTheory.K_DEF]);


val var_res_prop_expression___CONS_CONST = store_thm (
"var_res_prop_expression___CONS_CONST",
``var_res_prop_expression f emp p ((var_res_exp_const c)::eL) =
  var_res_prop_expression f emp (\l. p (c::l)) eL``,
SIMP_TAC list_ss [var_res_prop_expression_def, LET_THM,
  var_res_exp_const_def]);


val var_res_prop_binexpression_REWRITES =
store_thm ("var_res_prop_binexpression_REWRITES",
``(!p. irreflexive p ==>
      (!f emp e. var_res_prop_binexpression f emp p e e = asl_false)) /\
  (!p. reflexive p ==>
      (!f emp e. var_res_prop_binexpression f emp p e e =
      if emp then var_res_exp_is_defined f e else var_res_exp_weak_is_defined e)) /\
  (!f emp p c1 c2. var_res_prop_binexpression f emp p (var_res_exp_const c1) (var_res_exp_const c2) =
      if emp then var_res_bool_proposition f (p c1 c2) else (K (p c1 c2)))``,

SIMP_TAC std_ss [var_res_prop_binexpression_def, LET_THM,
                 reflexive_def, irreflexive_def,
                 var_res_bool_proposition_def,
                 var_res_exp_const_def, var_res_exp_is_defined_def,
                 var_res_exp_weak_is_defined_def,
                 var_res_stack_proposition_def, asl_false_def,
                 EMPTY_DEF, combinTheory.K_DEF] THEN
SIMP_TAC std_ss [EXTENSION, IN_ABS, COND_RAND, COND_RATOR]);



val var_res_prop_binexpression___emp___consts =
store_thm ("var_res_prop_binexpression___emp___consts",
``!f p c1 c2. var_res_prop_binexpression f T p (var_res_exp_const c1) (var_res_exp_const c2) =
              var_res_bool_proposition f (p c1 c2)``,
SIMP_TAC std_ss [var_res_prop_binexpression_REWRITES]);


local
   val equal_COLLAPSE = prove (``(\x1 x2. x1 = x2) = $=``, SIMP_TAC std_ss [FUN_EQ_THM])
in

val var_res_prop_binexpression_ELIM = save_thm ("var_res_prop_binexpression_ELIM",
  LIST_CONJ [GSYM var_res_prop_equal_def, GSYM var_res_prop_unequal_def,
             var_res_prop_binexpression___emp___consts,
             GSYM var_res_prop_weak_unequal_def, GSYM var_res_prop_weak_equal_def,
             CONV_RULE ((STRIP_QUANT_CONV o LHS_CONV) (ONCE_REWRITE_CONV [GSYM equal_COLLAPSE]))
                  (GSYM var_res_prop_equal_def),
             CONV_RULE ((STRIP_QUANT_CONV o LHS_CONV) (ONCE_REWRITE_CONV [GSYM equal_COLLAPSE]))
                  (GSYM var_res_prop_weak_equal_def)])

end;


val var_res_prop_binexpression_symmetric =
store_thm ("var_res_prop_binexpression_symmetric",
``!p1 p2. (!c1 c2. p1 c1 c2 = p2 c2 c1)  ==>
  (!f emp e1 e2.
      (var_res_prop_binexpression f emp p1 e1 e2 =
       var_res_prop_binexpression f emp p2 e2 e1))``,
SIMP_TAC std_ss [var_res_prop_binexpression_def,
                 var_res_stack_proposition_def, LET_THM, EXTENSION,
                 IN_ABS] THEN
SIMP_TAC (std_ss++EQUIV_EXTRACT_ss) []);


val var_res_prop_equal_symmetric = store_thm ("var_res_prop_equal_symmetric",
``!f e1 e2. var_res_prop_equal f e1 e2 = var_res_prop_equal f e2 e1``,
REWRITE_TAC [var_res_prop_equal_def] THEN
MATCH_MP_TAC var_res_prop_binexpression_symmetric THEN
PROVE_TAC[]);


val var_res_prop_unequal_symmetric = store_thm ("var_res_prop_unequal_symmetric",
``!f e1 e2. var_res_prop_unequal f e1 e2 = var_res_prop_unequal f e2 e1``,
REWRITE_TAC [var_res_prop_unequal_def] THEN
MATCH_MP_TAC var_res_prop_binexpression_symmetric THEN
PROVE_TAC[]);


val var_res_prop_weak_equal_symmetric = store_thm ("var_res_prop_weak_equal_symmetric",
``!e1 e2. var_res_prop_weak_equal e1 e2 = var_res_prop_weak_equal e2 e1``,
REWRITE_TAC [var_res_prop_weak_equal_def, var_res_prop_weak_binexpression_def] THEN
MATCH_MP_TAC var_res_prop_binexpression_symmetric THEN
PROVE_TAC[]);

val var_res_prop_weak_unequal_symmetric = store_thm ("var_res_prop_weak_unequal_symmetric",
``!e1 e2. var_res_prop_weak_unequal e1 e2 = var_res_prop_weak_unequal e2 e1``,
REWRITE_TAC [var_res_prop_weak_unequal_def, var_res_prop_weak_binexpression_def] THEN
MATCH_MP_TAC var_res_prop_binexpression_symmetric THEN
PROVE_TAC[]);


val var_res_prop_equal_unequal_REWRITES =
store_thm ("var_res_prop_equal_unequal_REWRITES",
``(!f e. var_res_prop_equal f e e = var_res_exp_is_defined f e) /\
  (!e. var_res_prop_weak_equal e e = var_res_exp_weak_is_defined e) /\
  (!f e. var_res_prop_unequal f e e = asl_false) /\
  (!e. var_res_prop_weak_unequal e e = asl_false) /\

  (!c1 c2. var_res_prop_weak_equal (var_res_exp_const c1) (var_res_exp_const c2) =
             (K (c1 = c2))) /\
  (!c1 c2. var_res_prop_weak_unequal (var_res_exp_const c1) (var_res_exp_const c2) =
             (K (~(c1 = c2)))) /\
  (!f c1 c2. var_res_prop_equal f (var_res_exp_const c1) (var_res_exp_const c2) =
             var_res_bool_proposition f (c1 = c2)) /\
  (!f c1 c2. var_res_prop_unequal f (var_res_exp_const c1) (var_res_exp_const c2) =
             var_res_bool_proposition f (~(c1 = c2)))``,

SIMP_TAC std_ss [
   var_res_prop_unequal_def, var_res_prop_equal_def,
   var_res_prop_weak_unequal_def, var_res_prop_weak_equal_def,
   var_res_prop_weak_binexpression_def,
   var_res_prop_binexpression_REWRITES,
   prove (``(reflexive $=) /\ (irreflexive (\n1 n2. ~(n1 = n2)))``,
          SIMP_TAC std_ss [reflexive_def, irreflexive_def])]);


val var_res_prop_equal_unequal_EXPAND =
store_thm ("var_res_prop_equal_unequal_EXPAND",
``(!f e1 e2. var_res_prop_equal f e1 e2 =
     (\state. SND state IN asl_emp f /\ IS_SOME (e1 (FST state)) /\
              IS_SOME (e2 (FST state)) /\
              (THE (e1 (FST state)) = THE (e2 (FST state))))) /\
  (!f e1 e2. var_res_prop_unequal f e1 e2 =
     (\state. SND state IN asl_emp f /\ IS_SOME (e1 (FST state)) /\
              IS_SOME (e2 (FST state)) /\
              ~(THE (e1 (FST state)) = THE (e2 (FST state))))) /\
  (!e1 e2. var_res_prop_weak_equal e1 e2 =
     (\state. IS_SOME (e1 (FST state)) /\
              IS_SOME (e2 (FST state)) /\
              (THE (e1 (FST state)) = THE (e2 (FST state))))) /\
  (!e1 e2. var_res_prop_weak_unequal e1 e2 =
     (\state. IS_SOME (e1 (FST state)) /\
              IS_SOME (e2 (FST state)) /\
              ~(THE (e1 (FST state)) = THE (e2 (FST state)))))``,

SIMP_TAC std_ss [var_res_prop_unequal_def,
 var_res_prop_equal_def, var_res_prop_binexpression_def,
 var_res_stack_proposition_def, IN_ABS,
 LET_THM, var_res_prop_weak_equal_def,
 var_res_prop_weak_unequal_def,
 var_res_prop_weak_binexpression_def]);


val VAR_RES_IS_WEAK_STACK_PROPOSITION_def = Define
`VAR_RES_IS_WEAK_STACK_PROPOSITION (P:('a,'b,'c) var_res_proposition) =
 !s. s IN P ==> (!x. (FST s, x) IN P)`;


val VAR_RES_IS_WEAK_STACK_PROPOSITION___weak_stack_proposition = store_thm (
"VAR_RES_IS_WEAK_STACK_PROPOSITION___weak_stack_proposition",
``!f p. VAR_RES_IS_WEAK_STACK_PROPOSITION (var_res_stack_proposition f F p)``,
SIMP_TAC std_ss [VAR_RES_IS_WEAK_STACK_PROPOSITION_def,
                 var_res_stack_proposition_def, IN_ABS]);

val VAR_RES_IS_WEAK_STACK_PROPOSITION___asl_false = store_thm (
"VAR_RES_IS_WEAK_STACK_PROPOSITION___asl_false",
``VAR_RES_IS_WEAK_STACK_PROPOSITION asl_false``,
SIMP_TAC std_ss [VAR_RES_IS_WEAK_STACK_PROPOSITION_def, asl_bool_EVAL]);

val VAR_RES_IS_WEAK_STACK_PROPOSITION___asl_true = store_thm (
"VAR_RES_IS_WEAK_STACK_PROPOSITION___asl_true",
``VAR_RES_IS_WEAK_STACK_PROPOSITION asl_true``,
SIMP_TAC std_ss [VAR_RES_IS_WEAK_STACK_PROPOSITION_def, asl_bool_EVAL]);


val VAR_RES_IS_WEAK_STACK_PROPOSITION___asl_and = store_thm (
"VAR_RES_IS_WEAK_STACK_PROPOSITION___asl_and",
``!p1 p2.
      (VAR_RES_IS_WEAK_STACK_PROPOSITION p1 /\
       VAR_RES_IS_WEAK_STACK_PROPOSITION p2) ==>
       VAR_RES_IS_WEAK_STACK_PROPOSITION (asl_and p1 p2)``,
SIMP_TAC std_ss [VAR_RES_IS_WEAK_STACK_PROPOSITION_def, asl_bool_EVAL]);


val VAR_RES_IS_WEAK_STACK_PROPOSITION___asl_or = store_thm (
"VAR_RES_IS_WEAK_STACK_PROPOSITION___asl_or",
``!p1 p2.
      (VAR_RES_IS_WEAK_STACK_PROPOSITION p1 /\
       VAR_RES_IS_WEAK_STACK_PROPOSITION p2) ==>
       VAR_RES_IS_WEAK_STACK_PROPOSITION (asl_or p1 p2)``,
SIMP_TAC std_ss [VAR_RES_IS_WEAK_STACK_PROPOSITION_def, asl_bool_EVAL] THEN
METIS_TAC[]);


val VAR_RES_IS_WEAK_STACK_PROPOSITION___asl_neg = store_thm (
"VAR_RES_IS_WEAK_STACK_PROPOSITION___asl_neg",
``!p. VAR_RES_IS_WEAK_STACK_PROPOSITION p ==>
      VAR_RES_IS_WEAK_STACK_PROPOSITION (asl_neg p)``,
SIMP_TAC std_ss [VAR_RES_IS_WEAK_STACK_PROPOSITION_def, asl_bool_EVAL,
   PAIR_FORALL_THM] THEN
METIS_TAC[]);


val VAR_RES_IS_WEAK_STACK_PROPOSITION___ASL_INTUITIONISTIC_NEGATION = store_thm (
"VAR_RES_IS_WEAK_STACK_PROPOSITION___ASL_INTUITIONISTIC_NEGATION",
``!f p. IS_SEPARATION_COMBINATOR f /\ VAR_RES_IS_WEAK_STACK_PROPOSITION p ==>
        VAR_RES_IS_WEAK_STACK_PROPOSITION (ASL_INTUITIONISTIC_NEGATION (VAR_RES_COMBINATOR f) p)``,
SIMP_TAC std_ss [VAR_RES_IS_WEAK_STACK_PROPOSITION_def, asl_bool_EVAL,
   PAIR_FORALL_THM, ASL_INTUITIONISTIC_NEGATION_def, IN_ABS,
   ASL_IS_SEPARATE_def, VAR_RES_COMBINATOR_REWRITE,
   LET_THM, COND_NONE_SOME_REWRITES] THEN
SIMP_TAC std_ss [IS_SOME_EXISTS, GSYM RIGHT_EXISTS_AND_THM,
   GSYM LEFT_EXISTS_AND_THM, GSYM LEFT_FORALL_IMP_THM,
   IS_SEPARATION_COMBINATOR_EXPAND_THM] THEN
REPEAT STRIP_TAC THEN
METIS_TAC[]);


val var_res_bigstar_def = Define `var_res_bigstar f b =
   asl_bigstar (VAR_RES_COMBINATOR f) (BAG_INSERT (var_res_prop_stack_true f) b)`

val var_res_bigstar_list_def = Define `var_res_bigstar_list f l =
   asl_bigstar_list (VAR_RES_COMBINATOR f) ((var_res_prop_stack_true f)::l)`

val var_res_map_def = Define `var_res_map f P l =
   var_res_bigstar_list f (MAP P l)`;

val VAR_RES_IS_PURE_PROPOSITION_def = Define
`VAR_RES_IS_PURE_PROPOSITION f (P:('a,'b,'c) var_res_proposition) =
 !s. s IN P ==> (SND s IN asl_emp f)`


val VAR_RES_IS_PURE_PROPOSITION___pure_proposition = store_thm (
"VAR_RES_IS_PURE_PROPOSITION___pure_proposition",
``!f p. VAR_RES_IS_PURE_PROPOSITION f (var_res_stack_proposition f T p)``,
SIMP_TAC std_ss [VAR_RES_IS_PURE_PROPOSITION_def,
                 var_res_stack_proposition_def, IN_ABS]);

val VAR_RES_IS_PURE_PROPOSITION___asl_false = store_thm (
"VAR_RES_IS_PURE_PROPOSITION___asl_false",
``!f. VAR_RES_IS_PURE_PROPOSITION f asl_false``,
SIMP_TAC std_ss [VAR_RES_IS_PURE_PROPOSITION_def, asl_bool_EVAL]);


val VAR_RES_IS_PURE_PROPOSITION___asl_emp = store_thm (
"VAR_RES_IS_PURE_PROPOSITION___asl_emp",
``!f. IS_SEPARATION_COMBINATOR f ==>
      VAR_RES_IS_PURE_PROPOSITION f (asl_emp (VAR_RES_COMBINATOR f))``,
SIMP_TAC std_ss [
   VAR_RES_IS_PURE_PROPOSITION_def,
   VAR_RES_COMBINATOR_def, 
   PRODUCT_SEPARATION_COMBINATOR___asl_emp,
   IN_ABS]);


val VAR_RES_IS_PURE_PROPOSITION___asl_star =
store_thm ("VAR_RES_IS_PURE_PROPOSITION___asl_star",
``!f P1 P2.
IS_SEPARATION_COMBINATOR f ==>
(VAR_RES_IS_PURE_PROPOSITION f P1 /\
VAR_RES_IS_PURE_PROPOSITION f P2) ==>
VAR_RES_IS_PURE_PROPOSITION f (asl_star (VAR_RES_COMBINATOR f) P1 P2)``,

REPEAT GEN_TAC THEN STRIP_TAC THEN
FULL_SIMP_TAC std_ss [VAR_RES_IS_PURE_PROPOSITION_def,
  IS_SEPARATION_COMBINATOR_EXPAND_THM, asl_emp_def, IN_ABS,
  asl_star_def, VAR_RES_COMBINATOR_REWRITE] THEN
REPEAT STRIP_TAC THEN
RES_TAC THEN
Q.PAT_ASSUM `X = SOME (SND s)` MP_TAC THEN
ASM_SIMP_TAC std_ss [] THEN
METIS_TAC[]);




val VAR_RES_IS_PURE_PROPOSITION___asl_bigstar =
store_thm ("VAR_RES_IS_PURE_PROPOSITION___asl_bigstar",
``!f sfb. IS_SEPARATION_COMBINATOR f ==>
BAG_EVERY (VAR_RES_IS_PURE_PROPOSITION f) sfb ==>
VAR_RES_IS_PURE_PROPOSITION f (asl_bigstar (VAR_RES_COMBINATOR f) sfb)``,

REPEAT GEN_TAC THEN STRIP_TAC THEN
Tactical.REVERSE (Cases_on `FINITE_BAG sfb`) THEN1 (
   ASM_SIMP_TAC std_ss [asl_bigstar_def,
      VAR_RES_IS_PURE_PROPOSITION___asl_false]
) THEN
POP_ASSUM MP_TAC THEN
Q.SPEC_TAC (`sfb`, `sfb`) THEN
HO_MATCH_MP_TAC FINITE_BAG_INDUCT THEN
ASM_SIMP_TAC std_ss [IS_SEPARATION_COMBINATOR___VAR_RES_COMBINATOR,
   asl_bigstar_REWRITE, BAG_EVERY_THM,
   VAR_RES_IS_PURE_PROPOSITION___asl_emp,
   VAR_RES_IS_PURE_PROPOSITION___asl_star]);



val VAR_RES_IS_PURE_PROPOSITION___BASIC_PROPS = store_thm (
"VAR_RES_IS_PURE_PROPOSITION___BASIC_PROPS",
``VAR_RES_IS_PURE_PROPOSITION f (var_res_prop_equal f e1 e2) /\
  VAR_RES_IS_PURE_PROPOSITION f (var_res_prop_unequal f e1 e2) /\
  VAR_RES_IS_PURE_PROPOSITION f (var_res_prop_stack_true f) /\
  VAR_RES_IS_PURE_PROPOSITION f (asl_false) /\
  VAR_RES_IS_PURE_PROPOSITION f (var_res_exp_is_defined f e1) /\
  VAR_RES_IS_PURE_PROPOSITION f (var_res_bool_proposition f c) /\
  VAR_RES_IS_PURE_PROPOSITION f (var_res_prop_binexpression f T p e1 e2) /\
  VAR_RES_IS_PURE_PROPOSITION f (var_res_prop_expression f T p' el)``,

SIMP_TAC std_ss [VAR_RES_IS_PURE_PROPOSITION___pure_proposition,
   var_res_prop_expression_def,
   var_res_prop_binexpression_def, var_res_prop_unequal_def, var_res_prop_equal_def,
   var_res_bool_proposition_def, var_res_exp_is_defined_def,
   var_res_prop_stack_true_def, VAR_RES_IS_PURE_PROPOSITION___asl_false]);


val VAR_RES_IS_PURE_PROPOSITION___var_res_bigstar =
store_thm ("VAR_RES_IS_PURE_PROPOSITION___var_res_bigstar",
``!f sfb. IS_SEPARATION_COMBINATOR f ==>
BAG_EVERY (VAR_RES_IS_PURE_PROPOSITION f) sfb ==>
VAR_RES_IS_PURE_PROPOSITION f (var_res_bigstar f sfb)``,

REWRITE_TAC [var_res_bigstar_def] THEN
REPEAT STRIP_TAC THEN
MATCH_MP_TAC (MP_CANON VAR_RES_IS_PURE_PROPOSITION___asl_bigstar) THEN
ASM_SIMP_TAC std_ss [BAG_EVERY_THM,
   VAR_RES_IS_PURE_PROPOSITION___BASIC_PROPS]);


val VAR_RES_IS_PURE_PROPOSITION___EQ_REWRITE = store_thm (
"VAR_RES_IS_PURE_PROPOSITION___EQ_REWRITE",
``!f P. VAR_RES_IS_PURE_PROPOSITION f P =
        (!s. s IN P = (s IN P /\ (SND s IN asl_emp f)))``,
PROVE_TAC [VAR_RES_IS_PURE_PROPOSITION_def]);


val var_res_prop_binexpression_cond_def = Define `
var_res_prop_binexpression_cond (f:'d bin_option_function) p (e1:('a,'b,'c) var_res_expression)
    (e2:('a,'b,'c) var_res_expression) (p1:('a,'b,'d) var_res_proposition) p2 =
\s. IS_SOME (e1 (FST s)) /\ IS_SOME (e2 (FST s)) /\
    if (p (THE (e1 (FST s))) (THE (e2 (FST s)))) then s IN p1 else s IN p2`


val var_res_prop_binexpression_cond___CONST_REWRITE = store_thm
("var_res_prop_binexpression_cond___CONST_REWRITE",
``!f p c1 c2 p1 p2. var_res_prop_binexpression_cond f p (var_res_exp_const c1) (var_res_exp_const c2) p1 p2 =
  if (p c1 c2) then p1 else p2``,
SIMP_TAC (list_ss++EQUIV_EXTRACT_ss) [FUN_EQ_THM, var_res_prop_binexpression_cond_def,
  var_res_exp_const_def, IN_DEF, COND_RAND, COND_RATOR]);



(******************************************************
 Stack Imprecise
 ******************************************************)

val VAR_RES_IS_STACK_IMPRECISE_def = Define `
    VAR_RES_IS_STACK_IMPRECISE P =
    (!st1 st2 h. (VAR_RES_STACK___IS_EQUAL_UPTO_PERMISSIONS EMPTY st1 st2) ==>
          ((st1,h) IN P = (st2,h) IN P)) /\
    (!st1 st2 h. (VAR_RES_STACK_IS_SUBSTATE st1 st2 /\ (st1,h) IN P) ==>
                 (st2,h) IN P) `;

val VAR_RES_IS_STACK_IMPRECISE___USED_VARS_def = Define `
    VAR_RES_IS_STACK_IMPRECISE___USED_VARS exS P =
    ((!s. ((DRESTRICT (FST s) exS, SND s)) IN P = s IN P) /\
     (VAR_RES_IS_STACK_IMPRECISE P))`;


val VAR_RES_IS_STACK_IMPRECISE___USED_VARS___ALTERNATIVE_DEF =
store_thm ("VAR_RES_IS_STACK_IMPRECISE___USED_VARS___ALTERNATIVE_DEF",
``!vs P. VAR_RES_IS_STACK_IMPRECISE___USED_VARS vs P =

(!s s2. (s2 IN P /\ (SND s2 = SND s) /\
     FDOM (FST s2) INTER vs SUBSET FDOM (FST s) /\
     (!v.  v IN FDOM (FST s2) /\ v IN vs ==>
            (FST ((FST s) ' v) = FST ((FST s2) ' v))))
==> s IN P)``,


SIMP_TAC std_ss [VAR_RES_IS_STACK_IMPRECISE___USED_VARS_def,
                 VAR_RES_IS_STACK_IMPRECISE_def,
                 NOT_IN_EMPTY] THEN
REPEAT GEN_TAC THEN EQ_TAC THEN STRIP_TAC THEN REPEAT CONJ_TAC THENL [
   REPEAT STRIP_TAC THEN
   `?st1 st2 h. (s = (st1,h)) /\ (s2 = (st2,h))` by ALL_TAC THEN1 (
      Cases_on `s` THEN Cases_on `s2` THEN FULL_SIMP_TAC std_ss []
   ) THEN
   FULL_SIMP_TAC std_ss [] THEN
   NTAC 2 (POP_ASSUM (K ALL_TAC)) THEN
   Q.ABBREV_TAC `st1' = (VAR_RES_STACK___UPDATE_PERMISSION_ALL (\v. (SOME p)) st1)` THEN
   Q.ABBREV_TAC `st2' = (VAR_RES_STACK___UPDATE_PERMISSION_ALL (\v. (SOME p)) st2)` THEN
   `((st1,h) IN P = (st1',h) IN P) /\
    ((st2,h) IN P = (st2',h) IN P)` by ALL_TAC THEN1 (
       Q.UNABBREV_TAC `st1'` THEN
       Q.UNABBREV_TAC `st2'` THEN
       Q.PAT_ASSUM `!st1 st2 h. X ==> (Y = Z)` (fn thm => CONSEQ_REWRITE_TAC ([thm, VAR_RES_STACK___IS_EQUAL_UPTO_PERMISSIONS_THM], [],[])) THEN
       SIMP_TAC std_ss [NOT_IN_EMPTY]
   ) THEN
   FULL_SIMP_TAC std_ss [] THEN
   NTAC 2 (POP_ASSUM (K ALL_TAC)) THEN

   Q.ABBREV_TAC `st2'' = (DRESTRICT st2' vs)` THEN
   `(st2'',h) IN P` by METIS_TAC [pairTheory.FST, pairTheory.SND] THEN

   Q.PAT_ASSUM `!st1 st2 h. X ==> (st2, h) IN P` MATCH_MP_TAC THEN
   Q.EXISTS_TAC `st2''` THEN

   Q.UNABBREV_TAC `st1'` THEN
   Q.UNABBREV_TAC `st2''` THEN
   Q.UNABBREV_TAC `st2'` THEN
   FULL_SIMP_TAC std_ss [VAR_RES_STACK_IS_SUBSTATE_REWRITE,
                        DRESTRICT_DEF, VAR_RES_STACK___UPDATE_PERMISSION_ALL_def,
                        FUN_FMAP_DEF, FDOM_FINITE, IN_INTER, SUBSET_DEF,
                        IS_VAR_RES_SUBPERMISSION_THM],



   REPEAT STRIP_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THENL [
      Q.PAT_ASSUM `!s s2. X` MATCH_MP_TAC THEN
      Q.EXISTS_TAC `(DRESTRICT (FST s) vs,SND s)` THEN
      ASM_SIMP_TAC std_ss [DRESTRICT_DEF, SUBSET_DEF, IN_INTER],

      Q.PAT_ASSUM `!s s2. X` MATCH_MP_TAC THEN
      Q.EXISTS_TAC `s` THEN
      ASM_SIMP_TAC std_ss [DRESTRICT_DEF, SUBSET_DEF, IN_INTER]
   ],



   Tactical.REVERSE (`!st1 st2 h.
      (VAR_RES_STACK___IS_EQUAL_UPTO_PERMISSIONS {} st1 st2 /\
      (st1,h) IN P) ==> (st2,h) IN P` by ALL_TAC) THEN1 (
      PROVE_TAC[REWRITE_RULE [COMM_DEF]
                  (CONJUNCT1 VAR_RES_STACK___IS_EQUAL_UPTO_PERMISSIONS_THM)]
   ) THEN
   REPEAT STRIP_TAC THEN
   Q.PAT_ASSUM `!s s2. X` MATCH_MP_TAC THEN
   Q.EXISTS_TAC `(st1,h)` THEN
   FULL_SIMP_TAC std_ss [VAR_RES_STACK___IS_EQUAL_UPTO_PERMISSIONS_def,
                         SUBSET_DEF, IN_INTER],


   REPEAT STRIP_TAC THEN
   Q.PAT_ASSUM `!s s2. X` MATCH_MP_TAC THEN
   Q.EXISTS_TAC `(st1,h)` THEN
   FULL_SIMP_TAC std_ss [VAR_RES_STACK_IS_SUBSTATE_REWRITE, SUBSET_DEF, IN_INTER]
]);




val VAR_RES_IS_STACK_IMPRECISE___ALTERNATIVE_DEF = store_thm (
"VAR_RES_IS_STACK_IMPRECISE___ALTERNATIVE_DEF",
``!P. VAR_RES_IS_STACK_IMPRECISE P = VAR_RES_IS_STACK_IMPRECISE___USED_VARS UNIV P``,
SIMP_TAC std_ss [VAR_RES_IS_STACK_IMPRECISE___USED_VARS_def, DRESTRICT_UNIV]);



val VAR_RES_IS_STACK_IMPRECISE___ALTERNATIVE_DEF_2=
store_thm ("VAR_RES_IS_STACK_IMPRECISE___ALTERNATIVE_DEF_2",
``!P. VAR_RES_IS_STACK_IMPRECISE P =
(!s s2. (s2 IN P /\ (SND s2 = SND s) /\
     FDOM (FST s2) SUBSET FDOM (FST s) /\
     (!v.  v IN FDOM (FST s2) ==>
            (FST ((FST s) ' v) = FST ((FST s2) ' v)))) ==> s IN P)``,

SIMP_TAC std_ss [VAR_RES_IS_STACK_IMPRECISE___ALTERNATIVE_DEF,
       VAR_RES_IS_STACK_IMPRECISE___USED_VARS___ALTERNATIVE_DEF,
       IN_UNIV, INTER_UNIV]);




val VAR_RES_IS_STACK_IMPRECISE___SUBSTATE = store_thm (
"VAR_RES_IS_STACK_IMPRECISE___SUBSTATE",
``!P s s'. (VAR_RES_IS_STACK_IMPRECISE P /\
      (s' IN P) /\ (VAR_RES_STACK_IS_SUBSTATE (FST s') (FST s))) ==>
      (FST s, SND s') IN P``,

REPEAT STRIP_TAC THEN
FULL_SIMP_TAC std_ss [VAR_RES_IS_STACK_IMPRECISE_def] THEN
Cases_on `s` THEN Cases_on `s'` THEN
FULL_SIMP_TAC std_ss [] THEN
METIS_TAC[]);


val VAR_RES_IS_STACK_IMPRECISE___IMP = store_thm (
"VAR_RES_IS_STACK_IMPRECISE___IMP",
``!P vs. VAR_RES_IS_STACK_IMPRECISE___USED_VARS vs P ==>
         VAR_RES_IS_STACK_IMPRECISE P``,
SIMP_TAC std_ss [VAR_RES_IS_STACK_IMPRECISE___USED_VARS_def]);



val VAR_RES_IS_STACK_IMPRECISE___USED_VARS___SUBSET = store_thm (
"VAR_RES_IS_STACK_IMPRECISE___USED_VARS___SUBSET",
``!exS1 exS2 P. ((exS1 SUBSET exS2) /\
VAR_RES_IS_STACK_IMPRECISE___USED_VARS exS1 P) ==>
VAR_RES_IS_STACK_IMPRECISE___USED_VARS exS2 P``,

SIMP_TAC std_ss [VAR_RES_IS_STACK_IMPRECISE___USED_VARS_def] THEN
REPEAT STRIP_TAC THEN
Tactical.REVERSE (
   `DRESTRICT (DRESTRICT (FST s) exS2) exS1 = (DRESTRICT (FST s) exS1)` by ALL_TAC) THEN1 (
   METIS_TAC[pairTheory.FST, pairTheory.SND]
) THEN
ASM_SIMP_TAC std_ss [DRESTRICT_DRESTRICT] THEN
PROVE_TAC[INTER_SUBSET_EQN]);




val VAR_RES_IS_STACK_IMPRECISE___USED_VARS___asl_false =
store_thm ("VAR_RES_IS_STACK_IMPRECISE___USED_VARS___asl_false",
``!vs. VAR_RES_IS_STACK_IMPRECISE___USED_VARS vs asl_false``,
SIMP_TAC std_ss [VAR_RES_IS_STACK_IMPRECISE___USED_VARS___ALTERNATIVE_DEF,
                 asl_bool_EVAL]);


val VAR_RES_IS_STACK_IMPRECISE___asl_false =
store_thm ("VAR_RES_IS_STACK_IMPRECISE___asl_false",
``VAR_RES_IS_STACK_IMPRECISE asl_false``,
SIMP_TAC std_ss [VAR_RES_IS_STACK_IMPRECISE___IMP,
                 VAR_RES_IS_STACK_IMPRECISE___USED_VARS___asl_false]);



val VAR_RES_IS_STACK_IMPRECISE___USED_VARS___asl_true =
store_thm ("VAR_RES_IS_STACK_IMPRECISE___USED_VARS___asl_true",
``!vs. VAR_RES_IS_STACK_IMPRECISE___USED_VARS vs asl_true``,
SIMP_TAC std_ss [VAR_RES_IS_STACK_IMPRECISE___USED_VARS___ALTERNATIVE_DEF,
                 asl_bool_EVAL]);


val VAR_RES_IS_STACK_IMPRECISE___asl_true =
store_thm ("VAR_RES_IS_STACK_IMPRECISE___asl_true",
``VAR_RES_IS_STACK_IMPRECISE asl_true``,
SIMP_TAC std_ss [VAR_RES_IS_STACK_IMPRECISE___IMP,
                 VAR_RES_IS_STACK_IMPRECISE___USED_VARS___asl_true]);



val VAR_RES_IS_STACK_IMPRECISE___USED_VARS___var_res_bool_proposition =
store_thm ("VAR_RES_IS_STACK_IMPRECISE___USED_VARS___var_res_bool_proposition",
``!f vs c. VAR_RES_IS_STACK_IMPRECISE___USED_VARS vs (var_res_bool_proposition f c)``,
SIMP_TAC (std_ss++CONJ_ss) [VAR_RES_IS_STACK_IMPRECISE___USED_VARS___ALTERNATIVE_DEF,
   var_res_bool_proposition_REWRITE, IN_ABS]);


val VAR_RES_IS_STACK_IMPRECISE___var_res_bool_proposition =
store_thm ("VAR_RES_IS_STACK_IMPRECISE___var_res_bool_proposition",
``!f c. VAR_RES_IS_STACK_IMPRECISE (var_res_bool_proposition f c)``,
SIMP_TAC std_ss [VAR_RES_IS_STACK_IMPRECISE___ALTERNATIVE_DEF,
                 VAR_RES_IS_STACK_IMPRECISE___USED_VARS___var_res_bool_proposition]);


val VAR_RES_IS_STACK_IMPRECISE___USED_VARS___var_res_prop_stack_true =
store_thm ("VAR_RES_IS_STACK_IMPRECISE___USED_VARS___var_res_prop_stack_true",
``!f vs. VAR_RES_IS_STACK_IMPRECISE___USED_VARS vs (var_res_prop_stack_true f)``,
REWRITE_TAC[var_res_prop_stack_true_def,
            VAR_RES_IS_STACK_IMPRECISE___USED_VARS___var_res_bool_proposition]);


val VAR_RES_IS_STACK_IMPRECISE___var_res_prop_stack_true =
store_thm ("VAR_RES_IS_STACK_IMPRECISE___var_res_prop_stack_true",
``!f. VAR_RES_IS_STACK_IMPRECISE (var_res_prop_stack_true f)``,
SIMP_TAC std_ss [VAR_RES_IS_STACK_IMPRECISE___IMP,
                 VAR_RES_IS_STACK_IMPRECISE___USED_VARS___var_res_prop_stack_true]);



val VAR_RES_IS_STACK_IMPRECISE___asl_emp =
store_thm ("VAR_RES_IS_STACK_IMPRECISE___asl_emp",
``!f. IS_SEPARATION_COMBINATOR f ==>
      ~(VAR_RES_IS_STACK_IMPRECISE (asl_emp (VAR_RES_COMBINATOR f)))``,
SIMP_TAC std_ss [VAR_RES_IS_STACK_IMPRECISE___ALTERNATIVE_DEF_2,
                 asl_emp___VAR_RES_COMBINATOR, IN_ABS] THEN
SIMP_TAC (std_ss++CONJ_ss) [PAIR_EXISTS_THM, FDOM_FEMPTY, NOT_IN_EMPTY,
                            EMPTY_SUBSET] THEN
SIMP_TAC std_ss [IS_SEPARATION_COMBINATOR_EXPAND_THM, asl_emp_def,
                 IN_ABS, GSYM LEFT_EXISTS_AND_THM] THEN
REPEAT STRIP_TAC THEN
Q.EXISTS_TAC `FEMPTY |+ (ARB,ARB)` THEN
Q.EXISTS_TAC `uf x` THEN
Q.EXISTS_TAC `x` THEN
ASM_SIMP_TAC std_ss [NOT_EQ_FEMPTY_FUPDATE]);


val VAR_RES_IS_STACK_IMPRECISE___USED_VARS___asl_emp =
store_thm ("VAR_RES_IS_STACK_IMPRECISE___USED_VARS___asl_emp",
``!f vs. IS_SEPARATION_COMBINATOR f ==>
         ~(VAR_RES_IS_STACK_IMPRECISE___USED_VARS vs (asl_emp (VAR_RES_COMBINATOR f)))``,
PROVE_TAC [VAR_RES_IS_STACK_IMPRECISE___IMP, VAR_RES_IS_STACK_IMPRECISE___asl_emp]);



val VAR_RES_IS_STACK_IMPRECISE___asl_or = store_thm (
"VAR_RES_IS_STACK_IMPRECISE___asl_or",
``!P1 P2.
(VAR_RES_IS_STACK_IMPRECISE P1 /\ VAR_RES_IS_STACK_IMPRECISE P2) ==>
 VAR_RES_IS_STACK_IMPRECISE (asl_or P1 P2)``,

SIMP_TAC std_ss [VAR_RES_IS_STACK_IMPRECISE_def, asl_bool_EVAL] THEN
PROVE_TAC[]);


val VAR_RES_IS_STACK_IMPRECISE___USED_VARS___asl_or = store_thm (
"VAR_RES_IS_STACK_IMPRECISE___USED_VARS___asl_or",
``!exS P1 P2.
(VAR_RES_IS_STACK_IMPRECISE___USED_VARS exS P1 /\
 VAR_RES_IS_STACK_IMPRECISE___USED_VARS exS P2) ==>
VAR_RES_IS_STACK_IMPRECISE___USED_VARS exS (asl_or P1 P2)``,

SIMP_TAC std_ss [VAR_RES_IS_STACK_IMPRECISE___USED_VARS_def, asl_bool_EVAL] THEN
PROVE_TAC[VAR_RES_IS_STACK_IMPRECISE___asl_or]);




val VAR_RES_IS_STACK_IMPRECISE___asl_and = store_thm (
"VAR_RES_IS_STACK_IMPRECISE___asl_and",
``!P1 P2.
(VAR_RES_IS_STACK_IMPRECISE P1 /\ VAR_RES_IS_STACK_IMPRECISE P2) ==>
 VAR_RES_IS_STACK_IMPRECISE (asl_and P1 P2)``,

SIMP_TAC std_ss [VAR_RES_IS_STACK_IMPRECISE_def, asl_bool_EVAL] THEN
PROVE_TAC[]);


val VAR_RES_IS_STACK_IMPRECISE___USED_VARS___asl_and = store_thm (
"VAR_RES_IS_STACK_IMPRECISE___USED_VARS___asl_and",
``!exS P1 P2.
(VAR_RES_IS_STACK_IMPRECISE___USED_VARS exS P1 /\
 VAR_RES_IS_STACK_IMPRECISE___USED_VARS exS P2) ==>
VAR_RES_IS_STACK_IMPRECISE___USED_VARS exS (asl_and P1 P2)``,

SIMP_TAC std_ss [VAR_RES_IS_STACK_IMPRECISE___USED_VARS_def, asl_bool_EVAL] THEN
PROVE_TAC[VAR_RES_IS_STACK_IMPRECISE___asl_and]);



val VAR_RES_IS_STACK_IMPRECISE___const = store_thm (
"VAR_RES_IS_STACK_IMPRECISE___const",
``!c. VAR_RES_IS_STACK_IMPRECISE (K c)``,
SIMP_TAC std_ss [VAR_RES_IS_STACK_IMPRECISE_def, IN_DEF]);


val VAR_RES_IS_STACK_IMPRECISE___USED_VARS___const = store_thm (
"VAR_RES_IS_STACK_IMPRECISE___USED_VARS___const",
``!exS c. VAR_RES_IS_STACK_IMPRECISE___USED_VARS exS (K c)``,
SIMP_TAC std_ss [VAR_RES_IS_STACK_IMPRECISE___USED_VARS_def, IN_DEF,
                 VAR_RES_IS_STACK_IMPRECISE_def]);


val VAR_RES_IS_STACK_IMPRECISE___USED_VARS___asl_trivial_cond = store_thm (
"VAR_RES_IS_STACK_IMPRECISE___USED_VARS___asl_trivial_cond",
``!exS c P.
(c ==> VAR_RES_IS_STACK_IMPRECISE___USED_VARS exS P) ==>
VAR_RES_IS_STACK_IMPRECISE___USED_VARS exS (asl_trivial_cond c P)``,

Cases_on `c` THEN
SIMP_TAC std_ss [asl_trivial_cond_TF,
   VAR_RES_IS_STACK_IMPRECISE___USED_VARS___asl_false]);


val VAR_RES_IS_STACK_IMPRECISE___asl_trivial_cond = store_thm (
"VAR_RES_IS_STACK_IMPRECISE___asl_trivial_cond",
``!c P.
(c ==> VAR_RES_IS_STACK_IMPRECISE P) ==>
VAR_RES_IS_STACK_IMPRECISE (asl_trivial_cond c P)``,
Cases_on `c` THEN
SIMP_TAC std_ss [asl_trivial_cond_TF, VAR_RES_IS_STACK_IMPRECISE___asl_false]);


val VAR_RES_IS_STACK_IMPRECISE___USED_VARS___cond = store_thm (
"VAR_RES_IS_STACK_IMPRECISE___USED_VARS___cond",
``!exS c P1 P2.
(if c then VAR_RES_IS_STACK_IMPRECISE___USED_VARS exS P1 else
           VAR_RES_IS_STACK_IMPRECISE___USED_VARS exS P2) ==>
VAR_RES_IS_STACK_IMPRECISE___USED_VARS exS (if c then P1 else P2)``,
Cases_on `c` THEN REWRITE_TAC[]);


val VAR_RES_IS_STACK_IMPRECISE___cond = store_thm (
"VAR_RES_IS_STACK_IMPRECISE___cond",
``!c P1 P2.
(if c then VAR_RES_IS_STACK_IMPRECISE P1 else
           VAR_RES_IS_STACK_IMPRECISE P2) ==>
VAR_RES_IS_STACK_IMPRECISE (if c then P1 else P2)``,
Cases_on `c` THEN REWRITE_TAC[]);


val VAR_RES_IS_STACK_IMPRECISE___USED_VARS___asl_exists = store_thm (
"VAR_RES_IS_STACK_IMPRECISE___USED_VARS___asl_exists",
``!exS P.
(!s x. P x s ==> (?x2. P x2 s /\ VAR_RES_IS_STACK_IMPRECISE___USED_VARS exS (P x2))) ==>
VAR_RES_IS_STACK_IMPRECISE___USED_VARS exS (asl_exists x. P x)``,

REPEAT STRIP_TAC THEN
FULL_SIMP_TAC std_ss [VAR_RES_IS_STACK_IMPRECISE___USED_VARS___ALTERNATIVE_DEF,
       asl_exists_def, IN_DEF] THEN
METIS_TAC[]);


val VAR_RES_IS_STACK_IMPRECISE___asl_exists = store_thm (
"VAR_RES_IS_STACK_IMPRECISE___asl_exists",
``!P.
(!s x. P x s ==> (?x2. P x2 s /\ VAR_RES_IS_STACK_IMPRECISE (P x2))) ==>
VAR_RES_IS_STACK_IMPRECISE (asl_exists x. P x)``,
METIS_TAC [VAR_RES_IS_STACK_IMPRECISE___ALTERNATIVE_DEF,
           VAR_RES_IS_STACK_IMPRECISE___USED_VARS___asl_exists]);



val VAR_RES_IS_STACK_IMPRECISE___USED_VARS___asl_exists_direct = store_thm (
"VAR_RES_IS_STACK_IMPRECISE___USED_VARS___asl_exists_direct",
``!exS P. (!x. VAR_RES_IS_STACK_IMPRECISE___USED_VARS exS (P x)) ==>
          VAR_RES_IS_STACK_IMPRECISE___USED_VARS exS (asl_exists x. P x)``,

REPEAT STRIP_TAC THEN
MATCH_MP_TAC VAR_RES_IS_STACK_IMPRECISE___USED_VARS___asl_exists THEN
REPEAT STRIP_TAC THEN
Q.EXISTS_TAC `x` THEN
ASM_REWRITE_TAC[]);


val VAR_RES_IS_STACK_IMPRECISE___asl_exists_direct = store_thm (
"VAR_RES_IS_STACK_IMPRECISE___asl_exists_direct",
``!P. (!x. VAR_RES_IS_STACK_IMPRECISE (P x)) ==>
       VAR_RES_IS_STACK_IMPRECISE (asl_exists x. P x)``,
METIS_TAC [VAR_RES_IS_STACK_IMPRECISE___ALTERNATIVE_DEF,
           VAR_RES_IS_STACK_IMPRECISE___USED_VARS___asl_exists_direct]);






val VAR_RES_IS_STACK_IMPRECISE___USED_VARS___asl_star = store_thm (
"VAR_RES_IS_STACK_IMPRECISE___USED_VARS___asl_star",
``!f exS P1 P2.
  (VAR_RES_IS_STACK_IMPRECISE___USED_VARS exS P1 /\
   VAR_RES_IS_STACK_IMPRECISE___USED_VARS exS P2) ==>
  VAR_RES_IS_STACK_IMPRECISE___USED_VARS exS (asl_star (VAR_RES_COMBINATOR f) P1 P2)``,

SIMP_TAC std_ss [VAR_RES_IS_STACK_IMPRECISE___USED_VARS___ALTERNATIVE_DEF,
                 asl_star_def, IN_ABS, VAR_RES_COMBINATOR_def,
                 PRODUCT_SEPARATION_COMBINATOR_REWRITE] THEN
REPEAT STRIP_TAC THEN
Q.EXISTS_TAC `(VAR_RES_STACK_SPLIT EMPTY EMPTY (FST s), SND p)` THEN
Q.EXISTS_TAC `(VAR_RES_STACK_SPLIT EMPTY EMPTY (FST s), SND q)` THEN
ASM_SIMP_TAC std_ss [VAR_RES_STACK_COMBINE___VAR_RES_STACK_SPLIT,
                     INTER_EMPTY, COMPL_EMPTY, DRESTRICT_UNIV] THEN
Q.PAT_ASSUM `!s s2. X ==> s IN P1` (fn thm =>  CONSEQ_REWRITE_TAC ([], [
   Q.SPECL [`(VAR_RES_STACK_SPLIT {} {} (FST s), SND p)`] thm], [])) THEN
Q.PAT_ASSUM `!s s2. X ==> s IN P2` (fn thm =>  CONSEQ_REWRITE_TAC ([], [
   Q.SPECL [`(VAR_RES_STACK_SPLIT {} {} (FST s), SND q)`] thm], [])) THEN
SIMP_TAC std_ss [GSYM LEFT_EXISTS_AND_THM, GSYM RIGHT_EXISTS_AND_THM] THEN
Q.EXISTS_TAC `p` THEN Q.EXISTS_TAC `q` THEN
FULL_SIMP_TAC (std_ss++CONJ_ss) [VAR_RES_STACK_SPLIT___REWRITES, DIFF_EMPTY,
                                 NOT_IN_EMPTY, SUBSET_DEF, IN_INTER,
                                 SOME___VAR_RES_STACK_COMBINE] THEN
Q.PAT_ASSUM `FST s2 = X` ASSUME_TAC THEN
FULL_SIMP_TAC std_ss [FMERGE_DEF, IN_UNION, VAR_RES_STACK_COMBINE___MERGE_FUNC_def,
                      COND_REWRITES, VAR_RES_STACK_IS_SEPARATE_def]);




val VAR_RES_IS_STACK_IMPRECISE___asl_star = store_thm (
"VAR_RES_IS_STACK_IMPRECISE___asl_star",
``!P1 P2 f. (VAR_RES_IS_STACK_IMPRECISE P1 /\
           VAR_RES_IS_STACK_IMPRECISE P2) ==>
          VAR_RES_IS_STACK_IMPRECISE (asl_star (VAR_RES_COMBINATOR f) P1 P2)``,
METIS_TAC[VAR_RES_IS_STACK_IMPRECISE___ALTERNATIVE_DEF,
          VAR_RES_IS_STACK_IMPRECISE___USED_VARS___asl_star]);







val VAR_RES_IS_STACK_IMPRECISE___USED_VARS___asl_bigstar = store_thm (
"VAR_RES_IS_STACK_IMPRECISE___USED_VARS___asl_bigstar",
``
!f. IS_SEPARATION_COMBINATOR f ==>
!sfb exS.
      (~(sfb = EMPTY_BAG) /\
      !sf. BAG_IN sf sfb ==> (VAR_RES_IS_STACK_IMPRECISE___USED_VARS exS sf)) ==>
(VAR_RES_IS_STACK_IMPRECISE___USED_VARS exS
         (asl_bigstar (VAR_RES_COMBINATOR f) sfb))``,

GEN_TAC THEN STRIP_TAC THEN
IMP_RES_TAC IS_SEPARATION_COMBINATOR___VAR_RES_COMBINATOR THEN
GEN_TAC THEN
Tactical.REVERSE (Cases_on `FINITE_BAG sfb`) THEN1 (
    ASM_REWRITE_TAC
       [asl_bigstar_def, VAR_RES_IS_STACK_IMPRECISE___USED_VARS___asl_false]
) THEN
POP_ASSUM MP_TAC THEN Q.SPEC_TAC (`sfb`, `sfb`) THEN
HO_MATCH_MP_TAC FINITE_BAG_INDUCT THEN
ASM_SIMP_TAC (std_ss++BAG_ss) [BAG_INSERT_NOT_EMPTY, bagTheory.BAG_IN_BAG_INSERT,
                               DISJ_IMP_THM, FORALL_AND_THM, asl_bigstar_REWRITE] THEN
GEN_TAC THEN Cases_on `sfb = EMPTY_BAG` THENL [
   ASM_SIMP_TAC std_ss [asl_bigstar_REWRITE, asl_star___PROPERTIES],

   CONSEQ_REWRITE_TAC ([VAR_RES_IS_STACK_IMPRECISE___USED_VARS___asl_star], [],[]) THEN
   ASM_SIMP_TAC std_ss []
]);



val VAR_RES_IS_STACK_IMPRECISE___asl_bigstar = store_thm (
"VAR_RES_IS_STACK_IMPRECISE___asl_bigstar",
``!f sfb. (IS_SEPARATION_COMBINATOR f /\ (~(sfb = EMPTY_BAG)) /\
(!sf. BAG_IN sf sfb ==> (VAR_RES_IS_STACK_IMPRECISE sf))) ==>
(VAR_RES_IS_STACK_IMPRECISE (asl_bigstar (VAR_RES_COMBINATOR f) sfb))``,
SIMP_TAC std_ss [VAR_RES_IS_STACK_IMPRECISE___ALTERNATIVE_DEF,
       VAR_RES_IS_STACK_IMPRECISE___USED_VARS___asl_bigstar]);




val VAR_RES_IS_STACK_IMPRECISE___USED_VARS___asl_bigstar_list = store_thm (
"VAR_RES_IS_STACK_IMPRECISE___USED_VARS___asl_bigstar_list",
``!f. IS_SEPARATION_COMBINATOR f ==>
!L exS. ((~(L = [])) /\
(!sf. MEM sf L ==> (VAR_RES_IS_STACK_IMPRECISE___USED_VARS exS sf))) ==>
(VAR_RES_IS_STACK_IMPRECISE___USED_VARS exS (asl_bigstar_list (VAR_RES_COMBINATOR f) L))``,

REPEAT STRIP_TAC THEN
ASM_SIMP_TAC std_ss [
   asl_bigstar_list___DEF2,
   IS_SEPARATION_COMBINATOR___VAR_RES_COMBINATOR] THEN
MATCH_MP_TAC (SIMP_RULE std_ss [AND_IMP_INTRO, GSYM RIGHT_FORALL_IMP_THM]
                  VAR_RES_IS_STACK_IMPRECISE___USED_VARS___asl_bigstar) THEN
ASM_SIMP_TAC std_ss [IN_LIST_TO_BAG, LIST_TO_BAG_EQ_EMPTY]);



val VAR_RES_IS_STACK_IMPRECISE___asl_bigstar_list = store_thm (
"VAR_RES_IS_STACK_IMPRECISE___asl_bigstar_list",
``!f. IS_SEPARATION_COMBINATOR f ==>
!L.((~(L = [])) /\
(!sf. MEM sf L ==> (VAR_RES_IS_STACK_IMPRECISE sf))) ==>
(VAR_RES_IS_STACK_IMPRECISE (asl_bigstar_list (VAR_RES_COMBINATOR f) L))``,

SIMP_TAC std_ss [VAR_RES_IS_STACK_IMPRECISE___ALTERNATIVE_DEF,
       VAR_RES_IS_STACK_IMPRECISE___USED_VARS___asl_bigstar_list]);



val VAR_RES_IS_STACK_IMPRECISE___USED_VARS___var_res_bigstar = store_thm (
"VAR_RES_IS_STACK_IMPRECISE___USED_VARS___var_res_bigstar",
``!f sfb exS.
(IS_SEPARATION_COMBINATOR f /\
 BAG_EVERY (VAR_RES_IS_STACK_IMPRECISE___USED_VARS exS) sfb) ==>
(VAR_RES_IS_STACK_IMPRECISE___USED_VARS exS
         (var_res_bigstar f sfb))``,

REWRITE_TAC [var_res_bigstar_def] THEN
REPEAT STRIP_TAC THEN
MATCH_MP_TAC (MP_CANON VAR_RES_IS_STACK_IMPRECISE___USED_VARS___asl_bigstar) THEN
FULL_SIMP_TAC std_ss [BAG_EVERY,
   BAG_INSERT_NOT_EMPTY, BAG_IN_BAG_INSERT, DISJ_IMP_THM, FORALL_AND_THM,
   VAR_RES_IS_STACK_IMPRECISE___USED_VARS___var_res_prop_stack_true]);



val VAR_RES_IS_STACK_IMPRECISE___var_res_bigstar = store_thm (
"VAR_RES_IS_STACK_IMPRECISE___var_res_bigstar",
``!f sfb.
(IS_SEPARATION_COMBINATOR f /\
 BAG_EVERY VAR_RES_IS_STACK_IMPRECISE sfb) ==>
(VAR_RES_IS_STACK_IMPRECISE (var_res_bigstar f sfb))``,
SIMP_TAC std_ss [VAR_RES_IS_STACK_IMPRECISE___ALTERNATIVE_DEF,
   BAG_EVERY, VAR_RES_IS_STACK_IMPRECISE___USED_VARS___var_res_bigstar]);



val VAR_RES_IS_STACK_IMPRECISE___USED_VARS___var_res_bigstar_list = store_thm (
"VAR_RES_IS_STACK_IMPRECISE___USED_VARS___var_res_bigstar_list",
``!f L exS. (IS_SEPARATION_COMBINATOR f /\
         EVERY (VAR_RES_IS_STACK_IMPRECISE___USED_VARS exS) L) ==>
(VAR_RES_IS_STACK_IMPRECISE___USED_VARS exS (var_res_bigstar_list f L))``,

REWRITE_TAC[var_res_bigstar_list_def] THEN
REPEAT STRIP_TAC THEN
MATCH_MP_TAC (MP_CANON VAR_RES_IS_STACK_IMPRECISE___USED_VARS___asl_bigstar_list) THEN
FULL_SIMP_TAC list_ss [EVERY_MEM, DISJ_IMP_THM, FORALL_AND_THM,
   VAR_RES_IS_STACK_IMPRECISE___USED_VARS___var_res_prop_stack_true]);


val VAR_RES_IS_STACK_IMPRECISE___var_res_bigstar_list = store_thm (
"VAR_RES_IS_STACK_IMPRECISE___var_res_bigstar_list",
``!f L. (IS_SEPARATION_COMBINATOR f /\
       EVERY VAR_RES_IS_STACK_IMPRECISE L) ==>
(VAR_RES_IS_STACK_IMPRECISE (var_res_bigstar_list f L))``,
SIMP_TAC std_ss [VAR_RES_IS_STACK_IMPRECISE___ALTERNATIVE_DEF,
   EVERY_MEM, VAR_RES_IS_STACK_IMPRECISE___USED_VARS___var_res_bigstar_list]);



val VAR_RES_IS_STACK_IMPRECISE___USED_VARS___var_res_map = store_thm (
"VAR_RES_IS_STACK_IMPRECISE___USED_VARS___var_res_map",
``!f P L exS. (IS_SEPARATION_COMBINATOR f /\
         EVERY (\l. VAR_RES_IS_STACK_IMPRECISE___USED_VARS exS (P l)) L) ==>
(VAR_RES_IS_STACK_IMPRECISE___USED_VARS exS (var_res_map f P L))``,

REWRITE_TAC[var_res_map_def] THEN
REPEAT STRIP_TAC THEN
MATCH_MP_TAC (MP_CANON VAR_RES_IS_STACK_IMPRECISE___USED_VARS___var_res_bigstar_list) THEN
FULL_SIMP_TAC std_ss [EVERY_MAP]);


val VAR_RES_IS_STACK_IMPRECISE___var_res_map = store_thm (
"VAR_RES_IS_STACK_IMPRECISE___var_res_map",
``!f P L. (IS_SEPARATION_COMBINATOR f /\
           EVERY (\l. VAR_RES_IS_STACK_IMPRECISE (P l)) L) ==>
(VAR_RES_IS_STACK_IMPRECISE (var_res_map f P L))``,
SIMP_TAC std_ss [VAR_RES_IS_STACK_IMPRECISE___ALTERNATIVE_DEF,
   EVERY_MEM, VAR_RES_IS_STACK_IMPRECISE___USED_VARS___var_res_map]);


val VAR_RES_IS_STACK_IMPRECISE___USED_VARS___var_res_map___SIMPLE = store_thm (
"VAR_RES_IS_STACK_IMPRECISE___USED_VARS___var_res_map___SIMPLE",
``!f P L exS. (IS_SEPARATION_COMBINATOR f /\
              (!l. VAR_RES_IS_STACK_IMPRECISE___USED_VARS exS (P l))) ==>
(VAR_RES_IS_STACK_IMPRECISE___USED_VARS exS (var_res_map f P L))``,

REPEAT STRIP_TAC THEN
MATCH_MP_TAC VAR_RES_IS_STACK_IMPRECISE___USED_VARS___var_res_map THEN
ASM_SIMP_TAC std_ss [EVERY_MEM]);


val VAR_RES_IS_STACK_IMPRECISE___var_res_map___SIMPLE = store_thm (
"VAR_RES_IS_STACK_IMPRECISE___var_res_map___SIMPLE",
``!f P L. (IS_SEPARATION_COMBINATOR f /\
           (!l. VAR_RES_IS_STACK_IMPRECISE (P l))) ==>
(VAR_RES_IS_STACK_IMPRECISE (var_res_map f P L))``,

REPEAT STRIP_TAC THEN
MATCH_MP_TAC VAR_RES_IS_STACK_IMPRECISE___var_res_map THEN
ASM_SIMP_TAC std_ss [EVERY_MEM]);




(******************************************************
 Expressions Imprecise
 ******************************************************)


val VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_REL_def = Define `
    VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_REL
       (e:('a,'b,'c) var_res_expression) vs =
    (!st1 st2. VAR_RES_STACK___IS_EQUAL_UPTO_PERMISSIONS {} st1 st2 ==>
               (e st1 = e st2)) /\
    ((!st. e (DRESTRICT st vs) = e st) /\ FINITE vs /\
    (!st. IS_SOME (e st) = (vs SUBSET FDOM st)))`;


val VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_REL_11 = store_thm (
"VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_REL_11",
``(VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_REL e vs1 /\
   VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_REL e vs2) ==>
  (vs1 = vs2)``,
REPEAT STRIP_TAC THEN
CCONTR_TAC THEN
FULL_SIMP_TAC std_ss [VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_REL_def, EXTENSION, SUBSET_DEF] THEN
`?st:('b, 'a) var_res_state. FDOM st = (vs1 UNION vs2) DELETE x` by ALL_TAC THEN1 (
   Q.EXISTS_TAC `FUN_FMAP ARB ((vs1 UNION vs2) DELETE x)` THEN
   ASM_SIMP_TAC std_ss [FINITE_UNION, FINITE_DELETE, FUN_FMAP_DEF]
) THEN
Q.PAT_ASSUM `!st. (!x. P x st) = (!x. Q x st)` (MP_TAC o Q.SPEC `st`) THEN
ASM_SIMP_TAC std_ss [IN_UNION, IN_DELETE]);



val VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_def = Define `
VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS e =
if ?vs. VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_REL e vs then
SOME (@vs.VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_REL e vs) else
NONE`;


val VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_THM = store_thm ("VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_THM",
``(!e vs. ((VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS e = SOME vs) =
           (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_REL e vs))) /\
  (!e. (((VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS e = NONE) =
         !vs. ~(VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_REL e vs))))``,

SIMP_TAC std_ss [VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_def, COND_RAND, COND_RATOR] THEN
REPEAT GEN_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THENL [
   Q.PAT_ASSUM `X = vs` (fn thm => ONCE_REWRITE_TAC[GSYM thm]) THEN
   SELECT_ELIM_TAC THEN PROVE_TAC[],

   PROVE_TAC[],

   SELECT_ELIM_TAC THEN
   METIS_TAC[VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_REL_11]
]);




val VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_REL___REWRITE = store_thm (
"VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_REL___REWRITE",
``!e vs.
  VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_REL e vs =
  FINITE vs /\
  (!st. IS_SOME (e st) = vs SUBSET (FDOM st)) /\
  (!st1 st2. ((vs SUBSET FDOM st1) /\ (vs SUBSET FDOM st2) /\
             (!v. v IN vs ==> (FST (st1 ' v) = FST (st2 ' v)))) ==>
             ((e st1) = (e st2)))``,

SIMP_TAC (std_ss++EQUIV_EXTRACT_ss)
   [VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_REL_def,
    VAR_RES_STACK___IS_EQUAL_UPTO_PERMISSIONS_def, NOT_IN_EMPTY] THEN
REPEAT STRIP_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THENL [
   Tactical.REVERSE (`e (DRESTRICT st1 vs) = e (DRESTRICT st2 vs)` by ALL_TAC) THEN1 METIS_TAC[] THEN
   Q.PAT_ASSUM `!st1 st2. X st1 st2` MATCH_MP_TAC THEN
   FULL_SIMP_TAC std_ss [DRESTRICT_DEF, IN_INTER, SUBSET_DEF, EXTENSION] THEN
   METIS_TAC[],

   Tactical.REVERSE (Cases_on `vs SUBSET FDOM st1`) THEN1 PROVE_TAC[NOT_IS_SOME_EQ_NONE] THEN
   Q.PAT_ASSUM `!st1 st2. X ==> Y` MATCH_MP_TAC THEN
   FULL_SIMP_TAC std_ss [SUBSET_DEF] THEN
   PROVE_TAC[],

   `vs SUBSET FDOM st = vs SUBSET FDOM (DRESTRICT st vs)` by ALL_TAC THEN1 (
      SIMP_TAC std_ss [DRESTRICT_DEF, SUBSET_INTER, SUBSET_REFL]
   ) THEN
   Tactical.REVERSE (Cases_on `vs SUBSET FDOM st`) THEN1 PROVE_TAC[NOT_IS_SOME_EQ_NONE] THEN
   Q.PAT_ASSUM `!st1 st2. X ==> Y` MATCH_MP_TAC THEN
   FULL_SIMP_TAC std_ss [SUBSET_DEF] THEN
   PROVE_TAC[DRESTRICT_DEF]
]);


val VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_REL___EXPAND = store_thm (
"VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_REL___EXPAND",
``!e vs.
  VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_REL e vs =
  FINITE vs /\
  (!st. IS_SOME (e st) = vs SUBSET (FDOM st)) /\
  (!st. ((e st) = NONE) = ~(vs SUBSET (FDOM st))) /\
  (!st1 st2. ((vs SUBSET FDOM st1) /\ (vs SUBSET FDOM st2) /\
             (!v. v IN vs ==> (FST (st1 ' v) = FST (st2 ' v)))) ==>
             ((e st1) = (e st2)))``,

SIMP_TAC (std_ss++EQUIV_EXTRACT_ss)
   [VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_REL___REWRITE] THEN
REPEAT STRIP_TAC THEN
ASM_REWRITE_TAC[NONE_IS_NOT_SOME]);



val VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET_def = Define
`VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET vs e =
 (IS_SOME (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS e) /\
 (THE (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS e) SUBSET vs))`;


val VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET___REWRITE = store_thm (
"VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET___REWRITE",
``VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET vs e =
 ?vs'. vs' SUBSET vs /\ VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_REL e vs'``,
SIMP_TAC (std_ss++CONJ_ss)
  [VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET_def,
   IS_SOME_EXISTS, GSYM LEFT_EXISTS_AND_THM] THEN
SIMP_TAC std_ss [VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_THM] THEN
PROVE_TAC[]);



val VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET___UNIV_REWRITE =
store_thm ("VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET___UNIV_REWRITE",
``!e. VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET UNIV e =
      IS_SOME (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS e)``,
SIMP_TAC std_ss [VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET_def, SUBSET_UNIV]);


val IS_SOME___VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS___REWRITE =
store_thm("IS_SOME___VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS___REWRITE",
``IS_SOME (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS e) =
  ?vs. VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_REL e vs``,
SIMP_TAC std_ss [IS_SOME_EXISTS, VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_THM]);



val VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET___SUBSET = store_thm (
"VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET___SUBSET",
``!vs1 vs2 e.
(VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET vs1 e /\
 vs1 SUBSET vs2) ==>
VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET vs2 e``,

SIMP_TAC std_ss [VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET_def] THEN
METIS_TAC[SUBSET_TRANS]);


val VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET___EXP_EQ = store_thm (
"VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET___EXP_EQ",
``!st1 st2 vs e.
(VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET vs e /\
vs SUBSET FDOM st1 /\ vs SUBSET FDOM st2 /\
(!v. v IN vs ==> (FST (st1 ' v) = FST (st2 ' v)))) ==>
(e st1 = e st2)``,

REPEAT STRIP_TAC THEN
FULL_SIMP_TAC std_ss [VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET___REWRITE,
   VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_REL___REWRITE] THEN
Q.PAT_ASSUM `!st1 st2. X st1 st2 ==> (e st1 = e st2)` MATCH_MP_TAC THEN
FULL_SIMP_TAC std_ss [SUBSET_DEF]);


val VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET___EXP_EQ_IS_SOME = store_thm (
"VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET___EXP_EQ_IS_SOME",
``!st1 st2 vs e.
(VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET vs e /\
IS_SOME (e st1) /\ (FDOM st1 INTER vs) SUBSET FDOM st2 /\
(!v. v IN (FDOM st1 INTER vs) ==> (FST (st1 ' v) = FST (st2 ' v)))) ==>
(e st1 = e st2)``,

REPEAT STRIP_TAC THEN
FULL_SIMP_TAC std_ss [VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET___REWRITE,
   VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_REL___REWRITE] THEN
Q.PAT_ASSUM `!st1 st2. X st1 st2 ==> (e st1 = e st2)` MATCH_MP_TAC THEN
`vs' SUBSET (FDOM st1)` by METIS_TAC[] THEN
`vs' SUBSET (FDOM st1) INTER vs` by METIS_TAC[SUBSET_INTER] THEN
METIS_TAC[SUBSET_DEF]);


val IS_SOME___VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS___SUBSTATE_LEFT = store_thm (
"IS_SOME___VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS___SUBSTATE_LEFT",
``!st1 st2 e.
(IS_SOME (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS e) /\
 VAR_RES_STACK_IS_SUBSTATE st1 st2 /\
 IS_SOME (e st1)) ==>
(e st1 = e st2)``,

REPEAT STRIP_TAC THEN
FULL_SIMP_TAC std_ss [
   IS_SOME___VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS___REWRITE,
   VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_REL___REWRITE] THEN
Q.PAT_ASSUM `!st1 st2. X st1 st2 ==> (e st1 = e st2)` MATCH_MP_TAC THEN
Q.PAT_ASSUM `IS_SOME (e st1)` MP_TAC THEN
FULL_SIMP_TAC std_ss [VAR_RES_STACK_IS_SUBSTATE_REWRITE, SUBSET_DEF]);


val IS_SOME___VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS___SUBSTATE_RIGHT = store_thm (
"IS_SOME___VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS___SUBSTATE_RIGHT",
``!st1 st2 e.
(IS_SOME (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS e) /\
 VAR_RES_STACK_IS_SUBSTATE st1 st2 /\
 IS_SOME (e st1)) ==> (e st2 = e st1)``,

PROVE_TAC[IS_SOME___VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS___SUBSTATE_LEFT]);



val VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS___var_res_exp_const = store_thm (
"VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS___var_res_exp_const",
``!c. VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS (var_res_exp_const c) = SOME {}``,

SIMP_TAC std_ss [
   var_res_exp_const_def,
   VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_THM,
   VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_REL___REWRITE,
   EMPTY_SUBSET, FINITE_EMPTY]);


val VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS___var_res_exp_var = store_thm (
"VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS___var_res_exp_var",
``VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS (var_res_exp_var v) = SOME {v}``,
SIMP_TAC std_ss [
   VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_THM,
   VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_REL___REWRITE,
   var_res_exp_var_def, SUBSET_DEF, IN_SING, COND_REWRITES,
   FINITE_INSERT, FINITE_EMPTY]);



val VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS___var_res_exp_op = store_thm (
"VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS___var_res_exp_op",
``!f eL vs.
   (EVERY IS_SOME (MAP VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS eL) /\
    (vs = (FOLDR $UNION EMPTY (MAP
       (\e. THE (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS e)) eL)))) ==>

   (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS (var_res_exp_op f eL) =
    SOME vs)``,

SIMP_TAC list_ss [var_res_exp_op_def, LET_THM,
                  VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_THM,
                  VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_REL___REWRITE] THEN
GEN_TAC THEN
let
  val thm_rewr = prove (``!eL:('a, 'b,'c) var_res_expression list. EVERY (\e. e st1 = e st2) eL ==>
  ((if EVERY IS_SOME (MAP (\e. e st1) eL) then
       SOME (f (MAP THE (MAP (\e. e st1) eL)))
    else
       NONE) =
    if EVERY IS_SOME (MAP (\e. e st2) eL) then
       SOME (f (MAP THE (MAP (\e. e st2) eL)))
    else
      NONE)``,
   REPEAT STRIP_TAC THEN
   Tactical.REVERSE (`MAP (\e. e st1) eL = MAP (\e. e st2) eL` by ALL_TAC) THEN1 (
      ASM_REWRITE_TAC[]
   ) THEN
   Induct_on `eL` THEN
   ASM_SIMP_TAC list_ss []
   );
in
   CONSEQ_REWRITE_TAC ([thm_rewr],[],[])
end THEN

Induct_on `eL` THENL [
   SIMP_TAC list_ss [FINITE_EMPTY, EMPTY_SUBSET],

   Q.ABBREV_TAC `vsL = (MAP VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS eL)` THEN
   Q.ABBREV_TAC `vs = (FOLDR $UNION {} (MAP (\e.THE
                       (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS e)) eL))` THEN
   ASM_SIMP_TAC list_ss [FINITE_UNION, UNION_SUBSET] THEN
   GEN_TAC THEN STRIP_TAC THEN
   `?vsh. (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_REL h vsh) /\
          (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS h = SOME vsh)` by ALL_TAC THEN1 (
      FULL_SIMP_TAC std_ss [IS_SOME_EXISTS, VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_THM] THEN
      PROVE_TAC[]
   ) THEN
   FULL_SIMP_TAC std_ss [VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_REL___EXPAND,
                         IN_UNION, COND_NONE_SOME_REWRITES]
]);





val VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS___var_res_exp_binop = store_thm (
"VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS___var_res_exp_binop",
``!binop e1 e2 vs1 vs2 vs.
   ((VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS e1 = SOME vs1) /\
    (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS e2 = SOME vs2) /\
    (vs = vs1 UNION vs2)) ==>

   (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS (var_res_exp_binop binop e1 e2) =
    SOME vs)``,

SIMP_TAC list_ss [var_res_exp_binop_def] THEN
REPEAT STRIP_TAC THEN
MATCH_MP_TAC VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS___var_res_exp_op THEN
ASM_SIMP_TAC list_ss [UNION_EMPTY]);


val VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS___var_res_exp_binop_const = store_thm (
"VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS___var_res_exp_binop_const",
``!binop e n vs.
   (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS e = SOME vs) ==>

   (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS (var_res_exp_binop_const binop e n) =
    SOME vs)``,

SIMP_TAC list_ss [var_res_exp_binop_const___ALTERNATIVE_DEF] THEN
REPEAT STRIP_TAC THEN
MATCH_MP_TAC VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS___var_res_exp_op THEN
ASM_SIMP_TAC list_ss [UNION_EMPTY]);


val VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS___var_res_exp_add_sub =
 save_thm ("VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS___var_res_exp_add_sub",
 var_res_exp_add_sub___INST_THM VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS___var_res_exp_binop_const);


val VAR_RES_IS_STACK_IMPRECISE___USED_VARS___var_res_prop_expression = store_thm (
"VAR_RES_IS_STACK_IMPRECISE___USED_VARS___var_res_prop_expression",

``!f emp p el vs.
  (EVERY (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET vs) el) ==>
(VAR_RES_IS_STACK_IMPRECISE___USED_VARS vs (var_res_prop_expression f emp p el))``,

SIMP_TAC std_ss [VAR_RES_IS_STACK_IMPRECISE___USED_VARS___ALTERNATIVE_DEF,
                 var_res_prop_expression_def, LET_THM, UNION_SUBSET,
                 var_res_stack_proposition_def, IN_ABS] THEN
REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
SIMP_TAC (std_ss++EQUIV_EXTRACT_ss++CONJ_ss) [] THEN
Q.ABBREV_TAC `c = ((SND s) IN asl_emp f \/ ~emp)` THEN STRIP_TAC THEN
Tactical.REVERSE (`EVERY (\e. e (FST s2) = e (FST s)) el` by ALL_TAC) THEN1 (
   `MAP (\e. e (FST s)) el = MAP (\e. e (FST s2)) el` by ALL_TAC THEN1 (
       POP_ASSUM MP_TAC THEN REPEAT (POP_ASSUM (K ALL_TAC)) THEN
       Induct_on `el` THEN
       ASM_SIMP_TAC list_ss []
   ) THEN
   ASM_SIMP_TAC std_ss []
) THEN

FULL_SIMP_TAC std_ss [EVERY_MEM] THEN
REPEAT STRIP_TAC THEN
RES_TAC THEN
MATCH_MP_TAC VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET___EXP_EQ_IS_SOME THEN
Q.EXISTS_TAC `vs` THEN
FULL_SIMP_TAC std_ss [MEM_MAP, GSYM LEFT_FORALL_IMP_THM, IN_INTER]);




val VAR_RES_IS_STACK_IMPRECISE___USED_VARS___var_res_prop_binexpression = store_thm (
"VAR_RES_IS_STACK_IMPRECISE___USED_VARS___var_res_prop_binexpression",
``!f emp p e1 e2 vs.
  ((VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET vs e1) /\
  (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET vs e2)) ==>
(VAR_RES_IS_STACK_IMPRECISE___USED_VARS vs (var_res_prop_binexpression f emp p e1 e2))``,

SIMP_TAC std_ss [var_res_prop_binexpression___ALTERNATIVE_DEF] THEN
REPEAT STRIP_TAC THEN
MATCH_MP_TAC VAR_RES_IS_STACK_IMPRECISE___USED_VARS___var_res_prop_expression THEN
ASM_SIMP_TAC list_ss []);



val VAR_RES_IS_STACK_IMPRECISE___USED_VARS___var_res_prop_equal = store_thm (
"VAR_RES_IS_STACK_IMPRECISE___USED_VARS___var_res_prop_equal",
``!f e1 e2 vs.
  ((VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET vs e1) /\
  (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET vs e2)) ==>
(VAR_RES_IS_STACK_IMPRECISE___USED_VARS vs (var_res_prop_equal f e1 e2))``,

SIMP_TAC std_ss [var_res_prop_equal_def, VAR_RES_IS_STACK_IMPRECISE___USED_VARS___var_res_prop_binexpression]);




val VAR_RES_IS_STACK_IMPRECISE___USED_VARS___var_res_prop_unequal = store_thm (
"VAR_RES_IS_STACK_IMPRECISE___USED_VARS___var_res_prop_unequal",
``!f e1 e2 vs.
  ((VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET vs e1) /\
  (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET vs e2)) ==>
(VAR_RES_IS_STACK_IMPRECISE___USED_VARS vs (var_res_prop_unequal f e1 e2))``,

SIMP_TAC std_ss [var_res_prop_unequal_def, VAR_RES_IS_STACK_IMPRECISE___USED_VARS___var_res_prop_binexpression]);



val VAR_RES_IS_STACK_IMPRECISE___USED_VARS___var_res_prop_weak_equal = store_thm (
"VAR_RES_IS_STACK_IMPRECISE___USED_VARS___var_res_prop_weak_equal",
``!e1 e2 vs.
  ((VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET vs e1) /\
  (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET vs e2)) ==>
(VAR_RES_IS_STACK_IMPRECISE___USED_VARS vs (var_res_prop_weak_equal e1 e2))``,

SIMP_TAC std_ss [var_res_prop_weak_equal_def, VAR_RES_IS_STACK_IMPRECISE___USED_VARS___var_res_prop_binexpression,
                 var_res_prop_weak_binexpression_def]);


val VAR_RES_IS_STACK_IMPRECISE___USED_VARS___var_res_prop_weak_unequal = store_thm (
"VAR_RES_IS_STACK_IMPRECISE___USED_VARS___var_res_prop_weak_unequal",
``!e1 e2 vs.
  ((VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET vs e1) /\
  (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET vs e2)) ==>
(VAR_RES_IS_STACK_IMPRECISE___USED_VARS vs (var_res_prop_weak_unequal e1 e2))``,

SIMP_TAC std_ss [var_res_prop_weak_unequal_def, VAR_RES_IS_STACK_IMPRECISE___USED_VARS___var_res_prop_binexpression,
                 var_res_prop_weak_binexpression_def]);


val VAR_RES_IS_STACK_IMPRECISE___var_res_prop_expression = store_thm (
"VAR_RES_IS_STACK_IMPRECISE___var_res_prop_expression",

``!f emp p el.
  (EVERY (\e. IS_SOME (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS e)) el) ==>
  (VAR_RES_IS_STACK_IMPRECISE (var_res_prop_expression f emp p el))``,

SIMP_TAC std_ss [GSYM VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET___UNIV_REWRITE,
                 VAR_RES_IS_STACK_IMPRECISE___ALTERNATIVE_DEF, EVERY_MEM,
                 VAR_RES_IS_STACK_IMPRECISE___USED_VARS___var_res_prop_expression]);


val VAR_RES_IS_STACK_IMPRECISE___var_res_prop_binexpression = store_thm (
"VAR_RES_IS_STACK_IMPRECISE___var_res_prop_binexpression",

``!f emp p e1 e2.
  (IS_SOME (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS e1)) /\
  (IS_SOME (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS e2)) ==>
(VAR_RES_IS_STACK_IMPRECISE (var_res_prop_binexpression f emp p e1 e2))``,

SIMP_TAC std_ss [GSYM VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET___UNIV_REWRITE,
                 VAR_RES_IS_STACK_IMPRECISE___ALTERNATIVE_DEF,
                 VAR_RES_IS_STACK_IMPRECISE___USED_VARS___var_res_prop_binexpression]);


val VAR_RES_IS_STACK_IMPRECISE___var_res_prop_unequal = store_thm (
"VAR_RES_IS_STACK_IMPRECISE___var_res_prop_unequal",
``!f e1 e2.
  (IS_SOME (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS e1)) /\
  (IS_SOME (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS e2)) ==>
  (VAR_RES_IS_STACK_IMPRECISE (var_res_prop_unequal f e1 e2))``,
SIMP_TAC std_ss [var_res_prop_unequal_def, VAR_RES_IS_STACK_IMPRECISE___var_res_prop_binexpression]);


val VAR_RES_IS_STACK_IMPRECISE___var_res_prop_equal = store_thm (
"VAR_RES_IS_STACK_IMPRECISE___var_res_prop_equal",
``!f e1 e2.
  (IS_SOME (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS e1)) /\
  (IS_SOME (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS e2)) ==>
  (VAR_RES_IS_STACK_IMPRECISE (var_res_prop_equal f e1 e2))``,
SIMP_TAC std_ss [var_res_prop_equal_def, VAR_RES_IS_STACK_IMPRECISE___var_res_prop_binexpression]);


val VAR_RES_IS_STACK_IMPRECISE___var_res_prop_weak_unequal = store_thm (
"VAR_RES_IS_STACK_IMPRECISE___var_res_prop_weak_unequal",
``!e1 e2.
  (IS_SOME (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS e1)) /\
  (IS_SOME (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS e2)) ==>
  (VAR_RES_IS_STACK_IMPRECISE (var_res_prop_weak_unequal e1 e2))``,
SIMP_TAC std_ss [var_res_prop_weak_unequal_def, VAR_RES_IS_STACK_IMPRECISE___var_res_prop_binexpression,
   var_res_prop_weak_binexpression_def]);


val VAR_RES_IS_STACK_IMPRECISE___var_res_prop_weak_equal = store_thm (
"VAR_RES_IS_STACK_IMPRECISE___var_res_prop_weak_equal",
``!e1 e2.
  (IS_SOME (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS e1)) /\
  (IS_SOME (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS e2)) ==>
  (VAR_RES_IS_STACK_IMPRECISE (var_res_prop_weak_equal e1 e2))``,
SIMP_TAC std_ss [var_res_prop_weak_equal_def, VAR_RES_IS_STACK_IMPRECISE___var_res_prop_binexpression,
   var_res_prop_weak_binexpression_def]);



val asl_star___VAR_RES_IS_STACK_IMPRECISE =
store_thm ("asl_star___VAR_RES_IS_STACK_IMPRECISE",
``!f P1 P2. (VAR_RES_IS_STACK_IMPRECISE P1 /\ VAR_RES_IS_STACK_IMPRECISE P2) ==>
(asl_star (VAR_RES_COMBINATOR f) P1 P2 =
\s. ?es1 es2. (f (SOME es1) (SOME es2) = SOME (SND s)) /\
              (FST s, es1) IN P1 /\ (FST s, es2) IN P2)``,

REPEAT STRIP_TAC THEN REWRITE_TAC [EXTENSION] THEN
GEN_TAC THEN
`?st es. x = (st,es)` by (Cases_on `x` THEN SIMP_TAC std_ss []) THEN
ASM_SIMP_TAC std_ss [IN_ABS] THEN POP_ASSUM (K ALL_TAC) THEN
SIMP_TAC std_ss [asl_star_def, IN_ABS, VAR_RES_COMBINATOR_def,
                 PRODUCT_SEPARATION_COMBINATOR_REWRITE] THEN
EQ_TAC THEN STRIP_TAC THENL [
   `?p1 p2 q1 q2. (p = (p1,p2)) /\ (q = (q1,q2))` by
      (Cases_on `p` THEN Cases_on `q` THEN SIMP_TAC std_ss []) THEN
   Q.EXISTS_TAC `p2` THEN Q.EXISTS_TAC `q2` THEN
   FULL_SIMP_TAC std_ss [] THEN
   `VAR_RES_STACK_IS_SUBSTATE p1 st /\ VAR_RES_STACK_IS_SUBSTATE q1 st` by
      PROVE_TAC[VAR_RES_STACK_IS_SUBSTATE_INTRO] THEN
   METIS_TAC[VAR_RES_IS_STACK_IMPRECISE_def],


   Q.EXISTS_TAC `(VAR_RES_STACK_SPLIT1 EMPTY st, es1)` THEN
   Q.EXISTS_TAC `(VAR_RES_STACK_SPLIT2 EMPTY st, es2)` THEN
   ASM_SIMP_TAC std_ss [VAR_RES_STACK_COMBINE___VAR_RES_STACK_SPLIT12] THEN
   METIS_TAC[VAR_RES_STACK___IS_EQUAL_UPTO_PERMISSIONS___VAR_RES_STACK_SPLIT,
             VAR_RES_IS_STACK_IMPRECISE_def]
]);



val asl_star___var_res_prop_stack_true =
store_thm ("asl_star___var_res_prop_stack_true",
``!f. IS_SEPARATION_COMBINATOR f ==>
!P. asl_star (VAR_RES_COMBINATOR f) (var_res_prop_stack_true f) P =
\s. (?st. VAR_RES_STACK_IS_SUBSTATE st (FST s) /\ (st, SND s) IN P)``,

GEN_TAC THEN STRIP_TAC THEN
ONCE_REWRITE_TAC [EXTENSION] THEN
FULL_SIMP_TAC std_ss [IS_SEPARATION_COMBINATOR_EXPAND_THM] THEN
ASM_SIMP_TAC std_ss [IN_ABS, asl_star_def,
   var_res_prop_stack_true_REWRITE,
   PAIR_FORALL_THM, PAIR_EXISTS_THM,
   VAR_RES_COMBINATOR_def,
   PRODUCT_SEPARATION_COMBINATOR_REWRITE,
   asl_emp_def, GSYM RIGHT_EXISTS_AND_THM,
   GSYM LEFT_EXISTS_AND_THM,
   VAR_RES_STACK_IS_SUBSTATE_def,
   ASL_IS_SUBSTATE_def] THEN
METIS_TAC[VAR_RES_STACK_COMBINE___IS_SEPARATION_COMBINATOR,
     IS_SEPARATION_COMBINATOR_def, COMM_DEF]);



val asl_star___var_res_prop_stack_true___STACK_IMPRECISE =
store_thm ("asl_star___var_res_prop_stack_true___STACK_IMPRECISE",
``!f. IS_SEPARATION_COMBINATOR f ==>
(!P. VAR_RES_IS_STACK_IMPRECISE P ==>
(asl_star (VAR_RES_COMBINATOR f) (var_res_prop_stack_true f) P = P))``,


REPEAT STRIP_TAC THEN
ONCE_REWRITE_TAC [EXTENSION] THEN
ASM_SIMP_TAC std_ss [asl_star___VAR_RES_IS_STACK_IMPRECISE,
       VAR_RES_IS_STACK_IMPRECISE___var_res_prop_stack_true] THEN
FULL_SIMP_TAC std_ss [IN_ABS, var_res_prop_stack_true_REWRITE, asl_emp_def,
                      IS_SEPARATION_COMBINATOR_EXPAND_THM,
                      GSYM RIGHT_EXISTS_AND_THM, GSYM LEFT_EXISTS_AND_THM] THEN
METIS_TAC[]);


val asl_star___var_res_prop_stack_true___STACK_IMPRECISE___COMM =
store_thm ("asl_star___var_res_prop_stack_true___STACK_IMPRECISE___COMM",
``!f. IS_SEPARATION_COMBINATOR f ==>
(!P. VAR_RES_IS_STACK_IMPRECISE P ==>
(asl_star (VAR_RES_COMBINATOR f) P (var_res_prop_stack_true f) = P))``,

METIS_TAC[asl_star___var_res_prop_stack_true___STACK_IMPRECISE,
  asl_star___PROPERTIES, COMM_DEF, IS_SEPARATION_COMBINATOR___VAR_RES_COMBINATOR]);


val asl_star___var_res_prop_stack_true___IDEM =
store_thm ("asl_star___var_res_prop_stack_true___IDEM",
``!f. IS_SEPARATION_COMBINATOR f ==>
(asl_star (VAR_RES_COMBINATOR f) (var_res_prop_stack_true f) (var_res_prop_stack_true f) =
 (var_res_prop_stack_true f))``,
SIMP_TAC std_ss [asl_star___var_res_prop_stack_true___STACK_IMPRECISE,
                 VAR_RES_IS_STACK_IMPRECISE___var_res_prop_stack_true]);



val asl_star___var_res_prop_stack_true___IDEM_2 =
store_thm ("asl_star___var_res_prop_stack_true___IDEM_2",
``!f. IS_SEPARATION_COMBINATOR f ==>
!P. asl_star (VAR_RES_COMBINATOR f) (var_res_prop_stack_true f)
(asl_star (VAR_RES_COMBINATOR f) (var_res_prop_stack_true f) P) =
asl_star (VAR_RES_COMBINATOR f) (var_res_prop_stack_true f) P``,

REPEAT STRIP_TAC THEN
IMP_RES_TAC asl_star___var_res_prop_stack_true___IDEM THEN
Q.ABBREV_TAC `ff = VAR_RES_COMBINATOR f` THEN
`IS_SEPARATION_COMBINATOR ff` by PROVE_TAC[IS_SEPARATION_COMBINATOR___VAR_RES_COMBINATOR] THEN
`COMM (asl_star ff) /\ ASSOC (asl_star ff)` by PROVE_TAC[asl_star___PROPERTIES] THEN
METIS_TAC [COMM_DEF, ASSOC_DEF]);


val asl_star___var_res_prop_stack_true___IDEM_3 =
store_thm ("asl_star___var_res_prop_stack_true___IDEM_3",
``!f. IS_SEPARATION_COMBINATOR f ==>
!P1 P2. asl_star (VAR_RES_COMBINATOR f)
       (asl_star (VAR_RES_COMBINATOR f) (var_res_prop_stack_true f) P1)
       (asl_star (VAR_RES_COMBINATOR f) (var_res_prop_stack_true f) P2) =

       asl_star (VAR_RES_COMBINATOR f) (var_res_prop_stack_true f)
       (asl_star (VAR_RES_COMBINATOR f) P1 P2)``,


REPEAT STRIP_TAC THEN
IMP_RES_TAC asl_star___var_res_prop_stack_true___IDEM THEN
Q.ABBREV_TAC `ff = VAR_RES_COMBINATOR f` THEN
`IS_SEPARATION_COMBINATOR ff` by PROVE_TAC[IS_SEPARATION_COMBINATOR___VAR_RES_COMBINATOR] THEN
`COMM (asl_star ff) /\ ASSOC (asl_star ff)` by PROVE_TAC[asl_star___PROPERTIES] THEN
METIS_TAC [COMM_DEF, ASSOC_DEF]);


val asl_star___swap_var_res_prop_stack_true = store_thm (
"asl_star___swap_var_res_prop_stack_true",
``!f p1 p2. IS_SEPARATION_COMBINATOR f ==>
  (asl_star (VAR_RES_COMBINATOR f) (var_res_prop_stack_true f)
      (asl_star (VAR_RES_COMBINATOR f) p1 p2) =
   asl_star (VAR_RES_COMBINATOR f) p1
      (asl_star (VAR_RES_COMBINATOR f) (var_res_prop_stack_true f) p2))``,

REPEAT STRIP_TAC THEN
MATCH_MP_TAC asl_star___swap THEN
MATCH_MP_TAC IS_SEPARATION_COMBINATOR___VAR_RES_COMBINATOR THEN
ASM_REWRITE_TAC[]);


val var_res_bigstar_REWRITE = store_thm ("var_res_bigstar_REWRITE",
``(!f. IS_SEPARATION_COMBINATOR f ==>
    (var_res_bigstar f EMPTY_BAG = var_res_prop_stack_true f)) /\
  (!f p pL. IS_SEPARATION_COMBINATOR f ==>
    (var_res_bigstar f (BAG_INSERT p pL) =
     asl_star (VAR_RES_COMBINATOR f) p
       (var_res_bigstar f pL)))``,
SIMP_TAC std_ss [var_res_bigstar_def, asl_bigstar_REWRITE,
   asl_star___PROPERTIES, asl_star___swap_var_res_prop_stack_true,
   IS_SEPARATION_COMBINATOR___VAR_RES_COMBINATOR]);

val var_res_bigstar_list_REWRITE = store_thm ("var_res_bigstar_list_REWRITE",
``(!f. IS_SEPARATION_COMBINATOR f ==>
    (var_res_bigstar_list f [] = var_res_prop_stack_true f)) /\
  (!f p pL. IS_SEPARATION_COMBINATOR f ==>
    (var_res_bigstar_list f (p::pL) =
     asl_star (VAR_RES_COMBINATOR f) p
       (var_res_bigstar_list f pL)))``,
SIMP_TAC std_ss [var_res_bigstar_list_def, asl_bigstar_list_REWRITE,
   asl_star___PROPERTIES, asl_star___swap_var_res_prop_stack_true,
   IS_SEPARATION_COMBINATOR___VAR_RES_COMBINATOR]);


val var_res_bigstar_list_APPEND = store_thm ("var_res_bigstar_list_APPEND",
``!f l1 l2. IS_SEPARATION_COMBINATOR f ==>
    (var_res_bigstar_list f (l1++l2) =
     asl_star (VAR_RES_COMBINATOR f)
       (var_res_bigstar_list f l1)
       (var_res_bigstar_list f l2))``,
SIMP_TAC std_ss [var_res_bigstar_list_def, asl_bigstar_list_APPEND,
   IS_SEPARATION_COMBINATOR___VAR_RES_COMBINATOR, GSYM APPEND] THEN
SIMP_TAC std_ss [asl_star___swap_var_res_prop_stack_true,
   asl_bigstar_list_REWRITE,
   asl_star___var_res_prop_stack_true___IDEM_3] THEN
METIS_TAC[ASSOC_DEF, COMM_DEF, asl_star___PROPERTIES,
   IS_SEPARATION_COMBINATOR___VAR_RES_COMBINATOR,
   asl_star___swap_var_res_prop_stack_true]);

val var_res_bigstar_list_SNOC = store_thm ("var_res_bigstar_list_SNOC",
``!f p pL. IS_SEPARATION_COMBINATOR f ==>
    (var_res_bigstar_list f (SNOC p pL) =
     asl_star (VAR_RES_COMBINATOR f)
       (var_res_bigstar_list f pL) p)``,
SIMP_TAC std_ss [var_res_bigstar_list_def, asl_bigstar_list_SNOC,
   GSYM SNOC, IS_SEPARATION_COMBINATOR___VAR_RES_COMBINATOR]);

val var_res_bigstar_list_REVERSE = store_thm ("var_res_bigstar_list_REVERSE",
``!f pL. IS_SEPARATION_COMBINATOR f ==>
    (var_res_bigstar_list f (REVERSE pL) =
     var_res_bigstar_list f pL)``,
SIMP_TAC std_ss [var_res_bigstar_list_def, asl_bigstar_list_REWRITE,
   asl_bigstar_list_REVERSE, IS_SEPARATION_COMBINATOR___VAR_RES_COMBINATOR]);


val var_res_map_REWRITE = store_thm ("var_res_map_REWRITE",
``(!f P. IS_SEPARATION_COMBINATOR f ==>
    (var_res_map f P [] = var_res_prop_stack_true f)) /\
  (!f P p pL. IS_SEPARATION_COMBINATOR f ==>
    (var_res_map f P (p::pL) =
     asl_star (VAR_RES_COMBINATOR f) (P p)
       (var_res_map f P pL)))``,
SIMP_TAC list_ss [var_res_map_def, var_res_bigstar_list_REWRITE]);


val var_res_map_APPEND = store_thm ("var_res_map_APPEND",
``!f P l1 l2. IS_SEPARATION_COMBINATOR f ==>
    (var_res_map f P (l1++l2) =
     asl_star (VAR_RES_COMBINATOR f)
       (var_res_map f P l1)
       (var_res_map f P l2))``,
SIMP_TAC std_ss [var_res_map_def, var_res_bigstar_list_APPEND, MAP_APPEND]);


val var_res_map_SNOC = store_thm ("var_res_map_SNOC",
``!f P e l. IS_SEPARATION_COMBINATOR f ==>
    (var_res_map f P (SNOC e l) =
     asl_star (VAR_RES_COMBINATOR f)
       (var_res_map f P l)
       (P e))``,
SIMP_TAC std_ss [var_res_map_def, var_res_bigstar_list_SNOC, MAP_SNOC]);

val var_res_map_REVERSE = store_thm ("var_res_map_REVERSE",
``!f P l. IS_SEPARATION_COMBINATOR f ==>
    (var_res_map f P (REVERSE l) =
     var_res_map f P l)``,
SIMP_TAC std_ss [var_res_map_def, var_res_bigstar_list_REVERSE, MAP_REVERSE]);

val var_res_map_MAP = store_thm ("var_res_map_MAP",
``!f f2 P l.  (var_res_map f P (MAP f2 l) =
               var_res_map f (P o f2) l)``,
SIMP_TAC std_ss [var_res_map_def, MAP_MAP_o]);

val var_res_map___REWRITES = save_thm ("var_res_map___REWRITES",
LIST_CONJ [var_res_map_REWRITE, var_res_map_APPEND, var_res_map_SNOC,
           var_res_map_REVERSE])

val var_res_map___FUN_EQ = store_thm ("var_res_map___FUN_EQ",
``!f P1 P2 l. IS_SEPARATION_COMBINATOR f /\
  (!e. MEM e l ==> (P1 e = P2 e)) ==>
  (var_res_map f P1 l = var_res_map f P2 l)``,

NTAC 3 GEN_TAC THEN
Induct_on `l` THEN (
   FULL_SIMP_TAC list_ss [var_res_map_def]
) THEN
FULL_SIMP_TAC std_ss [var_res_bigstar_list_REWRITE]);


val var_res_bigstar_UNION = store_thm ("var_res_bigstar_UNION",
``!f b1 b2. IS_SEPARATION_COMBINATOR f ==>
    (var_res_bigstar f (BAG_UNION b1 b2) =
     asl_star (VAR_RES_COMBINATOR f)
       (var_res_bigstar f b1)
       (var_res_bigstar f b2))``,
SIMP_TAC std_ss [var_res_bigstar_def, asl_bigstar_UNION,
   IS_SEPARATION_COMBINATOR___VAR_RES_COMBINATOR, GSYM BAG_UNION_INSERT] THEN
SIMP_TAC std_ss [asl_star___swap_var_res_prop_stack_true,
   asl_bigstar_REWRITE, IS_SEPARATION_COMBINATOR___VAR_RES_COMBINATOR,
   asl_star___var_res_prop_stack_true___IDEM_3] THEN
METIS_TAC[ASSOC_DEF, COMM_DEF, asl_star___PROPERTIES,
   IS_SEPARATION_COMBINATOR___VAR_RES_COMBINATOR,
   asl_star___swap_var_res_prop_stack_true]);


val var_res_bigstar_list___var_res_prop_stack_true = store_thm ("var_res_bigstar_list___var_res_prop_stack_true",
``!f pL. IS_SEPARATION_COMBINATOR f ==>
    (var_res_bigstar_list f ((var_res_prop_stack_true f)::pL) =
    var_res_bigstar_list f pL)``,
SIMP_TAC std_ss [var_res_bigstar_list_def,
   asl_bigstar_list_REWRITE, asl_star___var_res_prop_stack_true___IDEM_2]);


val var_res_bigstar___var_res_prop_stack_true = store_thm ("var_res_bigstar___var_res_prop_stack_true",
``!f pL. IS_SEPARATION_COMBINATOR f ==>
    (var_res_bigstar f (BAG_INSERT (var_res_prop_stack_true f) pL) =
    var_res_bigstar f pL)``,
SIMP_TAC std_ss [var_res_bigstar_def, IS_SEPARATION_COMBINATOR___VAR_RES_COMBINATOR,
   asl_bigstar_REWRITE, asl_star___var_res_prop_stack_true___IDEM_2]);


val var_res_bigstar___var_res_prop_stack_true___asl_star_ELIM = store_thm ("var_res_bigstar___var_res_prop_stack_true___asl_star_ELIM",
``!f pL. IS_SEPARATION_COMBINATOR f ==>
    ((asl_star (VAR_RES_COMBINATOR f) (var_res_prop_stack_true f) (var_res_bigstar f pL) =
    var_res_bigstar f pL) /\
    (asl_star (VAR_RES_COMBINATOR f) (var_res_bigstar f pL) (var_res_prop_stack_true f) =
    var_res_bigstar f pL))``,
SIMP_TAC std_ss [var_res_bigstar_def, IS_SEPARATION_COMBINATOR___VAR_RES_COMBINATOR,
   asl_bigstar_REWRITE, asl_star___var_res_prop_stack_true___IDEM_2] THEN
METIS_TAC[asl_star___var_res_prop_stack_true___IDEM_2,
   IS_SEPARATION_COMBINATOR___VAR_RES_COMBINATOR,
   asl_star___PROPERTIES, COMM_DEF]);


val var_res_bigstar_REWRITE_EXT = save_thm ("var_res_bigstar_REWRITE_EXT",
CONJ var_res_bigstar_REWRITE var_res_bigstar___var_res_prop_stack_true___asl_star_ELIM)

val asl_bigstar_list___VAR_RES_IS_STACK_IMPRECISE =
store_thm ("asl_bigstar_list___VAR_RES_IS_STACK_IMPRECISE",
``!f P1 PL. IS_SEPARATION_COMBINATOR f /\ (EVERY VAR_RES_IS_STACK_IMPRECISE (P1::PL)) ==>

(asl_bigstar_list (VAR_RES_COMBINATOR f) (P1::PL) =
\s. ?es1 es2. (f (SOME es1) (SOME es2) = SOME (SND s)) /\
              (FST s, es1) IN P1 /\ (FST s, es2) IN
              asl_bigstar_list (VAR_RES_COMBINATOR f) ((var_res_prop_stack_true f)::PL))``,

Cases_on `PL` THENL [
   SIMP_TAC std_ss [asl_bigstar_list_REWRITE,
      asl_star___PROPERTIES, IS_SEPARATION_COMBINATOR___VAR_RES_COMBINATOR] THEN
   REPEAT STRIP_TAC THEN
   IMP_RES_TAC IS_SEPARATION_COMBINATOR_NEUTRAL_ELEMENT_FUNCTION_IMP THEN
   FULL_SIMP_TAC std_ss [var_res_prop_stack_true_REWRITE, IN_ABS,
      IS_SEPARATION_COMBINATOR_NEUTRAL_ELEMENT_FUNCTION___WITH_COMBINATOR_THM,
      asl_emp_def, GSYM RIGHT_EXISTS_AND_THM, GSYM LEFT_EXISTS_AND_THM] THEN
   QUANT_INSTANTIATE_TAC [] THEN
   SIMP_TAC std_ss [IN_ABS3],

   SIMP_TAC list_ss [asl_bigstar_list_REWRITE,
      REWRITE_RULE [ASSOC_DEF] asl_star___PROPERTIES, IS_SEPARATION_COMBINATOR___VAR_RES_COMBINATOR,
      asl_star___var_res_prop_stack_true___STACK_IMPRECISE] THEN
   REPEAT STRIP_TAC THEN
   Q.ABBREV_TAC `P2 = asl_star (VAR_RES_COMBINATOR f) h
           (asl_bigstar_list (VAR_RES_COMBINATOR f) t)` THEN
   ASM_SIMP_TAC list_ss [REWRITE_RULE [ASSOC_SYM] asl_star___PROPERTIES,
     IS_SEPARATION_COMBINATOR___VAR_RES_COMBINATOR] THEN
   Tactical.REVERSE (`VAR_RES_IS_STACK_IMPRECISE P2` by ALL_TAC) THEN1 (
      ASM_SIMP_TAC std_ss [asl_star___VAR_RES_IS_STACK_IMPRECISE]
   ) THEN
   Q.UNABBREV_TAC `P2` THEN
   REWRITE_TAC[GSYM asl_bigstar_list_REWRITE] THEN
   MATCH_MP_TAC (MP_CANON VAR_RES_IS_STACK_IMPRECISE___asl_bigstar_list) THEN
   FULL_SIMP_TAC list_ss [DISJ_IMP_THM, EVERY_MEM]
]);


val var_res_bigstar_list___VAR_RES_IS_STACK_IMPRECISE =
store_thm ("var_res_bigstar_list___VAR_RES_IS_STACK_IMPRECISE",
``!f P1 PL. IS_SEPARATION_COMBINATOR f /\ (EVERY VAR_RES_IS_STACK_IMPRECISE (P1::PL)) ==>

(var_res_bigstar_list f (P1::PL) =
\s. ?es1 es2. (f (SOME es1) (SOME es2) = SOME (SND s)) /\
              (FST s, es1) IN P1 /\ (FST s, es2) IN
              var_res_bigstar_list f PL)``,

SIMP_TAC list_ss [var_res_bigstar_list_def] THEN
REPEAT STRIP_TAC THEN
`asl_bigstar_list (VAR_RES_COMBINATOR f)
  (var_res_prop_stack_true f::P1::PL) =
 asl_bigstar_list (VAR_RES_COMBINATOR f)
  (P1::var_res_prop_stack_true f::PL)` by ALL_TAC THEN1 (
   MATCH_MP_TAC asl_bigstar_list_PERM THEN
   ASM_SIMP_TAC (std_ss++permLib.PERM_ss) [IS_SEPARATION_COMBINATOR___VAR_RES_COMBINATOR]
) THEN
ASM_REWRITE_TAC[] THEN POP_ASSUM (K ALL_TAC) THEN
ASM_SIMP_TAC list_ss [
  Once asl_bigstar_list___VAR_RES_IS_STACK_IMPRECISE,
  VAR_RES_IS_STACK_IMPRECISE___var_res_prop_stack_true] THEN
ASM_SIMP_TAC std_ss [GSYM var_res_bigstar_list_def,
   var_res_bigstar_list___var_res_prop_stack_true]);


val var_res_bigstar___VAR_RES_IS_STACK_IMPRECISE =
store_thm ("var_res_bigstar___VAR_RES_IS_STACK_IMPRECISE",
``!f P1 PL. IS_SEPARATION_COMBINATOR f /\ (BAG_EVERY VAR_RES_IS_STACK_IMPRECISE (BAG_INSERT P1 PL)) ==>

(var_res_bigstar f (BAG_INSERT P1 PL) =
\s. ?es1 es2. (f (SOME es1) (SOME es2) = SOME (SND s)) /\
              (FST s, es1) IN P1 /\ (FST s, es2) IN
              var_res_bigstar f PL)``,

SIMP_TAC list_ss [var_res_bigstar_REWRITE] THEN
REPEAT STRIP_TAC THEN
HO_MATCH_MP_TAC asl_star___VAR_RES_IS_STACK_IMPRECISE THEN
FULL_SIMP_TAC std_ss [BAG_EVERY_THM,
   VAR_RES_IS_STACK_IMPRECISE___var_res_bigstar]);



val asl_and___weak_binexpression = store_thm ("asl_and___weak_binexpression",
``!f e1 e2 P p.
  IS_SEPARATION_COMBINATOR f /\
  IS_SOME (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS e1) /\
  IS_SOME (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS e2) /\
  VAR_RES_IS_STACK_IMPRECISE P ==>

( asl_and (var_res_prop_weak_binexpression p e1 e2) P =
  asl_star (VAR_RES_COMBINATOR f)
       (var_res_prop_binexpression f T p e1 e2) P)``,

SIMP_TAC std_ss [asl_star___VAR_RES_IS_STACK_IMPRECISE, EXTENSION,
   var_res_prop_weak_binexpression_def,
   VAR_RES_IS_STACK_IMPRECISE___var_res_prop_binexpression] THEN
SIMP_TAC (std_ss++EQUIV_EXTRACT_ss) [IN_ABS, var_res_prop_binexpression_def,
   var_res_stack_proposition_def, LET_THM, asl_bool_EVAL] THEN
REPEAT STRIP_TAC THEN
`?uf. IS_SEPARATION_COMBINATOR_NEUTRAL_ELEMENT_FUNCTION___WITH_COMBINATOR f uf` by ALL_TAC THEN1 (
   METIS_TAC[IS_SEPARATION_COMBINATOR_NEUTRAL_ELEMENT_FUNCTION_IMP]
) THEN
FULL_SIMP_TAC std_ss [IS_SEPARATION_COMBINATOR_NEUTRAL_ELEMENT_FUNCTION___WITH_COMBINATOR_THM,
   asl_emp_def, IN_ABS, GSYM RIGHT_EXISTS_AND_THM, GSYM LEFT_EXISTS_AND_THM] THEN
METIS_TAC[]);





val VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET___VAR_CONST_EVAL = store_thm (
   "VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET___VAR_CONST_EVAL",
``(!vs c. (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET vs (var_res_exp_const c))) /\
  (!vs v. (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET vs (var_res_exp_var v) = v IN vs))``,

SIMP_TAC std_ss [VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET_def,
   VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS___var_res_exp_const,
   VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS___var_res_exp_var,
   SUBSET_DEF, IN_INSERT, NOT_IN_EMPTY]);


val VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET___var_res_exp_op = store_thm (
   "VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET___var_res_exp_op",
``!vs f el.
EVERY (\e. VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET vs e) el ==>
VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET vs (var_res_exp_op f el)``,

SIMP_TAC std_ss [VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET___REWRITE,
GSYM VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_THM] THEN
REPEAT STRIP_TAC THEN
CONSEQ_REWRITE_TAC ([], [
   VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS___var_res_exp_op], []) THEN
FULL_SIMP_TAC std_ss [EVERY_MEM, MEM_MAP, GSYM LEFT_FORALL_IMP_THM] THEN
Tactical.REVERSE (REPEAT STRIP_TAC) THEN1 PROVE_TAC[IS_SOME_EXISTS] THEN
Induct_on `el` THEN (
   SIMP_TAC list_ss [EMPTY_SUBSET, DISJ_IMP_THM, FORALL_AND_THM, FOLDR]
) THEN
REPEAT STRIP_TAC THEN
FULL_SIMP_TAC std_ss [UNION_SUBSET]);


val VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET___var_res_exp_binop = store_thm (
   "VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET___var_res_exp_binop",
``!f vs e1 e2.
VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET vs e1 /\
VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET vs e2 ==>
VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET vs (var_res_exp_binop f e1 e2)``,

REPEAT STRIP_TAC THEN
REWRITE_TAC[var_res_exp_binop_def] THEN
MATCH_MP_TAC VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET___var_res_exp_op THEN
ASM_SIMP_TAC list_ss []);


val VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET___var_res_exp_binop_const = store_thm (
   "VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET___var_res_exp_binop_const",
``!f vs e n.
VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET vs e ==>
VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET vs (var_res_exp_binop_const f e n)``,

SIMP_TAC std_ss [VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET___var_res_exp_binop,
   VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET___VAR_CONST_EVAL,
   var_res_exp_binop_const_def]);


val VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET___var_res_exp_add_sub =
 save_thm ("VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET___var_res_exp_add_sub",
 var_res_exp_add_sub___INST_THM VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET___var_res_exp_binop_const);


val VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET___IS_SOME_IMPL = store_thm (
   "VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET___IS_SOME_IMPL",
   ``!vs e s. VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET vs e /\
              (vs SUBSET FDOM s) ==>
              (IS_SOME (e s))``,

SIMP_TAC std_ss [VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET___REWRITE,
                 GSYM LEFT_FORALL_IMP_THM, GSYM LEFT_EXISTS_AND_THM,
                 VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_REL___EXPAND] THEN
PROVE_TAC[SUBSET_TRANS]);




val IS_SOME___VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS___VAR_CONST_EVAL = store_thm (
   "IS_SOME___VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS___VAR_CONST_EVAL",
``!c. (IS_SOME (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS (var_res_exp_const c))) /\
  !v. (IS_SOME (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS (var_res_exp_var v)))``,

SIMP_TAC std_ss [
   VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS___var_res_exp_const,
   VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS___var_res_exp_var]);


val IS_SOME___VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS___var_res_exp_op = store_thm (
   "IS_SOME___VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS___var_res_exp_op",
``!f el.
EVERY (\e. IS_SOME (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS e)) el ==>
IS_SOME (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS (var_res_exp_op f el))``,

REWRITE_TAC[GSYM VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET___UNIV_REWRITE] THEN
METIS_TAC[VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET___var_res_exp_op]);


val IS_SOME___VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS___var_res_exp_binop = store_thm (
   "IS_SOME___VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS___var_res_exp_binop",
``!f e1 e2.
IS_SOME (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS e1) /\
IS_SOME (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS e2) ==>
IS_SOME (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS (var_res_exp_binop f e1 e2))``,

FULL_SIMP_TAC std_ss [
   GSYM VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET___UNIV_REWRITE,
   VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET___var_res_exp_binop]);


val IS_SOME___VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS___var_res_exp_binop_const = store_thm (
   "IS_SOME___VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS___var_res_exp_binop_const",
``!f e n.
IS_SOME (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS e) ==>
IS_SOME (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS (var_res_exp_binop_const f e n))``,

FULL_SIMP_TAC std_ss [
   GSYM VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET___UNIV_REWRITE,
   VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET___var_res_exp_binop_const]);


val IS_SOME___VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS___var_res_exp_add_sub =
 save_thm ("IS_SOME___VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS___var_res_exp_add_sub",
 var_res_exp_add_sub___INST_THM IS_SOME___VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS___var_res_exp_binop_const);

val VAR_RES_IS_STACK_IMPRECISE___USED_VARS___var_res_exp_is_defined =
store_thm ("VAR_RES_IS_STACK_IMPRECISE___USED_VARS___var_res_exp_is_defined",
``!f e vs. VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET vs e ==>
   (VAR_RES_IS_STACK_IMPRECISE___USED_VARS vs (var_res_exp_is_defined f e))``,

SIMP_TAC (std_ss++CONJ_ss) [
   VAR_RES_IS_STACK_IMPRECISE___USED_VARS___ALTERNATIVE_DEF,
   var_res_exp_is_defined_REWRITE, IN_ABS,
   VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET___REWRITE,
   GSYM LEFT_FORALL_IMP_THM,
   VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_REL___EXPAND] THEN
REPEAT STRIP_TAC THEN
FULL_SIMP_TAC std_ss [SUBSET_DEF, IN_INTER]);


val VAR_RES_IS_STACK_IMPRECISE___var_res_exp_is_defined =
store_thm ("VAR_RES_IS_STACK_IMPRECISE___var_res_exp_is_defined",
``!f e. IS_SOME (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS e) ==>
        VAR_RES_IS_STACK_IMPRECISE (var_res_exp_is_defined f e)``,

SIMP_TAC std_ss [VAR_RES_IS_STACK_IMPRECISE___ALTERNATIVE_DEF,
                 GSYM VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET___UNIV_REWRITE,
                 VAR_RES_IS_STACK_IMPRECISE___USED_VARS___var_res_exp_is_defined]);



val VAR_RES_IS_STACK_IMPRECISE___USED_VARS___var_res_exp_prop =
store_thm ("VAR_RES_IS_STACK_IMPRECISE___USED_VARS___var_res_exp_prop",
``!e P vs. 
(VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET vs e /\
!c. VAR_RES_IS_STACK_IMPRECISE___USED_VARS vs (P c)) ==>
VAR_RES_IS_STACK_IMPRECISE___USED_VARS vs (var_res_exp_prop e P)``,


SIMP_TAC (std_ss++CONJ_ss) [VAR_RES_IS_STACK_IMPRECISE___USED_VARS___ALTERNATIVE_DEF,
   var_res_exp_prop_def, IN_ABS, LET_THM] THEN
REPEAT (GEN_TAC ORELSE DISCH_TAC) THEN
FULL_SIMP_TAC std_ss [] THEN
`e (FST s2) = e (FST s)` by ALL_TAC THEN1 (
   MATCH_MP_TAC VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET___EXP_EQ_IS_SOME THEN
   Q.EXISTS_TAC `vs` THEN
   ASM_SIMP_TAC std_ss [SUBSET_DEF, IN_INTER]
) THEN
`?ec. e (FST s) = SOME ec` by METIS_TAC[IS_SOME_EXISTS] THEN
FULL_SIMP_TAC std_ss [] THEN
METIS_TAC[IN_DEF]);


val VAR_RES_IS_STACK_IMPRECISE___var_res_exp_prop =
store_thm ("VAR_RES_IS_STACK_IMPRECISE___var_res_exp_prop",
``!e P. IS_SOME (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS e) ==>
        (!c. VAR_RES_IS_STACK_IMPRECISE (P c)) ==>
        VAR_RES_IS_STACK_IMPRECISE (var_res_exp_prop e P)``,

SIMP_TAC std_ss [VAR_RES_IS_STACK_IMPRECISE___ALTERNATIVE_DEF,
                 GSYM VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET___UNIV_REWRITE,
                 VAR_RES_IS_STACK_IMPRECISE___USED_VARS___var_res_exp_prop]);



(******************************************************
 var_res_prop
 ******************************************************)

(* Definitions *)
val var_res_prop_internal___COND_def = Define `
   var_res_prop_internal___COND (f:'c bin_option_function)
       (wpb,rpb:'b -> num) d (sfb:('a,'b,'c) var_res_proposition -> num) =
        d /\ FINITE_BAG sfb /\ IS_SEPARATION_COMBINATOR f /\
        (BAG_ALL_DISTINCT (BAG_UNION wpb rpb)) /\
        (!sf. BAG_IN sf sfb ==>
          VAR_RES_IS_STACK_IMPRECISE___USED_VARS (SET_OF_BAG (BAG_UNION wpb rpb)) sf
        )`;


val var_res_prop_internal___PROP_def = Define `
   var_res_prop_internal___PROP f (wpb, rpb) (wp, rp) sfb P = \s.
   (!v. BAG_IN v wpb ==> var_res_sl___has_write_permission v (FST s)) /\
   (!v. BAG_IN v rpb ==> var_res_sl___has_read_permission v (FST s)) /\
   (!v. v IN wp ==> var_res_sl___has_write_permission v (FST s)) /\
   (!v. v IN rp ==> var_res_sl___has_read_permission v (FST s)) /\
   (s IN var_res_bigstar f (BAG_INSERT P sfb))`;


val var_res_prop_internal_def = Define `
   var_res_prop_internal f (wpb, rpb) (wp, rp) d sfb P =

   (var_res_prop_internal___COND f (wpb, rpb) d sfb,
    if var_res_prop_internal___COND f (wpb, rpb) d sfb then
       var_res_prop_internal___PROP f (wpb, rpb) (wp, rp) sfb P
    else asl_false)`;



val var_res_prop_input_ap_distinct_def = Define `
    var_res_prop_input_ap_distinct f (wp, rp:'a -> bool) (d:'a list) P =
    (asl_and (K (ALL_DISTINCT d))
     (var_res_prop_internal___PROP f (EMPTY_BAG, EMPTY_BAG) (wp,rp)
          EMPTY_BAG P))`;


val var_res_prop_input_distinct_def = Define `
  var_res_prop_input_distinct f (wp,rp) d P =
  (ALL_DISTINCT d,  var_res_prop_input_ap_distinct f (wp,rp) d P)`;

val var_res_prop_input_def = Define `
  var_res_prop_input f (wp,rp) P =
  var_res_prop_input_distinct f (wp,rp) [] P`


val var_res_prop_input_distinct___REWRITE = store_thm (
"var_res_prop_input_distinct___REWRITE",
``!f wp rp d P. IS_SEPARATION_COMBINATOR f ==>
  ((var_res_prop_input_distinct f (wp,rp) d P) =
   (var_res_prop_internal f (EMPTY_BAG, EMPTY_BAG) (wp,rp) (ALL_DISTINCT d) EMPTY_BAG P))``,

SIMP_TAC (std_ss++CONJ_ss) [var_res_prop_internal_def,
   var_res_prop_input_distinct_def, var_res_prop_input_ap_distinct_def] THEN
SIMP_TAC (std_ss++CONJ_ss) [var_res_prop_internal___COND_def,
   FINITE_BAG_THM, BAG_ALL_DISTINCT_THM, BAG_UNION_EMPTY,
   NOT_IN_EMPTY_BAG] THEN
SIMP_TAC std_ss [COND_RATOR, COND_RAND, asl_bool_REWRITES]);


val var_res_prop_input_ap_def = Define `
  var_res_prop_input_ap f (wp,rp) P =
  var_res_prop_input_ap_distinct f (wp, rp) [] P`;

val var_res_prop_input_ap_distinct_ELIM = store_thm (
"var_res_prop_input_ap_distinct_ELIM",
``var_res_prop_input_ap_distinct f (wp, rp) [v] P =
  var_res_prop_input_ap f (wp,rp) P``,

SIMP_TAC list_ss [var_res_prop_input_ap_distinct_def,
   var_res_prop_input_ap_def, ALL_DISTINCT]);

val var_res_prop_def = Define `
   var_res_prop f (wpb, rpb) sfb =
   var_res_prop_internal f (wpb, rpb) (EMPTY, EMPTY) T sfb (asl_emp (VAR_RES_COMBINATOR f))`;


val var_res_prop___PROP_def = Define `
   var_res_prop___PROP f (wpb, rpb) sfb =
   var_res_prop_internal___PROP f (wpb, rpb) (EMPTY, EMPTY) sfb
       (asl_emp (VAR_RES_COMBINATOR f))`;



val var_res_prop___PROP___REWRITE_2 = store_thm ("var_res_prop___PROP___REWRITE_2",
``!f wpb rpb sfb.
    var_res_prop___PROP f (wpb,rpb) sfb =
       (\s.
          (!v. BAG_IN v wpb ==> var_res_sl___has_write_permission v (FST s)) /\
          (!v. BAG_IN v rpb ==> var_res_sl___has_read_permission v (FST s)) /\
          s IN var_res_bigstar f (BAG_INSERT (asl_emp (VAR_RES_COMBINATOR f)) sfb))``,
SIMP_TAC list_ss [var_res_prop_internal___PROP_def, NOT_IN_EMPTY,
    var_res_prop___PROP_def]);


val var_res_prop___PROP___REWRITE = store_thm ("var_res_prop___PROP___REWRITE",
``!f wpb rpb sfb.
    IS_SEPARATION_COMBINATOR f ==>
    (var_res_prop___PROP f (wpb,rpb) sfb =
       (\s.
          (!v. BAG_IN v wpb ==> var_res_sl___has_write_permission v (FST s)) /\
          (!v. BAG_IN v rpb ==> var_res_sl___has_read_permission v (FST s)) /\
          s IN var_res_bigstar f sfb))``,
SIMP_TAC list_ss [var_res_prop___PROP___REWRITE_2,
var_res_bigstar_REWRITE, asl_star___PROPERTIES,
    IS_SEPARATION_COMBINATOR___VAR_RES_COMBINATOR]);



val var_res_prop___COND_def = Define `
   var_res_prop___COND f (wpb, rpb) sfb =
   var_res_prop_internal___COND f (wpb, rpb) T sfb`;

val var_res_prop___COND___REWRITE = save_thm ("var_res_prop___COND___REWRITE",
SIMP_RULE list_ss [var_res_prop_internal___COND_def] var_res_prop___COND_def);


val var_res_prop___REWRITE = save_thm ("var_res_prop___REWRITE",
SIMP_RULE list_ss [var_res_prop_internal_def, GSYM var_res_prop___COND_def,
   GSYM var_res_prop___PROP_def] var_res_prop_def);



(* Simple rewrites *)
val var_res_prop_internal___COND___EXPAND = store_thm (
"var_res_prop_internal___COND___EXPAND",
``!f wpb rpb sfb d.
  (var_res_prop_internal___COND f (wpb,rpb) d sfb =
  IS_SEPARATION_COMBINATOR f /\ d /\ FINITE_BAG sfb /\
  BAG_ALL_DISTINCT (BAG_UNION wpb rpb) /\
  (BAG_EVERY (VAR_RES_IS_STACK_IMPRECISE___USED_VARS (SET_OF_BAG (BAG_UNION wpb rpb))) sfb) /\
  (VAR_RES_IS_STACK_IMPRECISE___USED_VARS (SET_OF_BAG (BAG_UNION wpb rpb))
      (var_res_bigstar f sfb)))``,

SIMP_TAC (std_ss++EQUIV_EXTRACT_ss) [var_res_prop_internal___COND_def,
   BAG_EVERY] THEN
REPEAT STRIP_TAC THEN
MATCH_MP_TAC VAR_RES_IS_STACK_IMPRECISE___USED_VARS___var_res_bigstar THEN
ASM_SIMP_TAC std_ss [BAG_EVERY]);


val var_res_prop___COND___EXPAND = save_thm ("var_res_prop___COND___EXPAND",
SIMP_RULE list_ss [var_res_prop_internal___COND___EXPAND] var_res_prop___COND_def);


val var_res_prop_internal___EQ = store_thm ("var_res_prop_internal___EQ",
``(var_res_prop_internal f (wpb, rpb) (wp,rp) d sfb P =
   var_res_prop_internal f (wpb', rpb') (wp',rp') d' sfb' P') =

  ((var_res_prop_internal___COND f (wpb, rpb) d sfb =
    var_res_prop_internal___COND f (wpb', rpb') d' sfb') /\
   ((var_res_prop_internal___COND f (wpb, rpb) d sfb) ==>
    (var_res_prop_internal___PROP f (wpb, rpb) (wp,rp) sfb P =
     var_res_prop_internal___PROP f (wpb', rpb') (wp',rp') sfb' P')))``,

SIMP_TAC (std_ss++EQUIV_EXTRACT_ss) [var_res_prop_internal_def] THEN
METIS_TAC[]);



val var_res_prop___EQ = store_thm ("var_res_prop___EQ",
``(var_res_prop f (wpb, rpb) sfb =
   var_res_prop f (wpb', rpb') sfb') =

  ((var_res_prop___COND f (wpb, rpb) sfb =
    var_res_prop___COND f (wpb', rpb') sfb') /\
   ((var_res_prop___COND f (wpb, rpb) sfb) ==>
    (var_res_prop___PROP f (wpb, rpb) sfb =
     var_res_prop___PROP f (wpb', rpb') sfb')))``,

SIMP_TAC std_ss [var_res_prop_def, var_res_prop_internal___EQ,
  var_res_prop___COND_def, var_res_prop___PROP_def]);




(* Transforming var_res_prop_input_ap into var_res_prop *)

(*Move asl_exists to the front*)
val var_res_prop_internal___EXISTS = store_thm ("var_res_prop_internal___EXISTS",
``(var_res_prop_internal f (EMPTY_BAG, EMPTY_BAG) (wb, rp) d EMPTY_BAG (asl_exists x. P x)) =
  COND_PROP___STRONG_EXISTS (\x. var_res_prop_internal f (EMPTY_BAG, EMPTY_BAG) (wb, rp) d EMPTY_BAG (P x))``,

SIMP_TAC std_ss [var_res_prop_internal___COND_def,
   var_res_prop_internal___PROP_def, var_res_prop_internal_def,
   NOT_IN_EMPTY_BAG, BAG_ALL_DISTINCT_THM,
   FINITE_BAG_THM, BAG_UNION_EMPTY, IS_SEPARATION_COMBINATOR___VAR_RES_COMBINATOR,
   var_res_bigstar_REWRITE, asl_bool_EVAL,
   GSYM asl_exists___asl_star_THM,
   COND_PROP___STRONG_EXISTS_def] THEN
ONCE_REWRITE_TAC[EXTENSION] THEN
Tactical.REVERSE (Cases_on `d /\ IS_SEPARATION_COMBINATOR f`) THEN (
   ASM_SIMP_TAC std_ss [asl_bool_EVAL, asl_exists_def, IN_ABS,
                        RIGHT_EXISTS_AND_THM]
));


(*move all variables form the sets to bags, establishing that they
  are distinct to each other. This fact was previously stored in d.
  At the end, d can be deleted.*)
val var_res_prop_internal___VARS_TO_BAGS = store_thm ("var_res_prop_internal___VARS_TO_BAGS",
``((d ==> (~(BAG_IN v wpb) /\ ~(BAG_IN v rpb))) ==>
(var_res_prop_internal f (wpb, rpb) (v INSERT wp,rp) d EMPTY_BAG P =
 var_res_prop_internal f (BAG_INSERT v wpb, rpb) (wp,rp) d EMPTY_BAG P)) /\

((d ==> (~(BAG_IN v wpb) /\ ~(BAG_IN v rpb))) ==>
(var_res_prop_internal f (wpb, rpb) (wp,v INSERT rp) d EMPTY_BAG P =
 var_res_prop_internal f (wpb, BAG_INSERT v rpb) (wp,rp) d EMPTY_BAG P))``,

SIMP_TAC std_ss [var_res_prop_internal___EQ,
  var_res_prop_internal___COND_def, var_res_prop_internal___PROP_def,
  FUN_EQ_THM, IN_INSERT, bagTheory.BAG_IN_BAG_INSERT, DISJ_IMP_THM,
  FORALL_AND_THM, BAG_ALL_DISTINCT_THM, IMP_CONJ_THM,
  NOT_IN_EMPTY_BAG, BAG_ALL_DISTINCT_THM, BAG_UNION_INSERT,
  BAG_IN_BAG_UNION] THEN
SIMP_TAC (std_ss++EQUIV_EXTRACT_ss) []);


val var_res_prop_internal___VARS_TO_BAGS___END = store_thm (
"var_res_prop_internal___VARS_TO_BAGS___END",
``(BAG_ALL_DISTINCT (BAG_UNION wpb rpb) ==> d) ==>
  (var_res_prop_internal f (wpb, rpb) (EMPTY, EMPTY) d EMPTY_BAG P =
   var_res_prop_internal f (wpb, rpb) (EMPTY, EMPTY) T EMPTY_BAG P)``,

SIMP_TAC std_ss [var_res_prop_internal___COND_def,
  var_res_prop_internal___PROP_def, var_res_prop_internal___EQ,
  ALL_DISTINCT, bagTheory.NOT_IN_EMPTY_BAG] THEN
SIMP_TAC (std_ss++EQUIV_EXTRACT_ss) []);





(*After all variables have been moved, break down P at * and move
  everything to sfb*)

val var_res_prop_internal___PROP_TO_BAG = store_thm (
"var_res_prop_internal___PROP_TO_BAG",
``!f f' wpb rpb sfb P1 P2.
  (IS_VAR_RES_COMBINATOR f /\ (GET_VAR_RES_COMBINATOR f = f') /\
   VAR_RES_IS_STACK_IMPRECISE___USED_VARS (SET_OF_BAG (BAG_UNION wpb rpb)) P2) ==>
  ((var_res_prop_internal f' (wpb, rpb) ({},{}) T sfb (asl_star f P1 P2) =
   var_res_prop_internal f' (wpb, rpb) ({},{}) T (BAG_INSERT P2 sfb) P1))``,

SIMP_TAC std_ss [IS_VAR_RES_COMBINATOR_def, GSYM LEFT_EXISTS_AND_THM,
   GSYM LEFT_FORALL_IMP_THM, GET_VAR_RES_COMBINATOR_THM] THEN
SIMP_TAC std_ss [var_res_prop_internal___EQ,
   var_res_prop_internal___PROP_def, var_res_prop_internal___COND_def,
   FUN_EQ_THM, NOT_IN_EMPTY, asl_star___PROPERTIES, ALL_DISTINCT,
   FINITE_BAG_THM] THEN
SIMP_TAC (std_ss++EQUIV_EXTRACT_ss) [
   BAG_IN_BAG_INSERT, DISJ_IMP_THM, NOT_IN_EMPTY,
   var_res_bigstar_REWRITE, IS_SEPARATION_COMBINATOR___VAR_RES_COMBINATOR] THEN
REPEAT STRIP_TAC THEN
`COMM  (asl_star ((VAR_RES_COMBINATOR f'):('b, 'a, 'c) var_res_ext_state bin_option_function)) /\
 ASSOC (asl_star ((VAR_RES_COMBINATOR f'):('b, 'a, 'c) var_res_ext_state bin_option_function))` by
   METIS_TAC[asl_star___PROPERTIES, IS_SEPARATION_COMBINATOR___VAR_RES_COMBINATOR] THEN
METIS_TAC[COMM_DEF, ASSOC_DEF]);


val var_res_prop_internal___PROP_TO_BAG___END = store_thm (
"var_res_prop_internal___PROP_TO_BAG___END",
``(VAR_RES_IS_STACK_IMPRECISE___USED_VARS (SET_OF_BAG (BAG_UNION wpb rpb)) P1 ==>
  (var_res_prop_internal f (wpb, rpb) ({},{}) T sfb P1 =
   var_res_prop_internal f (wpb, rpb) ({},{}) T (BAG_INSERT P1 sfb) (asl_emp (VAR_RES_COMBINATOR f))))``,

Tactical.REVERSE (Cases_on `IS_SEPARATION_COMBINATOR f`) THEN1 (
   ASM_SIMP_TAC std_ss [var_res_prop_internal_def, var_res_prop_internal___COND_def]
) THEN
`IS_VAR_RES_COMBINATOR (VAR_RES_COMBINATOR f)` by
   PROVE_TAC[IS_VAR_RES_COMBINATOR_def] THEN
METIS_TAC[asl_star___PROPERTIES, var_res_prop_internal___PROP_TO_BAG,
          GET_VAR_RES_COMBINATOR_THM,
          IS_SEPARATION_COMBINATOR___VAR_RES_COMBINATOR]);




(*Some rewrites for conds*)
val var_res_prop___COND_VAR_INSERT = store_thm (
"var_res_prop___COND_VAR_INSERT",
``!f wpb rpb sfb v.
  (var_res_prop___COND f (wpb, rpb) sfb /\
   (~(v IN (SET_OF_BAG (BAG_UNION wpb rpb))))) ==>
  (var_res_prop___COND f (BAG_INSERT v wpb, rpb) sfb)``,

SIMP_TAC std_ss [var_res_prop___COND___REWRITE, BAG_ALL_DISTINCT_THM,
       BAG_IN_BAG_UNION, bagTheory.IN_SET_OF_BAG,
       BAG_IN_BAG_INSERT, BAG_UNION_INSERT] THEN
REPEAT STRIP_TAC THEN
RES_TAC THEN
MATCH_MP_TAC VAR_RES_IS_STACK_IMPRECISE___USED_VARS___SUBSET THEN
Q.EXISTS_TAC `SET_OF_BAG (BAG_UNION wpb rpb)` THEN
ASM_SIMP_TAC std_ss [SUBSET_DEF, bagTheory.BAG_IN_BAG_INSERT,
           bagTheory.IN_SET_OF_BAG, bagTheory.BAG_IN_BAG_UNION,
           DISJ_IMP_THM]);



val var_res_prop___COND_INSERT = store_thm ("var_res_prop___COND_INSERT",

``!f wpb rpb sfb sf.
  (var_res_prop___COND f (wpb, rpb) (BAG_INSERT sf sfb) =
  ((var_res_prop___COND f (wpb, rpb) sfb) /\
   VAR_RES_IS_STACK_IMPRECISE___USED_VARS (SET_OF_BAG (BAG_UNION wpb rpb)) sf))``,

SIMP_TAC std_ss [var_res_prop___COND___REWRITE,
       bagTheory.BAG_IN_BAG_INSERT, DISJ_IMP_THM,
       FORALL_AND_THM, bagTheory.FINITE_BAG_THM] THEN
SIMP_TAC (std_ss++EQUIV_EXTRACT_ss) []);


val var_res_prop___COND_UNION = store_thm ("var_res_prop___COND_UNION",
``!f wpb rpb sfb1 sfb2.
  ((var_res_prop___COND f (wpb, rpb) (BAG_UNION sfb1 sfb2) =
  (var_res_prop___COND f (wpb, rpb) sfb1 /\
   var_res_prop___COND f (wpb, rpb) sfb2)))``,

SIMP_TAC std_ss [var_res_prop___COND___REWRITE,
   FORALL_AND_THM, bagTheory.FINITE_BAG_UNION,
   BAG_IN_BAG_UNION, DISJ_IMP_THM] THEN
SIMP_TAC (std_ss++EQUIV_EXTRACT_ss) []);


val var_res_prop___IMPLIES_VAR_DISTINCT = store_thm ("var_res_prop___IMPLIES_VAR_DISTINCT",
``!f wpb rpb sfb.
  FST (var_res_prop f (wpb, rpb) sfb) ==>
  BAG_ALL_DISTINCT (BAG_UNION wpb rpb)``,
SIMP_TAC std_ss [var_res_prop___REWRITE,
   var_res_prop___COND___REWRITE]);


val var_res_prop___PROP_EMPTY = store_thm (
"var_res_prop___PROP_EMPTY",
``!f wpb rpb. IS_SEPARATION_COMBINATOR f ==>
  (var_res_prop___PROP f (wpb, rpb) EMPTY_BAG =
  (\s. (!v. BAG_IN v wpb ==> var_res_sl___has_write_permission v (FST s)) /\
       (!v. BAG_IN v rpb ==> var_res_sl___has_read_permission v (FST s)) /\
       (SND s IN asl_emp f)))``,

SIMP_TAC std_ss [var_res_prop___PROP___REWRITE, var_res_bigstar_REWRITE,
       IS_SEPARATION_COMBINATOR___VAR_RES_COMBINATOR,
       asl_star___PROPERTIES] THEN
SIMP_TAC std_ss [var_res_prop_stack_true_REWRITE, IN_ABS]);



val var_res_prop___PROP___VARS = store_thm (
"var_res_prop___PROP___VARS",
``!s f wpb rpb sfb.
      s IN var_res_prop___PROP f (wpb,rpb) sfb ==>
      SET_OF_BAG (BAG_UNION wpb rpb) SUBSET FDOM (FST s)``,

SIMP_TAC std_ss [var_res_prop___PROP___REWRITE_2,
                 var_res_sl___has_read_permission_def,
                 var_res_sl___has_write_permission_def,
                 SUBSET_DEF, IN_SET_OF_BAG, IN_ABS,
                 BAG_IN_BAG_UNION, DISJ_IMP_THM]);


val var_res_prop___PROP_INSERT = store_thm (
"var_res_prop___PROP_INSERT",
``!f wpb rpb sf sfb.
  (var_res_prop___COND f (wpb, rpb) (BAG_INSERT sf sfb)) ==>

  (var_res_prop___PROP f (wpb, rpb) (BAG_INSERT sf sfb) =
  (\s. ?s1 s2.
      (f (SOME s1) (SOME s2) = SOME (SND s)) /\
      (FST s,s1) IN sf /\ (FST s,s2) IN var_res_prop___PROP f (wpb, rpb) sfb))``,

REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC [EXTENSION] THEN
FULL_SIMP_TAC std_ss [var_res_prop___COND_INSERT] THEN
FULL_SIMP_TAC std_ss [var_res_prop___COND___EXPAND] THEN
`BAG_EVERY VAR_RES_IS_STACK_IMPRECISE (BAG_INSERT sf sfb)` by ALL_TAC THEN1 (
   FULL_SIMP_TAC std_ss [BAG_EVERY, BAG_IN_BAG_INSERT, FORALL_AND_THM,
     DISJ_IMP_THM, VAR_RES_IS_STACK_IMPRECISE___USED_VARS_def]
) THEN
ASM_SIMP_TAC std_ss [var_res_prop___PROP___REWRITE,
   IN_ABS, var_res_bigstar___VAR_RES_IS_STACK_IMPRECISE] THEN
SIMP_TAC (std_ss++EQUIV_EXTRACT_ss) []);



val var_res_prop___PROP_UNION = store_thm ("var_res_prop___PROP_UNION",
``!f wpb rpb sfb1 sfb2.
var_res_prop___COND f (wpb,rpb) (BAG_UNION sfb1 sfb2) ==>

(var_res_prop___PROP f (wpb,rpb) (BAG_UNION sfb1 sfb2) =
(\s. ?s1 s2.
   (f (SOME s1) (SOME s2) = SOME (SND s)) /\
   (FST s,s1) IN (var_res_prop___PROP f (wpb,rpb) sfb1) /\
   (FST s,s2) IN (var_res_prop___PROP f (wpb,rpb) sfb2)))``,

REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC [EXTENSION] THEN
FULL_SIMP_TAC std_ss [var_res_prop___COND_INSERT] THEN
FULL_SIMP_TAC std_ss [var_res_prop___COND___EXPAND, IN_ABS] THEN
`BAG_EVERY VAR_RES_IS_STACK_IMPRECISE sfb1 /\
 BAG_EVERY VAR_RES_IS_STACK_IMPRECISE sfb2` by ALL_TAC THEN1 (
   FULL_SIMP_TAC std_ss [BAG_EVERY, BAG_IN_BAG_UNION, FORALL_AND_THM,
     DISJ_IMP_THM, VAR_RES_IS_STACK_IMPRECISE___USED_VARS_def]
) THEN
ASM_SIMP_TAC std_ss [var_res_prop___PROP___REWRITE,
   IN_ABS, var_res_bigstar_UNION, asl_star___VAR_RES_IS_STACK_IMPRECISE,
   VAR_RES_IS_STACK_IMPRECISE___var_res_bigstar] THEN
SIMP_TAC (std_ss++EQUIV_EXTRACT_ss) []);


val var_res_prop___PROP___asl_false =
store_thm ("var_res_prop___PROP___asl_false",
``!f wpb rpb sfb. (var_res_prop___PROP f (wpb,rpb) (BAG_INSERT asl_false sfb)) =
                   asl_false``,

SIMP_TAC std_ss [var_res_prop___PROP___REWRITE_2, bagTheory.BAG_INSERT_NOT_EMPTY,
   COND_RAND, COND_RATOR, asl_bool_EVAL, EXTENSION, IN_ABS,
   var_res_bigstar_def, asl_bigstar_def] THEN
CCONTR_TAC THEN FULL_SIMP_TAC std_ss [] THEN
Q.PAT_ASSUM `x IN Y` MP_TAC THEN
MATCH_MP_TAC (prove (``(Y = asl_false) ==> (x IN Y ==> Z)``, SIMP_TAC std_ss [asl_bool_EVAL])) THEN
MATCH_MP_TAC asl_bigstar_list_false THEN
ASM_SIMP_TAC std_ss [MEM_BAG_TO_LIST, bagTheory.BAG_IN_BAG_INSERT]);




val var_res_prop___var_res_exp_is_defined =
store_thm ("var_res_prop___var_res_exp_is_defined",
``!f e wpb rpb sfb.
  VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET (SET_OF_BAG (BAG_UNION wpb rpb)) e ==>
  ((var_res_prop f (wpb,rpb) (BAG_INSERT (var_res_exp_is_defined f e) sfb)) =
   (var_res_prop f (wpb,rpb) sfb))``,

REPEAT STRIP_TAC THEN
ASM_SIMP_TAC std_ss [
   var_res_prop___REWRITE, var_res_prop___COND_INSERT,
   var_res_prop___PROP_INSERT,
   VAR_RES_IS_STACK_IMPRECISE___USED_VARS___var_res_exp_is_defined] THEN
SIMP_TAC std_ss [COND_EQ_REWRITE, var_res_exp_is_defined_REWRITE, IN_ABS] THEN
REPEAT STRIP_TAC THEN
`IS_SEPARATION_COMBINATOR f` by FULL_SIMP_TAC std_ss [var_res_prop___COND___REWRITE] THEN
FULL_SIMP_TAC std_ss [IS_SEPARATION_COMBINATOR_EXPAND_THM, asl_emp_def, IN_ABS,
                      GSYM LEFT_EXISTS_AND_THM, GSYM RIGHT_EXISTS_AND_THM] THEN
QUANT_INSTANTIATE_TAC [] THEN
ONCE_REWRITE_TAC[EXTENSION] THEN
SIMP_TAC (std_ss++EQUIV_EXTRACT_ss) [IN_ABS] THEN
REPEAT STRIP_TAC THEN
MATCH_MP_TAC VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET___IS_SOME_IMPL THEN
Q.EXISTS_TAC `SET_OF_BAG (BAG_UNION wpb rpb)` THEN
IMP_RES_TAC var_res_prop___PROP___VARS THEN
ASM_REWRITE_TAC[]);



val var_res_exp_is_cond_defined___var_res_prop = store_thm ("var_res_exp_is_cond_defined___var_res_prop",
``!f e wpb rpb sfb vs.
  ((VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS e = SOME vs) /\
   (vs SUBSET (SET_OF_BAG (BAG_UNION wpb rpb)))) ==>

  (var_res_exp_is_cond_defined (var_res_prop___PROP f (wpb, rpb) sfb) e)``,

REPEAT GEN_TAC THEN
SIMP_TAC std_ss [VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_THM,
                 VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_REL___REWRITE,
                 var_res_exp_is_cond_defined_def] THEN
REPEAT STRIP_TAC THEN
FULL_SIMP_TAC std_ss [SUBSET_DEF, IN_SET_OF_BAG, BAG_IN_BAG_INSERT,
   BAG_IN_BAG_UNION, var_res_prop___PROP___REWRITE_2,
   var_res_sl___has_read_permission_def,
   var_res_sl___has_write_permission_def] THEN
REPEAT STRIP_TAC THEN
RES_TAC THEN RES_TAC THEN ASM_REWRITE_TAC[]);





val COND_PROP___STRONG_IMP___asl_cond_star___var_res_prop =
store_thm ("COND_PROP___STRONG_IMP___asl_cond_star___var_res_prop",
``!f f' wpb1 wpb2 rpb1 rpb2 sfb1 sfb2.
  (BAG_DISJOINT wpb1 wpb2 /\ BAG_DISJOINT wpb1 rpb2 /\ BAG_DISJOINT wpb2 rpb1 /\
  IS_VAR_RES_COMBINATOR f' /\ (GET_VAR_RES_COMBINATOR f' = f)) ==>

COND_PROP___STRONG_IMP
(asl_cond_star f'
   (var_res_prop f (wpb1, rpb1) sfb1)
   (var_res_prop f (wpb2, rpb2) sfb2))

(var_res_prop f (BAG_UNION wpb1 wpb2, BAG_MERGE rpb1 rpb2)
                (BAG_UNION sfb1 sfb2))``,

REPEAT STRIP_TAC THEN
FULL_SIMP_TAC std_ss [asl_cond_star_def, var_res_prop___REWRITE,
   COND_PROP___STRONG_IMP_def, IS_VAR_RES_COMBINATOR_def] THEN
`f'' = f` by METIS_TAC[GET_VAR_RES_COMBINATOR_THM] THEN
FULL_SIMP_TAC std_ss [] THEN POP_ASSUM (K ALL_TAC) THEN
REPEAT STRIP_TAC THENL [
   FULL_SIMP_TAC std_ss [var_res_prop___COND___REWRITE,
          BAG_ALL_DISTINCT_BAG_UNION,
          BAG_ALL_DISTINCT_BAG_MERGE,
          BAG_IN_BAG_MERGE, bagTheory.BAG_IN_BAG_UNION,
          BAG_DISJOINT_BAG_IN, DISJ_IMP_THM,
          IMP_CONJ_THM, FORALL_AND_THM,
          FINITE_BAG_UNION] THEN
   REPEAT STRIP_TAC THENL [
      PROVE_TAC[],

      MATCH_MP_TAC VAR_RES_IS_STACK_IMPRECISE___USED_VARS___SUBSET THEN
      Q.EXISTS_TAC `SET_OF_BAG (BAG_UNION wpb1 rpb1)` THEN
      ASM_SIMP_TAC std_ss [SUBSET_DEF, IN_SET_OF_BAG,
            BAG_IN_BAG_UNION, DISJ_IMP_THM, BAG_IN_BAG_MERGE],

      MATCH_MP_TAC VAR_RES_IS_STACK_IMPRECISE___USED_VARS___SUBSET THEN
      Q.EXISTS_TAC `SET_OF_BAG (BAG_UNION wpb2 rpb2)` THEN
      ASM_SIMP_TAC std_ss [SUBSET_DEF, IN_SET_OF_BAG,
            BAG_IN_BAG_UNION, DISJ_IMP_THM, BAG_IN_BAG_MERGE]
   ],


   ONCE_REWRITE_TAC [EXTENSION] THEN
   ASM_SIMP_TAC std_ss [var_res_prop___PROP___REWRITE, IN_ABS,
      var_res_bigstar_UNION, BAG_IN_BAG_MERGE, DISJ_IMP_THM, FORALL_AND_THM] THEN
   SIMP_TAC std_ss [asl_star_def, IN_ABS, BAG_IN_BAG_MERGE,
                    BAG_IN_BAG_UNION, DISJ_IMP_THM, FORALL_AND_THM,
                    GSYM RIGHT_EXISTS_AND_THM] THEN
   REPEAT STRIP_TAC THEN EQ_TAC THEN STRIP_TAC THENL [
      Q.EXISTS_TAC `p` THEN Q.EXISTS_TAC `q` THEN
      `ASL_IS_SUBSTATE (VAR_RES_COMBINATOR f) p x /\
       ASL_IS_SUBSTATE (VAR_RES_COMBINATOR f) q x` by
          PROVE_TAC[ASL_IS_SUBSTATE_INTRO, IS_SEPARATION_COMBINATOR___VAR_RES_COMBINATOR] THEN
      METIS_TAC[VAR_RES_WRITE_PERM___SUBSTATE, VAR_RES_READ_PERM___SUBSTATE],


      Q.EXISTS_TAC (`(VAR_RES_STACK_SPLIT (SET_OF_BAG wpb1) (SET_OF_BAG wpb2) (FST x), SND p)`) THEN
      Q.EXISTS_TAC (`(VAR_RES_STACK_SPLIT (SET_OF_BAG wpb2) (SET_OF_BAG wpb1) (FST x), SND q)`) THEN
      FULL_SIMP_TAC std_ss [VAR_RES_COMBINATOR_REWRITE,
                            VAR_RES_STACK_SPLIT___read_writes,
                            IN_SET_OF_BAG, BAG_DISJOINT_BAG_IN,
                            VAR_RES_STACK_COMBINE___VAR_RES_STACK_SPLIT] THEN
      REPEAT STRIP_TAC THENL [
         Tactical.REVERSE (`(SET_OF_BAG wpb1 INTER SET_OF_BAG wpb2) = EMPTY` by ALL_TAC) THEN1 (
            ASM_REWRITE_TAC[COMPL_EMPTY, DRESTRICT_UNIV]
         ) THEN
         ONCE_REWRITE_TAC[EXTENSION] THEN
         ASM_SIMP_TAC std_ss [NOT_IN_EMPTY, IN_INTER, bagTheory.IN_SET_OF_BAG],

         PROVE_TAC[],
         PROVE_TAC[],


         `VAR_RES_IS_STACK_IMPRECISE___USED_VARS (SET_OF_BAG (BAG_UNION wpb1 rpb1)) (var_res_bigstar f sfb1)` by
               FULL_SIMP_TAC std_ss [var_res_prop___COND___EXPAND] THEN
         POP_ASSUM (MATCH_MP_TAC o REWRITE_RULE [VAR_RES_IS_STACK_IMPRECISE___USED_VARS___ALTERNATIVE_DEF]) THEN
         Q.EXISTS_TAC `p` THEN
         FULL_SIMP_TAC (std_ss++CONJ_ss) [VAR_RES_STACK_SPLIT___REWRITES,
                               FMERGE_DEF, SOME___VAR_RES_STACK_COMBINE, IN_SET_OF_BAG,
                               FMERGE_DEF, SUBSET_DEF, IN_INTER, IN_UNION, IN_DIFF] THEN
         MATCH_MP_TAC (prove (``(A /\ (A ==> B)) ==> (A /\ B)``, PROVE_TAC[])) THEN
         CONJ_TAC THEN1 METIS_TAC[BAG_IN_BAG_UNION] THEN
         REPEAT STRIP_TAC THEN
         ASM_SIMP_TAC std_ss [COND_RATOR, COND_RAND,
                              VAR_RES_STACK_COMBINE___MERGE_FUNC_def],

         PROVE_TAC[],
         PROVE_TAC[],


         `VAR_RES_IS_STACK_IMPRECISE___USED_VARS (SET_OF_BAG (BAG_UNION wpb2 rpb2)) (var_res_bigstar f sfb2)` by
               FULL_SIMP_TAC std_ss [var_res_prop___COND___EXPAND] THEN
         POP_ASSUM (MATCH_MP_TAC o REWRITE_RULE [VAR_RES_IS_STACK_IMPRECISE___USED_VARS___ALTERNATIVE_DEF]) THEN
         Q.EXISTS_TAC `q` THEN
         FULL_SIMP_TAC (std_ss++CONJ_ss) [VAR_RES_STACK_SPLIT___REWRITES,
                               FMERGE_DEF, SOME___VAR_RES_STACK_COMBINE, IN_SET_OF_BAG,
                               FMERGE_DEF, SUBSET_DEF, IN_INTER, IN_UNION, IN_DIFF] THEN
         MATCH_MP_TAC (prove (``(A /\ (A ==> B)) ==> (A /\ B)``, PROVE_TAC[])) THEN
         CONJ_TAC THEN1 METIS_TAC[BAG_IN_BAG_UNION] THEN
         REPEAT STRIP_TAC THEN
         FULL_SIMP_TAC std_ss [COND_RATOR, COND_RAND,
                              VAR_RES_STACK_COMBINE___MERGE_FUNC_def] THEN
         PROVE_TAC[VAR_RES_STACK_IS_SEPARATE_def]
      ]
   ]
]);




val asl_star___var_res_prop___PROP = store_thm (
"asl_star___var_res_prop___PROP",
``!f wpb1 wpb2 rpb1 rpb2 sfb1 sfb2.
         BAG_DISJOINT wpb1 wpb2 /\ BAG_DISJOINT wpb1 rpb2 /\
         BAG_DISJOINT wpb2 rpb1 /\
         var_res_prop___COND f (wpb1,rpb1) sfb1 /\
         var_res_prop___COND f (wpb2,rpb2) sfb2 ==>

          (asl_star (VAR_RES_COMBINATOR f)
             (var_res_prop___PROP f (wpb1,rpb1) sfb1)
             (var_res_prop___PROP f (wpb2,rpb2) sfb2) =
           var_res_prop___PROP f (BAG_UNION wpb1 wpb2,BAG_MERGE rpb1 rpb2)
             (BAG_UNION sfb1 sfb2))``,
REPEAT STRIP_TAC THEN
`IS_SEPARATION_COMBINATOR f` by FULL_SIMP_TAC std_ss [var_res_prop___COND___EXPAND] THEN
Q.ABBREV_TAC `f'  = VAR_RES_COMBINATOR f` THEN
`IS_VAR_RES_COMBINATOR f' /\
 (GET_VAR_RES_COMBINATOR f' = f)` by METIS_TAC [
     IS_VAR_RES_COMBINATOR_def, GET_VAR_RES_COMBINATOR_THM] THEN
METIS_TAC[
SIMP_RULE (std_ss++CONJ_ss) [COND_PROP___STRONG_IMP_def,
  asl_cond_star_def, var_res_prop___REWRITE]
COND_PROP___STRONG_IMP___asl_cond_star___var_res_prop]);



val COND_PROP___STRONG_EQUIV___WEAK_COND_REWRITE =
store_thm ("COND_PROP___STRONG_EQUIV___WEAK_COND_REWRITE",
``!f wpb rpb sfb sfb'.
(BAG_ALL_DISTINCT (BAG_UNION wpb rpb) ==> (sfb = sfb')) ==>
(COND_PROP___STRONG_EQUIV (var_res_prop f (wpb,rpb) sfb)
                          (var_res_prop f (wpb,rpb) sfb'))``,
SIMP_TAC (std_ss++CONJ_ss) [
   COND_PROP___STRONG_EQUIV_REWRITE,
   var_res_prop___REWRITE, var_res_prop___COND___REWRITE]);


val COND_PROP___EQUIV___WEAK_COND_REWRITE =
store_thm ("COND_PROP___EQUIV___WEAK_COND_REWRITE",
``!f wpb rpb sfb sfb'.
(BAG_ALL_DISTINCT (BAG_UNION wpb rpb) ==> (sfb = sfb')) ==>
(COND_PROP___EQUIV (var_res_prop f (wpb,rpb) sfb)
                   (var_res_prop f (wpb,rpb) sfb'))``,
SIMP_TAC (std_ss++CONJ_ss) [
   COND_PROP___EQUIV_REWRITE,
   var_res_prop___REWRITE, var_res_prop___COND___REWRITE]);




val var_res_prop___PROP___var_res_bool_proposition =
store_thm ("var_res_prop___PROP___var_res_bool_proposition",
``!f c wpb rpb sfb.
  var_res_prop___COND f (wpb,rpb) sfb ==>
  ((var_res_prop___PROP f (wpb,rpb)
     (BAG_INSERT (var_res_bool_proposition f c) sfb)) =
   (\s. c /\ s IN (var_res_prop___PROP f (wpb,rpb) sfb)))``,

SIMP_TAC std_ss [
   var_res_prop___COND_INSERT,
   VAR_RES_IS_STACK_IMPRECISE___USED_VARS___var_res_bool_proposition,
   var_res_prop___PROP_INSERT] THEN
REPEAT STRIP_TAC THEN
`IS_SEPARATION_COMBINATOR f` by FULL_SIMP_TAC std_ss [var_res_prop___COND___EXPAND] THEN
FULL_SIMP_TAC std_ss [var_res_bool_proposition_REWRITE, IN_ABS,
   asl_emp_def, GSYM RIGHT_EXISTS_AND_THM, GSYM LEFT_EXISTS_AND_THM,
   IS_SEPARATION_COMBINATOR_EXPAND_THM] THEN
QUANT_INSTANTIATE_TAC [] THEN
SIMP_TAC std_ss [IN_ABS3]);


val var_res_prop___var_res_prop_stack_true =
store_thm ("var_res_prop___var_res_prop_stack_true",
``!f wpb rpb sfb.
  (var_res_prop f (wpb,rpb) (BAG_INSERT (var_res_prop_stack_true f) sfb)) =
  (var_res_prop f (wpb,rpb) sfb)``,

SIMP_TAC std_ss [
   var_res_prop___REWRITE, var_res_prop___COND_INSERT,
   VAR_RES_IS_STACK_IMPRECISE___USED_VARS___var_res_prop_stack_true,
   var_res_prop_stack_true_def, IN_ABS3,
   var_res_prop___PROP___var_res_bool_proposition]);



val COND_PROP___STRONG_EQUIV___var_res_prop_stack_true =
store_thm ("COND_PROP___STRONG_EQUIV___var_res_prop_stack_true",
``!f wpb rpb sfb.
  COND_PROP___STRONG_EQUIV
  (var_res_prop f (wpb,rpb) (BAG_INSERT (var_res_prop_stack_true f) sfb))
  (var_res_prop f (wpb,rpb) sfb)``,
SIMP_TAC std_ss [var_res_prop___var_res_prop_stack_true, COND_PROP___STRONG_EQUIV___REFL]);



val COND_PROP___EQUIV___var_res_prop_stack_true =
store_thm ("COND_PROP___EQUIV___var_res_prop_stack_true",
``!f wpb rpb sfb.
  COND_PROP___EQUIV
     (var_res_prop f (wpb,rpb) (BAG_INSERT (var_res_prop_stack_true f) sfb))
     (var_res_prop f (wpb,rpb) sfb)``,
SIMP_TAC std_ss [var_res_prop___var_res_prop_stack_true, COND_PROP___EQUIV___REFL]);



val var_res_prop___PROP___asl_star =
store_thm ("var_res_prop___PROP___asl_star",
``!f wpb rpb sfb P1 P2.
  IS_SEPARATION_COMBINATOR f ==>
  (var_res_prop___PROP f (wpb,rpb) (BAG_INSERT (asl_star (VAR_RES_COMBINATOR f) P1 P2) sfb) =
   var_res_prop___PROP f (wpb,rpb) (BAG_INSERT P1 (BAG_INSERT P2 sfb)))``,
SIMP_TAC std_ss [var_res_prop___PROP___REWRITE,
   var_res_bigstar_REWRITE,
   IS_SEPARATION_COMBINATOR___VAR_RES_COMBINATOR,
   REWRITE_RULE [ASSOC_DEF] asl_star___PROPERTIES]);

val var_res_prop___PROP___asl_bigstar =
store_thm ("var_res_prop___PROP___asl_bigstar",
``!f wpb rpb sfb1 sfb2.
  IS_SEPARATION_COMBINATOR f ==>
  (var_res_prop___PROP f (wpb,rpb) (BAG_INSERT (asl_bigstar (VAR_RES_COMBINATOR f) sfb1) sfb2) =
   var_res_prop___PROP f (wpb,rpb) (BAG_UNION sfb1 sfb2))``,

SIMP_TAC std_ss [var_res_prop___PROP___REWRITE,
   var_res_bigstar_def,
   asl_bigstar_REWRITE, asl_bigstar_UNION,
   IS_SEPARATION_COMBINATOR___VAR_RES_COMBINATOR,
   asl_star___swap_var_res_prop_stack_true,
   REWRITE_RULE [ASSOC_DEF] asl_star___PROPERTIES]);



val var_res_prop___PROP___var_res_bigstar =
store_thm ("var_res_prop___PROP___var_res_bigstar",
``!f wpb rpb sfb1 sfb2.
  IS_SEPARATION_COMBINATOR f ==>
  (var_res_prop___PROP f (wpb,rpb) (BAG_INSERT (var_res_bigstar f sfb1) sfb2) =
   var_res_prop___PROP f (wpb,rpb) (BAG_UNION sfb1 sfb2))``,
SIMP_TAC std_ss [var_res_prop___PROP___REWRITE,
   var_res_bigstar_REWRITE, var_res_bigstar_UNION]);


val var_res_prop___PROP___var_res_prop_stack_true =
store_thm ("var_res_prop___PROP___var_res_prop_stack_true",
``!f wpb rpb sfb.
  IS_SEPARATION_COMBINATOR f ==>
  (var_res_prop___PROP f (wpb,rpb) (BAG_INSERT (var_res_prop_stack_true f) sfb) =
   var_res_prop___PROP f (wpb,rpb) sfb)``,
SIMP_TAC std_ss [var_res_prop___PROP___REWRITE,
   var_res_bigstar___var_res_prop_stack_true]);


val var_res_prop___asl_star =
store_thm ("var_res_prop___asl_star",
``!f f' wpb rpb sfb P1 P2.
  (IS_VAR_RES_COMBINATOR f /\ (GET_VAR_RES_COMBINATOR f = f') /\
   (VAR_RES_IS_STACK_IMPRECISE___USED_VARS (SET_OF_BAG (BAG_UNION wpb rpb)) P1) /\
   (VAR_RES_IS_STACK_IMPRECISE___USED_VARS (SET_OF_BAG (BAG_UNION wpb rpb)) P2)) ==>
  ((var_res_prop f' (wpb,rpb) (BAG_INSERT (asl_star f P1 P2) sfb)) =
   (var_res_prop f' (wpb,rpb) (BAG_INSERT P1 (BAG_INSERT P2 sfb))))``,

SIMP_TAC (std_ss++CONJ_ss) [
  IS_VAR_RES_COMBINATOR_def,
  GSYM LEFT_EXISTS_AND_THM, GSYM LEFT_FORALL_IMP_THM,
  GET_VAR_RES_COMBINATOR_THM] THEN
SIMP_TAC std_ss [var_res_prop___REWRITE,
   var_res_prop___COND_INSERT,
   VAR_RES_IS_STACK_IMPRECISE___USED_VARS___asl_star,
   var_res_prop___PROP___asl_star]);


val var_res_prop___PROP___asl_exists =
store_thm ("var_res_prop___PROP___asl_exists",
``!f wpb rpb sfb P.
  IS_SEPARATION_COMBINATOR f ==>
  ((var_res_prop___PROP f (wpb,rpb) (BAG_INSERT (asl_exists y. P y) sfb)) =
   asl_exists y. var_res_prop___PROP f (wpb,rpb) (BAG_INSERT (P y) sfb))``,

SIMP_TAC std_ss [var_res_prop___PROP___REWRITE, EXTENSION] THEN
ASM_SIMP_TAC std_ss [asl_bool_EVAL, IN_ABS, var_res_bigstar_REWRITE,
   IS_SEPARATION_COMBINATOR___VAR_RES_COMBINATOR,
   GSYM asl_exists___asl_star_THM,
   RIGHT_EXISTS_AND_THM]);



val var_res_prop___asl_exists =
store_thm ("var_res_prop___asl_exists",
``!f wpb rpb sfb P.
  (!x. VAR_RES_IS_STACK_IMPRECISE___USED_VARS (SET_OF_BAG (BAG_UNION wpb rpb)) (P x)) ==>

  ((var_res_prop f (wpb,rpb) (BAG_INSERT (asl_exists y. P y) sfb)) =
   COND_PROP___STRONG_EXISTS (\y. var_res_prop f (wpb,rpb) (BAG_INSERT (P y) sfb)))``,

SIMP_TAC (std_ss++EQUIV_EXTRACT_ss) [COND_PROP___STRONG_EXISTS_def,
  var_res_prop___REWRITE, var_res_prop___COND_INSERT,
   VAR_RES_IS_STACK_IMPRECISE___USED_VARS___asl_exists_direct] THEN
REPEAT STRIP_TAC THEN
Tactical.REVERSE (Cases_on `var_res_prop___COND f (wpb,rpb) sfb`) THEN (
   ASM_SIMP_TAC std_ss [EXTENSION, asl_bool_EVAL, IN_ABS]
) THEN
`IS_SEPARATION_COMBINATOR f` by ALL_TAC THEN1 (
   FULL_SIMP_TAC std_ss [var_res_prop___COND___EXPAND]
) THEN
ASM_SIMP_TAC std_ss [var_res_prop___PROP___asl_exists,
   asl_bool_EVAL]);



(******************************************************
 var_res_prop_binexpression_cond and similar
 ******************************************************)


val VAR_RES_IS_STACK_IMPRECISE___USED_VARS___var_res_prop_binexpression_cond =
store_thm ("VAR_RES_IS_STACK_IMPRECISE___USED_VARS___var_res_prop_binexpression_cond",
``!f p e1 e2 vs P1 P2.
(VAR_RES_IS_STACK_IMPRECISE___USED_VARS vs P1 /\
 VAR_RES_IS_STACK_IMPRECISE___USED_VARS vs P2 /\
 VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET vs e1 /\
 VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET vs e2) ==>
 VAR_RES_IS_STACK_IMPRECISE___USED_VARS vs (var_res_prop_binexpression_cond f p e1 e2 P1 P2)``,


REPEAT STRIP_TAC THEN
SIMP_TAC std_ss [var_res_prop_binexpression_cond_def,
   VAR_RES_IS_STACK_IMPRECISE___USED_VARS___ALTERNATIVE_DEF, IN_ABS] THEN
REPEAT GEN_TAC THEN STRIP_TAC THEN

`?st2 st. (FST s2 = st2) /\ (FST s = st)` by ALL_TAC THEN1 (
   Cases_on `s2` THEN Cases_on `s` THEN SIMP_TAC std_ss []
) THEN
FULL_SIMP_TAC std_ss [] THEN
`(e1 st2 = e1 st) /\ (e2 st2 = e2 st)` by ALL_TAC THEN1 (
   CONSEQ_REWRITE_TAC ([], [VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET___EXP_EQ_IS_SOME], []) THEN
   SIMP_TAC std_ss [GSYM LEFT_EXISTS_AND_THM, GSYM RIGHT_EXISTS_AND_THM] THEN
   Q.LIST_EXISTS_TAC [`vs`, `vs`] THEN
   ASM_SIMP_TAC std_ss [IN_INTER]
) THEN
FULL_SIMP_TAC std_ss [VAR_RES_IS_STACK_IMPRECISE___USED_VARS___ALTERNATIVE_DEF] THEN
Cases_on `p (THE (e1 st)) (THE (e2 st))` THEN (
   FULL_SIMP_TAC std_ss [] THEN METIS_TAC[]
));


val VAR_RES_IS_STACK_IMPRECISE___var_res_prop_binexpression_cond =
store_thm ("VAR_RES_IS_STACK_IMPRECISE___var_res_prop_binexpression_cond",
``!f p e1 e2 P1 P2.
(VAR_RES_IS_STACK_IMPRECISE P1 /\ VAR_RES_IS_STACK_IMPRECISE P2 /\
 IS_SOME (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS e1) /\
 IS_SOME (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS e2)) ==>
 VAR_RES_IS_STACK_IMPRECISE (var_res_prop_binexpression_cond f p e1 e2 P1 P2)``,
SIMP_TAC std_ss [VAR_RES_IS_STACK_IMPRECISE___ALTERNATIVE_DEF,
                 GSYM VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET___UNIV_REWRITE,
                 VAR_RES_IS_STACK_IMPRECISE___USED_VARS___var_res_prop_binexpression_cond]);


val var_res_prop_binexpression_cond___COMM = store_thm (
"var_res_prop_binexpression_cond___COMM",
``!f p e1 e2 P1 P2.
  (var_res_prop_binexpression_cond f p e1 e2 P1 P2 =
  (var_res_prop_binexpression_cond f (\x1 x2. ~(p x1 x2)) e1 e2 P2 P1))``,

SIMP_TAC (std_ss++EQUIV_EXTRACT_ss) [
   var_res_prop_binexpression_cond_def, FUN_EQ_THM] THEN
METIS_TAC[]);


val var_res_prop_binexpression_cond___asl_false___false = store_thm (
"var_res_prop_binexpression_cond___asl_false___false",
``!f p e1 e2 P.
  (IS_SEPARATION_COMBINATOR f /\ VAR_RES_IS_STACK_IMPRECISE P /\
   IS_SOME (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS e1) /\
   IS_SOME (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS e2)) ==>
  (var_res_prop_binexpression_cond f p e1 e2 P asl_false =
      asl_star (VAR_RES_COMBINATOR f)
          (var_res_prop_binexpression f T p e1 e2) P)``,

SIMP_TAC std_ss [var_res_prop_binexpression_cond_def,
   asl_bool_EVAL, EXTENSION, IN_ABS] THEN
REPEAT STRIP_TAC THEN
ASM_SIMP_TAC std_ss [asl_star___VAR_RES_IS_STACK_IMPRECISE,
   VAR_RES_IS_STACK_IMPRECISE___var_res_prop_binexpression, IN_ABS] THEN
IMP_RES_TAC IS_SEPARATION_COMBINATOR_NEUTRAL_ELEMENT_FUNCTION_IMP THEN
SIMP_TAC (std_ss++EQUIV_EXTRACT_ss) [var_res_prop_binexpression_def,
   var_res_stack_proposition_def, LET_THM, IN_ABS] THEN
STRIP_TAC THEN
`?c1 c2. (e2 (FST x) = c2) /\ (e1 (FST x) = c1)` by ALL_TAC THEN1 (
   FULL_SIMP_TAC std_ss [IS_SOME_EXISTS]
) THEN
FULL_SIMP_TAC std_ss [IS_SEPARATION_COMBINATOR_NEUTRAL_ELEMENT_FUNCTION___WITH_COMBINATOR_THM,
   asl_emp_def, IN_ABS, GSYM RIGHT_EXISTS_AND_THM, GSYM LEFT_EXISTS_AND_THM] THEN
QUANT_INSTANTIATE_TAC []);

val var_res_prop_binexpression_cond___asl_false___true = store_thm (
"var_res_prop_binexpression_cond___asl_false___true",
``!f p e1 e2 P.
  (IS_SEPARATION_COMBINATOR f /\ VAR_RES_IS_STACK_IMPRECISE P /\
   IS_SOME (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS e1) /\
   IS_SOME (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS e2)) ==>
  (var_res_prop_binexpression_cond f p e1 e2 asl_false P=
      asl_star (VAR_RES_COMBINATOR f)
          (var_res_prop_binexpression f T (\x1 x2. ~(p x1 x2)) e1 e2) P)``,

ONCE_REWRITE_TAC [var_res_prop_binexpression_cond___COMM] THEN
SIMP_TAC std_ss [var_res_prop_binexpression_cond___asl_false___false]);





(******************************************************
 Extended Hoare Triples that preserve permissions
 ******************************************************)


val VAR_RES_HOARE_TRIPLE_def = Define `
   VAR_RES_HOARE_TRIPLE xenv penv P prog Q =
   !x. ASL_PROGRAM_HOARE_TRIPLE xenv penv
              (\s. s IN P /\ (s = x)) prog (\s. s IN Q /\ (VAR_RES_STACK___IS_EQUAL_UPTO_VALUES (FST x) (FST s)))`

val VAR_RES_PERM_HOARE_TRIPLE_def = Define `
VAR_RES_PERM_HOARE_TRIPLE xenv penv P prog =
!s s'. ((s IN P) /\ (ASL_PROGRAM_SEM xenv penv prog s = SOME s')) ==>
    (!s2. s2 IN s' ==> VAR_RES_STACK___IS_EQUAL_UPTO_VALUES (FST s) (FST s2))`;


val VAR_RES_HOARE_TRIPLE_REWRITE = store_thm (
"VAR_RES_HOARE_TRIPLE_REWRITE",
``VAR_RES_HOARE_TRIPLE xenv penv P prog Q =
  ASL_PROGRAM_HOARE_TRIPLE xenv penv P prog Q /\
  VAR_RES_PERM_HOARE_TRIPLE xenv penv P prog``,

SIMP_TAC std_ss [VAR_RES_HOARE_TRIPLE_def, SUBSET_DEF,
   ASL_PROGRAM_HOARE_TRIPLE_def, IN_ABS,
   VAR_RES_PERM_HOARE_TRIPLE_def,
   HOARE_TRIPLE_def, fasl_order_THM] THEN
METIS_TAC[SOME_11]);


val VAR_RES_HOARE_TRIPLE_QUANT_def = Define `
    VAR_RES_HOARE_TRIPLE_QUANT xenv penv pre body post =
!cond_arg arg.
VAR_RES_HOARE_TRIPLE xenv penv
    (pre arg cond_arg) (body arg) (post arg cond_arg)`;



val var_res_lock_invariant_def =
Define `var_res_lock_invariant f wp P =
(\s. (FDOM (FST s) = wp) /\
     (!v. v IN wp ==> (SND ((FST s) ' v) = var_res_write_permission)) /\
     s IN asl_star (VAR_RES_COMBINATOR f) (var_res_prop_stack_true f) P)`;


val VAR_RES_LOCK_ENV_MAP_def = Define `
VAR_RES_LOCK_ENV_MAP f =
MAP (\x. (FST x, var_res_lock_invariant f (LIST_TO_SET (FST (SND x))) (SND (SND x))))`;


val VAR_RES_COND_HOARE_TRIPLE_def = Define `
   VAR_RES_COND_HOARE_TRIPLE f P prog Q =
   (IS_SEPARATION_COMBINATOR f /\ (FST P) /\ (FST Q)) ==> VAR_RES_HOARE_TRIPLE (VAR_RES_COMBINATOR f, K asl_false) FEMPTY (SND P) prog (SND Q)`

val VAR_RES_PROGRAM_SEM_def = Define
`VAR_RES_PROGRAM_SEM f = ASL_PROGRAM_SEM (VAR_RES_COMBINATOR f, K asl_false) FEMPTY`


val VAR_RES_COND_HOARE_TRIPLE_REWRITE = store_thm (
"VAR_RES_COND_HOARE_TRIPLE_REWRITE",
``!f P prog Q.
  VAR_RES_COND_HOARE_TRIPLE f P prog Q =
  !x. COND_HOARE_TRIPLE  (IS_SEPARATION_COMBINATOR f /\ FST P, \s. s IN SND P /\ (s = x))
                         (VAR_RES_PROGRAM_SEM f prog)
                         (FST Q,
                          \s. s IN SND Q /\
                              VAR_RES_STACK___IS_EQUAL_UPTO_VALUES (FST x) (FST s))``,

Cases_on `P` THEN Cases_on `Q` THEN
SIMP_TAC std_ss [VAR_RES_COND_HOARE_TRIPLE_def,
   VAR_RES_HOARE_TRIPLE_def, ASL_PROGRAM_HOARE_TRIPLE_def,
   GSYM VAR_RES_PROGRAM_SEM_def, COND_HOARE_TRIPLE_def] THEN
METIS_TAC[]);


val VAR_RES_COND_HOARE_TRIPLE_INTRO = store_thm (
"VAR_RES_COND_HOARE_TRIPLE_INTRO",
``!f f' lock_env penv wp1 rp1 d P1 wp2 rp2 P2 prog.
  asl_prog_IS_RESOURCE_AND_PROCCALL_FREE prog /\ IS_VAR_RES_COMBINATOR f /\
  (GET_VAR_RES_COMBINATOR f = f') ==>

  (VAR_RES_HOARE_TRIPLE (f, lock_env) penv
                        (var_res_prop_input_ap_distinct f' (wp1, rp1) d P1)
                        prog
                        (var_res_prop_input_ap_distinct f' (wp2, rp2) d P2) =
   VAR_RES_COND_HOARE_TRIPLE f' (var_res_prop_input_distinct f' (wp1, rp1) d P1) prog
                               (var_res_prop_input_distinct f' (wp2, rp2) d P2))``,

SIMP_TAC std_ss [VAR_RES_COND_HOARE_TRIPLE_def,
   var_res_prop_input_distinct_def,
   var_res_prop_input_ap_distinct_def,
   asl_bool_REWRITES, EVERY_DEF,
   BAG_ALL_DISTINCT_THM, NOT_IN_EMPTY_BAG,
   VAR_RES_HOARE_TRIPLE_def, asl_bool_EVAL,
   BAG_UNION_EMPTY, FINITE_BAG_THM,
   ASL_PROGRAM_HOARE_TRIPLE_def, IN_ABS,
   HOARE_TRIPLE_def, fasl_order_THM, SUBSET_DEF,
   asl_prog_IS_RESOURCE_AND_PROCCALL_FREE_def] THEN
REPEAT STRIP_TAC THEN
Cases_on `ALL_DISTINCT d` THEN ASM_SIMP_TAC std_ss [] THEN
FULL_SIMP_TAC std_ss [IS_VAR_RES_COMBINATOR_def,
   GET_VAR_RES_COMBINATOR_THM] THEN
METIS_TAC[]);



val VAR_RES_COND_HOARE_TRIPLE___COND_PROP_IMP = store_thm (
"VAR_RES_COND_HOARE_TRIPLE___COND_PROP_IMP",
``!f P1 P2 prog Q.
  COND_PROP___IMP P1 P2 ==>
  (VAR_RES_COND_HOARE_TRIPLE f P2 prog Q ==>
   VAR_RES_COND_HOARE_TRIPLE f P1 prog Q)``,

SIMP_TAC std_ss [VAR_RES_COND_HOARE_TRIPLE_def,
   COND_PROP___IMP_def, VAR_RES_HOARE_TRIPLE_def,
   ASL_PROGRAM_HOARE_TRIPLE_def, HOARE_TRIPLE_def,
   fasl_order_THM, IN_ABS] THEN
METIS_TAC[]);


val VAR_RES_COND_HOARE_TRIPLE___COND_PROP_STRONG_IMP = store_thm (
"VAR_RES_COND_HOARE_TRIPLE___COND_PROP_STRONG_IMP",
``!f P1 P2 prog Q.
  COND_PROP___STRONG_IMP P1 P2 ==>
  (VAR_RES_COND_HOARE_TRIPLE f P2 prog Q ==>
   VAR_RES_COND_HOARE_TRIPLE f P1 prog Q)``,
METIS_TAC[COND_PROP___STRONG_IMP_IMP, VAR_RES_COND_HOARE_TRIPLE___COND_PROP_IMP]);


val VAR_RES_COND_HOARE_TRIPLE___COND_PROP_EQUIV = store_thm (
"VAR_RES_COND_HOARE_TRIPLE___COND_PROP_EQUIV",
``!f P1 P2 prog Q.
  COND_PROP___EQUIV P1 P2 ==>
  (VAR_RES_COND_HOARE_TRIPLE f P1 prog Q =
   VAR_RES_COND_HOARE_TRIPLE f P2 prog Q)``,
PROVE_TAC[COND_PROP___EQUIV_def,
   VAR_RES_COND_HOARE_TRIPLE___COND_PROP_IMP]);


val VAR_RES_COND_HOARE_TRIPLE___COND_PROP_STRONG_EQUIV = store_thm (
"VAR_RES_COND_HOARE_TRIPLE___COND_PROP_STRONG_EQUIV",
``!f P1 P2 prog Q.
  COND_PROP___STRONG_EQUIV P1 P2 ==>
  (VAR_RES_COND_HOARE_TRIPLE f P1 prog Q =
   VAR_RES_COND_HOARE_TRIPLE f P2 prog Q)``,
PROVE_TAC[COND_PROP___STRONG_EQUIV_def,
   VAR_RES_COND_HOARE_TRIPLE___COND_PROP_STRONG_IMP]);




val VAR_RES_COND_HOARE_TRIPLE___COND_EXISTS = store_thm (
"VAR_RES_COND_HOARE_TRIPLE___COND_EXISTS",
``!f P prog Q.
  (VAR_RES_COND_HOARE_TRIPLE f (COND_PROP___EXISTS x. P x) prog Q =
   !x. VAR_RES_COND_HOARE_TRIPLE f (P x) prog Q)``,

SIMP_TAC std_ss [COND_PROP___EXISTS_def,
  VAR_RES_COND_HOARE_TRIPLE_def, VAR_RES_HOARE_TRIPLE_def,
  GSYM LEFT_EXISTS_AND_THM, GSYM LEFT_FORALL_IMP_THM,
  HOARE_TRIPLE_def, IN_ABS, ASL_PROGRAM_HOARE_TRIPLE_def,
  fasl_order_THM] THEN
METIS_TAC[]);


val VAR_RES_PROGRAM_IS_ABSTRACTION_def = Define `
VAR_RES_PROGRAM_IS_ABSTRACTION f prog1 prog2 =
ASL_PROGRAM_IS_ABSTRACTION (VAR_RES_COMBINATOR f, K asl_false) FEMPTY prog1 prog2`


val VAR_RES_COND_HOARE_TRIPLE___PROGRAM_ABSTRACTION = store_thm (
"VAR_RES_COND_HOARE_TRIPLE___PROGRAM_ABSTRACTION",
``!f P prog1 prog2 Q.
  (IS_SEPARATION_COMBINATOR f ==>
   (VAR_RES_PROGRAM_IS_ABSTRACTION f prog1 prog2 /\
    VAR_RES_COND_HOARE_TRIPLE f P prog2 Q)) ==>
   VAR_RES_COND_HOARE_TRIPLE f P prog1 Q``,

SIMP_TAC std_ss [VAR_RES_PROGRAM_IS_ABSTRACTION_def,
   ASL_PROGRAM_IS_ABSTRACTION___ALTERNATIVE_DEF,
   VAR_RES_COND_HOARE_TRIPLE_def,
   VAR_RES_HOARE_TRIPLE_def]);


val VAR_RES_COND_HOARE_TRIPLE___PROGRAM_ABSTRACTION_EVAL = store_thm (
"VAR_RES_COND_HOARE_TRIPLE___PROGRAM_ABSTRACTION_EVAL",
``!f P prog1 prog2 Q.
  VAR_RES_PROGRAM_IS_ABSTRACTION f prog1 prog2 ==>
  VAR_RES_COND_HOARE_TRIPLE f P prog2 Q ==>
  VAR_RES_COND_HOARE_TRIPLE f P prog1 Q``,
PROVE_TAC [VAR_RES_COND_HOARE_TRIPLE___PROGRAM_ABSTRACTION]);



val VAR_RES_COND_HOARE_TRIPLE___PROGRAM_ABSTRACTION_first = store_thm (
"VAR_RES_COND_HOARE_TRIPLE___PROGRAM_ABSTRACTION_first",
``!f P prog1 prog2 prog3 Q.
  (IS_SEPARATION_COMBINATOR f ==>
   (VAR_RES_PROGRAM_IS_ABSTRACTION f prog1 prog2 /\
    VAR_RES_COND_HOARE_TRIPLE f P (asl_prog_seq prog2 prog3) Q)) ==>
   VAR_RES_COND_HOARE_TRIPLE f P (asl_prog_seq prog1 prog3) Q``,

REPEAT STRIP_TAC THEN
MATCH_MP_TAC VAR_RES_COND_HOARE_TRIPLE___PROGRAM_ABSTRACTION THEN
Q.EXISTS_TAC `asl_prog_seq prog2 prog3` THEN
FULL_SIMP_TAC std_ss [VAR_RES_PROGRAM_IS_ABSTRACTION_def] THEN
STRIP_TAC THEN
MATCH_MP_TAC ASL_PROGRAM_IS_ABSTRACTION___seq THEN
ASM_SIMP_TAC std_ss [ASL_PROGRAM_IS_ABSTRACTION___REFL]);


val VAR_RES_COND_HOARE_TRIPLE___PROGRAM_ABSTRACTION_first_block = store_thm (
"VAR_RES_COND_HOARE_TRIPLE___PROGRAM_ABSTRACTION_first_block",
``!f wpb rpb sfb prog1 prog2 progL Q.
  (BAG_ALL_DISTINCT (BAG_UNION wpb rpb) ==> VAR_RES_PROGRAM_IS_ABSTRACTION f prog1 prog2) ==>
  (VAR_RES_COND_HOARE_TRIPLE f (var_res_prop f (wpb,rpb) sfb) (asl_prog_block (prog2::progL)) Q ==>
   VAR_RES_COND_HOARE_TRIPLE f (var_res_prop f (wpb,rpb) sfb) (asl_prog_block (prog1::progL)) Q)``,

REPEAT STRIP_TAC THEN
Tactical.REVERSE (Cases_on `BAG_ALL_DISTINCT (BAG_UNION wpb rpb)`) THEN1 (
   ASM_SIMP_TAC std_ss [VAR_RES_COND_HOARE_TRIPLE_def,
      var_res_prop___REWRITE, var_res_prop___COND___REWRITE]
) THEN
MATCH_MP_TAC (MP_CANON VAR_RES_COND_HOARE_TRIPLE___PROGRAM_ABSTRACTION_EVAL) THEN
Q.EXISTS_TAC `asl_prog_block (prog2::progL)` THEN
FULL_SIMP_TAC std_ss [VAR_RES_PROGRAM_IS_ABSTRACTION_def] THEN
MATCH_MP_TAC (MP_CANON ASL_PROGRAM_IS_ABSTRACTION___block) THEN
ASM_REWRITE_TAC[ASL_PROGRAM_IS_ABSTRACTION___REFL]);


val VAR_RES_COND_HOARE_TRIPLE___PROGRAM_ABSTRACTION_first_block_simple = store_thm (
"VAR_RES_COND_HOARE_TRIPLE___PROGRAM_ABSTRACTION_first_block_simple",
``!f P prog1 prog2 progL Q.
  (VAR_RES_PROGRAM_IS_ABSTRACTION f prog1 prog2) ==>
  (VAR_RES_COND_HOARE_TRIPLE f P (asl_prog_block (prog2::progL)) Q ==>
   VAR_RES_COND_HOARE_TRIPLE f P (asl_prog_block (prog1::progL)) Q)``,

REPEAT STRIP_TAC THEN
MATCH_MP_TAC (MP_CANON VAR_RES_COND_HOARE_TRIPLE___PROGRAM_ABSTRACTION_EVAL) THEN
Q.EXISTS_TAC `asl_prog_block (prog2::progL)` THEN
FULL_SIMP_TAC std_ss [VAR_RES_PROGRAM_IS_ABSTRACTION_def] THEN
MATCH_MP_TAC (MP_CANON ASL_PROGRAM_IS_ABSTRACTION___block) THEN
ASM_REWRITE_TAC[ASL_PROGRAM_IS_ABSTRACTION___REFL]);

val var_res_best_local_action_def = Define `
    var_res_best_local_action f P Q =
    quant_best_local_action f (\x s. s IN P /\ (s = x))
(\x s. s IN Q /\ (VAR_RES_STACK___IS_EQUAL_UPTO_VALUES (FST x) (FST s)))`;


val var_res_cond_best_local_action_def = Define `
    var_res_cond_best_local_action f P Q =
    if ~(FST P) \/ ~(FST Q) then
       asla_diverge
    else
       var_res_best_local_action f (SND P) (SND Q)`;

val ASL_IS_LOCAL_ACTION___var_res_best_local_action = store_thm (
"ASL_IS_LOCAL_ACTION___var_res_best_local_action",
``!f P Q. IS_SEPARATION_COMBINATOR f ==>
          ASL_IS_LOCAL_ACTION f (var_res_best_local_action f P Q)``,
SIMP_TAC std_ss [var_res_best_local_action_def, quant_best_local_action_THM]);


val ASL_IS_LOCAL_ACTION___var_res_cond_best_local_action = store_thm (
"ASL_IS_LOCAL_ACTION___var_res_cond_best_local_action",
``!f P Q. IS_SEPARATION_COMBINATOR f ==>
          ASL_IS_LOCAL_ACTION f (var_res_cond_best_local_action f P Q)``,
SIMP_TAC std_ss [var_res_cond_best_local_action_def,
   COND_RAND, COND_RATOR, ASL_IS_LOCAL_ACTION___asla_diverge,
   ASL_IS_LOCAL_ACTION___var_res_best_local_action]);



val var_res_prog_best_local_action_def = Define `
        var_res_prog_best_local_action P Q =
        asl_prog_quant_best_local_action (\x s. s IN P /\ (s = x))
(\x s. s IN Q /\ (VAR_RES_STACK___IS_EQUAL_UPTO_VALUES (FST x) (FST s)))`;


val var_res_prog_cond_best_local_action_def = Define `
  var_res_prog_cond_best_local_action pre post =
     if ~(FST pre) \/ ~(FST post) then
        asl_prog_diverge
     else
        var_res_prog_best_local_action (SND pre) (SND post)`



val var_res_prog_best_local_action_REWRITE = store_thm (
"var_res_prog_best_local_action_REWRITE",
``var_res_prog_best_local_action pre post =
  asl_prog_prim_command (asl_pc_shallow_command
     (\f. var_res_best_local_action f pre post))``,

SIMP_TAC std_ss [
   var_res_prog_best_local_action_def,
   asl_prog_quant_best_local_action_def,
   asl_prog_diverge_def,
   asl_prog_prim_command_def, asl_pc_diverge_def,
   var_res_cond_best_local_action_def,
   combinTheory.K_DEF,
   COND_RAND, COND_RATOR,
   GSYM var_res_best_local_action_def]);


val var_res_prog_cond_best_local_action_REWRITE = store_thm (
"var_res_prog_cond_best_local_action_REWRITE",
``var_res_prog_cond_best_local_action pre post =
  asl_prog_prim_command (asl_pc_shallow_command
     (\f. var_res_cond_best_local_action f pre post))``,

SIMP_TAC std_ss [
   var_res_prog_cond_best_local_action_def,
   var_res_prog_best_local_action_def,
   asl_prog_quant_best_local_action_def,
   asl_prog_diverge_def,
   asl_prog_prim_command_def, asl_pc_diverge_def,
   var_res_cond_best_local_action_def,
   combinTheory.K_DEF,
   COND_RAND, COND_RATOR,
   GSYM var_res_best_local_action_def]);



val var_res_prog_cond_best_local_action___STRONG_EQUIV___pre_post =
store_thm ("var_res_prog_cond_best_local_action___STRONG_EQUIV___pre_post",
``!pre post pre' post'.
   (COND_PROP___STRONG_EQUIV pre pre' /\
    COND_PROP___STRONG_EQUIV post post') ==>

   (var_res_prog_cond_best_local_action pre post =
    var_res_prog_cond_best_local_action pre' post')``,


SIMP_TAC std_ss [var_res_prog_cond_best_local_action_def,
                 COND_PROP___STRONG_EQUIV_REWRITE]);


val var_res_prog_cond_best_local_action___STRONG_IMP___pre_post =
store_thm ("var_res_prog_cond_best_local_action___STRONG_IMP___pre_post",
``!f pre post pre' post'.
   (COND_PROP___STRONG_IMP pre pre' /\
    COND_PROP___STRONG_IMP post post') ==>

   (VAR_RES_PROGRAM_IS_ABSTRACTION f
      (var_res_prog_cond_best_local_action pre post)
      (var_res_prog_cond_best_local_action pre' post'))``,


SIMP_TAC std_ss [var_res_prog_cond_best_local_action_def,
                 COND_PROP___STRONG_IMP_def] THEN
REPEAT GEN_TAC THEN
Tactical.REVERSE (Cases_on `FST pre /\ FST post`) THEN (
   FULL_SIMP_TAC (std_ss++CONJ_ss) [VAR_RES_PROGRAM_IS_ABSTRACTION_def,
       ASL_PROGRAM_IS_ABSTRACTION___diverge,
       ASL_PROGRAM_IS_ABSTRACTION___REFL]
));



val var_res_quant_best_local_action_def = Define `
    var_res_quant_best_local_action f qP qQ =
    quant_best_local_action f (\x s. s IN (qP (FST x)) /\ (s = (SND x)))
(\x s. s IN (qQ (FST x)) /\ (VAR_RES_STACK___IS_EQUAL_UPTO_VALUES (FST (SND x)) (FST s)))`;


val var_res_cond_quant_best_local_action_def = Define `
    var_res_cond_quant_best_local_action f qP qQ =
    if ~(!x. FST (qP x)) \/ ~(!x. FST (qQ x)) then
       asla_diverge
    else
       var_res_quant_best_local_action f (\x. SND (qP x)) (\x. SND (qQ x))`;


val ASL_IS_LOCAL_ACTION___var_res_quant_best_local_action = store_thm (
"ASL_IS_LOCAL_ACTION___var_res_quant_best_local_action",
``!f P Q. IS_SEPARATION_COMBINATOR f ==>
          ASL_IS_LOCAL_ACTION f (var_res_quant_best_local_action f P Q)``,
SIMP_TAC std_ss [var_res_quant_best_local_action_def, quant_best_local_action_THM]);


val ASL_IS_LOCAL_ACTION___var_res_cond_quant_best_local_action = store_thm (
"ASL_IS_LOCAL_ACTION___var_res_cond_quant_best_local_action",
``!f P Q. IS_SEPARATION_COMBINATOR f ==>
          ASL_IS_LOCAL_ACTION f (var_res_cond_quant_best_local_action f P Q)``,
SIMP_TAC std_ss [var_res_cond_quant_best_local_action_def,
   COND_RAND, COND_RATOR, ASL_IS_LOCAL_ACTION___asla_diverge,
   ASL_IS_LOCAL_ACTION___var_res_quant_best_local_action]);



val var_res_prog_quant_best_local_action_def = Define `
        var_res_prog_quant_best_local_action qP qQ =
        asl_prog_quant_best_local_action (\x s. s IN (qP (FST x)) /\ (s = (SND x)))
(\x s. s IN (qQ (FST x)) /\ (VAR_RES_STACK___IS_EQUAL_UPTO_VALUES (FST (SND x)) (FST s)))`;


val var_res_prog_cond_quant_best_local_action_def = Define `
  var_res_prog_cond_quant_best_local_action qP qQ =
     if ~(!x. FST (qP x)) \/ ~(!x. FST (qQ x)) then
        asl_prog_diverge
     else
        var_res_prog_quant_best_local_action (\x. SND (qP x)) (\x. SND (qQ x))`


val var_res_prog_quant_best_local_action_REWRITE = store_thm (
"var_res_prog_quant_best_local_action_REWRITE",
``var_res_prog_quant_best_local_action qP qQ =
  asl_prog_prim_command (asl_pc_shallow_command
     (\f. var_res_quant_best_local_action f qP qQ))``,

SIMP_TAC std_ss [
   var_res_prog_quant_best_local_action_def,
   asl_prog_quant_best_local_action_def,
   asl_prog_diverge_def,
   asl_prog_prim_command_def, asl_pc_diverge_def,
   var_res_cond_quant_best_local_action_def,
   combinTheory.K_DEF,
   COND_RAND, COND_RATOR,
   GSYM var_res_quant_best_local_action_def]);


val var_res_prog_cond_quant_best_local_action_REWRITE = store_thm (
"var_res_prog_cond_quant_best_local_action_REWRITE",
``var_res_prog_cond_quant_best_local_action qP qQ =
  asl_prog_prim_command (asl_pc_shallow_command
     (\f. var_res_cond_quant_best_local_action f qP qQ))``,

SIMP_TAC std_ss [
   var_res_prog_cond_quant_best_local_action_def,
   var_res_prog_quant_best_local_action_def,
   asl_prog_quant_best_local_action_def,
   asl_prog_diverge_def,
   asl_prog_prim_command_def, asl_pc_diverge_def,
   var_res_cond_quant_best_local_action_def,
   combinTheory.K_DEF,
   COND_RAND, COND_RATOR,
   GSYM var_res_quant_best_local_action_def]);


val var_res_prog_cond_best_local_action_INTRO = store_thm (
"var_res_prog_cond_best_local_action_INTRO",
``!f f' wp wp' rp rp' d d' P P'.
  ALL_DISTINCT d /\ ALL_DISTINCT d' ==>
 (var_res_prog_best_local_action
     (var_res_prop_input_ap_distinct f  (wp,  rp)  d  P)
     (var_res_prop_input_ap_distinct f' (wp', rp') d' P') =
  var_res_prog_cond_best_local_action
     (var_res_prop_input_distinct f  (wp , rp ) d  P)
     (var_res_prop_input_distinct f' (wp', rp') d' P'))``,

SIMP_TAC std_ss [var_res_prog_cond_best_local_action_def,
   var_res_prop_input_distinct_def]);


val var_res_prog_cond_best_local_action_INTRO_star = store_thm (
"var_res_prog_cond_best_local_action_INTRO_star",
``!f f' wp1 wp1' rp1 rp1' d1 d1' P1 P1' wp2 wp2' rp2 rp2' d2 d2' P2 P2'.
  (ALL_DISTINCT d1 /\ ALL_DISTINCT d2 /\
  ALL_DISTINCT d1' /\ ALL_DISTINCT d2' /\
  IS_VAR_RES_COMBINATOR f' /\ (GET_VAR_RES_COMBINATOR f' = f)) ==>

 ((var_res_prog_best_local_action
     (asl_star f'
        (var_res_prop_input_ap_distinct f  (wp1,  rp1)  d1  P1)
        (var_res_prop_input_ap_distinct f  (wp2,  rp2)  d2  P2))
     (asl_star f'
        (var_res_prop_input_ap_distinct f (wp1', rp1') d1' P1')
        (var_res_prop_input_ap_distinct f (wp2', rp2') d2' P2'))) =
 (var_res_prog_cond_best_local_action
     (asl_cond_star f'
        (var_res_prop_input_distinct f  (wp1,  rp1)  d1  P1)
        (var_res_prop_input_distinct f  (wp2,  rp2)  d2  P2))
     (asl_cond_star f'
        (var_res_prop_input_distinct f (wp1', rp1') d1' P1')
        (var_res_prop_input_distinct f (wp2', rp2') d2' P2'))))``,

SIMP_TAC (std_ss++CONJ_ss) [var_res_prog_cond_best_local_action_def,
   var_res_prop_input_distinct_def, asl_cond_star_def,
   GET_VAR_RES_COMBINATOR_THM]);


val var_res_prog_cond_quant_best_local_action_INTRO = store_thm (
"var_res_prog_cond_quant_best_local_action_INTRO",
``!f f' wp wp' rp rp' d d' P P'.
  ALL_DISTINCT d /\ ALL_DISTINCT d' ==>
 (var_res_prog_quant_best_local_action
     (\x. var_res_prop_input_ap_distinct f  (wp,  rp)  d  (P  x))
     (\x. var_res_prop_input_ap_distinct f' (wp', rp') d' (P' x)) =
  var_res_prog_cond_quant_best_local_action
     (\x. var_res_prop_input_distinct f  (wp , rp ) d (P  x))
     (\x. var_res_prop_input_distinct f' (wp', rp') d' (P' x)))``,

SIMP_TAC std_ss [var_res_prog_cond_quant_best_local_action_def,
   var_res_prop_input_distinct_def, COND_RAND, COND_RATOR] THEN
SIMP_TAC std_ss [var_res_prop_input_ap_distinct_def, asl_bool_REWRITES]);


val var_res_prog_cond_quant_best_local_action___STRONG_EQUIV___pre_post =
store_thm ("var_res_prog_cond_quant_best_local_action___STRONG_EQUIV___pre_post",
``!pre post pre' post'.
   ((!x. COND_PROP___STRONG_EQUIV (pre x) (pre' x)) /\
    (!x. COND_PROP___STRONG_EQUIV (post x) (post' x))) ==>

   (var_res_prog_cond_quant_best_local_action pre post =
    var_res_prog_cond_quant_best_local_action pre' post')``,


SIMP_TAC std_ss [var_res_prog_cond_quant_best_local_action_def,
                 COND_PROP___STRONG_EQUIV_REWRITE]);



val ASL_PROGRAM_IS_ABSTRACTION___var_res_quant_best_local_action =
store_thm ("ASL_PROGRAM_IS_ABSTRACTION___var_res_quant_best_local_action",
``!xenv penv qP prog qQ.
  IS_VAR_RES_COMBINATOR (FST xenv) ==>

  (ASL_PROGRAM_IS_ABSTRACTION xenv penv prog
     (var_res_prog_quant_best_local_action qP qQ) =
  !arg. VAR_RES_HOARE_TRIPLE xenv penv (qP arg) prog (qQ arg))``,

REPEAT STRIP_TAC THEN
IMP_RES_TAC IS_SEPARATION_COMBINATOR___IS_VAR_RES_COMBINATOR THEN
ASM_SIMP_TAC std_ss [var_res_prog_quant_best_local_action_def,
   ASL_PROGRAM_IS_ABSTRACTION___quant_best_local_action,
   VAR_RES_HOARE_TRIPLE_def, PAIR_FORALL_THM]);



val ASL_PROGRAM_IS_ABSTRACTION___var_res_best_local_action =
store_thm ("ASL_PROGRAM_IS_ABSTRACTION___var_res_best_local_action",
``!xenv penv P prog Q.
  IS_VAR_RES_COMBINATOR (FST xenv) ==>

  (ASL_PROGRAM_IS_ABSTRACTION xenv penv prog
     (var_res_prog_best_local_action P Q) =
  VAR_RES_HOARE_TRIPLE xenv penv P prog Q)``,

REPEAT STRIP_TAC THEN
IMP_RES_TAC IS_SEPARATION_COMBINATOR___IS_VAR_RES_COMBINATOR THEN
ASM_SIMP_TAC std_ss [var_res_prog_best_local_action_def,
   ASL_PROGRAM_IS_ABSTRACTION___quant_best_local_action,
   VAR_RES_HOARE_TRIPLE_def]);


val VAR_RES_HOARE_TRIPLE___comment___ELIM_preserve_names =
store_thm ("VAR_RES_HOARE_TRIPLE___comment___ELIM_preserve_names",
``!xenv penv  ref_args val_args P Q prog arg_refL arg_valL.
 (VAR_RES_HOARE_TRIPLE xenv penv
    ((asl_procedure_call_preserve_names_wrapper ref_args val_args P)
     (arg_refL, arg_valL))
     prog
     Q) =

  (LIST_UNROLL_GIVEN_ELEMENT_NAMES arg_refL ref_args ==>
   LIST_UNROLL_GIVEN_ELEMENT_NAMES arg_valL val_args ==>
   (VAR_RES_HOARE_TRIPLE xenv penv
    (P (arg_refL, arg_valL))  prog Q))``,


SIMP_TAC std_ss [
  asl_procedure_call_preserve_names_wrapper_def] THEN
REPEAT STRIP_TAC THEN
Cases_on `LIST_UNROLL_GIVEN_ELEMENT_NAMES arg_valL val_args /\
          LIST_UNROLL_GIVEN_ELEMENT_NAMES arg_refL ref_args` THEN
FULL_SIMP_TAC std_ss [asl_bool_REWRITES] THEN (
   SIMP_TAC std_ss [VAR_RES_HOARE_TRIPLE_def, NOT_IN_asl_false,
      ASL_PROGRAM_HOARE_TRIPLE_REWRITE, IN_ABS]
));





(******************************************************************************)
(* variable updates                                                           *)
(******************************************************************************)


(* -------------------------------------------------------------------------- *)
(* Basic defs                                                                 *)
(* -------------------------------------------------------------------------- *)

val var_res_state_var_update_def = Define `
   var_res_state_var_update v c s =
   s |+ (v, c, var_res_write_permission)`;

val var_res_state_varlist_update_def = Define `
   (var_res_state_varlist_update [] s = s) /\
   (var_res_state_varlist_update (vc::vL) s =
      var_res_state_var_update (FST vc) (SND vc) (var_res_state_varlist_update vL s))`

val var_res_ext_state_var_update_def = Define `
   var_res_ext_state_var_update vc s =
   (var_res_state_var_update (FST vc) (SND vc) (FST s), SND s)`;

val var_res_ext_state_varlist_update_def = Define `
   var_res_ext_state_varlist_update vL s =
   (var_res_state_varlist_update vL (FST s), SND s)`;

val var_res_prop_var_update_def = Define `
    var_res_prop_var_update vc P =
    \s. (var_res_ext_state_var_update vc s IN P)`;

val var_res_prop_varlist_update_def = Define `
    var_res_prop_varlist_update vL P =
    \s. (var_res_ext_state_varlist_update vL s IN P)`;

val var_res_exp_var_update_def = Define `
    var_res_exp_var_update vc e =
    \s. (e (var_res_state_var_update (FST vc) (SND vc) s))`;

val var_res_exp_varlist_update_def = Define `
    var_res_exp_varlist_update vL e =
    \s. (e (var_res_state_varlist_update vL s))`;



val var_res_state_varlist_update_REWRITE = store_thm (
"var_res_state_varlist_update_REWRITE",
``var_res_state_varlist_update vL s =
  (s |++ (MAP (\vc. (FST vc, SND vc, var_res_write_permission)) (REVERSE vL)))``,

Induct_on `vL` THENL [
   SIMP_TAC list_ss [FUPDATE_LIST_THM, var_res_state_varlist_update_def],

   ASM_SIMP_TAC list_ss [FUPDATE_LIST_THM, var_res_state_varlist_update_def,
      var_res_state_var_update_def,
      FUPDATE_LIST_APPEND]
]);


val var_res_state_varlist_update_THM = store_thm (
 "var_res_state_varlist_update_THM",
``(var_res_state_varlist_update [] = I) /\
  (var_res_state_varlist_update (v::vL) = \s.
  (var_res_state_var_update (FST v) (SND v)
     (var_res_state_varlist_update vL s)))``,
SIMP_TAC std_ss [var_res_state_varlist_update_def, FUN_EQ_THM])


val var_res_exp_varlist_update_THM = store_thm (
 "var_res_exp_varlist_update_THM",
``(var_res_exp_varlist_update [] = I) /\
  (var_res_exp_varlist_update (v::vL) = \s.
  (var_res_exp_varlist_update vL (var_res_exp_var_update v s)))``,
SIMP_TAC std_ss [var_res_exp_varlist_update_def, FUN_EQ_THM,
    var_res_state_varlist_update_THM, var_res_exp_var_update_def]);

val var_res_exp_varlist_update_NIL = store_thm (
 "var_res_exp_varlist_update_NIL",
``!e. (var_res_exp_varlist_update [] e = e)``,
SIMP_TAC std_ss [var_res_exp_varlist_update_THM]);

val var_res_exp_varlist_update_SING = store_thm (
"var_res_exp_varlist_update_SING",
``var_res_exp_varlist_update [vc] =
  var_res_exp_var_update vc``,
SIMP_TAC std_ss [var_res_exp_varlist_update_THM, FUN_EQ_THM]);

val var_res_prop_varlist_update_THM = store_thm (
"var_res_prop_varlist_update_THM",
``(var_res_prop_varlist_update [] = I) /\
  (var_res_prop_varlist_update (v::vL) = \p.
  (var_res_prop_varlist_update vL (var_res_prop_var_update v p)))``,
SIMP_TAC std_ss [var_res_prop_varlist_update_def, FUN_EQ_THM,
    var_res_ext_state_varlist_update_def, IN_DEF,
    var_res_state_varlist_update_THM,
    var_res_prop_var_update_def,
    var_res_ext_state_var_update_def]);

val var_res_prop_varlist_update_SING = store_thm (
"var_res_prop_varlist_update_SING",
``var_res_prop_varlist_update [vc] =
  var_res_prop_var_update vc``,
SIMP_TAC std_ss [var_res_prop_varlist_update_THM, FUN_EQ_THM]);



(* -------------------------------------------------------------------------- *)
(* Basic evals on expressions                                                 *)
(* -------------------------------------------------------------------------- *)

val var_res_exp_varlist_update___const_EVAL = store_thm ("var_res_exp_varlist_update___const_EVAL",
``!vL c. var_res_exp_varlist_update vL (var_res_exp_const c) = var_res_exp_const c``,
SIMP_TAC std_ss [var_res_exp_varlist_update_def, var_res_exp_const_def,
   combinTheory.K_DEF]);


val var_res_exp_varlist_update___var_EVAL = store_thm ("var_res_exp_varlist_update___var_EVAL",
``!v1 v2 c vL.
     var_res_exp_varlist_update ((v1,c)::vL) (var_res_exp_var v2) =
     if (v1 = v2) then (var_res_exp_const c) else
        (var_res_exp_varlist_update vL (var_res_exp_var v2))``,

SIMP_TAC list_ss [var_res_exp_varlist_update_def,
   var_res_exp_var_def, var_res_state_varlist_update_REWRITE,
   FDOM_FUPDATE_LIST, IN_UNION, IN_LIST_TO_SET, IN_SING,
   MEM_MAP, GSYM RIGHT_EXISTS_AND_THM, MAP_APPEND,
   FUPDATE_LIST_APPEND, FUPDATE_LIST_THM,
   FDOM_FUPDATE, IN_INSERT, var_res_exp_const_def,
   FDOM_FUPDATE_LIST, IN_UNION, IN_LIST_TO_SET,
   FAPPLY_FUPDATE_THM, combinTheory.K_DEF] THEN
REPEAT STRIP_TAC THEN
Cases_on `v1 = v2` THEN (
   ASM_SIMP_TAC std_ss []
));


val var_res_exp_varlist_update___var_res_exp_op_EVAL = store_thm (
"var_res_exp_varlist_update___var_res_exp_op_EVAL",
``!vL f eL.
(var_res_exp_varlist_update vL (var_res_exp_op f eL) =
 var_res_exp_op f (MAP (var_res_exp_varlist_update vL) eL))``,

SIMP_TAC std_ss [var_res_exp_varlist_update_def,
   var_res_exp_op_def, LET_THM, MAP_MAP_o, combinTheory.o_DEF]);


val var_res_exp_varlist_update___var_res_exp_binop_EVAL = store_thm (
"var_res_exp_varlist_update___var_res_exp_binop_EVAL",
``!vL f e1 e2.
var_res_exp_varlist_update vL (var_res_exp_binop f e1 e2) =
var_res_exp_binop f (var_res_exp_varlist_update vL e1) (var_res_exp_varlist_update vL e2)``,

SIMP_TAC list_ss [var_res_exp_binop_def,
   var_res_exp_varlist_update___var_res_exp_op_EVAL]);


val var_res_exp_varlist_update___var_res_exp_binop_const_EVAL = store_thm (
"var_res_exp_varlist_update___var_res_exp_binop_const_EVAL",
``!f vL e n.
var_res_exp_varlist_update vL (var_res_exp_binop_const f e n) =
var_res_exp_binop_const f (var_res_exp_varlist_update vL e) n``,

SIMP_TAC list_ss [var_res_exp_binop_const___ALTERNATIVE_DEF,
   var_res_exp_varlist_update___var_res_exp_op_EVAL]);

val var_res_exp_varlist_update___var_res_exp_add_sub_EVAL =
 save_thm ("var_res_exp_varlist_update___var_res_exp_add_sub_EVAL",
 var_res_exp_add_sub___INST_THM var_res_exp_varlist_update___var_res_exp_binop_const_EVAL);


(* -------------------------------------------------------------------------- *)
(* Stack imprecise                                                            *)
(* -------------------------------------------------------------------------- *)

val VAR_RES_IS_STACK_IMPRECISE___USED_VARS___var_res_prop_var_update___INSERT =
store_thm ("VAR_RES_IS_STACK_IMPRECISE___USED_VARS___var_res_prop_var_update___INSERT",
``!vc vs P.
(VAR_RES_IS_STACK_IMPRECISE___USED_VARS (FST vc INSERT vs) P ==>
 VAR_RES_IS_STACK_IMPRECISE___USED_VARS vs (var_res_prop_var_update vc P))``,

SIMP_TAC std_ss [VAR_RES_IS_STACK_IMPRECISE___USED_VARS___ALTERNATIVE_DEF,
   var_res_prop_var_update_def, IN_ABS,
   var_res_ext_state_var_update_def, var_res_state_var_update_def] THEN
REPEAT STRIP_TAC THEN
Q.PAT_ASSUM `!s s2. X s s2` MATCH_MP_TAC THEN
Q.EXISTS_TAC `(FST s2 |+ (FST vc,SND vc,var_res_write_permission),SND s2)` THEN
FULL_SIMP_TAC std_ss [FDOM_FUPDATE, SUBSET_DEF, IN_INTER, IN_DELETE,
            IN_INSERT, FAPPLY_FUPDATE_THM] THEN
METIS_TAC[]);


val VAR_RES_IS_STACK_IMPRECISE___USED_VARS___var_res_prop_varlist_update___INSERT =
store_thm ("VAR_RES_IS_STACK_IMPRECISE___USED_VARS___var_res_prop_varlist_update___INSERT",
``!vcL vs P.
(VAR_RES_IS_STACK_IMPRECISE___USED_VARS (LIST_TO_SET (MAP FST vcL) UNION vs) P ==>
 VAR_RES_IS_STACK_IMPRECISE___USED_VARS vs (var_res_prop_varlist_update vcL P))``,

Induct_on `vcL` THEN (
   SIMP_TAC list_ss [var_res_prop_varlist_update_THM, UNION_EMPTY]
) THEN
REPEAT STRIP_TAC THEN
Q.PAT_ASSUM `!vs P. X` MATCH_MP_TAC THEN
MATCH_MP_TAC VAR_RES_IS_STACK_IMPRECISE___USED_VARS___var_res_prop_var_update___INSERT THEN
ASM_REWRITE_TAC[GSYM INSERT_UNION_EQ]);



val VAR_RES_IS_STACK_IMPRECISE___USED_VARS___var_res_prop_var_update =
store_thm ("VAR_RES_IS_STACK_IMPRECISE___USED_VARS___var_res_prop_var_update",
``!vc vs P.
(VAR_RES_IS_STACK_IMPRECISE___USED_VARS vs P ==>
 VAR_RES_IS_STACK_IMPRECISE___USED_VARS vs (var_res_prop_var_update vc P))``,

REPEAT STRIP_TAC THEN
MATCH_MP_TAC VAR_RES_IS_STACK_IMPRECISE___USED_VARS___var_res_prop_var_update___INSERT THEN
MATCH_MP_TAC VAR_RES_IS_STACK_IMPRECISE___USED_VARS___SUBSET THEN
Q.EXISTS_TAC `vs` THEN
ASM_SIMP_TAC std_ss [SUBSET_DEF, IN_INSERT]);


val VAR_RES_IS_STACK_IMPRECISE___USED_VARS___var_res_prop_varlist_update =
store_thm ("VAR_RES_IS_STACK_IMPRECISE___USED_VARS___var_res_prop_varlist_update",
``!vcL vs P.
(VAR_RES_IS_STACK_IMPRECISE___USED_VARS vs P ==>
 VAR_RES_IS_STACK_IMPRECISE___USED_VARS vs (var_res_prop_varlist_update vcL P))``,

REPEAT STRIP_TAC THEN
MATCH_MP_TAC VAR_RES_IS_STACK_IMPRECISE___USED_VARS___var_res_prop_varlist_update___INSERT THEN
MATCH_MP_TAC VAR_RES_IS_STACK_IMPRECISE___USED_VARS___SUBSET THEN
Q.EXISTS_TAC `vs` THEN
ASM_SIMP_TAC std_ss [SUBSET_DEF, IN_UNION]);



val VAR_RES_IS_STACK_IMPRECISE___var_res_prop_var_update =
store_thm ("VAR_RES_IS_STACK_IMPRECISE___var_res_prop_var_update",
``!vc P. (VAR_RES_IS_STACK_IMPRECISE P ==>
          VAR_RES_IS_STACK_IMPRECISE (var_res_prop_var_update vc P))``,
SIMP_TAC std_ss [VAR_RES_IS_STACK_IMPRECISE___ALTERNATIVE_DEF,
                 VAR_RES_IS_STACK_IMPRECISE___USED_VARS___var_res_prop_var_update]);

val VAR_RES_IS_STACK_IMPRECISE___var_res_prop_varlist_update =
store_thm ("VAR_RES_IS_STACK_IMPRECISE___var_res_prop_varlist_update",
``!vc P. (VAR_RES_IS_STACK_IMPRECISE P ==>
          VAR_RES_IS_STACK_IMPRECISE (var_res_prop_varlist_update vc P))``,
SIMP_TAC std_ss [VAR_RES_IS_STACK_IMPRECISE___ALTERNATIVE_DEF,
                 VAR_RES_IS_STACK_IMPRECISE___USED_VARS___var_res_prop_varlist_update]);




val VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS___var_res_exp_var_update =
store_thm ("VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS___var_res_exp_var_update",
``!vc vs e. (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS e = SOME vs) ==>
            (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS
                (var_res_exp_var_update vc e) = SOME (vs DELETE (FST vc)))``,

SIMP_TAC std_ss [VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_THM,
                 VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_REL___REWRITE,
                 FINITE_DELETE, var_res_exp_var_update_def,
                 var_res_state_var_update_def, FDOM_FUPDATE,
                 DELETE_SUBSET_INSERT, IN_DELETE] THEN
REPEAT STRIP_TAC THEN
Q.PAT_ASSUM `!st1 st2. X st1 st2` MATCH_MP_TAC THEN
ASM_SIMP_TAC std_ss [FDOM_FUPDATE, FAPPLY_FUPDATE_THM, COND_RAND,
                     COND_RATOR]);



val VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS___var_res_exp_varlist_update =
store_thm ("VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS___var_res_exp_varlist_update",
``!vcL vs e. (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS e = SOME vs) ==>
             (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS
                (var_res_exp_varlist_update vcL e) =
                SOME (vs DIFF (LIST_TO_SET (MAP FST vcL))))``,

Induct_on `vcL` THEN1 (
   SIMP_TAC list_ss [var_res_exp_varlist_update_THM, DIFF_EMPTY]
) THEN
SIMP_TAC list_ss [var_res_exp_varlist_update_THM, DIFF_INSERT] THEN
REPEAT STRIP_TAC THEN
Q.PAT_ASSUM `!vs e. X` MATCH_MP_TAC THEN
MATCH_MP_TAC VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS___var_res_exp_var_update THEN
ASM_REWRITE_TAC[]);



val VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET___var_res_exp_var_update =
store_thm ("VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET___var_res_exp_var_update",
``!vc vs e. (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET vs e ==>
             VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET vs (var_res_exp_var_update vc e))``,

SIMP_TAC std_ss [
   VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET___REWRITE,
   GSYM VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_THM] THEN
REPEAT STRIP_TAC THEN
Q.EXISTS_TAC `vs' DELETE FST vc` THEN
ASM_SIMP_TAC std_ss [
   VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS___var_res_exp_var_update] THEN
FULL_SIMP_TAC std_ss [SUBSET_DEF, IN_DELETE]);



val VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET___var_res_exp_varlist_update =
store_thm ("VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET___var_res_exp_varlist_update",
``!vcL vs e. (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET vs e ==>
              VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET vs (var_res_exp_varlist_update vcL e))``,

SIMP_TAC std_ss [
   VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET___REWRITE,
   GSYM VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_THM] THEN
REPEAT STRIP_TAC THEN
Q.EXISTS_TAC `vs' DIFF LIST_TO_SET (MAP FST vcL)` THEN
ASM_SIMP_TAC std_ss [
   VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS___var_res_exp_varlist_update] THEN
FULL_SIMP_TAC std_ss [SUBSET_DEF, IN_DIFF]);





(* -------------------------------------------------------------------------- *)
(* Some applications on real predicates                                       *)
(* -------------------------------------------------------------------------- *)

val var_res_prop_var_update___asl_star =
store_thm ("var_res_prop_var_update___asl_star",
``
!f vc p1 p2.
(VAR_RES_IS_STACK_IMPRECISE p1 /\ VAR_RES_IS_STACK_IMPRECISE p2) ==>

(var_res_prop_var_update vc (asl_star (VAR_RES_COMBINATOR f) p1 p2) =
 asl_star (VAR_RES_COMBINATOR f) (var_res_prop_var_update vc p1) (var_res_prop_var_update vc p2))``,

SIMP_TAC std_ss [var_res_prop_var_update_def, asl_star_def, EXTENSION, IN_ABS] THEN
REPEAT STRIP_TAC THEN
`?v c. vc = (v, c)` by (Cases_on `vc` THEN SIMP_TAC std_ss []) THEN
ASM_REWRITE_TAC[] THEN
EQ_TAC THEN STRIP_TAC THENL [
   Q.EXISTS_TAC `(DRESTRICT (FST p) (COMPL {v}), SND p)` THEN
   Q.EXISTS_TAC `(FUNION (DRESTRICT (FST q) (COMPL {v}))
                         (DRESTRICT (FST x) {v}), SND q)` THEN
   Q.PAT_ASSUM `VAR_RES_IS_STACK_IMPRECISE p1`
          (fn thm => ONCE_CONSEQ_REWRITE_TAC (
      [],[REWRITE_RULE [VAR_RES_IS_STACK_IMPRECISE___ALTERNATIVE_DEF_2] thm], []))
     THEN
   Q.PAT_ASSUM `VAR_RES_IS_STACK_IMPRECISE p2`
          (fn thm => ONCE_CONSEQ_REWRITE_TAC ([REWRITE_RULE [VAR_RES_IS_STACK_IMPRECISE___ALTERNATIVE_DEF_2] thm], [], [])) THEN
   SIMP_TAC std_ss [GSYM LEFT_EXISTS_AND_THM, GSYM RIGHT_EXISTS_AND_THM] THEN
   Q.EXISTS_TAC `p` THEN Q.EXISTS_TAC `q` THEN
   FULL_SIMP_TAC std_ss [VAR_RES_COMBINATOR_REWRITE,
      SOME___VAR_RES_STACK_COMBINE,
      var_res_ext_state_var_update_def,
      var_res_state_var_update_def,
      FDOM_FUPDATE, DRESTRICT_DEF,
      VAR_RES_STACK_IS_SEPARATE_def, IN_INTER, IN_COMPL,
      IN_SING, FAPPLY_FUPDATE_THM, FUNION_DEF, IN_UNION,
      SUBSET_DEF, IN_INSERT] THEN
   ASM_SIMP_TAC std_ss [COND_RAND, COND_RATOR] THEN
   Q.PAT_ASSUM `FST x |+ Y = Z` MP_TAC THEN
   ONCE_REWRITE_TAC [GSYM fmap_EQ_THM] THEN
   ASM_SIMP_TAC (std_ss++CONJ_ss) [FMERGE_DEF, FDOM_FUPDATE] THEN
   ASM_SIMP_TAC std_ss [IN_UNION, FAPPLY_FUPDATE_THM, IN_SING, EXTENSION,
                        DRESTRICT_DEF, FUNION_DEF, IN_INTER, IN_COMPL,
                        IN_INSERT, GSYM FORALL_AND_THM] THEN
   STRIP_TAC THEN REPEAT CONJ_TAC THENL [
      GEN_TAC THEN
      Q.PAT_ASSUM `!x'. X x'` (MP_TAC o Q.SPEC `x'`) THEN
      Cases_on `x' = v` THEN ASM_SIMP_TAC std_ss [] THEN
      METIS_TAC[],

      STRIP_TAC THEN
      REPEAT (Q.PAT_ASSUM `!x'. X x'` (MP_TAC o Q.SPEC `v`)) THEN
      ASM_SIMP_TAC std_ss [VAR_RES_STACK_COMBINE___MERGE_FUNC_def] THEN
      METIS_TAC[pairTheory.FST],

      STRIP_TAC THEN
      Q.PAT_ASSUM `!x'. X x'` (MP_TAC o Q.SPEC `v`) THEN
      ASM_SIMP_TAC std_ss [VAR_RES_STACK_COMBINE___MERGE_FUNC_def] THEN
      METIS_TAC[pairTheory.FST]
   ],



   Q.EXISTS_TAC `(FST p |+ (v, c, var_res_permission_split var_res_write_permission), SND p)` THEN
   Q.EXISTS_TAC `(FST q |+ (v, c, var_res_permission_split var_res_write_permission), SND q)` THEN
   Q.PAT_ASSUM `VAR_RES_IS_STACK_IMPRECISE p1`
          (fn thm => ONCE_CONSEQ_REWRITE_TAC ([REWRITE_RULE [VAR_RES_IS_STACK_IMPRECISE___ALTERNATIVE_DEF_2] thm], [], [])) THEN
   Q.PAT_ASSUM `VAR_RES_IS_STACK_IMPRECISE p2`
          (fn thm => ONCE_CONSEQ_REWRITE_TAC ([REWRITE_RULE [VAR_RES_IS_STACK_IMPRECISE___ALTERNATIVE_DEF_2] thm], [], [])) THEN
   SIMP_TAC std_ss [GSYM LEFT_EXISTS_AND_THM, GSYM RIGHT_EXISTS_AND_THM] THEN
   Q.EXISTS_TAC `var_res_ext_state_var_update (v, c) p` THEN Q.EXISTS_TAC `var_res_ext_state_var_update (v, c) q` THEN
   FULL_SIMP_TAC std_ss [VAR_RES_COMBINATOR_REWRITE, FDOM_FUPDATE, SUBSET_DEF, IN_INSERT,
      SOME___VAR_RES_STACK_COMBINE, var_res_ext_state_var_update_def,
      var_res_state_var_update_def, VAR_RES_STACK_IS_SEPARATE_def,
      FAPPLY_FUPDATE_THM, GSYM LEFT_OR_OVER_AND] THEN
   ASM_SIMP_TAC std_ss [COND_RATOR, COND_RAND, var_res_permission_THM2] THEN
   CONJ_TAC THEN1 METIS_TAC[] THEN
   SIMP_TAC (std_ss++EQUIV_EXTRACT_ss) [GSYM fmap_EQ_THM, FMERGE_DEF, EXTENSION, FDOM_FUPDATE,
                    IN_INSERT, IN_UNION, VAR_RES_STACK_COMBINE___MERGE_FUNC_def,
                    FAPPLY_FUPDATE_THM] THEN
   GEN_TAC THEN Cases_on `x' = v` THEN
   ASM_SIMP_TAC std_ss [var_res_permission_THM2]
]);


val var_res_prop_varlist_update___bool_cond =
store_thm ("var_res_prop_varlist_update___bool_cond",
``!c vL p1 p2.
(var_res_prop_varlist_update vL (if c then p1 else p2) =
 if c then (var_res_prop_varlist_update vL p1) else
    (var_res_prop_varlist_update vL p2))``,
Cases_on `c` THEN SIMP_TAC std_ss [])



val var_res_prop_varlist_update___asl_star =
store_thm ("var_res_prop_varlist_update___asl_star",
``!f vL p1 p2.
(VAR_RES_IS_STACK_IMPRECISE p1 /\ VAR_RES_IS_STACK_IMPRECISE p2) ==>

(var_res_prop_varlist_update vL (asl_star (VAR_RES_COMBINATOR f) p1 p2) =
 asl_star (VAR_RES_COMBINATOR f) (var_res_prop_varlist_update vL p1)
    (var_res_prop_varlist_update vL p2))``,

Induct_on `vL` THEN1 (
   SIMP_TAC std_ss [var_res_prop_varlist_update_THM]
) THEN
ASM_SIMP_TAC std_ss [
   var_res_prop_varlist_update_THM,
   var_res_prop_var_update___asl_star,
   VAR_RES_IS_STACK_IMPRECISE___var_res_prop_var_update]);




val var_res_prop_var_update___var_res_prop_expression =
store_thm ("var_res_prop_var_update___var_res_prop_expression",
``!f vc emp p el.
var_res_prop_var_update vc (var_res_prop_expression f emp p el) =
var_res_prop_expression f emp p (MAP (var_res_exp_var_update vc) el)``,

ONCE_REWRITE_TAC [EXTENSION] THEN
SIMP_TAC std_ss [var_res_prop_var_update_def,
  var_res_prop_expression_def,
  var_res_stack_proposition_def, LET_THM,
  IN_ABS, var_res_ext_state_var_update_def,
  var_res_exp_var_update_def,
  MAP_MAP_o, combinTheory.o_DEF]);


val var_res_prop_var_update___var_res_prop_binexpression =
store_thm ("var_res_prop_var_update___var_res_prop_binexpression",
``!f vc emp p e1 e2.
var_res_prop_var_update vc (var_res_prop_binexpression f emp p e1 e2) =
var_res_prop_binexpression f emp p (var_res_exp_var_update vc e1) (var_res_exp_var_update vc e2)``,

SIMP_TAC std_ss [var_res_prop_binexpression___ALTERNATIVE_DEF,
  var_res_prop_var_update___var_res_prop_expression, MAP]);


val var_res_prop_varlist_update___var_res_prop_expression =
store_thm ("var_res_prop_varlist_update___var_res_prop_expression",
``!f vcL emp p el.
var_res_prop_varlist_update vcL (var_res_prop_expression f emp p el) =
var_res_prop_expression f emp p (MAP (var_res_exp_varlist_update vcL) el)``,

Induct_on `vcL` THEN (
   ASM_SIMP_TAC std_ss [var_res_prop_varlist_update_THM,
         var_res_exp_varlist_update_THM, MAP_ID, MAP_MAP_o,
         combinTheory.o_DEF,
         var_res_prop_var_update___var_res_prop_expression]
));


val var_res_prop_varlist_update___var_res_prop_binexpression =
store_thm ("var_res_prop_varlist_update___var_res_prop_binexpression",
``!f vcL emp p e1 e2.
var_res_prop_varlist_update vcL (var_res_prop_binexpression f emp p e1 e2) =
var_res_prop_binexpression f emp p (var_res_exp_varlist_update vcL e1)
   (var_res_exp_varlist_update vcL e2)``,

SIMP_TAC std_ss [var_res_prop_binexpression___ALTERNATIVE_DEF,
  var_res_prop_varlist_update___var_res_prop_expression, MAP]);





val var_res_prop_var_update___equal_unequal = store_thm (
"var_res_prop_var_update___equal_unequal",
``(var_res_prop_var_update vc (var_res_prop_equal f e1 e2) =
var_res_prop_equal f (var_res_exp_var_update vc e1) (var_res_exp_var_update vc e2)) /\

(var_res_prop_var_update vc (var_res_prop_unequal f e1 e2) =
 var_res_prop_unequal f (var_res_exp_var_update vc e1)
                        (var_res_exp_var_update vc e2)) /\

(var_res_prop_var_update vc (var_res_prop_weak_equal e1 e2) =
 var_res_prop_weak_equal (var_res_exp_var_update vc e1)
                         (var_res_exp_var_update vc e2)) /\

(var_res_prop_var_update vc (var_res_prop_weak_unequal e1 e2) =
 var_res_prop_weak_unequal (var_res_exp_var_update vc e1)
                           (var_res_exp_var_update vc e2))``,

SIMP_TAC std_ss [
   var_res_prop_equal_def,
   var_res_prop_unequal_def,
   var_res_prop_weak_unequal_def,
   var_res_prop_weak_equal_def,
   var_res_prop_weak_binexpression_def,
   var_res_prop_var_update___var_res_prop_binexpression]);



val var_res_prop_varlist_update___equal_unequal = store_thm (
"var_res_prop_varlist_update___equal_unequal",
``(var_res_prop_varlist_update vcL (var_res_prop_equal f e1 e2) =
var_res_prop_equal f (var_res_exp_varlist_update vcL e1) (var_res_exp_varlist_update vcL e2)) /\

(var_res_prop_varlist_update vcL (var_res_prop_unequal f e1 e2) =
 var_res_prop_unequal f (var_res_exp_varlist_update vcL e1)
                        (var_res_exp_varlist_update vcL e2)) /\

(var_res_prop_varlist_update vcL (var_res_prop_weak_equal e1 e2) =
 var_res_prop_weak_equal (var_res_exp_varlist_update vcL e1)
                         (var_res_exp_varlist_update vcL e2)) /\

(var_res_prop_varlist_update vcL (var_res_prop_weak_unequal e1 e2) =
 var_res_prop_weak_unequal (var_res_exp_varlist_update vcL e1)
                           (var_res_exp_varlist_update vcL e2))``,

SIMP_TAC std_ss [
   var_res_prop_equal_def,
   var_res_prop_unequal_def,
   var_res_prop_weak_unequal_def,
   var_res_prop_weak_equal_def,
   var_res_prop_weak_binexpression_def,
   var_res_prop_varlist_update___var_res_prop_binexpression]);



val var_res_prop_var_update___var_res_exp_is_defined =
store_thm ("var_res_prop_var_update___var_res_exp_is_defined",
``!f vc e.
var_res_prop_var_update vc (var_res_exp_is_defined f e) =
var_res_exp_is_defined f (var_res_exp_var_update vc e)``,

SIMP_TAC std_ss [var_res_prop_var_update_def, var_res_exp_is_defined_def,
       var_res_exp_var_update_def, var_res_stack_proposition_def, IN_ABS,
       var_res_ext_state_var_update_def]);


val var_res_prop_varlist_update___var_res_exp_is_defined =
store_thm ("var_res_prop_varlist_update___var_res_exp_is_defined",
``!f vcL e.
var_res_prop_varlist_update vcL (var_res_exp_is_defined f e) =
var_res_exp_is_defined f (var_res_exp_varlist_update vcL e)``,

SIMP_TAC std_ss [var_res_prop_varlist_update_def, var_res_exp_is_defined_def,
       var_res_exp_varlist_update_def, var_res_stack_proposition_def, IN_ABS,
       var_res_ext_state_varlist_update_def]);


val var_res_prop_var_update___var_res_exp_prop =
store_thm ("var_res_prop_var_update___var_res_exp_prop",
``!vc e P.
var_res_prop_var_update vc (var_res_exp_prop e P) =
var_res_exp_prop (var_res_exp_var_update vc e) (\c. var_res_prop_var_update vc (P c))``,

SIMP_TAC std_ss [var_res_prop_var_update_def, var_res_exp_prop_def, IN_ABS,
   LET_THM, FUN_EQ_THM, var_res_exp_var_update_def,
   var_res_ext_state_var_update_def, IN_DEF]);


val var_res_prop_varlist_update___var_res_exp_prop =
store_thm ("var_res_prop_varlist_update___var_res_exp_prop",
``!vcL e P.
var_res_prop_varlist_update vcL (var_res_exp_prop e P) =
var_res_exp_prop (var_res_exp_varlist_update vcL e) (\c. var_res_prop_varlist_update vcL (P c))``,
SIMP_TAC std_ss [var_res_prop_varlist_update_def, var_res_exp_prop_def, IN_DEF,
   var_res_exp_varlist_update_def, var_res_ext_state_varlist_update_def]);



val var_res_prop_var_update___BOOL = store_thm ("var_res_prop_var_update___BOOL",
``(var_res_prop_var_update vc (asl_and p1 p2) =
  asl_and (var_res_prop_var_update vc p1) (var_res_prop_var_update vc p2)) /\

  (var_res_prop_var_update vc (asl_or p1 p2) =
  asl_or (var_res_prop_var_update vc p1) (var_res_prop_var_update vc p2)) /\

  (var_res_prop_var_update vc (K cp) = (K cp)) /\

  (var_res_prop_var_update vc asl_false = asl_false) /\
  (var_res_prop_var_update vc (var_res_prop_stack_true f) = var_res_prop_stack_true f) /\
  (var_res_prop_var_update vc (var_res_bool_proposition f cp) = (var_res_bool_proposition f cp)) /\

  (var_res_prop_var_update vc (asl_exists x. p x) =
   asl_exists x. (var_res_prop_var_update vc (p x)))``,

ONCE_REWRITE_TAC [EXTENSION] THEN
SIMP_TAC std_ss [asl_bool_EVAL,
   var_res_prop_var_update_def,
   IN_ABS, asl_exists_def,
   asl_false_def, var_res_stack_proposition_def,
   var_res_prop_stack_true_def,
   var_res_bool_proposition_def,
   var_res_ext_state_var_update_def]);




val var_res_prop_varlist_update___BOOL = store_thm ("var_res_prop_varlist_update___BOOL",
``(var_res_prop_varlist_update vcL (asl_and p1 p2) =
  asl_and (var_res_prop_varlist_update vcL p1) (var_res_prop_varlist_update vcL p2)) /\

  (var_res_prop_varlist_update vcL (asl_or p1 p2) =
  asl_or (var_res_prop_varlist_update vcL p1) (var_res_prop_varlist_update vcL p2)) /\

  (var_res_prop_varlist_update vcL (asl_cond p1 p2 p3) =
  asl_cond (var_res_prop_varlist_update vcL p1) (var_res_prop_varlist_update vcL p2) (var_res_prop_varlist_update vcL p3)) /\

  (var_res_prop_varlist_update vcL (K cp) = (K cp)) /\

  (var_res_prop_varlist_update vcL asl_false = asl_false) /\
  (var_res_prop_varlist_update vcL (var_res_prop_stack_true f) = var_res_prop_stack_true f) /\
  (var_res_prop_varlist_update vcL (var_res_bool_proposition f cp) = (var_res_bool_proposition f cp)) /\

  (var_res_prop_varlist_update vcL (asl_exists x. p x) =
   asl_exists x. (var_res_prop_varlist_update vcL (p x)))``,

ONCE_REWRITE_TAC [EXTENSION] THEN
SIMP_TAC std_ss [asl_bool_EVAL,
   IN_ABS, asl_exists_def,
   asl_false_def, var_res_stack_proposition_def,
   var_res_prop_stack_true_def,
   var_res_bool_proposition_def,
   var_res_prop_varlist_update_def,
   var_res_ext_state_varlist_update_def,
   asl_cond_def]);


val var_res_prop_varlist_update___asl_trivial_cond =
store_thm ("var_res_prop_varlist_update___asl_trivial_cond",
``!vL c p.
(var_res_prop_varlist_update vL (asl_trivial_cond c p) =
 asl_trivial_cond c (var_res_prop_varlist_update vL p))``,
Cases_on `c` THEN
SIMP_TAC std_ss [asl_trivial_cond_TF,
   var_res_prop_varlist_update___BOOL]);


val var_res_prop_var_update___var_res_prop_binexpression_cond =
store_thm ("var_res_prop_var_update___var_res_prop_binexpression_cond",
``!p f vc e1 e2 P1 P2.
  var_res_prop_var_update vc (var_res_prop_binexpression_cond f p e1 e2 P1 P2) =
  var_res_prop_binexpression_cond f p (var_res_exp_var_update vc e1)
                                      (var_res_exp_var_update vc e2)
                                      (var_res_prop_var_update vc P1)
                                      (var_res_prop_var_update vc P2)``,
SIMP_TAC std_ss [var_res_prop_binexpression_cond_def,
  var_res_prop_var_update_def, IN_ABS,
  var_res_exp_var_update_def,
  var_res_ext_state_var_update_def]);


val var_res_prop_varlist_update___var_res_prop_binexpression_cond =
store_thm ("var_res_prop_varlist_update___var_res_prop_binexpression_cond",
``!p f vcL e1 e2 P1 P2.
  var_res_prop_varlist_update vcL (var_res_prop_binexpression_cond f p e1 e2 P1 P2) =
  var_res_prop_binexpression_cond f p (var_res_exp_varlist_update vcL e1)
                                      (var_res_exp_varlist_update vcL e2)
                                      (var_res_prop_varlist_update vcL P1)
                                      (var_res_prop_varlist_update vcL P2)``,
SIMP_TAC std_ss [var_res_prop_binexpression_cond_def,
  var_res_prop_varlist_update_def, IN_ABS,
  var_res_exp_varlist_update_def,
  var_res_ext_state_varlist_update_def]);


(* -------------------------------------------------------------------------- *)
(* Using varlist_update to rewrite var_res_prop                               *)
(* -------------------------------------------------------------------------- *)

val var_res_prop_varlist_update_IDEMPOT = store_thm(
"var_res_prop_varlist_update_IDEMPOT",
``!p vcL. var_res_prop_varlist_update vcL (var_res_prop_varlist_update vcL p) =
          var_res_prop_varlist_update vcL p``,

SIMP_TAC std_ss [var_res_prop_varlist_update_def,
   var_res_ext_state_varlist_update_def, IN_ABS,
   var_res_state_varlist_update_REWRITE,
   FUPDATE_LIST_IDEMPOT]);


val var_res_prop_varlist_update_IDEMPOT_o = store_thm(
"var_res_prop_varlist_update_IDEMPOT_o",
``!vcL. (var_res_prop_varlist_update vcL) o (var_res_prop_varlist_update vcL) =
         var_res_prop_varlist_update vcL``,
SIMP_TAC std_ss [combinTheory.o_DEF,
   var_res_prop_varlist_update_IDEMPOT, FUN_EQ_THM]);


val var_res_prop_varlist_update___asl_bigstar_list =
store_thm ("var_res_prop_varlist_update___asl_bigstar_list",
``!f vcL pL.
(IS_SEPARATION_COMBINATOR f /\ (~(pL = [])) /\ (!p. MEM p pL ==> VAR_RES_IS_STACK_IMPRECISE p))  ==>
(var_res_prop_varlist_update vcL (asl_bigstar_list (VAR_RES_COMBINATOR f) pL) =
 asl_bigstar_list (VAR_RES_COMBINATOR f) (MAP (var_res_prop_varlist_update vcL) pL))``,

REPEAT GEN_TAC THEN
Induct_on `pL` THEN1 REWRITE_TAC[] THEN
Cases_on `pL` THENL [
   FULL_SIMP_TAC list_ss [asl_bigstar_list_def, asl_bigstar_list_REWRITE,
      var_res_prop_var_update___asl_star,
      asl_star___PROPERTIES, IS_SEPARATION_COMBINATOR___VAR_RES_COMBINATOR],

   REPEAT STRIP_TAC THEN
   FULL_SIMP_TAC list_ss [DISJ_IMP_THM, FORALL_AND_THM] THEN
   FULL_SIMP_TAC list_ss [asl_bigstar_list_REWRITE] THEN
   `VAR_RES_IS_STACK_IMPRECISE
      (asl_star (VAR_RES_COMBINATOR f) h (asl_bigstar_list (VAR_RES_COMBINATOR f) t))` by ALL_TAC THEN1 (

      SIMP_TAC std_ss [GSYM asl_bigstar_list_REWRITE] THEN
      MATCH_MP_TAC (SIMP_RULE std_ss [AND_IMP_INTRO, GSYM RIGHT_FORALL_IMP_THM]
                    VAR_RES_IS_STACK_IMPRECISE___asl_bigstar_list) THEN
      ASM_SIMP_TAC list_ss [DISJ_IMP_THM, FORALL_AND_THM]
   ) THEN
   ASM_SIMP_TAC std_ss [var_res_prop_varlist_update___asl_star]
]);


val var_res_prop_varlist_update___var_res_bigstar_list =
store_thm ("var_res_prop_varlist_update___var_res_bigstar_list",
``!f vcL pL.
(IS_SEPARATION_COMBINATOR f /\ (EVERY VAR_RES_IS_STACK_IMPRECISE pL))  ==>
(var_res_prop_varlist_update vcL (var_res_bigstar_list f pL) =
 var_res_bigstar_list f (MAP (var_res_prop_varlist_update vcL) pL))``,

REWRITE_TAC [var_res_bigstar_list_def] THEN
REPEAT STRIP_TAC THEN
MP_TAC (Q.SPECL [`f`, `vcL`, `(var_res_prop_stack_true f)::pL`] var_res_prop_varlist_update___asl_bigstar_list) THEN
FULL_SIMP_TAC list_ss [DISJ_IMP_THM, FORALL_AND_THM, EVERY_MEM,
   VAR_RES_IS_STACK_IMPRECISE___var_res_prop_stack_true,
   var_res_prop_varlist_update___BOOL]);


val var_res_prop_varlist_update___var_res_map =
store_thm ("var_res_prop_varlist_update___var_res_map",
``!f vcL P l.
(IS_SEPARATION_COMBINATOR f /\ (!l. VAR_RES_IS_STACK_IMPRECISE (P l))) ==>
(var_res_prop_varlist_update vcL (var_res_map f P l) =
 var_res_map f ((var_res_prop_varlist_update vcL) o P) l)``,

SIMP_TAC std_ss [var_res_map_def] THEN
REPEAT STRIP_TAC THEN
ASM_SIMP_TAC list_ss [var_res_prop_varlist_update___var_res_bigstar_list, EVERY_MAP] THEN
SIMP_TAC std_ss [MAP_MAP_o]);




val var_res_prop_varlist_update___var_res_bigstar =
store_thm ("var_res_prop_varlist_update___var_res_bigstar",
``
!f vcL sfb.
  (IS_SEPARATION_COMBINATOR f /\ FINITE_BAG sfb /\
  (!sf. BAG_IN sf sfb ==> VAR_RES_IS_STACK_IMPRECISE sf))  ==>

(var_res_bigstar f
       (BAG_IMAGE (var_res_prop_varlist_update vcL) sfb) =
 var_res_prop_varlist_update vcL (var_res_bigstar f sfb))``,


NTAC 2 GEN_TAC THEN
Cases_on `IS_SEPARATION_COMBINATOR f` THEN ASM_REWRITE_TAC[] THEN
ONCE_REWRITE_TAC [GSYM AND_IMP_INTRO] THEN
HO_MATCH_MP_TAC STRONG_FINITE_BAG_INDUCT THEN
REPEAT STRIP_TAC THEN1 (
   ASM_SIMP_TAC std_ss [var_res_bigstar_REWRITE,
      BAG_IMAGE_EMPTY, var_res_prop_varlist_update___BOOL]
) THEN
FULL_SIMP_TAC std_ss [BAG_IN_BAG_INSERT, DISJ_IMP_THM,
  FORALL_AND_THM, var_res_bigstar_REWRITE,
  BAG_IMAGE_FINITE_INSERT] THEN
MATCH_MP_TAC (GSYM var_res_prop_varlist_update___asl_star) THEN
ASM_SIMP_TAC std_ss [VAR_RES_IS_STACK_IMPRECISE___var_res_bigstar, BAG_EVERY]);




val var_res_prop___var_eq_const_BAG_def =
Define `var_res_prop___var_eq_const_BAG f vL =
   LIST_TO_BAG (MAP (\x. var_res_prop_equal f (var_res_exp_var (FST x)) (var_res_exp_const (SND x)))
       vL)`

val var_res_prop___var_eq_const_BAG_THM = store_thm (
"var_res_prop___var_eq_const_BAG_THM",
``(var_res_prop___var_eq_const_BAG f [] = EMPTY_BAG) /\
  (var_res_prop___var_eq_const_BAG f (vc::vcL) =
     BAG_INSERT
        (var_res_prop_equal f (var_res_exp_var (FST vc)) (var_res_exp_const (SND vc)))
        (var_res_prop___var_eq_const_BAG f vcL))``,

SIMP_TAC list_ss [var_res_prop___var_eq_const_BAG_def,
  LIST_TO_BAG_def]);


val var_res_prop___PROP___var_res_prop_var_list_update___EQ_PRED_LIST =
store_thm ("var_res_prop___PROP___var_res_prop_var_list_update___EQ_PRED_LIST",
``!s f wpb rpb vcL. IS_SEPARATION_COMBINATOR f ==>
  (s IN var_res_prop___PROP f (wpb, rpb)
    (var_res_prop___var_eq_const_BAG f vcL) =
  (!v. v <: wpb ==> var_res_sl___has_write_permission v (FST s)) /\
  (!v. v <: rpb ==> var_res_sl___has_read_permission v (FST s)) /\
  (SND s IN asl_emp f) /\
  (EVERY (\vc. (FST vc IN FDOM (FST s)) /\
               (FST ((FST s) ' (FST vc)) = SND vc)) vcL))``,

SIMP_TAC (std_ss++EQUIV_EXTRACT_ss) [var_res_prop___PROP___REWRITE, IN_ABS] THEN
REPEAT STRIP_TAC THEN
`!v c. VAR_RES_IS_STACK_IMPRECISE
           (var_res_prop_equal f (var_res_exp_var v)
               (var_res_exp_const c))` by ALL_TAC THEN1 (
   EXT_CONSEQ_REWRITE_TAC [] [] ([], [
         VAR_RES_IS_STACK_IMPRECISE___var_res_prop_equal,
         IS_SOME___VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS___VAR_CONST_EVAL], [])
) THEN
`!vcL. BAG_EVERY VAR_RES_IS_STACK_IMPRECISE (var_res_prop___var_eq_const_BAG f vcL)` by ALL_TAC THEN1 (
   Induct_on `vcL` THEN
   ASM_SIMP_TAC list_ss [var_res_prop___var_eq_const_BAG_THM, BAG_EVERY_THM]
) THEN
Induct_on `vcL` THENL [
   ASM_SIMP_TAC list_ss [var_res_prop___var_eq_const_BAG_THM,
      var_res_bigstar_REWRITE, var_res_prop_stack_true_REWRITE,
      IN_ABS],

   ASM_SIMP_TAC list_ss [var_res_prop___var_eq_const_BAG_THM,
      var_res_bigstar___VAR_RES_IS_STACK_IMPRECISE,
      BAG_EVERY_THM, IN_ABS] THEN
   FULL_SIMP_TAC (std_ss++CONJ_ss) [var_res_prop_equal_unequal_EXPAND, IN_ABS, asl_emp_def,
      IS_SEPARATION_COMBINATOR_EXPAND_THM, GSYM RIGHT_EXISTS_AND_THM,
      GSYM LEFT_EXISTS_AND_THM, var_res_exp_const_def, IS_SOME_EXISTS,
      var_res_exp_var_def] THEN
   QUANT_INSTANTIATE_TAC [] THEN
   SIMP_TAC (std_ss++EQUIV_EXTRACT_ss) []
])



val var_res_prop___equal_const = store_thm (
"var_res_prop___equal_const",
``!f wpb rpb vcL sfb.
  COND_PROP___STRONG_IMP
  (var_res_prop f (wpb,rpb)
    (BAG_UNION (var_res_prop___var_eq_const_BAG f vcL) sfb))
  (var_res_prop f (wpb, rpb)
    (BAG_UNION (var_res_prop___var_eq_const_BAG f vcL)
     (BAG_IMAGE (var_res_prop_varlist_update vcL) sfb)))``,

SIMP_TAC std_ss [
   var_res_prop___REWRITE, COND_PROP___STRONG_IMP_def,
   var_res_prop___COND_UNION, var_res_prop___PROP_UNION] THEN
REPEAT STRIP_TAC THEN1 (
   FULL_SIMP_TAC std_ss [var_res_prop___COND___REWRITE,
      BAG_IMAGE_FINITE, BAG_IN_FINITE_BAG_IMAGE,
      GSYM LEFT_FORALL_IMP_THM,
      VAR_RES_IS_STACK_IMPRECISE___USED_VARS___var_res_prop_varlist_update]
) THEN
ONCE_REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN
`IS_SEPARATION_COMBINATOR f` by FULL_SIMP_TAC std_ss [var_res_prop___COND___REWRITE] THEN
ASM_SIMP_TAC std_ss [var_res_prop___PROP___var_res_prop_var_list_update___EQ_PRED_LIST] THEN
`?uf. IS_SEPARATION_COMBINATOR_NEUTRAL_ELEMENT_FUNCTION f uf` by
  PROVE_TAC[IS_SEPARATION_COMBINATOR_HALF_EXPAND_THM] THEN
POP_ASSUM MP_TAC THEN
ASM_SIMP_TAC std_ss [IS_SEPARATION_COMBINATOR_NEUTRAL_ELEMENT_FUNCTION_THM,
   asl_emp_def, IN_ABS, GSYM RIGHT_EXISTS_AND_THM, GSYM LEFT_EXISTS_AND_THM] THEN
STRIP_TAC THEN
QUANT_INSTANTIATE_TAC [] THEN
SIMP_TAC (std_ss++EQUIV_EXTRACT_ss) [] THEN
REPEAT STRIP_TAC THEN


`FINITE_BAG sfb /\
 !sf. BAG_IN sf sfb ==> VAR_RES_IS_STACK_IMPRECISE sf` by ALL_TAC THEN1 (
   FULL_SIMP_TAC std_ss [var_res_prop___COND___REWRITE,
      VAR_RES_IS_STACK_IMPRECISE___USED_VARS_def]
) THEN
ASM_SIMP_TAC std_ss [var_res_prop___PROP___REWRITE, IN_ABS,
   var_res_prop_varlist_update___var_res_bigstar] THEN
`?st1 h. x = (st1, h)` by (Cases_on `x` THEN SIMP_TAC std_ss []) THEN
FULL_SIMP_TAC std_ss [var_res_prop_varlist_update_def, IN_ABS,
   var_res_ext_state_varlist_update_def] THEN

Q.MATCH_ABBREV_TAC `(st1, h) IN P = (st2, h) IN P` THEN
`VAR_RES_IS_STACK_IMPRECISE P` by ALL_TAC THEN1 (
   FULL_SIMP_TAC std_ss [var_res_prop___COND___EXPAND,
     VAR_RES_IS_STACK_IMPRECISE___USED_VARS_def]
) THEN
Tactical.REVERSE (
   `VAR_RES_STACK___IS_EQUAL_UPTO_PERMISSIONS EMPTY st1 st2` by ALL_TAC) THEN1 (
   FULL_SIMP_TAC std_ss [VAR_RES_IS_STACK_IMPRECISE_def]
) THEN

Q.UNABBREV_TAC `st2` THEN
Q.PAT_ASSUM `EVERY X vcL` MP_TAC THEN
REPEAT (POP_ASSUM (K ALL_TAC)) THEN
Q.SPEC_TAC (`st1`, `st1`) THEN

Induct_on `vcL` THEN1 (
  SIMP_TAC list_ss [var_res_state_varlist_update_THM,
     VAR_RES_STACK___IS_EQUAL_UPTO_PERMISSIONS_def]
) THEN
SIMP_TAC list_ss [var_res_state_varlist_update_THM] THEN
REPEAT STRIP_TAC THEN
Q.PAT_ASSUM `!st. X` (MP_TAC o Q.SPEC `st1`) THEN
Q.ABBREV_TAC `st2 = (var_res_state_varlist_update vcL st1)` THEN
ASM_SIMP_TAC std_ss [VAR_RES_STACK___IS_EQUAL_UPTO_PERMISSIONS_def,
   NOT_IN_EMPTY, var_res_state_var_update_def, FAPPLY_FUPDATE_THM,
   FDOM_FUPDATE] THEN
SIMP_TAC (std_ss++EQUIV_EXTRACT_ss++CONJ_ss) [IN_INSERT, EXTENSION,
   COND_RAND, COND_RATOR] THEN
METIS_TAC[]);



val var_res_prop___equal_const___equal_var = store_thm (
"var_res_prop___equal_const___equal_var",
``!f wpb rpb v1 v2 c sfb.
  IS_SEPARATION_COMBINATOR f /\
  (BAG_IN v1 (BAG_UNION wpb rpb) /\ BAG_IN v2 (BAG_UNION wpb rpb)) ==>
  ((var_res_prop f (wpb,rpb)
    (BAG_INSERT (var_res_prop_equal f (var_res_exp_var v1) (var_res_exp_var v2))
     (BAG_INSERT (var_res_prop_equal f (var_res_exp_var v2) (var_res_exp_const c))
     sfb))) =
  (var_res_prop f (wpb, rpb)
    (BAG_INSERT (var_res_prop_equal f (var_res_exp_var v1) (var_res_exp_const c))
     (BAG_INSERT (var_res_prop_equal f (var_res_exp_var v2) (var_res_exp_const c))
      sfb))))``,

REPEAT STRIP_TAC THEN
`VAR_RES_IS_STACK_IMPRECISE___USED_VARS (SET_OF_BAG (wpb + rpb))
   (var_res_prop_equal f
        (var_res_exp_var v1) (var_res_exp_const c)) /\
 VAR_RES_IS_STACK_IMPRECISE___USED_VARS (SET_OF_BAG (wpb + rpb))
   (var_res_prop_equal f (var_res_exp_var v2) (var_res_exp_const c)) /\
 VAR_RES_IS_STACK_IMPRECISE___USED_VARS (SET_OF_BAG (wpb + rpb))
   (var_res_prop_equal f ((var_res_exp_var v1):('c, 'b, 'c) var_res_expression) (var_res_exp_var v2))` by ALL_TAC THEN1 (
   CONSEQ_REWRITE_TAC ([],
        [VAR_RES_IS_STACK_IMPRECISE___USED_VARS___var_res_prop_equal,
         VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET___VAR_CONST_EVAL],
        []) THEN
   ASM_SIMP_TAC std_ss [IN_SET_OF_BAG]
) THEN
ASM_SIMP_TAC std_ss [var_res_prop___EQ,
   var_res_prop___PROP_INSERT, var_res_prop___COND_INSERT] THEN
REPEAT STRIP_TAC THEN
ONCE_REWRITE_TAC[EXTENSION] THEN

SIMP_TAC std_ss [var_res_prop_equal_def, IN_ABS,
   var_res_prop_binexpression_def, var_res_stack_proposition_def,
   LET_THM, var_res_exp_var_def, var_res_exp_const_def] THEN
SIMP_TAC (std_ss++CONJ_ss) [COND_NONE_SOME_REWRITES,
   GSYM RIGHT_EXISTS_AND_THM] THEN
FULL_SIMP_TAC std_ss [IS_SEPARATION_COMBINATOR_EXPAND_THM,
   asl_emp_def, IN_ABS, GSYM LEFT_EXISTS_AND_THM, GSYM RIGHT_EXISTS_AND_THM] THEN
QUANT_INSTANTIATE_TAC [] THEN
SIMP_TAC (std_ss++EQUIV_EXTRACT_ss) []);



(***************************************************
 * Inferences
 ***************************************************)


val var_res_prop___CONST_INTRO = store_thm (
"var_res_prop___CONST_INTRO",
``!e f wpb rpb sfb.
(VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET (SET_OF_BAG (BAG_UNION wpb rpb)) e) ==>
(COND_PROP___EQUIV
 (var_res_prop f (wpb,rpb) sfb)
 (COND_PROP___EXISTS c.
    (var_res_prop f (wpb,rpb)
        (BAG_INSERT (var_res_prop_equal f e (var_res_exp_const c))
                    sfb))))``,

SIMP_TAC (std_ss++CONJ_ss++EQUIV_EXTRACT_ss) [
   var_res_prop___REWRITE, COND_PROP___EXISTS_def, COND_PROP___EQUIV_REWRITE,
   IN_ABS, var_res_prop___COND_INSERT, var_res_prop___PROP_INSERT,
   VAR_RES_IS_STACK_IMPRECISE___USED_VARS___var_res_prop_equal,
   VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET___VAR_CONST_EVAL] THEN
REPEAT STRIP_TAC THEN
FULL_SIMP_TAC std_ss [var_res_prop___COND___EXPAND,
   IS_SEPARATION_COMBINATOR_EXPAND_THM, var_res_prop_equal_def,
   var_res_prop_binexpression_def, var_res_stack_proposition_def,
   IN_ABS, LET_THM, var_res_exp_const_def, asl_emp_def,
   GSYM RIGHT_EXISTS_AND_THM, GSYM LEFT_EXISTS_AND_THM] THEN
QUANT_INSTANTIATE_TAC [] THEN
SIMP_TAC (std_ss++EQUIV_EXTRACT_ss) [] THEN

FULL_SIMP_TAC std_ss [
   VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET___REWRITE,
   VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_REL___REWRITE] THEN
Q.PAT_ASSUM `vs' SUBSET X` MP_TAC THEN
ASM_SIMP_TAC std_ss [SUBSET_DEF, var_res_prop___PROP___REWRITE_2,
   IN_SET_OF_BAG, BAG_IN_BAG_UNION, var_res_sl___has_write_permission_def,
   var_res_sl___has_read_permission_def, IN_ABS] THEN
METIS_TAC[]);



val VAR_RES_INFERENCE___EXISTS_PRE =
store_thm ("VAR_RES_INFERENCE___EXISTS_PRE",
``!xenv penv P prog Q.
(VAR_RES_HOARE_TRIPLE xenv penv (asl_exists x. P x) prog Q) =
(!x. VAR_RES_HOARE_TRIPLE xenv penv (P x) prog Q)``,

SIMP_TAC std_ss [VAR_RES_HOARE_TRIPLE_def, asl_bool_EVAL,
    ASL_PROGRAM_HOARE_TRIPLE_def, HOARE_TRIPLE_def, IN_ABS,
    GSYM LEFT_FORALL_IMP_THM] THEN
METIS_TAC[]);

val VAR_RES_COND_INFERENCE___STRONG_COND_EXISTS_PRE =
store_thm ("VAR_RES_COND_INFERENCE___STRONG_COND_EXISTS_PRE",
``!f P prog Q.
(!x. VAR_RES_COND_HOARE_TRIPLE f (P x) prog Q) ==>
(VAR_RES_COND_HOARE_TRIPLE f (COND_PROP___STRONG_EXISTS P) prog Q)``,

SIMP_TAC std_ss [COND_PROP___STRONG_EXISTS_def,
   VAR_RES_COND_HOARE_TRIPLE_REWRITE,
   COND_HOARE_TRIPLE_REWRITE, GSYM LEFT_EXISTS_AND_THM, IN_ABS,
   GSYM LEFT_FORALL_IMP_THM, HOARE_TRIPLE_def, asl_bool_EVAL] THEN
METIS_TAC[]);



val VAR_RES_COND_INFERENCE___STRONG_COND_EXISTS_POST =
store_thm ("VAR_RES_COND_INFERENCE___STRONG_COND_EXISTS_POST",
``!f P prog Q.
(?x. VAR_RES_COND_HOARE_TRIPLE f P prog (Q x)) ==>
(VAR_RES_COND_HOARE_TRIPLE f P prog (COND_PROP___STRONG_EXISTS Q))``,

SIMP_TAC std_ss [COND_PROP___STRONG_EXISTS_def,
  VAR_RES_COND_HOARE_TRIPLE_REWRITE, IN_ABS,
  COND_HOARE_TRIPLE_REWRITE, GSYM LEFT_EXISTS_AND_THM,
  GSYM LEFT_FORALL_IMP_THM, HOARE_TRIPLE_def, asl_bool_EVAL, asl_exists_def] THEN
SIMP_TAC std_ss [fasl_order_THM] THEN
REPEAT STRIP_TAC THEN
FULL_SIMP_TAC std_ss [] THEN
Q.PAT_ASSUM `!x'. x' IN SND P ==> X x'` (MP_TAC o Q.SPEC `x'`) THEN
ASM_SIMP_TAC std_ss [GSYM LEFT_FORALL_IMP_THM, SUBSET_DEF, IN_ABS] THEN
METIS_TAC[]);



val VAR_RES_COND_INFERENCE___asl_exists_pre =
store_thm ("VAR_RES_COND_INFERENCE___asl_exists_pre",
``!f wpb rpb sfb P prog Q.

(!y. VAR_RES_IS_STACK_IMPRECISE___USED_VARS (SET_OF_BAG (wpb + rpb)) (P y)) ==>

((VAR_RES_COND_HOARE_TRIPLE f (var_res_prop f (wpb,rpb)
        (BAG_INSERT (asl_exists y. P y) sfb)) prog Q) =
 (!y. VAR_RES_COND_HOARE_TRIPLE f (var_res_prop f (wpb,rpb)
        (BAG_INSERT (P y) sfb)) prog Q))``,

REPEAT STRIP_TAC THEN
ASM_SIMP_TAC std_ss [VAR_RES_COND_HOARE_TRIPLE_REWRITE,
   var_res_prop___REWRITE,
   var_res_prop___COND_INSERT,
   VAR_RES_IS_STACK_IMPRECISE___USED_VARS___asl_exists_direct,
   COND_HOARE_TRIPLE_REWRITE,
   var_res_prop___PROP___asl_exists] THEN
SIMP_TAC (std_ss++EQUIV_EXTRACT_ss) [IN_ABS, asl_bool_EVAL] THEN
REPEAT STRIP_TAC THEN
SIMP_TAC std_ss [GSYM LEFT_EXISTS_AND_THM, GSYM RIGHT_EXISTS_AND_THM,
   HOARE_TRIPLE_def, IN_ABS, GSYM LEFT_FORALL_IMP_THM] THEN
METIS_TAC[]);



val VAR_RES_COND_INFERENCE___asl_star_pre =
store_thm ("VAR_RES_COND_INFERENCE___asl_star_pre",
``!f f' wpb rpb sfb P1 P2 prog Q.
(IS_VAR_RES_COMBINATOR f' /\ (GET_VAR_RES_COMBINATOR f' = f) /\
 VAR_RES_IS_STACK_IMPRECISE___USED_VARS (SET_OF_BAG (wpb + rpb)) P1 /\
 VAR_RES_IS_STACK_IMPRECISE___USED_VARS (SET_OF_BAG (wpb + rpb)) P2) ==>
((VAR_RES_COND_HOARE_TRIPLE f (var_res_prop f (wpb,rpb)
        (BAG_INSERT (asl_star f' P1 P2) sfb)) prog Q) =
(VAR_RES_COND_HOARE_TRIPLE f (var_res_prop f (wpb,rpb)
        (BAG_INSERT P1 (BAG_INSERT P2 sfb))) prog Q))``,
SIMP_TAC std_ss [var_res_prop___asl_star]);


val VAR_RES_COND_INFERENCE___var_res_prop_stack_true = store_thm (
"VAR_RES_COND_INFERENCE___var_res_prop_stack_true",
``!f wpb rpb sfb prog post.
VAR_RES_COND_HOARE_TRIPLE f
   (var_res_prop f (wpb,rpb)
       (BAG_INSERT (var_res_prop_stack_true f) sfb)) prog post =
VAR_RES_COND_HOARE_TRIPLE f (var_res_prop f (wpb,rpb) sfb) prog post``,

SIMP_TAC std_ss [var_res_prop___var_res_prop_stack_true]);



val VAR_RES_COND_INFERENCE___false_precond = store_thm (
"VAR_RES_COND_INFERENCE___false_precond",
``!f wpb rpb sfb prog post.
VAR_RES_COND_HOARE_TRIPLE f
   (var_res_prop f (wpb,rpb)
       (BAG_INSERT asl_false sfb)) prog post``,

SIMP_TAC std_ss [VAR_RES_COND_HOARE_TRIPLE_def,
   var_res_prop___REWRITE, var_res_prop___PROP_INSERT,
   asl_bool_EVAL, VAR_RES_HOARE_TRIPLE_def,
   ASL_PROGRAM_HOARE_TRIPLE_def, IN_ABS,
   HOARE_TRIPLE_def]);




val VAR_RES_COND_INFERENCE___var_res_bool_proposition = store_thm (
"VAR_RES_COND_INFERENCE___var_res_bool_proposition",
``!c f wpb rpb sfb prog post.
VAR_RES_COND_HOARE_TRIPLE f
   (var_res_prop f (wpb,rpb)
       (BAG_INSERT (var_res_bool_proposition f c) sfb)) prog post =
(c ==>
 VAR_RES_COND_HOARE_TRIPLE f (var_res_prop f (wpb,rpb) sfb) prog post)``,

Cases_on `c` THEN (
   SIMP_TAC std_ss [
      VAR_RES_COND_INFERENCE___var_res_prop_stack_true,
      VAR_RES_COND_INFERENCE___false_precond,
      var_res_bool_proposition_TF]
));


val asl_trivial_cond___asl_star_var_res_bool_proposition = store_thm (
"asl_trivial_cond___asl_star_var_res_bool_proposition",
``(!f c p.
     (IS_SEPARATION_COMBINATOR f /\ VAR_RES_IS_STACK_IMPRECISE p) ==>
     (asl_star (VAR_RES_COMBINATOR f) (var_res_bool_proposition f c) p =
      asl_trivial_cond c p)) /\
  (!f c p.
     (IS_SEPARATION_COMBINATOR f /\ VAR_RES_IS_STACK_IMPRECISE p) ==>
     (asl_star (VAR_RES_COMBINATOR f) p (var_res_bool_proposition f c) =
      asl_trivial_cond c p))``,
REPEAT STRIP_TAC THEN
Cases_on `c` THEN
ASM_SIMP_TAC std_ss [asl_trivial_cond_def, var_res_bool_proposition_TF,
   asl_false___asl_star_THM,
   asl_star___var_res_prop_stack_true___STACK_IMPRECISE,
   asl_star___var_res_prop_stack_true___STACK_IMPRECISE___COMM]);


val asl_trivial_cond___var_res_bool_proposition = store_thm ("asl_trivial_cond___var_res_bool_proposition",
``!f c1 c2. asl_trivial_cond c1 (var_res_bool_proposition f c2) =
            var_res_bool_proposition f (c1 /\ c2)``,
Cases_on `c1` THEN Cases_on `c2` THEN
SIMP_TAC std_ss [asl_trivial_cond_def, var_res_bool_proposition_TF]);


val asl_trivial_cond___var_res_stack_true = store_thm ("asl_trivial_cond___var_res_stack_true",
``!f c. asl_trivial_cond c (var_res_prop_stack_true f) = var_res_bool_proposition f c``,
SIMP_TAC std_ss [var_res_prop_stack_true_def, asl_trivial_cond___var_res_bool_proposition]);



val VAR_RES_COND_INFERENCE___asl_trivial_cond = store_thm (
"VAR_RES_COND_INFERENCE___asl_trivial_cond",
``!c P f wpb rpb sfb prog post.
VAR_RES_COND_HOARE_TRIPLE f
   (var_res_prop f (wpb,rpb)
       (BAG_INSERT (asl_trivial_cond c P) sfb)) prog post =
(c ==>
 VAR_RES_COND_HOARE_TRIPLE f (var_res_prop f (wpb,rpb) (BAG_INSERT P sfb)) prog post)``,

Cases_on `c` THEN (
   SIMP_TAC std_ss [
      VAR_RES_COND_INFERENCE___false_precond,
      asl_trivial_cond_TF]
));



val VAR_RES_COND_INFERENCE___EQ_CASE_SPLIT = store_thm (
"VAR_RES_COND_INFERENCE___EQ_CASE_SPLIT",
``!f e1 e2 wpb rpb sfb prog post.

(VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET (SET_OF_BAG (BAG_UNION wpb rpb)) e1 /\
 VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET (SET_OF_BAG (BAG_UNION wpb rpb)) e2)  ==>

(VAR_RES_COND_HOARE_TRIPLE f (var_res_prop f (wpb,rpb) sfb) prog post =
((VAR_RES_COND_HOARE_TRIPLE f
        (var_res_prop f (wpb,rpb) (BAG_INSERT (var_res_prop_equal f e1 e2) sfb))
        prog post) /\
 (VAR_RES_COND_HOARE_TRIPLE f
        (var_res_prop f (wpb,rpb) (BAG_INSERT (var_res_prop_unequal f e1 e2) sfb))
        prog post)))``,


REPEAT STRIP_TAC THEN
`VAR_RES_IS_STACK_IMPRECISE___USED_VARS
        (SET_OF_BAG (BAG_UNION wpb rpb)) (var_res_prop_equal f e1 e2) /\
 VAR_RES_IS_STACK_IMPRECISE___USED_VARS
        (SET_OF_BAG (BAG_UNION wpb rpb)) (var_res_prop_unequal f e1 e2)` by ALL_TAC THEN1 (
  CONSEQ_REWRITE_TAC ([VAR_RES_IS_STACK_IMPRECISE___USED_VARS___var_res_prop_equal,
                       VAR_RES_IS_STACK_IMPRECISE___USED_VARS___var_res_prop_unequal],
                      [], []) THEN
  ASM_REWRITE_TAC[]
) THEN
ASM_SIMP_TAC (std_ss++EQUIV_EXTRACT_ss) [VAR_RES_COND_HOARE_TRIPLE_def,
   var_res_prop___REWRITE, var_res_prop___COND_INSERT,
   var_res_prop___PROP_INSERT] THEN
NTAC 2 (POP_ASSUM (K ALL_TAC)) THEN
REPEAT STRIP_TAC THEN
`IS_SEPARATION_COMBINATOR f` by PROVE_TAC[var_res_prop___COND___EXPAND] THEN
FULL_SIMP_TAC std_ss [var_res_prop_unequal_def, var_res_prop_equal_def,
   var_res_prop_binexpression_def, var_res_stack_proposition_def,
   LET_THM, IS_SEPARATION_COMBINATOR_EXPAND_THM, asl_emp_def,
   IN_ABS, GSYM RIGHT_EXISTS_AND_THM, GSYM LEFT_EXISTS_AND_THM,
   VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET___REWRITE,
   var_res_prop___PROP_INSERT, VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_REL___REWRITE] THEN
QUANT_INSTANTIATE_TAC [] THEN

SIMP_TAC std_ss [VAR_RES_HOARE_TRIPLE_def, IN_ABS,
                 ASL_PROGRAM_HOARE_TRIPLE_def, HOARE_TRIPLE_def,
                 fasl_order_THM, GSYM FORALL_AND_THM] THEN
CONSEQ_CONV_TAC (K FORALL_EQ___CONSEQ_CONV) THEN
SIMP_TAC (std_ss++EQUIV_EXTRACT_ss) [] THEN
REPEAT STRIP_TAC THEN
Tactical.REVERSE (`vs' SUBSET FDOM (FST x) /\ vs'' SUBSET FDOM (FST x)` by ALL_TAC) THEN1 (
   ASM_SIMP_TAC std_ss []
) THEN
IMP_RES_TAC var_res_prop___PROP___VARS THEN
PROVE_TAC[SUBSET_TRANS]);


val VAR_RES_COND_INFERENCE___CONST_INTRO = store_thm (
"VAR_RES_COND_INFERENCE___CONST_INTRO",
``!e f wpb rpb sfb prog post.
(VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET (SET_OF_BAG (BAG_UNION wpb rpb)) e) ==>

(VAR_RES_COND_HOARE_TRIPLE f (var_res_prop f (wpb,rpb) sfb) prog post =
 !c. VAR_RES_COND_HOARE_TRIPLE f
        (var_res_prop f (wpb,rpb)
                     (BAG_INSERT (var_res_prop_equal f e (var_res_exp_const c))
                                    sfb)) prog post)``,

REPEAT STRIP_TAC THEN
MP_TAC (Q.SPECL [`e`, `f`, `wpb`,`rpb`,`sfb`] var_res_prop___CONST_INTRO) THEN
ASM_SIMP_TAC std_ss [GSYM VAR_RES_COND_HOARE_TRIPLE___COND_EXISTS,
                     VAR_RES_COND_HOARE_TRIPLE___COND_PROP_EQUIV]);



val VAR_RES_COND_INFERENCE___TRIVIAL_CONST_INTRO = store_thm (
"VAR_RES_COND_INFERENCE___TRIVIAL_CONST_INTRO",
``!c f wpb rpb sfb prog post.
(VAR_RES_COND_HOARE_TRIPLE f (var_res_prop f (wpb,rpb) sfb) prog post =
 VAR_RES_COND_HOARE_TRIPLE f
        (var_res_prop f (wpb,rpb)
                     (BAG_INSERT (var_res_prop_equal f (var_res_exp_const c) (var_res_exp_const c))
                                    sfb)) prog post)``,

SIMP_TAC std_ss [var_res_prop_equal_unequal_REWRITES,
   var_res_bool_proposition_TF, VAR_RES_COND_INFERENCE___var_res_prop_stack_true]);



val var_res_prop___UNEQUAL_INTRO = store_thm (
"var_res_prop___UNEQUAL_INTRO",
``!f c1 c2 wpb rpb sfb.
(~(c1 = c2)) ==>
 (var_res_prop f (wpb,rpb) sfb =
  var_res_prop f (wpb,rpb) (BAG_INSERT (var_res_prop_unequal f
                                           (var_res_exp_const c1)
                                           (var_res_exp_const c2))
                                        sfb))``,


SIMP_TAC (std_ss++EQUIV_EXTRACT_ss) [var_res_prop___REWRITE,
   var_res_prop___COND_INSERT,
   var_res_prop___PROP_INSERT,
   VAR_RES_IS_STACK_IMPRECISE___USED_VARS___var_res_prop_unequal,
   VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET___VAR_CONST_EVAL] THEN
SIMP_TAC std_ss [COND_RATOR, COND_RAND] THEN
SIMP_TAC std_ss [var_res_prop_unequal_def, IN_ABS,
   var_res_prop_binexpression_def, var_res_stack_proposition_def,
   LET_THM, IN_ABS, var_res_exp_const_def, asl_emp_def] THEN
REPEAT STRIP_TAC THEN
`IS_SEPARATION_COMBINATOR f` by PROVE_TAC[var_res_prop___COND___EXPAND] THEN
FULL_SIMP_TAC std_ss [IS_SEPARATION_COMBINATOR_EXPAND_THM,
   GSYM RIGHT_EXISTS_AND_THM, GSYM LEFT_EXISTS_AND_THM] THEN
QUANT_INSTANTIATE_TAC [] THEN
SIMP_TAC std_ss [IN_ABS3]);




val VAR_RES_COND_INFERENCE___prog_block = store_thm (
"VAR_RES_COND_INFERENCE___prog_block",
``!f P prog L Q.
 (VAR_RES_COND_HOARE_TRIPLE f P (asl_prog_block (prog::L)) Q) =
 (VAR_RES_COND_HOARE_TRIPLE f P (asl_prog_seq prog (asl_prog_block L)) Q)``,

SIMP_TAC std_ss [VAR_RES_COND_HOARE_TRIPLE_def,
   VAR_RES_HOARE_TRIPLE_def, ASL_PROGRAM_HOARE_TRIPLE_def,
   ASL_PROGRAM_SEM___prog_block, ASL_PROGRAM_SEM___prog_seq]);


val VAR_RES_COND_INFERENCE___prog_block2 = store_thm (
"VAR_RES_COND_INFERENCE___prog_block2",
``!f P prog1 prog2 L Q.
 (VAR_RES_COND_HOARE_TRIPLE f P (asl_prog_block ((asl_prog_seq prog1 prog2)::L)) Q) =
 (VAR_RES_COND_HOARE_TRIPLE f P (asl_prog_block (prog1::prog2::L)) Q)``,

SIMP_TAC std_ss [VAR_RES_COND_HOARE_TRIPLE_def,
   VAR_RES_HOARE_TRIPLE_def, ASL_PROGRAM_HOARE_TRIPLE_def,
   ASL_PROGRAM_SEM___prog_block, ASL_PROGRAM_SEM___prog_seq,
   REWRITE_RULE [ASSOC_DEF] asla_seq___ASSOC]);


val VAR_RES_COND_INFERENCE___prog_block3 = store_thm (
"VAR_RES_COND_INFERENCE___prog_block3",
``!f P p1 pL pL2 Q.
 (VAR_RES_COND_HOARE_TRIPLE f P (asl_prog_block (p1::(asl_prog_block pL)::pL2)) Q) =
 (VAR_RES_COND_HOARE_TRIPLE f P (asl_prog_block (p1::(pL++pL2))) Q)``,

SIMP_TAC std_ss [VAR_RES_COND_HOARE_TRIPLE_def,
   VAR_RES_HOARE_TRIPLE_def, ASL_PROGRAM_HOARE_TRIPLE_def,
   ASL_PROGRAM_SEM___prog_block, ASL_PROGRAM_SEM___prog_block_append]);


val VAR_RES_INFERENCE___prog_parallel = store_thm (
"VAR_RES_INFERENCE___prog_parallel",
``!f lock_env penv P1 P2 Q1 Q2 p1 p2.
   IS_SEPARATION_COMBINATOR f /\
   VAR_RES_HOARE_TRIPLE (VAR_RES_COMBINATOR f, lock_env) penv P1 p1 Q1 /\
   VAR_RES_HOARE_TRIPLE (VAR_RES_COMBINATOR f, lock_env) penv P2 p2 Q2 ==>
   VAR_RES_HOARE_TRIPLE (VAR_RES_COMBINATOR f, lock_env) penv
           (asl_star (VAR_RES_COMBINATOR f) P1 P2)
           (asl_prog_parallel p1 p2)
           (asl_star (VAR_RES_COMBINATOR f) Q1 Q2)``,

SIMP_TAC std_ss [VAR_RES_HOARE_TRIPLE_def] THEN
REPEAT STRIP_TAC THEN
SIMP_TAC std_ss [IN_ABS, asl_star_def,
                 GSYM LEFT_EXISTS_AND_THM, GSYM RIGHT_EXISTS_AND_THM] THEN
SIMP_TAC std_ss [asl_exists___GSYM_REWRITE, IN_ABS3,
                 ASL_INFERENCE_asl_quant] THEN
REPEAT STRIP_TAC THEN

Q.PAT_ASSUM `!x. X x` (MP_TAC o Q.SPEC `q`) THEN
Q.PAT_ASSUM `!x. X x` (MP_TAC o Q.SPEC `p`) THEN
Q.ABBREV_TAC `P1' = (\s. s IN P1 /\ (s = p))` THEN
Q.ABBREV_TAC `P2' = (\s. s IN P2 /\ (s = q))` THEN
Q.ABBREV_TAC `Q1' = (\s. s IN Q1 /\
         VAR_RES_STACK___IS_EQUAL_UPTO_VALUES (FST p) (FST s))` THEN
Q.ABBREV_TAC `Q2' = (\s. s IN Q2 /\
         VAR_RES_STACK___IS_EQUAL_UPTO_VALUES (FST q) (FST s))` THEN
SIMP_TAC (std_ss++CONJ_ss) [] THEN
Tactical.REVERSE (Cases_on `VAR_RES_COMBINATOR f (SOME p) (SOME q) = SOME x`) THEN1 (
   ASM_SIMP_TAC std_ss [ASL_PROGRAM_HOARE_TRIPLE_def, HOARE_TRIPLE_def, IN_ABS]
) THEN
ASM_SIMP_TAC std_ss [] THEN REPEAT STRIP_TAC THEN
MATCH_MP_TAC ASL_INFERENCE_STRENGTHEN THEN
Q.EXISTS_TAC `asl_star (VAR_RES_COMBINATOR f) P1' P2'` THEN
Q.EXISTS_TAC `asl_star (VAR_RES_COMBINATOR f) Q1' Q2'` THEN
REPEAT STRIP_TAC THENL [
   Q.UNABBREV_TAC `P1'` THEN
   Q.UNABBREV_TAC `P2'` THEN
   ASM_SIMP_TAC (std_ss++EQUIV_EXTRACT_ss) [SUBSET_DEF, IN_ABS, asl_star_def],


   Q.UNABBREV_TAC `Q1'` THEN
   Q.UNABBREV_TAC `Q2'` THEN
   ASM_SIMP_TAC (std_ss++EQUIV_EXTRACT_ss) [
      SUBSET_DEF, IN_ABS, asl_star_def, asl_exists_def] THEN
   REPEAT STRIP_TAC THEN
   Q.EXISTS_TAC `p'` THEN Q.EXISTS_TAC `q'` THEN
   FULL_SIMP_TAC std_ss [VAR_RES_COMBINATOR_REWRITE,
      SOME___VAR_RES_STACK_COMBINE,
      VAR_RES_STACK___IS_EQUAL_UPTO_VALUES_def,
      FMERGE_DEF, VAR_RES_STACK_COMBINE___MERGE_FUNC_def,
      IN_UNION, VAR_RES_STACK_IS_SEPARATE_def] THEN
   SIMP_TAC std_ss [GSYM FORALL_AND_THM] THEN GEN_TAC THEN
   REPEAT (Q.PAT_ASSUM `!x. X x` (MP_TAC o Q.SPEC `x''`)) THEN
   Cases_on `x'' IN FDOM (FST p)` THEN
   Cases_on `x'' IN FDOM (FST p')` THEN
   Cases_on `x'' IN FDOM (FST q)` THEN
   Cases_on `x'' IN FDOM (FST q')` THEN
   ASM_SIMP_TAC (std_ss++CONJ_ss) [
      AND_IMP_INTRO, var_res_permission_THM2],


   MATCH_MP_TAC (SIMP_RULE std_ss [PAIR_FORALL_THM] ASL_INFERENCE_prog_parallel) THEN
   ASM_SIMP_TAC std_ss [IS_SEPARATION_COMBINATOR___VAR_RES_COMBINATOR]
]);



val VAR_RES_INFERENCE___prog_forall = store_thm (
"VAR_RES_INFERENCE___prog_forall",
``!xenv penv P Q body.
  (!d. VAR_RES_HOARE_TRIPLE xenv penv P (body d) Q) ==>
  VAR_RES_HOARE_TRIPLE xenv penv P (asl_prog_forall body) Q``,

SIMP_TAC std_ss [VAR_RES_HOARE_TRIPLE_def] THEN
METIS_TAC[ASL_INFERENCE_prog_forall]);


val VAR_RES_COND_INFERENCE___prog_forall = store_thm (
"VAR_RES_COND_INFERENCE___prog_forall",
``!f P Q body.
  (!d. VAR_RES_COND_HOARE_TRIPLE f P (body d) Q) ==>
  VAR_RES_COND_HOARE_TRIPLE f P (asl_prog_forall body) Q``,

SIMP_TAC std_ss [VAR_RES_COND_HOARE_TRIPLE_def] THEN
METIS_TAC[VAR_RES_INFERENCE___prog_forall]);



val VAR_RES_INFERENCE___prog_seq = store_thm (
"VAR_RES_INFERENCE___prog_seq",
``!xenv penv P Q R p1 p2.
  VAR_RES_HOARE_TRIPLE xenv penv P p1 Q /\
  VAR_RES_HOARE_TRIPLE xenv penv Q p2 R ==>
  VAR_RES_HOARE_TRIPLE xenv penv P (asl_prog_seq p1 p2) R``,

SIMP_TAC std_ss [VAR_RES_HOARE_TRIPLE_REWRITE] THEN
REPEAT STRIP_TAC THEN1 PROVE_TAC[ASL_INFERENCE_prog_seq] THEN
FULL_SIMP_TAC std_ss [
   VAR_RES_PERM_HOARE_TRIPLE_def, ASL_PROGRAM_SEM___prog_seq,
   SOME___asla_seq, GSYM RIGHT_EXISTS_AND_THM,
   GSYM LEFT_FORALL_IMP_THM, IN_BIGUNION, IN_IMAGE] THEN
REPEAT STRIP_TAC THEN
`VAR_RES_STACK___IS_EQUAL_UPTO_VALUES (FST s) (FST x')` by RES_TAC THEN
`x' IN Q` by ALL_TAC THEN1 (
   Q.PAT_ASSUM `ASL_PROGRAM_HOARE_TRIPLE xenv penv P p1 Q` MP_TAC THEN
   ASM_SIMP_TAC std_ss [
      ASL_PROGRAM_HOARE_TRIPLE_def, HOARE_TRIPLE_def,
      fasl_order_THM, GSYM LEFT_EXISTS_IMP_THM, SUBSET_DEF] THEN
   Q.EXISTS_TAC `s` THEN
   ASM_SIMP_TAC std_ss []
) THEN
`?s1'. ASL_PROGRAM_SEM xenv penv p2 x' = SOME s1'` by
   METIS_TAC[IS_SOME_EXISTS] THEN
FULL_SIMP_TAC std_ss [] THEN
`VAR_RES_STACK___IS_EQUAL_UPTO_VALUES (FST x') (FST s2)` by RES_TAC THEN
PROVE_TAC [VAR_RES_STACK___IS_EQUAL_UPTO_VALUES___TRANS]);



val VAR_RES_COND_INFERENCE___prog_seq = store_thm (
"VAR_RES_COND_INFERENCE___prog_seq",
``!f P Q R p1 p2.
  (FST P /\ FST R ==> FST Q) /\
  VAR_RES_COND_HOARE_TRIPLE f P p1 Q /\
  VAR_RES_COND_HOARE_TRIPLE f Q p2 R ==>
  VAR_RES_COND_HOARE_TRIPLE f P (asl_prog_seq p1 p2) R``,

SIMP_TAC std_ss [VAR_RES_COND_HOARE_TRIPLE_def] THEN
REPEAT STRIP_TAC THEN
MATCH_MP_TAC VAR_RES_INFERENCE___prog_seq THEN
Q.EXISTS_TAC `SND Q` THEN
ASM_SIMP_TAC std_ss []);




val VAR_RES_INFERENCE___STRENGTHEN = store_thm (
"VAR_RES_INFERENCE___STRENGTHEN",
``!xenv penv prog P1 Q1 P2 Q2.
  ((!x. x IN P2 ==> x IN P1) /\
   (!x y. y IN P2 /\ VAR_RES_STACK___IS_EQUAL_UPTO_VALUES (FST y) (FST x) /\
         x IN Q1 ==> x IN Q2) /\
   VAR_RES_HOARE_TRIPLE xenv penv P1 prog Q1) ==>
  VAR_RES_HOARE_TRIPLE xenv penv P2 prog Q2``,

SIMP_TAC std_ss [VAR_RES_HOARE_TRIPLE_def,
   ASL_PROGRAM_HOARE_TRIPLE_def, HOARE_TRIPLE_def,
   IN_ABS, fasl_order_THM, SUBSET_DEF] THEN
REPEAT STRIP_TAC THEN
`?s1. (ASL_PROGRAM_SEM xenv penv prog x = SOME s1) /\
      !x'. x' IN s1 ==> x' IN Q1 /\
      VAR_RES_STACK___IS_EQUAL_UPTO_VALUES (FST x) (FST x')` by METIS_TAC[] THEN
ASM_SIMP_TAC std_ss [] THEN
METIS_TAC[]);



val VAR_RES_INFERENCE___STRENGTHEN_PERMS = store_thm (
"VAR_RES_INFERENCE___STRENGTHEN_PERMS",
``!f xenv penv prog sfb1 sfb2 wpb1 wpb2 wpb1' wpb2' rpb1 rpb2.
  (((FST xenv = VAR_RES_COMBINATOR f) /\
   (!v. BAG_IN v wpb1 ==> BAG_IN v wpb2) /\
   (BAG_DISJOINT wpb2' rpb2) /\
   (!v. (BAG_IN v wpb1 \/ BAG_IN v rpb1) =
        (BAG_IN v wpb2 \/ BAG_IN v rpb2)) /\
   (!v. (BAG_IN v wpb1' \/ BAG_IN v rpb1) =
        (BAG_IN v wpb2' \/ BAG_IN v rpb2))) /\

   VAR_RES_HOARE_TRIPLE xenv penv
       (var_res_prop___PROP f (wpb1,rpb1) sfb1)
       prog
       (var_res_prop___PROP f (wpb1',rpb1) sfb2)) ==>
   VAR_RES_HOARE_TRIPLE xenv penv
       (var_res_prop___PROP f (wpb2,rpb2) sfb1)
       prog
       (var_res_prop___PROP f (wpb2',rpb2) sfb2)``,

REPEAT STRIP_TAC THEN
MATCH_MP_TAC VAR_RES_INFERENCE___STRENGTHEN THEN
Q.EXISTS_TAC `var_res_prop___PROP f (wpb1,rpb1) sfb1` THEN
Q.EXISTS_TAC `var_res_prop___PROP f (wpb1',rpb1) sfb2` THEN
FULL_SIMP_TAC std_ss [var_res_prop___PROP___REWRITE_2,
   IN_ABS, SUBSET_DEF, var_res_sl___has_read_permission_def,
   var_res_sl___has_write_permission_def,
   VAR_RES_STACK___IS_EQUAL_UPTO_VALUES_def,
   BAG_DISJOINT_BAG_IN] THEN
METIS_TAC[]);


val VAR_RES_INFERENCE___FRAME = store_thm (
"VAR_RES_INFERENCE___FRAME",
``!f xenv penv prog P Q R.
  (IS_SEPARATION_COMBINATOR f /\ (FST xenv = VAR_RES_COMBINATOR f) /\
  VAR_RES_HOARE_TRIPLE xenv penv P prog Q) ==>
  VAR_RES_HOARE_TRIPLE xenv penv (asl_star (VAR_RES_COMBINATOR f) P R) prog (asl_star (VAR_RES_COMBINATOR f) Q R)``,

SIMP_TAC std_ss [VAR_RES_HOARE_TRIPLE_def,
   ASL_PROGRAM_HOARE_TRIPLE_def, HOARE_TRIPLE_def,
   IN_ABS, fasl_order_THM2, SUBSET_DEF, asl_star_def] THEN
REPEAT STRIP_TAC THEN
Q.PAT_ASSUM `!x. X x` (MP_TAC o Q.SPEC `p`) THEN
ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
Q.PAT_ASSUM `SOME x = Y` (ASSUME_TAC o GSYM) THEN
Q.ABBREV_TAC `act = ASL_PROGRAM_SEM xenv penv prog` THEN
`ASL_IS_LOCAL_ACTION (FST xenv) act` by METIS_TAC[
   ASL_IS_LOCAL_ACTION___ASL_PROGRAM_SEM,
   IS_SEPARATION_COMBINATOR___VAR_RES_COMBINATOR] THEN
FULL_SIMP_TAC std_ss [ASL_IS_LOCAL_ACTION___ALTERNATIVE_EXT_DEF] THEN
Q.PAT_ASSUM `!s1 s2 s3. X s1 s2 s3` (
   MP_TAC o (Q.SPECL [`p`, `q`, `x`])) THEN
`ASL_IS_SUBSTATE (FST xenv) p x` by PROVE_TAC[ASL_IS_SUBSTATE_INTRO,
   IS_SEPARATION_COMBINATOR___VAR_RES_COMBINATOR] THEN
ASM_SIMP_TAC std_ss [GSYM LEFT_FORALL_IMP_THM, GSYM LEFT_EXISTS_AND_THM] THEN
REPEAT STRIP_TAC THEN
RES_TAC THEN
Q.EXISTS_TAC `t'` THEN Q.EXISTS_TAC `q` THEN
Q.PAT_ASSUM `!x'. x' IN s1 ==> Y` (MP_TAC o Q.SPEC `t'`) THEN
ASM_SIMP_TAC std_ss [] THEN
FULL_SIMP_TAC std_ss [VAR_RES_STACK___IS_EQUAL_UPTO_VALUES_def,
   VAR_RES_COMBINATOR_REWRITE, SOME___VAR_RES_STACK_COMBINE,
   FMERGE_DEF, IN_UNION, VAR_RES_STACK_IS_SEPARATE_def] THEN
ASM_SIMP_TAC (std_ss++CONJ_ss) [] THEN
STRIP_TAC THEN GEN_TAC THEN
Cases_on `x'' IN FDOM (FST q)` THEN ASM_SIMP_TAC std_ss [] THEN

Cases_on `x'' IN FDOM (FST t')` THEN
Cases_on `x'' IN FDOM (FST p)` THEN
ASM_SIMP_TAC std_ss [VAR_RES_STACK_COMBINE___MERGE_FUNC_def] THENL [
   `IS_SOME (var_res_permission_combine (SOME (SND (FST t' ' x'')))
                (SOME (SND (FST q ' x''))))` by METIS_TAC[] THEN
   `(SND (FST t' ' x'') = var_res_write_permission)` by RES_TAC THEN
   FULL_SIMP_TAC std_ss [var_res_permission_THM2],


   `IS_SOME (var_res_permission_combine (SOME (SND (FST p ' x'')))
              (SOME (SND (FST q ' x''))))` by METIS_TAC[] THEN
   `(SND (FST p ' x'') = var_res_write_permission)` by RES_TAC THEN
   FULL_SIMP_TAC std_ss [var_res_permission_THM2]
]);




(***************************************************
 * VAR_RES_FRAME_SPLIT
 ***************************************************)




(*VAR_RES_FRAME_SPLIT is used to compute frames.

  The general idea is to split sfb_split into
  sfb_rest and sfb_imp, i.e. sfb_split |=> sfb_rest * sfb_imp such
  that sfb_rest satisfies some predicate restP.

  However, this is complicated by the variables. One has currently
  the permission for the variables in (wpb,rpb). These permissions have to
  be split such that sfb_imp gets exclusive access to the ones in wpb'.
  All other variables can be used by sfb_rest as well. To ensure
  that everything is well with respect to variables,
  some side-conditions var_res_prop___COND as well as the actual split
  is used.


  For technical reasons, it is demanded that sfb_restP is satisfiable.
  Calculations are made simpler by explicitly moving common parts
  of sfb_imp and sfb_split into sfb_context.

  Finally the flag strong_rest has no semantics on the HOL-level but is
  used by tools to determine, whether as strong or weak sfb_rest is desired.
*)

val VAR_RES_FRAME_SPLIT___sfb_restP_OK_def = Define
`VAR_RES_FRAME_SPLIT___sfb_restP_OK f (wpb,rpb) sfb_restP =
(?sfb. sfb_restP sfb /\ (var_res_prop___COND f (wpb,rpb) sfb)) /\
(!sfbS. (!sfb. sfb IN sfbS ==>
            ((var_res_prop___COND f (wpb,rpb) sfb) /\ (sfb_restP sfb))) ==>
    sfb_restP {|\s. ?sfb. (sfb IN sfbS) /\
     s IN (var_res_bigstar f sfb) |})`


val VAR_RES_FRAME_SPLIT___sfb_restP_OK___REWRITE = store_thm (
"VAR_RES_FRAME_SPLIT___sfb_restP_OK___REWRITE",
``VAR_RES_FRAME_SPLIT___sfb_restP_OK f (wpb,rpb) sfb_restP =
(?sfb. sfb_restP sfb /\ (var_res_prop___COND f (wpb,rpb) sfb)) /\
(!sfbS. (!sfb. sfb IN sfbS ==>
            ((var_res_prop___COND f (wpb,rpb) sfb) /\ (sfb_restP sfb))) ==>
    sfb_restP {|asl_exists sfb. asl_and (K (sfb IN sfbS))
       (var_res_bigstar f sfb) |})``,

SIMP_TAC std_ss [VAR_RES_FRAME_SPLIT___sfb_restP_OK_def,
   asl_exists_def, asl_and_def, combinTheory.K_DEF, IN_ABS]);


val VAR_RES_FRAME_SPLIT___sfb_restP_OK___asl_exists_IMP = store_thm (
"VAR_RES_FRAME_SPLIT___sfb_restP_OK___asl_exists_IMP",
``VAR_RES_FRAME_SPLIT___sfb_restP_OK f (wpb,rpb) sfb_restP ==>
(!sfb. ((!x. (sfb_restP (sfb x)) /\
            (var_res_prop___COND f (wpb,rpb) (sfb x))) ==>
    sfb_restP {|asl_exists x. var_res_bigstar f (sfb x) |}))``,

SIMP_TAC std_ss [VAR_RES_FRAME_SPLIT___sfb_restP_OK_def] THEN
REPEAT STRIP_TAC THEN
Q.PAT_ASSUM `!sfbS. X ==> Y`
   (MP_TAC o Q.SPEC `IMAGE sfb' (UNIV:'d set)`) THEN

ASM_SIMP_TAC std_ss [IN_IMAGE, IN_UNIV, GSYM LEFT_FORALL_IMP_THM,
   asl_exists_def, GSYM LEFT_EXISTS_AND_THM, GSYM RIGHT_EXISTS_AND_THM]);




val VAR_RES_FRAME_SPLIT_def = Define `
VAR_RES_FRAME_SPLIT f (rfc:(bool # (label list option))) (wpb,rpb) wpb' sfb_context sfb_split sfb_imp sfb_restP =

VAR_RES_FRAME_SPLIT___sfb_restP_OK f (BAG_DIFF wpb wpb',BAG_DIFF rpb wpb') sfb_restP ==>
?sfb_rest.
sfb_restP sfb_rest /\
(var_res_prop___COND f (BAG_DIFF wpb wpb',BAG_DIFF rpb wpb') sfb_rest) /\
(var_res_prop___COND f (wpb,rpb) (BAG_UNION sfb_context (BAG_UNION sfb_split sfb_imp)) ==>
(!s. var_res_prop___PROP f (wpb,rpb) (BAG_UNION sfb_split sfb_context) s ==>
   var_res_prop___PROP f (wpb,rpb) (BAG_UNION sfb_imp (BAG_UNION sfb_rest sfb_context)) s))`



val var_res_prop___COND___var_set_extend =
store_thm ("var_res_prop___COND___var_set_extend",
``!f wpb rpb wpb' rpb' sfb.
   ((SET_OF_BAG (BAG_UNION wpb rpb)) SUBSET (SET_OF_BAG (BAG_UNION wpb' rpb')) /\
    (BAG_ALL_DISTINCT (BAG_UNION wpb' rpb')) /\
   var_res_prop___COND f (wpb, rpb) sfb) ==>
   var_res_prop___COND f (wpb', rpb') sfb``,

SIMP_TAC std_ss [var_res_prop___COND___REWRITE] THEN
METIS_TAC [VAR_RES_IS_STACK_IMPRECISE___USED_VARS___SUBSET]);


val var_res_prop___COND___BAG_DIFF_REMOVE =
store_thm ("var_res_prop___COND___BAG_DIFF_REMOVE",
``!f wpb rpb wpb' rpb' sfb.
   (BAG_ALL_DISTINCT (BAG_UNION wpb rpb) /\
   var_res_prop___COND f (BAG_DIFF wpb wpb', BAG_DIFF rpb rpb') sfb) ==>
   var_res_prop___COND f (wpb, rpb) sfb``,

REPEAT STRIP_TAC THEN
MATCH_MP_TAC var_res_prop___COND___var_set_extend THEN
Q.EXISTS_TAC `BAG_DIFF wpb wpb'` THEN
Q.EXISTS_TAC `BAG_DIFF rpb rpb'` THEN
FULL_SIMP_TAC std_ss [SUBSET_DEF, IN_SET_OF_BAG,
   BAG_IN_BAG_UNION, DISJ_IMP_THM, FORALL_AND_THM,
   BAG_IN_BAG_DIFF_ALL_DISTINCT, BAG_ALL_DISTINCT_BAG_UNION]);


val VAR_RES_FRAME_SPLIT_EXPAND = store_thm ("VAR_RES_FRAME_SPLIT_EXPAND",
``VAR_RES_FRAME_SPLIT f rfc (wpb,rpb) wpb' sfb_context sfb_split sfb_imp sfb_restP =

VAR_RES_FRAME_SPLIT___sfb_restP_OK f (BAG_DIFF wpb wpb',BAG_DIFF rpb wpb') sfb_restP ==>
?sfb_rest.
sfb_restP sfb_rest /\
(var_res_prop___COND f (BAG_DIFF wpb wpb',BAG_DIFF rpb wpb') sfb_rest) /\
((var_res_prop___COND f (wpb,rpb) (BAG_UNION sfb_context (BAG_UNION sfb_split sfb_imp)) /\
 var_res_prop___COND f (wpb,rpb) sfb_rest) ==>
(!s. var_res_prop___PROP f (wpb,rpb) (BAG_UNION sfb_split sfb_context) s ==>
   var_res_prop___PROP f (wpb,rpb) (BAG_UNION sfb_imp (BAG_UNION sfb_rest sfb_context)) s))``,

SIMP_TAC (std_ss++EQUIV_EXTRACT_ss) [VAR_RES_FRAME_SPLIT_def] THEN
REPEAT STRIP_TAC THEN
CONSEQ_CONV_TAC (K EXISTS_EQ___CONSEQ_CONV) THEN
SIMP_TAC (std_ss++EQUIV_EXTRACT_ss) [] THEN
REPEAT STRIP_TAC THEN
MATCH_MP_TAC var_res_prop___COND___BAG_DIFF_REMOVE THEN
Q.EXISTS_TAC `wpb'` THEN
Q.EXISTS_TAC `wpb'` THEN
FULL_SIMP_TAC std_ss [var_res_prop___COND___REWRITE]);



val VAR_RES_FRAME_SPLIT_NORMALISE = store_thm ("VAR_RES_FRAME_SPLIT_NORMALISE",
``VAR_RES_FRAME_SPLIT f rfc (wpb,rpb) wpb' sfb_context sfb_split sfb_imp sfb_restP =
  VAR_RES_FRAME_SPLIT f (F, NONE) (wpb,rpb) wpb' sfb_context sfb_split sfb_imp sfb_restP``,
SIMP_TAC std_ss [VAR_RES_FRAME_SPLIT_EXPAND]);



val VAR_RES_COND_HOARE_TRIPLE___SOLVE_WEAK_IMP = store_thm (
"VAR_RES_COND_HOARE_TRIPLE___SOLVE_WEAK_IMP",
``!f wpb rpb sfb wpb' rpb' sfb'.
  IS_SEPARATION_COMBINATOR f ==>
  (VAR_RES_COND_HOARE_TRIPLE f
    (var_res_prop f (wpb,rpb) sfb)
    (asl_prog_block [])
    (var_res_prop f (wpb',rpb') sfb') =
   COND_PROP___WEAK_IMP (var_res_prop f (wpb,rpb) sfb)
                       (var_res_prop f (wpb',rpb') sfb'))``,

SIMP_TAC (std_ss++EQUIV_EXTRACT_ss) [
   VAR_RES_COND_HOARE_TRIPLE_def, COND_PROP___WEAK_IMP_def,
   var_res_prop___REWRITE, VAR_RES_HOARE_TRIPLE_def,
   ASL_PROGRAM_HOARE_TRIPLE_def, asl_prog_block_def,
   ASL_PROGRAM_SEM___skip, HOARE_TRIPLE_def,
   fasl_order_THM, asla_skip_def, SUBSET_DEF, IN_ABS,
   IN_SING, VAR_RES_STACK___IS_EQUAL_UPTO_VALUES___REFL]);





val VAR_RES_FRAME_SPLIT___sfb_restP_OK___PURE_PROPOSITION =
store_thm ("VAR_RES_FRAME_SPLIT___sfb_restP_OK___PURE_PROPOSITION",
``IS_SEPARATION_COMBINATOR f /\ BAG_ALL_DISTINCT (BAG_UNION wpb rpb) ==>
VAR_RES_FRAME_SPLIT___sfb_restP_OK f (wpb,rpb)
          (BAG_EVERY (VAR_RES_IS_PURE_PROPOSITION f))``,

STRIP_TAC THEN
SIMP_TAC std_ss [VAR_RES_FRAME_SPLIT___sfb_restP_OK_def] THEN
CONJ_TAC THEN1 (
   Q.EXISTS_TAC `EMPTY_BAG` THEN
   ASM_SIMP_TAC std_ss [BAG_EVERY_THM, IN_DEF,
      var_res_prop___COND___REWRITE, FINITE_BAG_THM,
      NOT_IN_EMPTY_BAG]
) THEN

GEN_TAC THEN
SIMP_TAC std_ss [BAG_EVERY_THM,
      VAR_RES_IS_PURE_PROPOSITION_def,
      IN_ABS, GSYM LEFT_FORALL_IMP_THM] THEN
REPEAT STRIP_TAC THEN
`VAR_RES_IS_PURE_PROPOSITION f (var_res_bigstar f sfb)` by ALL_TAC THEN1 (
   MATCH_MP_TAC (MP_CANON VAR_RES_IS_PURE_PROPOSITION___var_res_bigstar) THEN
   ASM_SIMP_TAC std_ss [BAG_EVERY_THM, VAR_RES_IS_PURE_PROPOSITION___BASIC_PROPS]
) THEN
FULL_SIMP_TAC std_ss [VAR_RES_IS_PURE_PROPOSITION_def]);




val COND_PROP___WEAK_IMP___var_res_prop___SOLVE = store_thm (
  "COND_PROP___WEAK_IMP___var_res_prop___SOLVE",
``!f wpb rpb sfb wpb' rpb' sfb' src.

  ((SET_OF_BAG wpb' SUBSET SET_OF_BAG wpb) /\
   (SET_OF_BAG rpb' SUBSET SET_OF_BAG (BAG_UNION wpb rpb))) ==>

  ((VAR_RES_FRAME_SPLIT f src (wpb,rpb) EMPTY_BAG EMPTY_BAG sfb sfb'
  (BAG_EVERY (VAR_RES_IS_PURE_PROPOSITION f))) ==>

  COND_PROP___WEAK_IMP (var_res_prop f (wpb,rpb) sfb)
                       (var_res_prop f (wpb',rpb') sfb'))``,

SIMP_TAC (std_ss++CONJ_ss) [
    COND_PROP___WEAK_IMP_def,
    var_res_prop___REWRITE,
    SUBSET_DEF, IN_SING,
    IN_SET_OF_BAG, BAG_IN_BAG_UNION,
    VAR_RES_FRAME_SPLIT_def, BAG_EVERY,
    BAG_UNION_EMPTY, BAG_DIFF_EMPTY] THEN
REPEAT STRIP_TAC THEN
`IS_SEPARATION_COMBINATOR f /\ BAG_ALL_DISTINCT (BAG_UNION wpb rpb)` by ALL_TAC THEN1 (
    FULL_SIMP_TAC std_ss [var_res_prop___COND___REWRITE]
) THEN

FULL_SIMP_TAC std_ss [
   VAR_RES_FRAME_SPLIT___sfb_restP_OK___PURE_PROPOSITION] THEN
`var_res_prop___COND f (wpb,rpb) sfb'` by ALL_TAC THEN1 (
   MATCH_MP_TAC var_res_prop___COND___var_set_extend THEN
   Q.EXISTS_TAC `wpb'` THEN Q.EXISTS_TAC `rpb'` THEN
   ASM_SIMP_TAC std_ss [SUBSET_DEF, IN_SET_OF_BAG,
      BAG_IN_BAG_UNION, DISJ_IMP_THM, FORALL_AND_THM] THEN
   FULL_SIMP_TAC std_ss [var_res_prop___COND___REWRITE]
) THEN
FULL_SIMP_TAC std_ss [var_res_prop___COND_UNION] THEN
Q.PAT_ASSUM `!s. X s` (MP_TAC o Q.SPEC `x`) THEN
FULL_SIMP_TAC std_ss [IN_DEF,
   var_res_prop___PROP_UNION, var_res_prop___COND_UNION] THEN
REPEAT STRIP_TAC THEN
Tactical.REVERSE (`s2 IN asl_emp f` by ALL_TAC) THEN1 (
   Tactical.REVERSE (`s1 = SND x` by ALL_TAC) THEN1 (
      Q.PAT_ASSUM `var_res_prop___PROP f (wpb,rpb) sfb' XXX` MP_TAC THEN
      ASM_SIMP_TAC std_ss [var_res_prop___PROP___REWRITE,
          var_res_sl___has_write_permission_def,
          var_res_sl___has_read_permission_def] THEN
      METIS_TAC[]
   ) THEN
   Q.PAT_ASSUM `X = SOME (SND x)` MP_TAC THEN
   Q.PAT_ASSUM `s2 IN asl_emp f` MP_TAC THEN
   FULL_SIMP_TAC std_ss [asl_emp_def, IN_ABS, IS_SEPARATION_COMBINATOR_EXPAND_THM,
         GSYM LEFT_FORALL_IMP_THM]
) THEN
`?st h. x = (st,h)` by (Cases_on `x` THEN SIMP_TAC std_ss []) THEN
Q.PAT_ASSUM `IS_SEPARATION_COMBINATOR f` ASSUME_TAC THEN
FULL_SIMP_TAC std_ss [var_res_prop___PROP___REWRITE,
   IS_SEPARATION_COMBINATOR___VAR_RES_COMBINATOR] THEN
Tactical.REVERSE (`VAR_RES_IS_PURE_PROPOSITION f
   (var_res_bigstar f sfb_rest)` by ALL_TAC) THEN1 (
   FULL_SIMP_TAC std_ss [VAR_RES_IS_PURE_PROPOSITION_def] THEN
   POP_ASSUM (MP_TAC o Q.SPEC `(st, s2)`) THEN
   FULL_SIMP_TAC std_ss []
) THEN
MATCH_MP_TAC (MP_CANON VAR_RES_IS_PURE_PROPOSITION___var_res_bigstar) THEN
ASM_SIMP_TAC std_ss [BAG_EVERY, BAG_IN_BAG_INSERT,
   DISJ_IMP_THM, FORALL_AND_THM,
   VAR_RES_IS_PURE_PROPOSITION___BASIC_PROPS]);



val VAR_RES_COND_HOARE_TRIPLE___SOLVE = store_thm (
"VAR_RES_COND_HOARE_TRIPLE___SOLVE",
``!sr f wpb rpb sfb wpb' rpb' sfb'.

  ((SET_OF_BAG wpb' SUBSET SET_OF_BAG wpb) /\
   (SET_OF_BAG rpb' SUBSET SET_OF_BAG (BAG_UNION wpb rpb))) ==>

  ((VAR_RES_FRAME_SPLIT f sr (wpb,rpb) EMPTY_BAG EMPTY_BAG sfb sfb'
  (BAG_EVERY (VAR_RES_IS_PURE_PROPOSITION f))) ==>

  VAR_RES_COND_HOARE_TRIPLE f
    (var_res_prop f (wpb,rpb) sfb)
    (asl_prog_block [])
    (var_res_prop f (wpb',rpb') sfb'))``,

REPEAT STRIP_TAC THEN
Cases_on `IS_SEPARATION_COMBINATOR f` THENL [
   ASM_SIMP_TAC std_ss [VAR_RES_COND_HOARE_TRIPLE___SOLVE_WEAK_IMP] THEN
   MATCH_MP_TAC (MP_CANON COND_PROP___WEAK_IMP___var_res_prop___SOLVE) THEN
   METIS_TAC[],


   ASM_SIMP_TAC std_ss [VAR_RES_COND_HOARE_TRIPLE_def]
]);



val VAR_RES_COND_HOARE_TRIPLE___SOLVE_skip = save_thm (
"VAR_RES_COND_HOARE_TRIPLE___SOLVE_skip",
SIMP_RULE std_ss [asl_prog_block_def] VAR_RES_COND_HOARE_TRIPLE___SOLVE);




val VAR_RES_COND_INFERENCE___prog_diverge = store_thm (
"VAR_RES_COND_INFERENCE___prog_diverge",
``!f P progL Q.
  VAR_RES_COND_HOARE_TRIPLE f P (asl_prog_block (asl_prog_diverge::progL)) Q``,

SIMP_TAC std_ss [VAR_RES_COND_HOARE_TRIPLE_def,
   VAR_RES_HOARE_TRIPLE_def, ASL_PROGRAM_HOARE_TRIPLE_def,
   HOARE_TRIPLE_def, ASL_PROGRAM_SEM___prog_seq,
   ASL_PROGRAM_SEM___diverge, asla_seq_diverge,
   ASL_PROGRAM_SEM___prog_block] THEN
SIMP_TAC std_ss [asla_diverge_def, fasl_order_THM, EMPTY_SUBSET]);


val VAR_RES_COND_INFERENCE___first_command_REWRITE = store_thm (
"VAR_RES_COND_INFERENCE___first_command_REWRITE",
``!f p1 p1' wpb rpb sfb progL Q.

  (BAG_ALL_DISTINCT (BAG_UNION wpb rpb) ==> (p1 = p1')) ==>

  (VAR_RES_COND_HOARE_TRIPLE f
    (var_res_prop f (wpb,rpb) sfb)
    (asl_prog_block (p1::progL)) Q =
   VAR_RES_COND_HOARE_TRIPLE f
    (var_res_prop f (wpb,rpb) sfb)
    (asl_prog_block (p1'::progL)) Q)``,


REPEAT STRIP_TAC THEN
Cases_on `BAG_ALL_DISTINCT (BAG_UNION wpb rpb)` THENL [
   ASM_SIMP_TAC std_ss [],

   ASM_SIMP_TAC std_ss [VAR_RES_COND_HOARE_TRIPLE_def,
      var_res_prop___REWRITE, var_res_prop___COND___REWRITE]
]);



val VAR_RES_COND_INFERENCE___first_command_PRECOND_SEM = store_thm (
"VAR_RES_COND_INFERENCE___first_command_PRECOND_SEM",
``!f p1 p1' P progL Q.

  (!s. (IS_SEPARATION_COMBINATOR f /\ FST P /\ FST Q /\ (s IN (SND P))) ==>
     (ASL_PROGRAM_SEM (VAR_RES_COMBINATOR f, K asl_false) FEMPTY p1 s =
      ASL_PROGRAM_SEM (VAR_RES_COMBINATOR f, K asl_false) FEMPTY p1' s)) ==>

  (VAR_RES_COND_HOARE_TRIPLE f P
    (asl_prog_block (p1::progL)) Q =
   VAR_RES_COND_HOARE_TRIPLE f P
    (asl_prog_block (p1'::progL)) Q)``,


REPEAT STRIP_TAC THEN
SIMP_TAC std_ss [VAR_RES_COND_HOARE_TRIPLE_def, VAR_RES_HOARE_TRIPLE_def,
   ASL_PROGRAM_HOARE_TRIPLE_def, HOARE_TRIPLE_def,
      IN_ABS, fasl_order_THM] THEN

SIMP_TAC (std_ss++EQUIV_EXTRACT_ss) [] THEN
REPEAT STRIP_TAC THEN
CONSEQ_CONV_TAC (K FORALL_EQ___CONSEQ_CONV) THEN
SIMP_TAC (std_ss++EQUIV_EXTRACT_ss) [] THEN
REPEAT STRIP_TAC THEN
CONSEQ_CONV_TAC (K EXISTS_EQ___CONSEQ_CONV) THEN
SIMP_TAC (std_ss++EQUIV_EXTRACT_ss) [] THEN
REPEAT STRIP_TAC THEN

FULL_SIMP_TAC std_ss [ASL_PROGRAM_SEM___prog_block,
   asla_seq_def]);



val VAR_RES_COND_INFERENCE___var_res_prog_quant_best_local_action = store_thm (
"VAR_RES_COND_INFERENCE___var_res_prog_quant_best_local_action",
``!f P qP qQ progL Q.

  (?x.
    VAR_RES_COND_HOARE_TRIPLE f P
    (asl_prog_block (
        (var_res_prog_best_local_action (qP x) (qQ x))::
        progL))
    Q) ==>

  (VAR_RES_COND_HOARE_TRIPLE f P
    (asl_prog_block (
        (var_res_prog_quant_best_local_action qP qQ)::
        progL))
    Q)``,

REPEAT GEN_TAC THEN
`?P_ap P_cond. P = (P_cond, P_ap)` by (Cases_on `P` THEN SIMP_TAC std_ss []) THEN
`?Q_ap Q_cond. Q = (Q_cond, Q_ap)` by (Cases_on `Q` THEN SIMP_TAC std_ss []) THEN
SIMP_TAC std_ss [VAR_RES_COND_INFERENCE___prog_block] THEN
Q.ABBREV_TAC `prog = asl_prog_block progL` THEN
ASM_SIMP_TAC std_ss [
   VAR_RES_COND_HOARE_TRIPLE_def,
   VAR_RES_HOARE_TRIPLE_def,
   ASL_PROGRAM_HOARE_TRIPLE_def,
   ASL_PROGRAM_SEM___prog_seq] THEN
REPEAT STRIP_TAC THEN
FULL_SIMP_TAC std_ss [] THEN
Q.PAT_ASSUM `!x'. HOARE_TRIPLE (pre x') act (post x')` (MP_TAC o Q.SPEC `x'`) THEN
ASM_SIMP_TAC std_ss [
   var_res_prog_quant_best_local_action_REWRITE,
   var_res_prog_best_local_action_REWRITE,
   ASL_PROGRAM_SEM___prim_command,
   ASL_ATOMIC_ACTION_SEM_def,
   EVAL_asl_prim_command_THM,
   ASL_IS_LOCAL_ACTION___var_res_best_local_action,
   ASL_IS_LOCAL_ACTION___var_res_quant_best_local_action,
   IS_SEPARATION_COMBINATOR___VAR_RES_COMBINATOR] THEN
Q.MATCH_ABBREV_TAC `HOARE_TRIPLE pre (asla_seq a1  a2) post ==>
                    HOARE_TRIPLE pre (asla_seq a1' a2) post` THEN
Tactical.REVERSE (`fasl_action_order a1' a1` by ALL_TAC) THEN1 (
   FULL_SIMP_TAC std_ss [fasl_action_order_POINTWISE_DEF,
     HOARE_TRIPLE_def, fasl_order_THM,
     SOME___asla_seq, GSYM LEFT_EXISTS_AND_THM] THEN
   REPEAT STRIP_TAC THEN
   Q.PAT_ASSUM `!s. s IN pre ==> X s` (MP_TAC o Q.SPEC `s`) THEN
   ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
   Q.PAT_ASSUM `!s. fasl_order (a1' s) (a1 s)` (MP_TAC o Q.SPEC `s`) THEN
   ASM_SIMP_TAC std_ss [fasl_order_THM] THEN STRIP_TAC THEN
   FULL_SIMP_TAC std_ss [SUBSET_DEF, IN_BIGUNION,
    GSYM LEFT_FORALL_IMP_THM, IN_IMAGE, GSYM RIGHT_EXISTS_AND_THM] THEN
   METIS_TAC[]
) THEN
UNABBREV_ALL_TAC THEN

SIMP_TAC std_ss [
   var_res_quant_best_local_action_def,
   var_res_best_local_action_def,
   fasl_action_order_POINTWISE_DEF,
   fasl_order_EVAL,
   SOME___quant_best_local_action,
   SUBSET_DEF, IN_ABS] THEN
REPEAT STRIP_TAC THENL [
   Q.EXISTS_TAC `(x, x')` THEN
   Q.EXISTS_TAC `s0` THEN
   ASM_SIMP_TAC std_ss [],

   Q.PAT_ASSUM `!x''' s0. X x''' s0`
     (MP_TAC o Q.SPECL [`(x, x''')`, `s0'`]) THEN
   ASM_SIMP_TAC std_ss []
]);




val VAR_RES_COND_INFERENCE___var_res_prog_cond_quant_best_local_action = store_thm (
"VAR_RES_COND_INFERENCE___var_res_prog_cond_quant_best_local_action",
``!f P qP qQ progL Q.

  (?x.
    VAR_RES_COND_HOARE_TRIPLE f P
    (asl_prog_block (
        (var_res_prog_cond_best_local_action (qP x) (qQ x))::
        progL))
    Q) ==>

  (VAR_RES_COND_HOARE_TRIPLE f P
    (asl_prog_block (
        (var_res_prog_cond_quant_best_local_action qP qQ)::
        progL))
    Q)``,


SIMP_TAC std_ss [var_res_prog_cond_best_local_action_def,
   var_res_prog_cond_quant_best_local_action_def] THEN
REPEAT STRIP_TAC THEN
SIMP_TAC std_ss [COND_RAND, COND_RATOR, COND_EXPAND_IMP,
  VAR_RES_COND_INFERENCE___prog_diverge] THEN
REPEAT STRIP_TAC THEN
FULL_SIMP_TAC std_ss [] THEN
MATCH_MP_TAC VAR_RES_COND_INFERENCE___var_res_prog_quant_best_local_action THEN
Q.EXISTS_TAC `x` THEN
ASM_SIMP_TAC std_ss []);



val asl_exists___var_res_prop___UNION_PROP_REWRITE =
store_thm ("asl_exists___var_res_prop___UNION_PROP_REWRITE",
``!f wpb rpb sfb sfb'.
  IS_SEPARATION_COMBINATOR f ==>
 ((asl_exists x. var_res_prop___PROP f (wpb,rpb) (BAG_UNION (sfb x) sfb')) =
  var_res_prop___PROP f (wpb,rpb)
    (BAG_UNION {|(asl_exists x. (var_res_bigstar f (sfb x)))|} sfb'))``,

REPEAT STRIP_TAC THEN
ONCE_REWRITE_TAC[FUN_EQ_THM] THEN
ASM_SIMP_TAC std_ss [var_res_prop___PROP___REWRITE,
   var_res_bigstar_REWRITE,
   var_res_bigstar_UNION,
   GSYM asl_exists___asl_star_THM,
   var_res_bigstar___var_res_prop_stack_true___asl_star_ELIM] THEN
SIMP_TAC std_ss [asl_exists_def, IN_ABS, RIGHT_EXISTS_AND_THM]);




val asl_exists___var_res_prop___PROP_REWRITE =
store_thm ("asl_exists___var_res_prop___PROP_REWRITE",
``!f wpb rpb sfb.
  IS_SEPARATION_COMBINATOR f ==>
 ((asl_exists x. var_res_prop___PROP f (wpb,rpb) (sfb x)) =
  var_res_prop___PROP f (wpb,rpb)
        {| (asl_exists x. (var_res_bigstar f (sfb x))) |})``,

REPEAT STRIP_TAC THEN
MP_TAC (Q.SPECL [`f`, `wpb`, `rpb`, `sfb`, `EMPTY_BAG`] asl_exists___var_res_prop___UNION_PROP_REWRITE) THEN
ASM_SIMP_TAC std_ss [BAG_UNION_EMPTY]);




val VAR_RES_COND_INFERENCE___var_res_prog_cond_best_local_action___EXISTS_VAR_CHANGE = store_thm (
"VAR_RES_COND_INFERENCE___var_res_prog_cond_best_local_action___EXISTS_VAR_CHANGE",
``!rfc f wpb rpb sfb wpb' wpb'' rpb' sfb' sfb'' progL Q.
   ((SET_OF_BAG wpb') SUBSET (SET_OF_BAG wpb)) /\
   ((SET_OF_BAG rpb') SUBSET (SET_OF_BAG (BAG_UNION wpb rpb))) ==>

( (?x'. VAR_RES_FRAME_SPLIT f rfc (wpb,rpb) wpb' EMPTY_BAG sfb (sfb' x')
  (\sfb'''. !x''. VAR_RES_COND_HOARE_TRIPLE f
    (var_res_prop f (BAG_UNION (BAG_DIFF wpb wpb') wpb'',rpb) (BAG_UNION (sfb'' x'') sfb'''))
       (asl_prog_block progL) Q)) ==>

  VAR_RES_COND_HOARE_TRIPLE f
    (var_res_prop f (wpb,rpb) sfb)
    (asl_prog_block (
        (var_res_prog_cond_best_local_action
            (COND_PROP___STRONG_EXISTS (\x'.  var_res_prop f (wpb',rpb')  (sfb' x')))
            (COND_PROP___STRONG_EXISTS (\x''. var_res_prop f (wpb'',rpb') (sfb'' x''))))::
        progL))
    Q)``,


REPEAT GEN_TAC THEN
`?Q_ap Q_cond. Q = (Q_cond, Q_ap)` by (Cases_on `Q` THEN SIMP_TAC std_ss []) THEN
SIMP_TAC std_ss [VAR_RES_COND_INFERENCE___prog_block] THEN
Q.ABBREV_TAC `prog = asl_prog_block progL` THEN
ASM_SIMP_TAC std_ss [
   VAR_RES_COND_HOARE_TRIPLE_def,
   COND_PROP___STRONG_EXISTS_def,
   var_res_prop___REWRITE, var_res_prog_cond_best_local_action_def,
   SUBSET_DEF, IN_SET_OF_BAG, BAG_IN_BAG_UNION] THEN
REPEAT STRIP_TAC THEN
Cases_on `(?x'. (~var_res_prop___COND f (wpb',rpb') (sfb' x'))) \/
          (?x''. (~var_res_prop___COND f (wpb'',rpb') (sfb'' x'')))` THEN1 (
   ASM_REWRITE_TAC[] THEN
   REWRITE_TAC [VAR_RES_HOARE_TRIPLE_def,
                ASL_INFERENCE_prog_seq_diverge]
) THEN

FULL_SIMP_TAC std_ss [] THEN
FULL_SIMP_TAC std_ss [VAR_RES_FRAME_SPLIT_def, bagTheory.BAG_UNION_EMPTY] THEN
Q.PAT_ASSUM `X ==> Y` (fn thm => SUBGOAL_THEN (fst (dest_imp (concl thm)))
    (fn thm2 => MP_TAC (MP thm thm2))) THEN1 (

   SIMP_TAC std_ss [VAR_RES_FRAME_SPLIT___sfb_restP_OK___REWRITE,
      var_res_prop___COND_UNION] THEN
   REPEAT STRIP_TAC THEN1 (
      Q.EXISTS_TAC `{|asl_false|}` THEN
      ASM_SIMP_TAC std_ss [VAR_RES_HOARE_TRIPLE_def, var_res_prop___PROP___REWRITE,
         var_res_bigstar_REWRITE, var_res_bigstar_UNION,
         asl_false___asl_star_THM, asl_bool_EVAL, IN_ABS,
         ASL_PROGRAM_HOARE_TRIPLE_REWRITE] THEN
      FULL_SIMP_TAC std_ss [var_res_prop___COND___REWRITE,
         FINITE_BAG_THM, BAG_IN_BAG_INSERT, NOT_IN_EMPTY_BAG,
         VAR_RES_IS_STACK_IMPRECISE___USED_VARS___asl_false,
         BAG_ALL_DISTINCT_BAG_UNION,
         BAG_ALL_DISTINCT_DIFF,
         BAG_DISJOINT_BAG_IN,
         BAG_IN_BAG_DIFF_ALL_DISTINCT] THEN
       METIS_TAC[]
   ) THEN
   ASM_SIMP_TAC std_ss [BAG_UNION_INSERT, BAG_UNION_EMPTY,
      var_res_prop___PROP___asl_exists,
      VAR_RES_INFERENCE___EXISTS_PRE] THEN
   REPEAT STRIP_TAC THEN
   Tactical.REVERSE (Cases_on `sfb''' IN sfbS`) THEN1 (
      ASM_SIMP_TAC std_ss [asl_bool_REWRITES,
         var_res_prop___PROP___asl_false, IN_ABS,
         asl_bool_EVAL,
         VAR_RES_HOARE_TRIPLE_def, ASL_PROGRAM_HOARE_TRIPLE_REWRITE]
   ) THEN
   Q.PAT_ASSUM `!sfb'''. X` (MP_TAC o Q.SPEC `sfb'''`) THEN
   ASM_SIMP_TAC std_ss [asl_bool_REWRITES, BAG_UNION_INSERT,
      var_res_prop___PROP___var_res_bigstar] THEN
   REPEAT STRIP_TAC THEN
   `BAG_UNION sfb''' (sfb'' x'') = BAG_UNION (sfb'' x'') sfb'''` by PROVE_TAC[COMM_BAG_UNION] THEN
   ASM_REWRITE_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN
   Q.PAT_ASSUM `!x. X` MATCH_MP_TAC THEN
   ASM_REWRITE_TAC[] THEN
   MATCH_MP_TAC var_res_prop___COND___var_set_extend THEN
   Q.EXISTS_TAC `BAG_DIFF wpb wpb'` THEN
   Q.EXISTS_TAC `BAG_DIFF rpb wpb'` THEN
   ASM_SIMP_TAC std_ss [SUBSET_DEF, IN_SET_OF_BAG,
      BAG_IN_BAG_UNION, DISJ_IMP_THM,
      FORALL_AND_THM] THEN
   REPEAT STRIP_TAC THENL [
      METIS_TAC [BAG_IN_DIFF_E],
      FULL_SIMP_TAC std_ss [var_res_prop___COND___REWRITE]
   ]
) THEN
FULL_SIMP_TAC std_ss [var_res_prop___COND_UNION] THEN
`!x'. var_res_prop___COND f (wpb,rpb) (sfb' x')` by ALL_TAC THEN1 (
   GEN_TAC THEN
   Q.PAT_ASSUM `!x'. (var_res_prop___COND f (wpb',rpb') (sfb' x'))`
      (MP_TAC o Q.SPEC `x'`) THEN
   Q.PAT_ASSUM `var_res_prop___COND f (wpb,rpb) X` MP_TAC THEN
   ASM_SIMP_TAC std_ss [var_res_prop___COND___REWRITE] THEN
   REPEAT STRIP_TAC THEN
   MATCH_MP_TAC VAR_RES_IS_STACK_IMPRECISE___USED_VARS___SUBSET THEN
   Q.EXISTS_TAC `SET_OF_BAG (BAG_UNION wpb' rpb')` THEN
   ASM_SIMP_TAC std_ss [SUBSET_DEF, BAG_IN_BAG_UNION, IN_SET_OF_BAG,
      DISJ_IMP_THM]
) THEN
FULL_SIMP_TAC std_ss [] THEN
REPEAT STRIP_TAC THEN
Tactical.REVERSE (Cases_on `
   var_res_prop___COND f (BAG_DIFF wpb wpb',BAG_DIFF rpb wpb') sfb'''`) THEN1 (
   FULL_SIMP_TAC std_ss [] THEN
   FULL_SIMP_TAC std_ss [VAR_RES_HOARE_TRIPLE_def, IN_DEF,
      ASL_PROGRAM_HOARE_TRIPLE_REWRITE]
) THEN
`var_res_prop___COND f (wpb,rpb) sfb'''` by ALL_TAC THEN1 (
   MATCH_MP_TAC var_res_prop___COND___BAG_DIFF_REMOVE THEN
   Q.EXISTS_TAC `wpb'` THEN Q.EXISTS_TAC `wpb'` THEN
   ASM_SIMP_TAC std_ss [] THEN
   FULL_SIMP_TAC std_ss [var_res_prop___COND___REWRITE]
) THEN
FULL_SIMP_TAC std_ss [] THEN
Q.ABBREV_TAC `wpb''' = BAG_UNION (BAG_DIFF wpb wpb') wpb''` THEN
Tactical.REVERSE (Cases_on `BAG_ALL_DISTINCT (BAG_UNION wpb''' rpb)`) THEN1 (
   `?pv. BAG_IN pv wpb'' /\ ((~BAG_IN pv rpb) ==>
                     (BAG_IN pv wpb /\ ~(BAG_IN pv wpb')))` by ALL_TAC THEN1 (
       POP_ASSUM MP_TAC THEN
       Q.UNABBREV_TAC `wpb'''` THEN
       FULL_SIMP_TAC std_ss [BAG_ALL_DISTINCT_BAG_UNION,
          var_res_prop___COND___REWRITE, BAG_DISJOINT_BAG_IN,
          BAG_IN_BAG_DIFF_ALL_DISTINCT, BAG_IN_BAG_UNION] THEN
       METIS_TAC[]
   ) THEN
   MATCH_MP_TAC VAR_RES_INFERENCE___prog_seq THEN
   Q.EXISTS_TAC `asl_false` THEN
   ASM_SIMP_TAC std_ss [VAR_RES_HOARE_TRIPLE_def, asl_bool_EVAL,
      ASL_PROGRAM_HOARE_TRIPLE_def, HOARE_TRIPLE_def, IN_ABS,
      ASL_PROGRAM_SEM___prim_command,
      var_res_prog_best_local_action_def,
      asl_prog_quant_best_local_action_def,
      ASL_ATOMIC_ACTION_SEM_def, EVAL_asl_prim_command_THM,
      quant_best_local_action_THM, IS_SEPARATION_COMBINATOR___VAR_RES_COMBINATOR,
      fasl_order_THM, IN_DEF] THEN
   REPEAT STRIP_TAC THEN
   Q.EXISTS_TAC `EMPTY` THEN
   SIMP_TAC std_ss [SOME___quant_best_local_action, EMPTY_SUBSET, IN_ABS] THEN
   SIMP_TAC std_ss [EXTENSION, NOT_IN_EMPTY, IN_ABS] THEN
   HO_MATCH_MP_TAC (prove (``
      ((!x y z. Q x y z ==> P x y) /\ (?x y. !z. Q x y z)) ==>
      ((?x y. P x y) /\ (!z. ?x y. Q x y z))``, METIS_TAC[])) THEN
   SIMP_TAC std_ss [] THEN

   Q.PAT_ASSUM `!s. X s ==> Y s` (MP_TAC o Q.SPEC `x`) THEN
   ASM_SIMP_TAC std_ss [var_res_prop___PROP_UNION, var_res_prop___COND_UNION,
      VAR_RES_COMBINATOR_REWRITE] THEN
   REPEAT STRIP_TAC THEN
   Q.EXISTS_TAC `(VAR_RES_STACK_SPLIT1 (COMPL {pv}) (FST x), s1)` THEN
   Q.EXISTS_TAC `(VAR_RES_STACK_SPLIT2 (COMPL {pv}) (FST x), s2)` THEN
   ASM_SIMP_TAC std_ss [] THEN
   GEN_TAC THEN REPEAT CONJ_TAC THENL [
      SIMP_TAC std_ss [VAR_RES_STACK_COMBINE___VAR_RES_STACK_SPLIT,
         VAR_RES_STACK_SPLIT12___DEF, INTER_EMPTY, COMPL_EMPTY,
         DRESTRICT_UNIV],

      METIS_TAC[IS_SEPARATION_COMBINATOR_def, COMM_DEF],

      Q.EXISTS_TAC `x'` THEN
      Q.PAT_ASSUM `(FST x, s1) IN Y` MP_TAC THEN
      `BAG_ALL_DISTINCT (BAG_UNION wpb rpb)` by FULL_SIMP_TAC std_ss [var_res_prop___COND___REWRITE] THEN
      POP_ASSUM MP_TAC THEN
      ASM_SIMP_TAC std_ss [IN_ABS, var_res_prop___PROP___REWRITE,
         var_res_sl___has_write_permission_def, var_res_sl___has_read_permission_def,
         VAR_RES_STACK_SPLIT12___REWRITES, IN_COMPL, IN_SING,
         BAG_ALL_DISTINCT_BAG_UNION, BAG_DISJOINT_BAG_IN] THEN
      REPEAT STRIP_TAC THENL [
         METIS_TAC[],
         METIS_TAC[],

         Q.MATCH_ABBREV_TAC `xx IN P` THEN
         `VAR_RES_IS_STACK_IMPRECISE___USED_VARS (SET_OF_BAG (BAG_UNION wpb' rpb')) P` by
            METIS_TAC [var_res_prop___COND___EXPAND] THEN
         FULL_SIMP_TAC std_ss [VAR_RES_IS_STACK_IMPRECISE___USED_VARS___ALTERNATIVE_DEF] THEN
         POP_ASSUM MATCH_MP_TAC THEN
         Q.EXISTS_TAC `(FST x, s1)`  THEN
         Q.UNABBREV_TAC `xx` THEN
         ASM_SIMP_TAC std_ss [VAR_RES_STACK_SPLIT12___REWRITES, INTER_SUBSET]
      ],


      ASM_SIMP_TAC std_ss [asl_star_def, IN_SING, IN_ABS,
        VAR_RES_COMBINATOR_REWRITE, SOME___VAR_RES_STACK_COMBINE,
        PAIR_FORALL_THM] THEN
      CCONTR_TAC THEN FULL_SIMP_TAC std_ss [] THEN
      Q.PAT_ASSUM `VAR_RES_STACK_IS_SEPARATE x1 Y` MP_TAC THEN
      SIMP_TAC (std_ss++CONJ_ss) [
         VAR_RES_STACK_IS_SEPARATE_def, IN_SING,
         VAR_RES_STACK_SPLIT12___REWRITES, IN_DIFF, IN_COMPL] THEN
      `var_res_sl___has_write_permission pv x1 /\
       var_res_sl___has_read_permission pv (FST x)` by ALL_TAC THEN1 (
         FULL_SIMP_TAC std_ss [var_res_prop___PROP___REWRITE_2,
            var_res_sl___has_read_permission_def,
            var_res_sl___has_write_permission_def, IN_ABS] THEN
         METIS_TAC[]
      ) THEN
      FULL_SIMP_TAC std_ss [var_res_sl___has_write_permission_def,
         var_res_permission_THM2, var_res_sl___has_read_permission_def]
   ]
) THEN


`(!x''. var_res_prop___COND f (wpb''',rpb) (sfb'' x'')) /\
 var_res_prop___COND f (wpb''',rpb) sfb'''` by ALL_TAC THEN1 (
   Q.PAT_ASSUM `!x''. var_res_prop___COND f (wpb'',rpb') (sfb'' x'')` MP_TAC THEN
   Q.PAT_ASSUM `var_res_prop___COND f (BAG_DIFF wpb wpb',X) sfb'''` MP_TAC THEN
   ASM_SIMP_TAC (std_ss++CONJ_ss) [
      var_res_prop___COND___REWRITE] THEN
   Q.UNABBREV_TAC `wpb'''` THEN
   `BAG_ALL_DISTINCT (BAG_UNION wpb rpb) /\
    BAG_ALL_DISTINCT (BAG_UNION wpb' rpb')` by FULL_SIMP_TAC std_ss [var_res_prop___COND___REWRITE] THEN
   FULL_SIMP_TAC std_ss [BAG_ALL_DISTINCT_BAG_UNION, BAG_DISJOINT_BAG_IN] THEN
   REPEAT STRIP_TAC THEN MATCH_MP_TAC VAR_RES_IS_STACK_IMPRECISE___USED_VARS___SUBSET THENL [
      Q.EXISTS_TAC `SET_OF_BAG (BAG_UNION wpb'' rpb')` THEN
      FULL_SIMP_TAC std_ss [SUBSET_DEF, BAG_IN_BAG_UNION, IN_SET_OF_BAG,
         DISJ_IMP_THM, BAG_IN_BAG_DIFF_ALL_DISTINCT] THEN
      METIS_TAC[],

      Q.EXISTS_TAC `SET_OF_BAG (BAG_UNION (BAG_DIFF wpb wpb') (BAG_DIFF rpb wpb'))` THEN
      ASM_SIMP_TAC std_ss [SUBSET_DEF, BAG_IN_BAG_UNION, IN_SET_OF_BAG,
         DISJ_IMP_THM, BAG_IN_BAG_DIFF_ALL_DISTINCT]
   ]
) THEN
FULL_SIMP_TAC std_ss [] THEN

MATCH_MP_TAC VAR_RES_INFERENCE___prog_seq THEN
Q.EXISTS_TAC `asl_exists x''. var_res_prop___PROP f (wpb''',rpb) (BAG_UNION (sfb'' x'') sfb''')` THEN
Tactical.REVERSE CONJ_TAC THEN1 (
   Q.PAT_ASSUM `!x''. VAR_RES_HOARE_TRIPLE X Y pre prog Q_ap` MP_TAC THEN
   SIMP_TAC std_ss [VAR_RES_HOARE_TRIPLE_def, asl_bool_EVAL,
      ASL_PROGRAM_HOARE_TRIPLE_def, HOARE_TRIPLE_def, IN_ABS]
) THEN

MATCH_MP_TAC VAR_RES_INFERENCE___STRENGTHEN THEN
Q.EXISTS_TAC `var_res_prop___PROP f (wpb,rpb) (BAG_UNION (sfb' x') sfb''')` THEN
Q.EXISTS_TAC `asl_exists x''. var_res_prop___PROP f (wpb''',rpb) (BAG_UNION (sfb'' x'') sfb''')` THEN
ASM_SIMP_TAC std_ss [IN_DEF] THEN

Q.ABBREV_TAC `rpb'' = BAG_DIFF (BAG_UNION wpb rpb) wpb'` THEN
`BAG_ALL_DISTINCT (BAG_UNION wpb rpb)` by FULL_SIMP_TAC std_ss [var_res_prop___COND___EXPAND] THEN
`BAG_ALL_DISTINCT rpb''` by PROVE_TAC[BAG_ALL_DISTINCT_DIFF] THEN
`!x. BAG_IN x rpb'' = BAG_IN x (BAG_UNION wpb rpb) /\ ~(BAG_IN x wpb')` by ALL_TAC THEN1 (
   Q.UNABBREV_TAC `rpb''` THEN ASM_SIMP_TAC std_ss [BAG_IN_BAG_DIFF_ALL_DISTINCT]
) THEN
`BAG_UNION wpb' rpb'' = BAG_UNION wpb rpb` by ALL_TAC THEN1 (
   `BAG_ALL_DISTINCT (BAG_UNION wpb' rpb'')` by ALL_TAC THEN1 (
      FULL_SIMP_TAC std_ss [BAG_ALL_DISTINCT_BAG_UNION, var_res_prop___COND___EXPAND,
         BAG_DISJOINT_BAG_IN] THEN
      METIS_TAC[]
   ) THEN
   ASM_SIMP_TAC std_ss [BAG_ALL_DISTINCT_EXTENSION,
      BAG_IN_BAG_UNION] THEN
   GEN_TAC THEN
   Cases_on `BAG_IN x wpb'` THEN ASM_SIMP_TAC std_ss []
) THEN

`BAG_UNION wpb'' rpb'' = BAG_UNION wpb''' rpb` by ALL_TAC THEN1 (
   Q.PAT_ASSUM `BAG_ALL_DISTINCT (BAG_UNION wpb''' rpb)` MP_TAC THEN
   Q.UNABBREV_TAC `wpb'''` THEN
   FULL_SIMP_TAC std_ss [BAG_ALL_DISTINCT_BAG_UNION,
      BAG_ALL_DISTINCT_DIFF, BAG_DISJOINT_BAG_IN, BAG_IN_BAG_UNION,
      BAG_IN_BAG_DIFF_ALL_DISTINCT] THEN
   REPEAT STRIP_TAC THEN
   `BAG_ALL_DISTINCT (BAG_UNION wpb'' rpb'')` by ALL_TAC THEN1 (
      FULL_SIMP_TAC std_ss [BAG_ALL_DISTINCT_BAG_UNION, var_res_prop___COND___EXPAND,
         BAG_DISJOINT_BAG_IN] THEN
      METIS_TAC[]
   ) THEN
   `BAG_ALL_DISTINCT (BAG_UNION (BAG_UNION (BAG_DIFF wpb wpb') wpb'') rpb)` by ALL_TAC THEN1 (
      ASM_SIMP_TAC std_ss [BAG_ALL_DISTINCT_BAG_UNION,
         BAG_ALL_DISTINCT_DIFF, BAG_DISJOINT_BAG_IN, BAG_IN_BAG_UNION,
         BAG_IN_BAG_DIFF_ALL_DISTINCT]
   ) THEN
   ASM_SIMP_TAC std_ss [BAG_ALL_DISTINCT_EXTENSION,
      BAG_IN_BAG_UNION, BAG_IN_BAG_DIFF_ALL_DISTINCT] THEN
   METIS_TAC[]
) THEN


Q.SPEC_TAC (`x'`, `x'`) THEN
ASM_SIMP_TAC std_ss [GSYM VAR_RES_INFERENCE___EXISTS_PRE,
   asl_exists___var_res_prop___PROP_REWRITE,
   asl_exists___var_res_prop___UNION_PROP_REWRITE] THEN
Q.ABBREV_TAC `xsfb' = {|asl_exists x'.
    var_res_bigstar f (sfb' x')|}` THEN
Q.ABBREV_TAC `xsfb'' = {|asl_exists x''.
    var_res_bigstar f (sfb'' x'')|}` THEN

MATCH_MP_TAC VAR_RES_INFERENCE___STRENGTHEN_PERMS THEN
Q.EXISTS_TAC `wpb'` THEN Q.EXISTS_TAC `wpb''` THEN Q.EXISTS_TAC `rpb''` THEN
CONJ_TAC THEN1 (
   Q.UNABBREV_TAC `wpb'''` THEN
   FULL_SIMP_TAC std_ss [BAG_IN_BAG_UNION, BAG_ALL_DISTINCT_BAG_UNION,
      BAG_IN_BAG_DIFF_ALL_DISTINCT, BAG_DISJOINT_BAG_IN] THEN
   METIS_TAC[]
) THEN

Tactical.REVERSE (`?wpb''' rpb'''.
(var_res_prop___PROP f (wpb',rpb'') (BAG_UNION xsfb' sfb''') =
 asl_star (VAR_RES_COMBINATOR f)
   (var_res_prop___PROP f (wpb',rpb') xsfb')
   (var_res_prop___PROP f (wpb''',rpb''') sfb''')) /\
(var_res_prop___PROP f (wpb'',rpb'') (BAG_UNION xsfb'' sfb''') =
 asl_star (VAR_RES_COMBINATOR f)
   (var_res_prop___PROP f (wpb'',rpb') xsfb'')
   (var_res_prop___PROP f (wpb''',rpb''') sfb'''))` by ALL_TAC) THEN1 (
   ASM_SIMP_TAC std_ss [] THEN
   MATCH_MP_TAC VAR_RES_INFERENCE___FRAME THEN
   ASM_SIMP_TAC std_ss [VAR_RES_HOARE_TRIPLE_def,
      var_res_prog_best_local_action_def,
      ASL_PROGRAM_HOARE_TRIPLE_def,
      asl_prog_quant_best_local_action_def,
      ASL_PROGRAM_SEM___prim_command,
      ASL_ATOMIC_ACTION_SEM_def, EVAL_asl_prim_command_THM,
      quant_best_local_action_THM, IS_SEPARATION_COMBINATOR___VAR_RES_COMBINATOR] THEN
   HO_MATCH_MP_TAC (
      el 2 (BODY_CONJUNCTS (SIMP_RULE std_ss [IMP_CONJ_THM, FORALL_AND_THM] quant_best_local_action_THM))) THEN
   ASM_SIMP_TAC std_ss [IS_SEPARATION_COMBINATOR___VAR_RES_COMBINATOR]
) THEN
Q.EXISTS_TAC `EMPTY_BAG` THEN Q.EXISTS_TAC `rpb''` THEN
MP_TAC (Q.SPECL [`f`, `wpb'`, `EMPTY_BAG`, `rpb'`, `rpb''`, `xsfb'`, `sfb'''`]
   asl_star___var_res_prop___PROP) THEN
MP_TAC (Q.SPECL [`f`, `wpb''`, `EMPTY_BAG`, `rpb'`, `rpb''`, `xsfb''`, `sfb'''`]
   asl_star___var_res_prop___PROP) THEN


`BAG_DISJOINT wpb'' rpb'' /\ BAG_DISJOINT wpb' rpb''` by ALL_TAC THEN1 (
   Q.PAT_ASSUM `BAG_ALL_DISTINCT (BAG_UNION wpb''' rpb)` MP_TAC THEN
   Q.UNABBREV_TAC `wpb'''` THEN
   FULL_SIMP_TAC std_ss [
      BAG_DISJOINT_BAG_IN, BAG_ALL_DISTINCT_BAG_UNION,
      BAG_IN_BAG_UNION, BAG_IN_BAG_DIFF_ALL_DISTINCT] THEN
   METIS_TAC[]
) THEN
`BAG_MERGE rpb' rpb'' = rpb''` by ALL_TAC THEN1 (
   `BAG_ALL_DISTINCT (BAG_MERGE rpb' rpb'') /\
    BAG_DISJOINT wpb' rpb'` by
      FULL_SIMP_TAC std_ss [BAG_ALL_DISTINCT_BAG_MERGE, var_res_prop___COND___EXPAND,
         BAG_ALL_DISTINCT_BAG_UNION] THEN
   ASM_SIMP_TAC std_ss [BAG_ALL_DISTINCT_EXTENSION] THEN
   FULL_SIMP_TAC std_ss [BAG_IN_BAG_UNION, BAG_IN_BAG_MERGE,
      BAG_DISJOINT_BAG_IN] THEN
   METIS_TAC[]
) THEN
`var_res_prop___COND f (EMPTY_BAG,rpb'') sfb'''` by ALL_TAC THEN1 (
   Q.PAT_ASSUM `var_res_prop___COND f (BAG_DIFF wpb wpb', X) sfb'''` MP_TAC THEN
   ASM_SIMP_TAC std_ss [var_res_prop___COND___REWRITE, BAG_UNION_EMPTY] THEN
   Tactical.REVERSE (`
      SET_OF_BAG (BAG_UNION (BAG_DIFF wpb wpb') (BAG_DIFF rpb wpb')) =
      (SET_OF_BAG rpb'')` by ALL_TAC) THEN1 ASM_SIMP_TAC std_ss [] THEN
   FULL_SIMP_TAC std_ss [BAG_ALL_DISTINCT_BAG_UNION] THEN
   ASM_SIMP_TAC (std_ss++EQUIV_EXTRACT_ss) [EXTENSION, IN_SET_OF_BAG,
      BAG_IN_BAG_UNION, BAG_IN_BAG_DIFF_ALL_DISTINCT]
) THEN
`var_res_prop___COND f (wpb' ,rpb') xsfb' /\
 var_res_prop___COND f (wpb'',rpb') xsfb''` by ALL_TAC THEN1 (
   UNABBREV_ALL_TAC THEN
   Q.PAT_ASSUM `!x'. var_res_prop___COND f (wpb', rpb') (sfb' x')` MP_TAC THEN
   Q.PAT_ASSUM `!x''. var_res_prop___COND f (wpb'', rpb') (sfb'' x'')` MP_TAC THEN
   ASM_SIMP_TAC std_ss [var_res_prop___COND___REWRITE,
      FINITE_BAG_THM, BAG_IN_BAG_INSERT, NOT_IN_EMPTY_BAG] THEN
   CONSEQ_HO_REWRITE_TAC ([], [
      VAR_RES_IS_STACK_IMPRECISE___USED_VARS___asl_exists_direct,
      MP_CANON VAR_RES_IS_STACK_IMPRECISE___USED_VARS___var_res_bigstar], []) THEN
   ASM_SIMP_TAC std_ss [BAG_INSERT_NOT_EMPTY, BAG_IN_BAG_INSERT,
     DISJ_IMP_THM, FORALL_AND_THM, BAG_EVERY] THEN
   METIS_TAC[]
) THEN
ASM_SIMP_TAC std_ss [BAG_DISJOINT_EMPTY, BAG_UNION_EMPTY]);



val VAR_RES_COND_INFERENCE___var_res_prog_cond_best_local_action___VAR_CHANGE = store_thm (
"VAR_RES_COND_INFERENCE___var_res_prog_cond_best_local_action___VAR_CHANGE",
``!rfc f wpb rpb sfb wpb' wpb'' rpb' sfb' sfb'' progL Q.
   ((SET_OF_BAG wpb') SUBSET (SET_OF_BAG wpb)) /\
   ((SET_OF_BAG rpb') SUBSET (SET_OF_BAG (BAG_UNION wpb rpb))) ==>

( VAR_RES_FRAME_SPLIT f rfc (wpb,rpb) wpb' EMPTY_BAG sfb sfb'
  (\sfb'''. VAR_RES_COND_HOARE_TRIPLE f
    (var_res_prop f (BAG_UNION (BAG_DIFF wpb wpb') wpb'',rpb) (BAG_UNION sfb'' sfb'''))
       (asl_prog_block progL) Q) ==>

  VAR_RES_COND_HOARE_TRIPLE f
    (var_res_prop f (wpb,rpb) sfb)
    (asl_prog_block (
        (var_res_prog_cond_best_local_action
            (var_res_prop f (wpb',rpb') sfb')
            (var_res_prop f (wpb'',rpb') sfb''))::
        progL))
    Q)``,

REPEAT STRIP_TAC THEN
`!f wpb sfb. (var_res_prop f (wpb,rpb') sfb) =
 (COND_PROP___STRONG_EXISTS (\x:unit. (var_res_prop f (wpb,rpb') sfb)))` by
  REWRITE_TAC[COND_PROP___STRONG_EXISTS___ELIM] THEN
ONCE_ASM_REWRITE_TAC[] THEN POP_ASSUM (K ALL_TAC) THEN

HO_MATCH_MP_TAC (MP_CANON
   VAR_RES_COND_INFERENCE___var_res_prog_cond_best_local_action___EXISTS_VAR_CHANGE) THEN
Q.EXISTS_TAC `rfc` THEN
ASM_SIMP_TAC std_ss [] THEN
METIS_TAC[]);




val VAR_RES_COND_INFERENCE___var_res_prog_cond_best_local_action___EXISTS = store_thm (
"VAR_RES_COND_INFERENCE___var_res_prog_cond_best_local_action___EXISTS",
``!rfc f wpb rpb sfb wpb' rpb' sfb' sfb'' progL Q.
   ((SET_OF_BAG wpb') SUBSET (SET_OF_BAG wpb)) /\
   ((SET_OF_BAG rpb') SUBSET (SET_OF_BAG (BAG_UNION wpb rpb))) ==>

( (?x'. VAR_RES_FRAME_SPLIT f rfc (wpb,rpb) wpb' EMPTY_BAG sfb (sfb' x')
  (\sfb'''. !x''. VAR_RES_COND_HOARE_TRIPLE f
    (var_res_prop f (wpb,rpb) (BAG_UNION (sfb'' x'') sfb'''))
       (asl_prog_block progL) Q)) ==>

  VAR_RES_COND_HOARE_TRIPLE f
    (var_res_prop f (wpb,rpb) sfb)
    (asl_prog_block (
        (var_res_prog_cond_best_local_action
            (COND_PROP___STRONG_EXISTS (\x'. var_res_prop f (wpb',rpb') (sfb' x')))
            (COND_PROP___STRONG_EXISTS (\x''. var_res_prop f (wpb',rpb') (sfb'' x'')))::
        progL)))
    Q)``,


REPEAT STRIP_TAC THEN
Tactical.REVERSE (Cases_on `BAG_ALL_DISTINCT (BAG_UNION wpb rpb) /\
                            BAG_ALL_DISTINCT (BAG_UNION wpb' rpb')`) THEN1 (
   FULL_SIMP_TAC std_ss [VAR_RES_COND_HOARE_TRIPLE_def,
      var_res_prop___REWRITE, var_res_prop___COND___REWRITE,
      var_res_prog_cond_best_local_action_def,
      COND_PROP___STRONG_EXISTS___ELIM] THEN
   DISCH_TAC THEN POP_ASSUM (K ALL_TAC) THEN
   SIMP_TAC std_ss [VAR_RES_HOARE_TRIPLE_def,
      ASL_PROGRAM_HOARE_TRIPLE_def, HOARE_TRIPLE_def,
      ASL_PROGRAM_SEM___diverge, ASL_PROGRAM_SEM___prog_seq,
      asla_seq_diverge, fasl_order_THM, ASL_PROGRAM_SEM___prog_block] THEN
   SIMP_TAC std_ss [asla_diverge_def, EMPTY_SUBSET]
) THEN
HO_MATCH_MP_TAC (MP_CANON VAR_RES_COND_INFERENCE___var_res_prog_cond_best_local_action___EXISTS_VAR_CHANGE) THEN
ASM_SIMP_TAC std_ss [] THEN
Q.LIST_EXISTS_TAC [`rfc`, `x'`] THEN
Tactical.REVERSE (`BAG_UNION (BAG_DIFF wpb wpb') wpb' = wpb` by ALL_TAC) THEN1 ASM_REWRITE_TAC[] THEN

`BAG_ALL_DISTINCT wpb /\ BAG_ALL_DISTINCT (BAG_UNION (BAG_DIFF wpb wpb') wpb')` by ALL_TAC THEN1 (
   FULL_SIMP_TAC std_ss [BAG_ALL_DISTINCT_BAG_UNION,
      BAG_ALL_DISTINCT_DIFF, BAG_DISJOINT_BAG_IN, BAG_IN_BAG_DIFF_ALL_DISTINCT] THEN
   METIS_TAC[]
) THEN
FULL_SIMP_TAC std_ss [
   BAG_ALL_DISTINCT_EXTENSION, BAG_IN_BAG_DIFF_ALL_DISTINCT, BAG_IN_BAG_UNION,
   SUBSET_DEF, IN_SET_OF_BAG] THEN
METIS_TAC[]);




val VAR_RES_COND_INFERENCE___var_res_prog_cond_best_local_action = store_thm (
"VAR_RES_COND_INFERENCE___var_res_prog_cond_best_local_action",
``!rfc f wpb rpb sfb wpb' rpb' sfb' sfb'' progL Q.
   ((SET_OF_BAG wpb') SUBSET (SET_OF_BAG wpb)) /\
   ((SET_OF_BAG rpb') SUBSET (SET_OF_BAG (BAG_UNION wpb rpb))) ==>

( VAR_RES_FRAME_SPLIT f rfc (wpb,rpb) wpb' EMPTY_BAG sfb sfb'
  (\sfb'''. VAR_RES_COND_HOARE_TRIPLE f
    (var_res_prop f (wpb,rpb) (BAG_UNION sfb'' sfb'''))
       (asl_prog_block progL) Q) ==>

  VAR_RES_COND_HOARE_TRIPLE f
    (var_res_prop f (wpb,rpb) sfb)
    (asl_prog_block (
        (var_res_prog_cond_best_local_action
            (var_res_prop f (wpb',rpb') sfb')
            (var_res_prop f (wpb',rpb') sfb''))::
        progL))
    Q)``,

REPEAT STRIP_TAC THEN
`!f wpb sfb. (var_res_prop f (wpb,rpb') sfb) =
 (COND_PROP___STRONG_EXISTS (\x:unit. (var_res_prop f (wpb,rpb') sfb)))` by
  REWRITE_TAC[COND_PROP___STRONG_EXISTS___ELIM] THEN
ONCE_ASM_REWRITE_TAC[] THEN POP_ASSUM (K ALL_TAC) THEN
HO_MATCH_MP_TAC
   (MP_CANON VAR_RES_COND_INFERENCE___var_res_prog_cond_best_local_action___EXISTS) THEN
Q.EXISTS_TAC `rfc` THEN
ASM_SIMP_TAC std_ss []);



val VAR_RES_FRAME_SPLIT___IMP_OK_def = Define
`VAR_RES_FRAME_SPLIT___IMP_OK f (wpb,rpb)
     sfb_context' sfb_split' sfb_imp'
     sfb_context  sfb_split  sfb_imp =

   !sfb_rest s.
      var_res_prop___COND f (wpb,rpb) sfb_rest ==>

      ((var_res_prop___COND f (wpb,rpb) sfb_context /\
        var_res_prop___COND f (wpb,rpb) sfb_split /\
        var_res_prop___COND f (wpb,rpb) sfb_imp /\
        var_res_prop___PROP f (wpb,rpb) (sfb_split + sfb_context) s ==>
        var_res_prop___PROP f (wpb,rpb) (sfb_imp + (sfb_rest + sfb_context)) s) ==>
       (var_res_prop___COND f (wpb,rpb) sfb_context' /\
        var_res_prop___COND f (wpb,rpb) sfb_split' /\
        var_res_prop___COND f (wpb,rpb) sfb_imp' /\
        var_res_prop___PROP f (wpb,rpb) (sfb_split' + sfb_context') s ==>
        var_res_prop___PROP f (wpb,rpb) (sfb_imp' + (sfb_rest + sfb_context')) s))`




val VAR_RES_FRAME_SPLIT___REWRITE_OK_def = Define
`VAR_RES_FRAME_SPLIT___REWRITE_OK f (wpb,rpb)
     sfb_context  sfb_split  sfb_imp
     sfb_context' sfb_split' sfb_imp' =

   !sfb_rest s.
      var_res_prop___COND f (wpb,rpb) sfb_rest ==>

      ((var_res_prop___COND f (wpb,rpb) sfb_context /\
        var_res_prop___COND f (wpb,rpb) sfb_split /\
        var_res_prop___COND f (wpb,rpb) sfb_imp /\
        var_res_prop___PROP f (wpb,rpb) (sfb_split + sfb_context) s ==>
        var_res_prop___PROP f (wpb,rpb) (sfb_imp + (sfb_rest + sfb_context)) s) =
       (var_res_prop___COND f (wpb,rpb) sfb_context' /\
        var_res_prop___COND f (wpb,rpb) sfb_split' /\
        var_res_prop___COND f (wpb,rpb) sfb_imp' /\
        var_res_prop___PROP f (wpb,rpb) (sfb_split' + sfb_context') s ==>
        var_res_prop___PROP f (wpb,rpb) (sfb_imp' + (sfb_rest + sfb_context')) s))`



val VAR_RES_FRAME_SPLIT___REWRITE_OK___IMP_REWRITE =
store_thm ("VAR_RES_FRAME_SPLIT___REWRITE_OK___IMP_REWRITE",
``VAR_RES_FRAME_SPLIT___REWRITE_OK f (wpb,rpb)
     sfb_context  sfb_split  sfb_imp
     sfb_context' sfb_split' sfb_imp' =
  (VAR_RES_FRAME_SPLIT___IMP_OK f (wpb,rpb)
     sfb_context  sfb_split  sfb_imp
     sfb_context' sfb_split' sfb_imp' /\
  VAR_RES_FRAME_SPLIT___IMP_OK f (wpb,rpb)
     sfb_context' sfb_split' sfb_imp'
     sfb_context  sfb_split  sfb_imp)``,

SIMP_TAC std_ss [VAR_RES_FRAME_SPLIT___IMP_OK_def,
   VAR_RES_FRAME_SPLIT___REWRITE_OK_def] THEN
METIS_TAC[]);


val VAR_RES_FRAME_SPLIT___REWRITE_OK___REWRITE =
store_thm ("VAR_RES_FRAME_SPLIT___REWRITE_OK___REWRITE",
``VAR_RES_FRAME_SPLIT___REWRITE_OK f (wpb,rpb)
     sfb_context  sfb_split  sfb_imp
     sfb_context' sfb_split' sfb_imp' =
  !sfb_rest s.
      BAG_ALL_DISTINCT (BAG_UNION wpb rpb) /\
      IS_SEPARATION_COMBINATOR f /\
      var_res_prop___COND f (wpb,rpb) sfb_rest ==>

      ((var_res_prop___COND f (wpb,rpb) sfb_context /\
        var_res_prop___COND f (wpb,rpb) sfb_split /\
        var_res_prop___COND f (wpb,rpb) sfb_imp /\
        var_res_prop___PROP f (wpb,rpb) (sfb_split + sfb_context) s ==>
        var_res_prop___PROP f (wpb,rpb) (sfb_imp + (sfb_rest + sfb_context)) s) =
       (var_res_prop___COND f (wpb,rpb) sfb_context' /\
        var_res_prop___COND f (wpb,rpb) sfb_split' /\
        var_res_prop___COND f (wpb,rpb) sfb_imp' /\
        var_res_prop___PROP f (wpb,rpb) (sfb_split' + sfb_context') s ==>
        var_res_prop___PROP f (wpb,rpb) (sfb_imp' + (sfb_rest + sfb_context')) s))``,

SIMP_TAC std_ss [VAR_RES_FRAME_SPLIT___REWRITE_OK_def] THEN
EQ_TAC THEN SIMP_TAC std_ss [] THEN
REPEAT STRIP_TAC THEN
FULL_SIMP_TAC std_ss [var_res_prop___COND___REWRITE]);



val VAR_RES_FRAME_SPLIT___IMP_OK___REWRITE =
store_thm ("VAR_RES_FRAME_SPLIT___IMP_OK___REWRITE",
``VAR_RES_FRAME_SPLIT___IMP_OK f (wpb,rpb)
     sfb_context' sfb_split' sfb_imp'
     sfb_context  sfb_split  sfb_imp  =
  !sfb_rest s.
      BAG_ALL_DISTINCT (BAG_UNION wpb rpb) /\
      IS_SEPARATION_COMBINATOR f /\
      var_res_prop___COND f (wpb,rpb) sfb_rest /\
      var_res_prop___COND f (wpb,rpb) sfb_context' /\
      var_res_prop___COND f (wpb,rpb) sfb_split' /\
      var_res_prop___COND f (wpb,rpb) sfb_imp' /\
      var_res_prop___PROP f (wpb,rpb) (sfb_split' + sfb_context') s ==>

      ((var_res_prop___COND f (wpb,rpb) sfb_context /\
       var_res_prop___COND f (wpb,rpb) sfb_split /\
       var_res_prop___COND f (wpb,rpb) sfb_imp /\
       var_res_prop___PROP f (wpb,rpb) (sfb_split + sfb_context) s ==>
       var_res_prop___PROP f (wpb,rpb) (sfb_imp + (sfb_rest + sfb_context)) s) ==>
       var_res_prop___PROP f (wpb,rpb) (sfb_imp' + (sfb_rest + sfb_context')) s)``,

SIMP_TAC std_ss [VAR_RES_FRAME_SPLIT___IMP_OK_def] THEN
EQ_TAC THEN SIMP_TAC std_ss [] THEN
REPEAT STRIP_TAC THEN
FULL_SIMP_TAC std_ss [var_res_prop___COND___REWRITE]);



val VAR_RES_FRAME_SPLIT___IMP_OK___THM = store_thm (
"VAR_RES_FRAME_SPLIT___IMP_OK___THM",
``!f strong_rest wpb rpb wpb' sfb_context sfb_split sfb_imp
   sfb_context' sfb_split' sfb_imp' sfb_restP.

  VAR_RES_FRAME_SPLIT___IMP_OK f (wpb,rpb)
     sfb_context  sfb_split  sfb_imp
     sfb_context' sfb_split' sfb_imp' ==>

  (VAR_RES_FRAME_SPLIT f strong_rest (wpb,rpb) wpb' sfb_context'
           sfb_split' sfb_imp' sfb_restP ==>
   VAR_RES_FRAME_SPLIT f strong_rest (wpb,rpb) wpb' sfb_context
           sfb_split sfb_imp sfb_restP)``,


SIMP_TAC std_ss [VAR_RES_FRAME_SPLIT_EXPAND,
   VAR_RES_FRAME_SPLIT___IMP_OK_def] THEN
REPEAT STRIP_TAC THEN
FULL_SIMP_TAC std_ss [] THEN
Q.EXISTS_TAC `sfb_rest` THEN
Q.PAT_ASSUM `!sfb_rest s. X` (MP_TAC o Q.SPECL [`sfb_rest`]) THEN
FULL_SIMP_TAC std_ss [var_res_prop___COND_UNION]);



val VAR_RES_FRAME_SPLIT___REWRITE_OK___THM = store_thm (
"VAR_RES_FRAME_SPLIT___REWRITE_OK___THM",
``!f strong_rest wpb rpb wpb' sfb_context sfb_split sfb_imp
   sfb_context' sfb_split' sfb_imp' sfb_restP.

  VAR_RES_FRAME_SPLIT___REWRITE_OK f (wpb,rpb)
     sfb_context  sfb_split  sfb_imp
     sfb_context' sfb_split' sfb_imp' ==>

  (VAR_RES_FRAME_SPLIT f strong_rest (wpb,rpb) wpb' sfb_context
           sfb_split sfb_imp sfb_restP =
   VAR_RES_FRAME_SPLIT f strong_rest (wpb,rpb) wpb' sfb_context'
           sfb_split' sfb_imp' sfb_restP)``,


SIMP_TAC (std_ss++EQUIV_EXTRACT_ss) [VAR_RES_FRAME_SPLIT_EXPAND,
   VAR_RES_FRAME_SPLIT___REWRITE_OK_def] THEN
REPEAT STRIP_TAC THEN
CONSEQ_CONV_TAC (K EXISTS_EQ___CONSEQ_CONV) THEN
SIMP_TAC (std_ss++EQUIV_EXTRACT_ss) [GSYM RIGHT_FORALL_IMP_THM,
   var_res_prop___COND_UNION] THEN
METIS_TAC[]);



val VAR_RES_FRAME_SPLIT___REWRITE_OK___SYM =
store_thm ("VAR_RES_FRAME_SPLIT___REWRITE_OK___SYM",
``VAR_RES_FRAME_SPLIT___REWRITE_OK f (wpb,rpb)
     sfb_context  sfb_split  sfb_imp
     sfb_context' sfb_split' sfb_imp' =
  VAR_RES_FRAME_SPLIT___REWRITE_OK f (wpb,rpb)
     sfb_context' sfb_split' sfb_imp'
     sfb_context  sfb_split  sfb_imp``,
SIMP_TAC std_ss [VAR_RES_FRAME_SPLIT___REWRITE_OK_def] THEN
REPEAT STRIP_TAC THEN EQ_TAC THEN ASM_SIMP_TAC std_ss [])


val VAR_RES_FRAME_SPLIT___REWRITE_OK___EQ_REWRITE =
store_thm ("VAR_RES_FRAME_SPLIT___REWRITE_OK___EQ_REWRITE",
``VAR_RES_FRAME_SPLIT___REWRITE_OK f (wpb,rpb)
     sfb_context  sfb_split  sfb_imp
     sfb_context' sfb_split' sfb_imp' =

  (VAR_RES_FRAME_SPLIT___REWRITE_OK f (wpb,rpb)
     sfb_context  sfb_split  sfb_imp =
   VAR_RES_FRAME_SPLIT___REWRITE_OK f (wpb,rpb)
     sfb_context' sfb_split'  sfb_imp')``,

SIMP_TAC std_ss [VAR_RES_FRAME_SPLIT___REWRITE_OK_def,
   FUN_EQ_THM] THEN
REPEAT STRIP_TAC THEN EQ_TAC THEN ASM_SIMP_TAC std_ss [])




val VAR_RES_FRAME_SPLIT___IMP_OK___asl_star = store_thm (
"VAR_RES_FRAME_SPLIT___IMP_OK___asl_star",
``!P1 P2 f wpb rpb sfb_context sfb_split sfb_imp
   sfb_context' sfb_split' sfb_imp'.

  (VAR_RES_IS_STACK_IMPRECISE___USED_VARS
      (SET_OF_BAG (BAG_UNION wpb rpb)) P1) /\
  (VAR_RES_IS_STACK_IMPRECISE___USED_VARS
      (SET_OF_BAG (BAG_UNION wpb rpb)) P2) ==>

((VAR_RES_FRAME_SPLIT___IMP_OK f (wpb,rpb)
   (BAG_INSERT (asl_star (VAR_RES_COMBINATOR f) P1 P2) sfb_context)
       sfb_split sfb_imp
   sfb_context' sfb_split' sfb_imp' =
 VAR_RES_FRAME_SPLIT___IMP_OK f (wpb,rpb)
   (BAG_INSERT P1 (BAG_INSERT P2 sfb_context)) sfb_split  sfb_imp
   sfb_context' sfb_split' sfb_imp') /\

(VAR_RES_FRAME_SPLIT___IMP_OK f (wpb,rpb)
    sfb_context sfb_split sfb_imp
   (BAG_INSERT (asl_star (VAR_RES_COMBINATOR f) P1 P2) sfb_context')
       sfb_split' sfb_imp' =
 VAR_RES_FRAME_SPLIT___IMP_OK f (wpb,rpb)
   sfb_context sfb_split  sfb_imp
   (BAG_INSERT P1 (BAG_INSERT P2 sfb_context')) sfb_split' sfb_imp') /\

(VAR_RES_FRAME_SPLIT___IMP_OK f (wpb,rpb)
    sfb_context  (BAG_INSERT (asl_star (VAR_RES_COMBINATOR f) P1 P2) sfb_split) sfb_imp
    sfb_context' sfb_split' sfb_imp' =
 VAR_RES_FRAME_SPLIT___IMP_OK f (wpb,rpb)
   sfb_context (BAG_INSERT P1 (BAG_INSERT P2 sfb_split)) sfb_imp
   sfb_context' sfb_split' sfb_imp') /\

(VAR_RES_FRAME_SPLIT___IMP_OK f (wpb,rpb)
   sfb_context sfb_split sfb_imp
   sfb_context' (BAG_INSERT (asl_star (VAR_RES_COMBINATOR f) P1 P2) sfb_split') sfb_imp' =
 VAR_RES_FRAME_SPLIT___IMP_OK f (wpb,rpb)
   sfb_context sfb_split  sfb_imp
   sfb_context' (BAG_INSERT P1 (BAG_INSERT P2 sfb_split')) sfb_imp') /\

(VAR_RES_FRAME_SPLIT___IMP_OK f (wpb,rpb)
    sfb_context  sfb_split  (BAG_INSERT (asl_star (VAR_RES_COMBINATOR f) P1 P2) sfb_imp)
    sfb_context' sfb_split' sfb_imp' =
 VAR_RES_FRAME_SPLIT___IMP_OK f (wpb,rpb)
   sfb_context  sfb_split (BAG_INSERT P1 (BAG_INSERT P2 sfb_imp))
   sfb_context' sfb_split' sfb_imp') /\

(VAR_RES_FRAME_SPLIT___IMP_OK f (wpb,rpb)
    sfb_context sfb_split sfb_imp
    sfb_context' sfb_split' (BAG_INSERT (asl_star (VAR_RES_COMBINATOR f) P1 P2) sfb_imp') =
 VAR_RES_FRAME_SPLIT___IMP_OK f (wpb,rpb)
   sfb_context  sfb_split  sfb_imp
   sfb_context' sfb_split' (BAG_INSERT P1 (BAG_INSERT P2 sfb_imp')))
)``,

SIMP_TAC (std_ss++CONJ_ss) [VAR_RES_FRAME_SPLIT___IMP_OK___REWRITE,
   var_res_prop___COND_INSERT, var_res_prop___COND_UNION,
   VAR_RES_IS_STACK_IMPRECISE___USED_VARS___asl_star,
   BAG_UNION_INSERT, var_res_prop___PROP___asl_star]);




val VAR_RES_FRAME_SPLIT___REWRITE_OK___var_res_bool_proposition = store_thm (
"VAR_RES_FRAME_SPLIT___REWRITE_OK___var_res_bool_proposition",
``!b f wpb rpb sfb_context sfb_split sfb_imp
   sfb_context' sfb_split' sfb_imp'.


((VAR_RES_FRAME_SPLIT___REWRITE_OK f (wpb,rpb)
   sfb_context
   (BAG_INSERT (var_res_bool_proposition f b) sfb_split)
   sfb_imp =
 VAR_RES_FRAME_SPLIT___REWRITE_OK f (wpb,rpb)
   (BAG_INSERT (var_res_bool_proposition f b) sfb_context)
   sfb_split sfb_imp)) /\

((VAR_RES_FRAME_SPLIT___REWRITE_OK f (wpb,rpb)
   sfb_context
   (BAG_INSERT (var_res_bool_proposition f b) sfb_split)
   sfb_imp sfb_context'
   (BAG_INSERT (var_res_bool_proposition f b) sfb_split')
   sfb_imp') =

  b ==>
 (VAR_RES_FRAME_SPLIT___REWRITE_OK f (wpb,rpb)
   sfb_context sfb_split sfb_imp sfb_context' sfb_split' sfb_imp')) /\


((VAR_RES_FRAME_SPLIT___REWRITE_OK f (wpb,rpb)
   (BAG_INSERT (var_res_bool_proposition f b) sfb_context)
   sfb_split sfb_imp
   (BAG_INSERT (var_res_bool_proposition f b) sfb_context')
   sfb_split' sfb_imp') =

  b ==>
 (VAR_RES_FRAME_SPLIT___REWRITE_OK f (wpb,rpb)
   sfb_context sfb_split sfb_imp sfb_context' sfb_split' sfb_imp'))``,

REPEAT STRIP_TAC THEN
SIMP_TAC (std_ss++EQUIV_EXTRACT_ss) [GSYM VAR_RES_FRAME_SPLIT___REWRITE_OK___EQ_REWRITE,
   VAR_RES_FRAME_SPLIT___REWRITE_OK___REWRITE,
   var_res_prop___COND_INSERT, BAG_UNION_INSERT,
   VAR_RES_IS_STACK_IMPRECISE___USED_VARS___var_res_bool_proposition] THEN
REPEAT STRIP_TAC THEN
Cases_on `b` THEN
FULL_SIMP_TAC (std_ss++EQUIV_EXTRACT_ss) [
   var_res_bool_proposition_TF,
   var_res_prop___PROP___asl_false,
   var_res_prop___PROP___var_res_prop_stack_true,
   asl_bool_EVAL]);





val VAR_RES_FRAME_SPLIT___REWRITE_OK___asl_star = store_thm (
"VAR_RES_FRAME_SPLIT___REWRITE_OK___asl_star",
``!P1 P2 f wpb rpb sfb_context sfb_split sfb_imp
   sfb_context' sfb_split' sfb_imp'.

  (VAR_RES_IS_STACK_IMPRECISE___USED_VARS
      (SET_OF_BAG (BAG_UNION wpb rpb)) P1) /\
  (VAR_RES_IS_STACK_IMPRECISE___USED_VARS
      (SET_OF_BAG (BAG_UNION wpb rpb)) P2) ==>

((VAR_RES_FRAME_SPLIT___REWRITE_OK f (wpb,rpb)
   (BAG_INSERT (asl_star (VAR_RES_COMBINATOR f) P1 P2) sfb_context)
       sfb_split sfb_imp
   sfb_context' sfb_split' sfb_imp' =
 VAR_RES_FRAME_SPLIT___REWRITE_OK f (wpb,rpb)
   (BAG_INSERT P1 (BAG_INSERT P2 sfb_context)) sfb_split  sfb_imp
   sfb_context' sfb_split' sfb_imp') /\

(VAR_RES_FRAME_SPLIT___REWRITE_OK f (wpb,rpb)
    sfb_context sfb_split sfb_imp
   (BAG_INSERT (asl_star (VAR_RES_COMBINATOR f) P1 P2) sfb_context')
       sfb_split' sfb_imp' =
 VAR_RES_FRAME_SPLIT___REWRITE_OK f (wpb,rpb)
   sfb_context sfb_split  sfb_imp
   (BAG_INSERT P1 (BAG_INSERT P2 sfb_context')) sfb_split' sfb_imp') /\

(VAR_RES_FRAME_SPLIT___REWRITE_OK f (wpb,rpb)
    sfb_context  (BAG_INSERT (asl_star (VAR_RES_COMBINATOR f) P1 P2) sfb_split) sfb_imp
    sfb_context' sfb_split' sfb_imp' =
 VAR_RES_FRAME_SPLIT___REWRITE_OK f (wpb,rpb)
   sfb_context (BAG_INSERT P1 (BAG_INSERT P2 sfb_split)) sfb_imp
   sfb_context' sfb_split' sfb_imp') /\

(VAR_RES_FRAME_SPLIT___REWRITE_OK f (wpb,rpb)
   sfb_context sfb_split sfb_imp
   sfb_context' (BAG_INSERT (asl_star (VAR_RES_COMBINATOR f) P1 P2) sfb_split') sfb_imp' =
 VAR_RES_FRAME_SPLIT___REWRITE_OK f (wpb,rpb)
   sfb_context sfb_split  sfb_imp
   sfb_context' (BAG_INSERT P1 (BAG_INSERT P2 sfb_split')) sfb_imp') /\

(VAR_RES_FRAME_SPLIT___REWRITE_OK f (wpb,rpb)
    sfb_context  sfb_split  (BAG_INSERT (asl_star (VAR_RES_COMBINATOR f) P1 P2) sfb_imp)
    sfb_context' sfb_split' sfb_imp' =
 VAR_RES_FRAME_SPLIT___REWRITE_OK f (wpb,rpb)
   sfb_context  sfb_split (BAG_INSERT P1 (BAG_INSERT P2 sfb_imp))
   sfb_context' sfb_split' sfb_imp') /\

(VAR_RES_FRAME_SPLIT___REWRITE_OK f (wpb,rpb)
    sfb_context sfb_split sfb_imp
    sfb_context' sfb_split' (BAG_INSERT (asl_star (VAR_RES_COMBINATOR f) P1 P2) sfb_imp') =
 VAR_RES_FRAME_SPLIT___REWRITE_OK f (wpb,rpb)
   sfb_context  sfb_split  sfb_imp
   sfb_context' sfb_split' (BAG_INSERT P1 (BAG_INSERT P2 sfb_imp')))
)``,

SIMP_TAC std_ss [VAR_RES_FRAME_SPLIT___REWRITE_OK___REWRITE,
   var_res_prop___COND_INSERT, var_res_prop___COND_UNION,
   VAR_RES_IS_STACK_IMPRECISE___USED_VARS___asl_star,
   BAG_UNION_INSERT, var_res_prop___PROP___asl_star]);





val VAR_RES_FRAME_SPLIT___REWRITE_OK___exists_imp = store_thm (
"VAR_RES_FRAME_SPLIT___REWRITE_OK___exists_imp",
``!f wpb rpb sfb_context sfb_split sfb_imp
   sfb_context' sfb_split' sfb_imp' sf sf'.

  (!n. VAR_RES_IS_STACK_IMPRECISE___USED_VARS
         (SET_OF_BAG (BAG_UNION wpb rpb)) (sf n)) /\
  (!n. VAR_RES_IS_STACK_IMPRECISE___USED_VARS
         (SET_OF_BAG (BAG_UNION wpb rpb)) (sf' n)) /\
  (!n. VAR_RES_FRAME_SPLIT___REWRITE_OK f (wpb,rpb)
     sfb_context  sfb_split  (BAG_INSERT (sf n) sfb_imp)
     sfb_context' sfb_split' (BAG_INSERT (sf' n) sfb_imp')) ==>


  VAR_RES_FRAME_SPLIT___REWRITE_OK f (wpb,rpb)
     sfb_context  sfb_split  (BAG_INSERT (asl_exists n. sf n) sfb_imp)
     sfb_context' sfb_split' (BAG_INSERT (asl_exists n. sf' n) sfb_imp')``,

SIMP_TAC (std_ss++CONJ_ss) [VAR_RES_FRAME_SPLIT___REWRITE_OK_def,
   var_res_prop___COND_INSERT,
   VAR_RES_IS_STACK_IMPRECISE___USED_VARS___asl_exists_direct] THEN
REPEAT STRIP_TAC THEN
`IS_SEPARATION_COMBINATOR f` by ALL_TAC THEN1 (
   FULL_SIMP_TAC std_ss [var_res_prop___COND___REWRITE]
) THEN
FULL_SIMP_TAC std_ss [var_res_prop___PROP___asl_exists,
   BAG_UNION_INSERT, asl_bool_EVAL, IN_DEF,
   GSYM RIGHT_EXISTS_IMP_THM]);






val VAR_RES_FRAME_SPLIT___IMP_OK___asl_exists = store_thm (
"VAR_RES_FRAME_SPLIT___IMP_OK___asl_exists",
``!P f wpb rpb sfb_context sfb_split sfb_imp
   sfb_context' sfb_split' sfb_imp'.

  (!x. (VAR_RES_IS_STACK_IMPRECISE___USED_VARS
      (SET_OF_BAG (BAG_UNION wpb rpb)) (P x))) ==>

(((!x. VAR_RES_FRAME_SPLIT___IMP_OK f (wpb,rpb)
   (BAG_INSERT (P x) sfb_context) sfb_split  sfb_imp
   sfb_context' sfb_split' sfb_imp') ==>
 (VAR_RES_FRAME_SPLIT___IMP_OK f (wpb,rpb)
   (BAG_INSERT (asl_exists x. P x) sfb_context)
       sfb_split sfb_imp
   sfb_context' sfb_split' sfb_imp')) /\

 ((VAR_RES_FRAME_SPLIT___IMP_OK f (wpb,rpb) sfb_context
   (BAG_INSERT (asl_exists x. P x) sfb_split) sfb_imp
   sfb_context' sfb_split' sfb_imp') =
  (!x. VAR_RES_FRAME_SPLIT___IMP_OK f (wpb,rpb) sfb_context
   (BAG_INSERT (P x) sfb_split) sfb_imp
   sfb_context' sfb_split' sfb_imp')) /\

 ((?x. VAR_RES_FRAME_SPLIT___IMP_OK f (wpb,rpb) sfb_context sfb_split
   (BAG_INSERT (P x) sfb_imp)
   sfb_context' sfb_split' sfb_imp') ==>
  (VAR_RES_FRAME_SPLIT___IMP_OK f (wpb,rpb) sfb_context sfb_split
   (BAG_INSERT (asl_exists x. P x) sfb_imp)
   sfb_context' sfb_split' sfb_imp')) /\

 ((!x. VAR_RES_FRAME_SPLIT___IMP_OK f (wpb,rpb)
   sfb_context' sfb_split' sfb_imp'
   (BAG_INSERT (P x) sfb_context) sfb_split  sfb_imp) ==>
 (VAR_RES_FRAME_SPLIT___IMP_OK f (wpb,rpb)
   sfb_context' sfb_split' sfb_imp'
   (BAG_INSERT (asl_exists x. P x) sfb_context)
       sfb_split sfb_imp)) /\

 (((?x. VAR_RES_FRAME_SPLIT___IMP_OK f (wpb,rpb) sfb_context
    sfb_context' sfb_split' sfb_imp'
    (BAG_INSERT (P x) sfb_split) sfb_imp) ==>
   VAR_RES_FRAME_SPLIT___IMP_OK f (wpb,rpb) sfb_context
   sfb_context' sfb_split' sfb_imp'
   (BAG_INSERT (asl_exists x. P x) sfb_split) sfb_imp)) /\


 ((!x. VAR_RES_FRAME_SPLIT___IMP_OK f (wpb,rpb) sfb_context sfb_split
   sfb_context' sfb_split' sfb_imp'
   (BAG_INSERT (P x) sfb_imp)) ==>

  (VAR_RES_FRAME_SPLIT___IMP_OK f (wpb,rpb) sfb_context sfb_split
   sfb_context' sfb_split' sfb_imp'
   (BAG_INSERT (asl_exists x. P x) sfb_imp)))
)``,

REPEAT GEN_TAC THEN
Cases_on `IS_SEPARATION_COMBINATOR f` THEN ASM_REWRITE_TAC[VAR_RES_FRAME_SPLIT___IMP_OK___REWRITE] THEN
ASM_SIMP_TAC (std_ss++EQUIV_EXTRACT_ss) [VAR_RES_FRAME_SPLIT___IMP_OK___REWRITE,
   BAG_UNION_INSERT, var_res_prop___PROP___asl_exists, asl_bool_EVAL,
   GSYM LEFT_EXISTS_AND_THM, GSYM RIGHT_EXISTS_AND_THM, IN_DEF,
   GSYM LEFT_FORALL_IMP_THM,
   var_res_prop___COND_INSERT,
   VAR_RES_IS_STACK_IMPRECISE___USED_VARS___asl_exists_direct] THEN
METIS_TAC[]);






val VAR_RES_FRAME_SPLIT___REWRITE_OK___FRAME = store_thm ("VAR_RES_FRAME_SPLIT___REWRITE_OK___FRAME",
``!f wpb rpb sfb_context sfb_split sfb_imp sf.
VAR_RES_FRAME_SPLIT___REWRITE_OK f (wpb,rpb)
   sfb_context (BAG_INSERT sf sfb_split) (BAG_INSERT sf sfb_imp)
   (BAG_INSERT sf sfb_context) sfb_split sfb_imp``,

SIMP_TAC (std_ss++EQUIV_EXTRACT_ss) [
   VAR_RES_FRAME_SPLIT___REWRITE_OK___REWRITE,
   var_res_prop___COND_UNION,
   var_res_prop___COND_INSERT,
   bagTheory.BAG_UNION_INSERT]);


val VAR_RES_FRAME_SPLIT___FRAME = store_thm ("VAR_RES_FRAME_SPLIT___FRAME",
``!f wpb rpb wpb' sfb_context sfb_split sfb_imp sfb_restP sr sf.
VAR_RES_FRAME_SPLIT f sr (wpb,rpb) wpb' sfb_context (BAG_INSERT sf sfb_split) (BAG_INSERT sf sfb_imp) sfb_restP =
VAR_RES_FRAME_SPLIT f sr (wpb,rpb) wpb' (BAG_INSERT sf sfb_context) sfb_split sfb_imp sfb_restP``,

SIMP_TAC (std_ss++EQUIV_EXTRACT_ss) [
   VAR_RES_FRAME_SPLIT_def,
   var_res_prop___COND_UNION,
   var_res_prop___COND_INSERT,
   bagTheory.BAG_UNION_INSERT] THEN
REPEAT STRIP_TAC THEN
CONSEQ_CONV_TAC (K EXISTS_EQ___CONSEQ_CONV) THEN
SIMP_TAC (std_ss++EQUIV_EXTRACT_ss) []);


val VAR_RES_FRAME_SPLIT___ELIM_CONTEXT = store_thm ("VAR_RES_FRAME_SPLIT___ELIM_CONTEXT",
``!f wpb rpb wpb' sfb_context sfb_split sfb_imp sfb_restP sr.
VAR_RES_FRAME_SPLIT f sr (wpb,rpb) wpb' sfb_context sfb_split sfb_imp sfb_restP =
VAR_RES_FRAME_SPLIT f sr (wpb,rpb) wpb' EMPTY_BAG (BAG_UNION sfb_context sfb_split)
   (BAG_UNION sfb_context sfb_imp) sfb_restP``,

SIMP_TAC (std_ss++EQUIV_EXTRACT_ss) [
   VAR_RES_FRAME_SPLIT_EXPAND, BAG_UNION_EMPTY] THEN
REPEAT STRIP_TAC THEN
CONSEQ_CONV_TAC (K EXISTS_EQ___CONSEQ_CONV) THEN
SIMP_TAC (std_ss++EQUIV_EXTRACT_ss) [var_res_prop___COND_UNION] THEN
REPEAT STRIP_TAC THEN
Q.MATCH_ABBREV_TAC `
(!s. var_res_prop___PROP f (wpb,rpb) (sfb_split_context) s ==>
     var_res_prop___PROP f (wpb,rpb) (sfb_imp_rest_context) s) <=>
(!s. var_res_prop___PROP f (wpb,rpb) (sfb_context_split) s ==>
     var_res_prop___PROP f (wpb,rpb) (sfb_context_imp_rest) s)` THEN
Tactical.REVERSE (`(sfb_context_imp_rest = sfb_imp_rest_context) /\
   (sfb_split_context = sfb_context_split)` by ALL_TAC) THEN1 (
   ASM_REWRITE_TAC[]
) THEN
UNABBREV_ALL_TAC THEN
METIS_TAC[COMM_BAG_UNION, ASSOC_BAG_UNION]);





val VAR_RES_PROP_IS_EQUIV_FALSE_def = Define `
   VAR_RES_PROP_IS_EQUIV_FALSE (c:label list option) f (wpb,rpb) sfb =
    COND_PROP___EQUIV (var_res_prop f (wpb,rpb) sfb) cond_prop_false`


val VAR_RES_PROP_IS_EQUIV_FALSE___REWRITE =
store_thm ("VAR_RES_PROP_IS_EQUIV_FALSE___REWRITE",
``!f wpb rpb sfb c.
  VAR_RES_PROP_IS_EQUIV_FALSE c f (wpb,rpb) sfb =
   (var_res_prop___COND f (wpb,rpb) sfb ==>
   !x. ~(x IN var_res_prop___PROP f (wpb,rpb) sfb))``,
SIMP_TAC (std_ss++EQUIV_EXTRACT_ss) [
   VAR_RES_PROP_IS_EQUIV_FALSE_def, COND_PROP___EQUIV_REWRITE,
   var_res_prop___REWRITE, cond_prop_false_def]);

val VAR_RES_PROP_IS_EQUIV_FALSE___comment_REWRITE =
store_thm ("VAR_RES_PROP_IS_EQUIV_FALSE___comment_REWRITE",
``!c1 c2 f wpb rpb sfb.
  VAR_RES_PROP_IS_EQUIV_FALSE c1 f (wpb,rpb) sfb =
  VAR_RES_PROP_IS_EQUIV_FALSE c2 f (wpb,rpb) sfb``,
SIMP_TAC std_ss [VAR_RES_PROP_IS_EQUIV_FALSE___REWRITE])


val VAR_RES_PROP_IS_EQUIV_FALSE___INTRO =
store_thm ("VAR_RES_PROP_IS_EQUIV_FALSE___INTRO",
``!f rf c wpb rpb wpb' sfb_context sfb_split sfb_restP.
    VAR_RES_FRAME_SPLIT f (rf, c) (wpb,rpb) wpb' sfb_context sfb_split {|asl_false|} sfb_restP =

    (VAR_RES_FRAME_SPLIT___sfb_restP_OK f (BAG_DIFF wpb wpb', BAG_DIFF rpb wpb') sfb_restP ==>
    VAR_RES_PROP_IS_EQUIV_FALSE c f (wpb,rpb) (BAG_UNION sfb_context sfb_split))``,

SIMP_TAC std_ss [VAR_RES_PROP_IS_EQUIV_FALSE___REWRITE,
   VAR_RES_FRAME_SPLIT_def, BAG_UNION_EMPTY,
   BAG_UNION_INSERT, var_res_prop___COND_INSERT,
   var_res_prop___PROP___asl_false, COND_PROP___EQUIV_REWRITE,
   cond_prop_false_def, var_res_prop___REWRITE,
   VAR_RES_IS_STACK_IMPRECISE___USED_VARS___asl_false,
   BAG_DIFF_EMPTY, BAG_EVERY_THM] THEN
SIMP_TAC (std_ss++CONJ_ss++EQUIV_EXTRACT_ss) [COND_RAND, COND_RATOR,
   asl_bool_EVAL] THEN
REPEAT STRIP_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THEN1 (
   METIS_TAC[IN_DEF, COMM_BAG_UNION]
) THEN
FULL_SIMP_TAC std_ss [VAR_RES_FRAME_SPLIT___sfb_restP_OK___REWRITE] THEN
Q.EXISTS_TAC `sfb` THEN
METIS_TAC[IN_DEF, COMM_BAG_UNION])



val VAR_RES_PROP_IS_EQUIV_FALSE___INTRO_IMP =
store_thm ("VAR_RES_PROP_IS_EQUIV_FALSE___INTRO_IMP",
``!f c sr wpb rpb wpb' sfb_context sfb_split sfb_restP.
    VAR_RES_PROP_IS_EQUIV_FALSE c f (wpb,rpb) (BAG_UNION sfb_context sfb_split) ==>
    VAR_RES_FRAME_SPLIT f sr (wpb,rpb) wpb' sfb_context sfb_split {|asl_false|}
       sfb_restP``,
Cases_on`sr` THEN
METIS_TAC[VAR_RES_PROP_IS_EQUIV_FALSE___INTRO, VAR_RES_PROP_IS_EQUIV_FALSE___comment_REWRITE]);




val VAR_RES_PROP_IS_EQUIV_FALSE___FRAME_SPLIT_DEF =
store_thm ("VAR_RES_PROP_IS_EQUIV_FALSE___FRAME_SPLIT_DEF",
``!f wpb rpb sfb c.
  VAR_RES_PROP_IS_EQUIV_FALSE c f (wpb,rpb) sfb =
  VAR_RES_FRAME_SPLIT f (F,c) (wpb,rpb) EMPTY_BAG EMPTY_BAG sfb {| asl_false |} (K T)``,

SIMP_TAC (std_ss++EQUIV_EXTRACT_ss) [VAR_RES_PROP_IS_EQUIV_FALSE___INTRO,
   BAG_DIFF_EMPTY, BAG_UNION_EMPTY, VAR_RES_FRAME_SPLIT___sfb_restP_OK___REWRITE] THEN
REPEAT STRIP_TAC THEN
Q.EXISTS_TAC `EMPTY_BAG` THEN
FULL_SIMP_TAC std_ss [var_res_prop___COND___REWRITE,
    VAR_RES_PROP_IS_EQUIV_FALSE___REWRITE, FINITE_BAG_THM,
    NOT_IN_EMPTY_BAG]);


val VAR_RES_PROP_IS_EQUIV_FALSE___FRAME_SPLIT_DEF2 =
store_thm ("VAR_RES_PROP_IS_EQUIV_FALSE___FRAME_SPLIT_DEF2",
``!f wpb rpb sfb c.
  VAR_RES_PROP_IS_EQUIV_FALSE c f (wpb,rpb) sfb =
  VAR_RES_FRAME_SPLIT f (F,c) (wpb,rpb) EMPTY_BAG sfb EMPTY_BAG {| asl_false |} (K T)``,
SIMP_TAC std_ss [VAR_RES_PROP_IS_EQUIV_FALSE___FRAME_SPLIT_DEF,
  VAR_RES_FRAME_SPLIT_def, bagTheory.BAG_UNION_EMPTY,
  bagTheory.BAG_UNION_INSERT, var_res_prop___PROP___asl_false]);



val VAR_RES_FRAME_SPLIT___SOLVE___bool_prop = store_thm ("VAR_RES_FRAME_SPLIT___SOLVE___bool_prop",
``!b rfc f wpb rpb wpb' sfb_context sfb_split sfb_restP.
(BAG_EVERY (VAR_RES_IS_STACK_IMPRECISE___USED_VARS (SET_OF_BAG
           (BAG_DIFF (BAG_UNION wpb rpb) wpb'))) sfb_split) ==>
(~(VAR_RES_PROP_IS_EQUIV_FALSE (SND rfc) f (wpb,rpb) (BAG_UNION sfb_context sfb_split)) ==>
 (b /\ (b ==> (sfb_restP sfb_split))))  ==>
VAR_RES_FRAME_SPLIT f rfc (wpb,rpb) wpb' sfb_context sfb_split {|var_res_bool_proposition f b|} sfb_restP``,

REPEAT GEN_TAC THEN STRIP_TAC THEN
SIMP_TAC (std_ss++EQUIV_EXTRACT_ss++CONJ_ss) [
   VAR_RES_FRAME_SPLIT_EXPAND,
   BAG_UNION_EMPTY, FINITE_BAG_UNION, FINITE_BAG_THM,
   VAR_RES_PROP_IS_EQUIV_FALSE_def, COND_PROP___EQUIV_REWRITE,
   cond_prop_false_def, var_res_prop___REWRITE, BAG_UNION_INSERT,
   BAG_UNION_EMPTY] THEN
SIMP_TAC std_ss [var_res_prop___COND_INSERT, var_res_prop___COND_UNION,
   BAG_UNION_INSERT] THEN
Tactical.REVERSE (Cases_on `var_res_prop___COND f (wpb,rpb) (BAG_UNION sfb_context sfb_split)`) THEN1 (
   FULL_SIMP_TAC std_ss [VAR_RES_FRAME_SPLIT___sfb_restP_OK___REWRITE,
      var_res_prop___COND_UNION]
) THEN
Tactical.REVERSE (Cases_on `b`) THEN1 (
   FULL_SIMP_TAC std_ss [VAR_RES_FRAME_SPLIT___sfb_restP_OK___REWRITE,
      var_res_prop___PROP___asl_false, var_res_bool_proposition_TF,
      asl_bool_EVAL, VAR_RES_IS_STACK_IMPRECISE___USED_VARS___asl_false,
      var_res_prop___COND_UNION, IN_DEF] THEN
   REPEAT STRIP_TAC THEN
   METIS_TAC[COMM_BAG_UNION]
) THEN
`IS_SEPARATION_COMBINATOR f /\ BAG_ALL_DISTINCT (wpb + rpb)` by ALL_TAC THEN1 (
   FULL_SIMP_TAC std_ss [var_res_prop___COND___EXPAND]
) THEN
FULL_SIMP_TAC std_ss [var_res_bool_proposition_TF,
   VAR_RES_IS_STACK_IMPRECISE___USED_VARS___var_res_prop_stack_true,
   var_res_prop___COND_UNION,
   var_res_prop___PROP___var_res_prop_stack_true] THEN
REPEAT STRIP_TAC THEN
Cases_on `var_res_prop___PROP f (wpb,rpb) (sfb_context + sfb_split) = asl_false` THEN1 (
   FULL_SIMP_TAC std_ss [VAR_RES_FRAME_SPLIT___sfb_restP_OK___REWRITE] THEN
   Q.EXISTS_TAC `sfb` THEN
   `sfb_split + sfb_context = sfb_context + sfb_split` by METIS_TAC[COMM_BAG_UNION] THEN
   ASM_REWRITE_TAC [asl_bool_EVAL]
) THEN
`sfb_restP sfb_split` by ALL_TAC THEN1 (
   Q.PAT_ASSUM `X ==> Y` MATCH_MP_TAC THEN
   FULL_SIMP_TAC std_ss [EXTENSION, asl_bool_EVAL] THEN
   METIS_TAC[]
) THEN
Q.EXISTS_TAC `sfb_split` THEN
FULL_SIMP_TAC std_ss [var_res_prop___COND_UNION] THEN
REPEAT STRIP_TAC THEN
FULL_SIMP_TAC std_ss [var_res_prop___COND___REWRITE, BAG_EVERY] THEN
REPEAT STRIP_TAC THENL [
   FULL_SIMP_TAC std_ss [
      BAG_ALL_DISTINCT_BAG_UNION,
      BAG_ALL_DISTINCT_DIFF, BAG_DISJOINT_BAG_IN,
      BAG_IN_BAG_DIFF_ALL_DISTINCT] THEN
   METIS_TAC [],

   Tactical.REVERSE (`(SET_OF_BAG (BAG_UNION (BAG_DIFF wpb wpb') (BAG_DIFF rpb wpb'))) =
                      (SET_OF_BAG (BAG_DIFF (BAG_UNION wpb rpb) wpb'))` by ALL_TAC) THEN1 (
     ASM_SIMP_TAC std_ss []
   ) THEN
   `BAG_ALL_DISTINCT wpb /\ BAG_ALL_DISTINCT rpb` by FULL_SIMP_TAC std_ss [BAG_ALL_DISTINCT_BAG_UNION] THEN
   ASM_SIMP_TAC std_ss [EXTENSION, IN_SET_OF_BAG, BAG_IN_BAG_UNION,
     IN_UNION, IN_DIFF, BAG_IN_BAG_DIFF_ALL_DISTINCT] THEN
   METIS_TAC[]
]);


val VAR_RES_FRAME_SPLIT___SOLVE___bool_prop___MP = store_thm ("VAR_RES_FRAME_SPLIT___SOLVE___bool_prop___MP",
``!b. b ==> !rfc f wpb rpb wpb' sfb_context sfb_split sfb_restP.
(BAG_EVERY (VAR_RES_IS_STACK_IMPRECISE___USED_VARS (SET_OF_BAG
           (BAG_DIFF (BAG_UNION wpb rpb) wpb'))) sfb_split) ==>
(~(VAR_RES_PROP_IS_EQUIV_FALSE (SND rfc) f (wpb,rpb) (BAG_UNION sfb_context sfb_split)) ==>
 (sfb_restP sfb_split))  ==>
VAR_RES_FRAME_SPLIT f rfc (wpb,rpb) wpb' sfb_context sfb_split {|var_res_bool_proposition f b|} sfb_restP``,
SIMP_TAC std_ss [VAR_RES_FRAME_SPLIT___SOLVE___bool_prop]);


val VAR_RES_FRAME_SPLIT___SOLVE_WEAK___bool_prop = store_thm ("VAR_RES_FRAME_SPLIT___SOLVE_WEAK___bool_prop",
``!b rfc f wpb rpb wpb' sfb_context sfb_split sfb_restP.
(BAG_EVERY (VAR_RES_IS_STACK_IMPRECISE___USED_VARS (SET_OF_BAG
           (BAG_DIFF (BAG_UNION wpb rpb) wpb'))) sfb_split) ==>
 (b /\ (b ==> (sfb_restP sfb_split)))  ==>
VAR_RES_FRAME_SPLIT f rfc (wpb,rpb) wpb' sfb_context sfb_split {|var_res_bool_proposition f b|} sfb_restP``,
SIMP_TAC std_ss [VAR_RES_FRAME_SPLIT___SOLVE___bool_prop]);


val VAR_RES_FRAME_SPLIT___SOLVE_WEAK___bool_prop___MP = store_thm ("VAR_RES_FRAME_SPLIT___SOLVE_WEAK___bool_prop___MP",
``!b. b ==> !rfc f wpb rpb wpb' sfb_context sfb_split sfb_restP.
(BAG_EVERY (VAR_RES_IS_STACK_IMPRECISE___USED_VARS (SET_OF_BAG
           (BAG_DIFF (BAG_UNION wpb rpb) wpb'))) sfb_split) ==>
 (sfb_restP sfb_split)  ==>
VAR_RES_FRAME_SPLIT f rfc (wpb,rpb) wpb' sfb_context sfb_split {|var_res_bool_proposition f b|} sfb_restP``,
SIMP_TAC std_ss [VAR_RES_FRAME_SPLIT___SOLVE___bool_prop]);



val VAR_RES_PROP_IS_EQUIV_FALSE___FRAME_SPLIT_IMP =
store_thm ("VAR_RES_PROP_IS_EQUIV_FALSE___FRAME_SPLIT_IMP",
``!f wpb rpb wpb' sfb_context sfb_split sfb_imp sfb_restP rfc.
VAR_RES_PROP_IS_EQUIV_FALSE (SND rfc) f (wpb,rpb) (BAG_UNION sfb_context sfb_split) ==>
(VAR_RES_FRAME_SPLIT f rfc (wpb,rpb) wpb' sfb_context sfb_split sfb_imp sfb_restP)``,

REPEAT STRIP_TAC THEN
IMP_RES_TAC VAR_RES_PROP_IS_EQUIV_FALSE___INTRO_IMP THEN
POP_ASSUM (ASSUME_TAC o Q.SPECL [`wpb'`, `sr`, `sfb_restP`]) THEN
FULL_SIMP_TAC std_ss [VAR_RES_FRAME_SPLIT_def,
   BAG_UNION_INSERT, BAG_UNION_EMPTY] THEN
FULL_SIMP_TAC std_ss [
   var_res_prop___PROP___asl_false, asl_bool_EVAL,
   var_res_prop___COND_UNION, var_res_prop___COND_INSERT,
   VAR_RES_IS_STACK_IMPRECISE___USED_VARS___asl_false] THEN
METIS_TAC[]);




val VAR_RES_FRAME_SPLIT___PURE_PROPOSITION_INTRO = store_thm ("VAR_RES_FRAME_SPLIT___PURE_PROPOSITION_INTRO",
``!f sf wpb rpb wpb' sfb_context sfb_split sfb_imp sfb_restP sr.
VAR_RES_IS_PURE_PROPOSITION f sf ==>
((VAR_RES_FRAME_SPLIT f sr (wpb,rpb) wpb' sfb_context (BAG_INSERT sf sfb_split)
  sfb_imp sfb_restP) =
 (VAR_RES_FRAME_SPLIT f sr (wpb,rpb) wpb' sfb_context
   (BAG_INSERT sf sfb_split)
   (BAG_INSERT sf sfb_imp)
   sfb_restP))``,

SIMP_TAC (std_ss++EQUIV_EXTRACT_ss) [
   VAR_RES_FRAME_SPLIT_EXPAND, BAG_UNION_INSERT] THEN
REPEAT STRIP_TAC THEN
CONSEQ_CONV_TAC (K EXISTS_EQ___CONSEQ_CONV) THEN
SIMP_TAC (std_ss++EQUIV_EXTRACT_ss) [
   var_res_prop___COND_INSERT, var_res_prop___COND_UNION] THEN
REPEAT STRIP_TAC THEN
CONSEQ_CONV_TAC (K FORALL_EQ___CONSEQ_CONV) THEN
SIMP_TAC (std_ss++EQUIV_EXTRACT_ss) [] THEN
ASM_SIMP_TAC std_ss [
   var_res_prop___PROP_INSERT, var_res_prop___COND_INSERT,
   var_res_prop___COND_UNION] THEN
Q.PAT_ASSUM `VAR_RES_IS_PURE_PROPOSITION f sf` (fn thm =>
   ONCE_REWRITE_TAC[REWRITE_RULE [VAR_RES_IS_PURE_PROPOSITION___EQ_REWRITE] thm]) THEN
`?uf. IS_SEPARATION_COMBINATOR_NEUTRAL_ELEMENT_FUNCTION___WITH_COMBINATOR f uf` by ALL_TAC THEN1 (
   FULL_SIMP_TAC std_ss [var_res_prop___COND___REWRITE] THEN
   METIS_TAC[IS_SEPARATION_COMBINATOR_NEUTRAL_ELEMENT_FUNCTION_IMP]
) THEN
FULL_SIMP_TAC std_ss [IS_SEPARATION_COMBINATOR_NEUTRAL_ELEMENT_FUNCTION___WITH_COMBINATOR_THM,
   asl_emp_def, IN_ABS, GSYM RIGHT_EXISTS_AND_THM, GSYM LEFT_EXISTS_AND_THM] THEN
QUANT_INSTANTIATE_TAC [] THEN
SIMP_TAC std_ss [IN_DEF]);





val VAR_RES_FRAME_SPLIT___PURE_PROPOSITION___TO_CONTEXT = store_thm (
"VAR_RES_FRAME_SPLIT___PURE_PROPOSITION___TO_CONTEXT",
``!f wpb rpb wpb' sfb_context sfb_split sfb_imp sfb_restP sr sf.
VAR_RES_IS_PURE_PROPOSITION f sf ==>
((VAR_RES_FRAME_SPLIT f sr (wpb,rpb) wpb' sfb_context (BAG_INSERT sf sfb_split)
   sfb_imp sfb_restP) =
 (VAR_RES_FRAME_SPLIT f sr (wpb,rpb) wpb' (BAG_INSERT sf sfb_context)
   sfb_split sfb_imp sfb_restP))``,

REPEAT STRIP_TAC THEN
MP_TAC (Q.SPECL [`f`, `sf`] VAR_RES_FRAME_SPLIT___PURE_PROPOSITION_INTRO) THEN
ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
ONCE_ASM_REWRITE_TAC[] THEN
REWRITE_TAC [VAR_RES_FRAME_SPLIT___FRAME]);




val VAR_RES_FRAME_SPLIT___PURE_PROPOSITION___CONTEXT_FRAME = store_thm (
"VAR_RES_FRAME_SPLIT___PURE_PROPOSITION___CONTEXT_FRAME",
``!f wpb rpb wpb' sfb_context sfb_split sfb_imp sfb_restP sr sf.
VAR_RES_IS_PURE_PROPOSITION f sf ==>

((VAR_RES_FRAME_SPLIT f sr (wpb,rpb) wpb' (BAG_INSERT sf sfb_context)
   sfb_split (BAG_INSERT sf sfb_imp) sfb_restP) =
 (VAR_RES_FRAME_SPLIT f sr (wpb,rpb) wpb'
   (BAG_INSERT sf sfb_context) sfb_split sfb_imp sfb_restP))``,

PROVE_TAC[VAR_RES_FRAME_SPLIT___PURE_PROPOSITION___TO_CONTEXT,
     VAR_RES_FRAME_SPLIT___FRAME]);




val VAR_RES_FRAME_SPLIT___COND_PROP_IMP___split =
store_thm ("VAR_RES_FRAME_SPLIT___COND_PROP_IMP___split",
``!f wpb rpb wpb' sfb_context  sfb_split  sfb_imp sfb_split' sfb_restP sr.
(COND_PROP___IMP (var_res_prop f (wpb,rpb) sfb_split)
                 (var_res_prop f (wpb,rpb) sfb_split')) ==>
((VAR_RES_FRAME_SPLIT f sr (wpb,rpb) wpb'
   sfb_context sfb_split' sfb_imp sfb_restP) ==>
 (VAR_RES_FRAME_SPLIT f sr (wpb,rpb) wpb'
   sfb_context sfb_split sfb_imp sfb_restP))``,

REPEAT STRIP_TAC THEN
FULL_SIMP_TAC (std_ss++CONJ_ss)
   [VAR_RES_FRAME_SPLIT_def,
    var_res_prop___COND_UNION,
    var_res_prop___PROP_UNION,
    IN_ABS, GSYM RIGHT_EXISTS_AND_THM,
    GSYM LEFT_FORALL_IMP_THM] THEN
REPEAT STRIP_TAC THEN
FULL_SIMP_TAC std_ss [] THEN
Q.EXISTS_TAC `sfb_rest` THEN
ASM_REWRITE_TAC[] THEN
STRIP_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
`?sst sh. s = (sst,sh)` by (Cases_on `s` THEN SIMP_TAC std_ss []) THEN
FULL_SIMP_TAC (std_ss++CONJ_ss) [COND_PROP___IMP_def, var_res_prop___REWRITE] THEN
`var_res_prop___COND f (wpb,rpb) sfb_split' /\
 (sst,s1) IN var_res_prop___PROP f (wpb,rpb) sfb_split'` by ALL_TAC THEN1 (
   RES_TAC THEN
   ASM_REWRITE_TAC[]
) THEN
FULL_SIMP_TAC std_ss [] THEN
Q.PAT_ASSUM `!s h1 h2. X s h1 h2` (MP_TAC o Q.SPECL [`s`, `s1`, `s2`]) THEN
ASM_SIMP_TAC std_ss []);



val VAR_RES_FRAME_SPLIT___equal_const___context = store_thm ("VAR_RES_FRAME_SPLIT___equal_const___context",
``!vcL f wpb rpb wpb' sfb_context sfb_split sfb_imp sfb_restP sr.

((VAR_RES_FRAME_SPLIT f sr (wpb,rpb) wpb'
   (BAG_UNION
      (var_res_prop___var_eq_const_BAG f vcL)
      (BAG_IMAGE (var_res_prop_varlist_update vcL) sfb_context))
   (BAG_IMAGE (var_res_prop_varlist_update vcL) sfb_split)
   (BAG_IMAGE (var_res_prop_varlist_update vcL) sfb_imp)
   sfb_restP) ==>

(VAR_RES_FRAME_SPLIT f sr (wpb,rpb) wpb'
   (BAG_UNION
      (var_res_prop___var_eq_const_BAG f vcL)
      sfb_context) sfb_split
   sfb_imp sfb_restP))
``,


SIMP_TAC std_ss [VAR_RES_FRAME_SPLIT_EXPAND, bagTheory.BAG_UNION_INSERT] THEN
REPEAT STRIP_TAC THEN
FULL_SIMP_TAC std_ss [] THEN
Q.EXISTS_TAC `sfb_rest` THEN
ASM_REWRITE_TAC[] THEN STRIP_TAC THEN GEN_TAC THEN
`FINITE_BAG sfb_imp /\ FINITE_BAG sfb_context /\ FINITE_BAG sfb_split` by ALL_TAC THEN1 (
   FULL_SIMP_TAC std_ss [var_res_prop___COND___REWRITE, FINITE_BAG_UNION, FINITE_BAG_THM]
) THEN
FULL_SIMP_TAC std_ss [GSYM BAG_IMAGE_FINITE_UNION, FINITE_BAG_UNION,
   GSYM ASSOC_BAG_UNION] THEN
ASSUME_TAC (ISPECL [``f:'c bin_option_function``,
        ``wpb:'a -> num``, ``rpb:'a->num``, ``vcL:('a # 'b) list``]
      var_res_prop___equal_const) THEN
POP_ASSUM (fn thm=> (MP_TAC (Q.SPEC `BAG_UNION sfb_imp (BAG_UNION sfb_rest sfb_context)` thm)) THEN
                     ASSUME_TAC thm) THEN
POP_ASSUM (fn thm=> (MP_TAC (Q.SPEC `BAG_UNION sfb_split sfb_context` thm)) THEN
                     ASSUME_TAC thm) THEN
POP_ASSUM (fn thm=> (MP_TAC (Q.SPEC `sfb_imp` thm)) THEN
                     ASSUME_TAC thm) THEN
POP_ASSUM (fn thm=> (MP_TAC (Q.SPEC `(BAG_UNION (BAG_IMAGE (var_res_prop_varlist_update vcL) sfb_imp)
                    (BAG_UNION sfb_rest (BAG_IMAGE (var_res_prop_varlist_update vcL) sfb_context)))` thm))) THEN

`!sfb. var_res_prop___COND f (wpb, rpb) sfb ==>
       var_res_prop___COND f (wpb, rpb)
         (BAG_IMAGE (var_res_prop_varlist_update vcL) sfb)` by ALL_TAC THEN1 (
   ASM_SIMP_TAC (std_ss++EQUIV_EXTRACT_ss) [var_res_prop___COND___REWRITE,
      BAG_IMAGE_FINITE, BAG_IN_FINITE_BAG_IMAGE, GSYM LEFT_FORALL_IMP_THM,
      VAR_RES_IS_STACK_IMPRECISE___USED_VARS___var_res_prop_varlist_update]
) THEN
`(!b. BAG_UNION b (var_res_prop___var_eq_const_BAG f vcL) =
      BAG_UNION (var_res_prop___var_eq_const_BAG f vcL) b) /\
 (!b1 b2.
      BAG_UNION b1 (BAG_UNION (var_res_prop___var_eq_const_BAG f vcL) b2) =
      BAG_UNION (var_res_prop___var_eq_const_BAG f vcL) (BAG_UNION b1 b2))` by ALL_TAC THEN1 (
   METIS_TAC[COMM_BAG_UNION, ASSOC_BAG_UNION]
) THEN

FULL_SIMP_TAC (std_ss++CONJ_ss) [
   COND_PROP___STRONG_IMP_def, var_res_prop___REWRITE,
   var_res_prop___COND_UNION, BAG_IMAGE_FINITE_UNION] THEN
REPEAT DISCH_TAC THEN
Q.PAT_ASSUM `!s. var_res_prop___PROP f (wpb,rpb) X s ==> Y` (MP_TAC o Q.SPEC `s`) THEN
FULL_SIMP_TAC std_ss [BAG_IMAGE_FINITE_UNION, BAG_IMAGE_FINITE_INSERT,
   FINITE_BAG_THM, FINITE_BAG_UNION, BAG_IMAGE_FINITE,
   GSYM BAG_IMAGE_COMPOSE] THEN
REPEAT STRIP_TAC THEN
`FINITE_BAG sfb_rest` by PROVE_TAC [var_res_prop___COND___REWRITE] THEN
Q.PAT_ASSUM `var_res_prop___PROP f (wpb,rpb) X s` MP_TAC THEN
ASM_SIMP_TAC std_ss [BAG_IMAGE_FINITE_UNION, BAG_IMAGE_FINITE,
   FINITE_BAG_UNION, GSYM BAG_IMAGE_COMPOSE,
   var_res_prop_varlist_update_IDEMPOT_o]);



val VAR_RES_FRAME_SPLIT___equal_const___context_SING = store_thm ("VAR_RES_FRAME_SPLIT___equal_const___context_SING",
``!v c f wpb rpb wpb' sfb_context sfb_split sfb_imp sfb_restP sr.
((VAR_RES_FRAME_SPLIT f sr (wpb,rpb) wpb'
   (BAG_INSERT
      (var_res_prop_equal f (var_res_exp_var v) (var_res_exp_const c))
      (BAG_IMAGE (var_res_prop_var_update (v, c)) sfb_context))
   (BAG_IMAGE (var_res_prop_var_update (v, c)) sfb_split)
   (BAG_IMAGE (var_res_prop_var_update (v, c)) sfb_imp)
   sfb_restP) ==>

(VAR_RES_FRAME_SPLIT f sr (wpb,rpb) wpb'
   (BAG_INSERT
      (var_res_prop_equal f (var_res_exp_var v) (var_res_exp_const c))
      sfb_context) sfb_split
   sfb_imp sfb_restP))``,

REPEAT GEN_TAC THEN
ASSUME_TAC (Q.SPECL [`[v, c]`, `f`, `wpb`, `rpb`, `wpb'`, `sfb_context`, `sfb_split`,
  `sfb_imp`, `sfb_restP`, `sr`] VAR_RES_FRAME_SPLIT___equal_const___context) THEN
REPEAT STRIP_TAC THEN
FULL_SIMP_TAC (std_ss++ETA_ss) [var_res_prop___var_eq_const_BAG_THM,
   BAG_UNION_INSERT, BAG_UNION_EMPTY, var_res_prop_varlist_update_THM]);




val VAR_RES_FRAME_SPLIT___equal_const = store_thm ("VAR_RES_FRAME_SPLIT___equal_const",
``!vcL f wpb rpb wpb' sfb_context sfb_split sfb_imp sfb_restP sr.

((VAR_RES_FRAME_SPLIT f sr (wpb,rpb) wpb'
   (BAG_UNION
      (var_res_prop___var_eq_const_BAG f vcL)
      (BAG_IMAGE (var_res_prop_varlist_update vcL) sfb_context))
   (BAG_IMAGE (var_res_prop_varlist_update vcL) sfb_split)
   (BAG_IMAGE (var_res_prop_varlist_update vcL) sfb_imp)
   sfb_restP) ==>

(VAR_RES_FRAME_SPLIT f sr (wpb,rpb) wpb' sfb_context
   (BAG_UNION
      (var_res_prop___var_eq_const_BAG f vcL)
      sfb_split)
   sfb_imp sfb_restP))
``,

REPEAT STRIP_TAC THEN
IMP_RES_TAC VAR_RES_FRAME_SPLIT___equal_const___context THEN
POP_ASSUM MP_TAC THEN
MATCH_MP_TAC (prove (``(B = A) ==> (A ==> B)``, SIMP_TAC std_ss [])) THEN
REPEAT (POP_ASSUM (K ALL_TAC)) THEN
Q.SPEC_TAC (`sfb_context`, `sfb_context`) THEN

Induct_on `vcL` THEN
ASM_SIMP_TAC std_ss [var_res_prop___var_eq_const_BAG_THM,
   BAG_UNION_EMPTY, BAG_UNION_INSERT,
   VAR_RES_FRAME_SPLIT___PURE_PROPOSITION___TO_CONTEXT,
   VAR_RES_IS_PURE_PROPOSITION___BASIC_PROPS]);



val VAR_RES_FRAME_SPLIT___equal_const_SING = store_thm ("VAR_RES_FRAME_SPLIT___equal_const_SING",
``!v c f wpb rpb wpb' sfb_context sfb_split sfb_imp sfb_restP sr.
((VAR_RES_FRAME_SPLIT f sr (wpb,rpb) wpb'
   (BAG_INSERT
      (var_res_prop_equal f (var_res_exp_var v) (var_res_exp_const c))
      (BAG_IMAGE (var_res_prop_var_update (v, c)) sfb_context))
   (BAG_IMAGE (var_res_prop_var_update (v, c)) sfb_split)
   (BAG_IMAGE (var_res_prop_var_update (v, c)) sfb_imp)
   sfb_restP) ==>

(VAR_RES_FRAME_SPLIT f sr (wpb,rpb) wpb' sfb_context
   (BAG_INSERT
      (var_res_prop_equal f (var_res_exp_var v) (var_res_exp_const c))
      sfb_split)
   sfb_imp sfb_restP))
``,

ASM_SIMP_TAC std_ss [VAR_RES_FRAME_SPLIT___equal_const___context_SING,
   VAR_RES_FRAME_SPLIT___PURE_PROPOSITION___TO_CONTEXT,
   VAR_RES_IS_PURE_PROPOSITION___BASIC_PROPS]);




val VAR_RES_FRAME_SPLIT___WEAK_COND_REWRITE = store_thm (
"VAR_RES_FRAME_SPLIT___WEAK_COND_REWRITE",
``!f wpb rpb wpb' sfb_context sfb_split sfb_imp sfb_context' sfb_split' sfb_imp' sfb_restP sr.

(BAG_ALL_DISTINCT (BAG_UNION wpb rpb) ==>
 (sfb_context = sfb_context') /\
 (sfb_split = sfb_split') /\
 (sfb_imp = sfb_imp')) ==>

((VAR_RES_FRAME_SPLIT f sr (wpb,rpb) wpb'
   sfb_context sfb_split sfb_imp sfb_restP) =
 (VAR_RES_FRAME_SPLIT f sr (wpb,rpb) wpb'
   sfb_context' sfb_split' sfb_imp' sfb_restP))
``,

REPEAT STRIP_TAC THEN
Cases_on `BAG_ALL_DISTINCT (BAG_UNION wpb rpb)` THEN1 (
   FULL_SIMP_TAC std_ss []
) THEN
`!sfb. ~(var_res_prop___COND f (wpb,rpb) sfb)` by
  FULL_SIMP_TAC std_ss [var_res_prop___COND___REWRITE] THEN
ASM_SIMP_TAC std_ss [VAR_RES_FRAME_SPLIT_def]);





val VAR_RES_FRAME_SPLIT___COND_PROP_STRONG_IMP =
store_thm ("VAR_RES_FRAME_SPLIT___COND_PROP_STRONG_IMP",
``!f wpb rpb wpb' sfb_context  sfb_split sfb_imp
                sfb_context' sfb_split' sfb_imp' sfb_restP sr.

((COND_PROP___STRONG_IMP (var_res_prop f (wpb,rpb) sfb_context)
                        (var_res_prop f (wpb,rpb) sfb_context')) /\
(COND_PROP___STRONG_IMP (var_res_prop f (wpb,rpb) sfb_split)
                        (var_res_prop f (wpb,rpb) sfb_split')) /\
(COND_PROP___STRONG_IMP (var_res_prop f (wpb,rpb) sfb_imp)
                        (var_res_prop f (wpb,rpb) sfb_imp'))) ==>

((VAR_RES_FRAME_SPLIT f sr (wpb,rpb) wpb'
   sfb_context' sfb_split' sfb_imp' sfb_restP) ==>
(VAR_RES_FRAME_SPLIT f sr (wpb,rpb) wpb'
   sfb_context sfb_split sfb_imp sfb_restP))``,


REPEAT STRIP_TAC THEN
FULL_SIMP_TAC (std_ss++CONJ_ss)
   [VAR_RES_FRAME_SPLIT_EXPAND,
    var_res_prop___COND_UNION,
    var_res_prop___PROP_UNION,
    IN_ABS, GSYM RIGHT_EXISTS_AND_THM,
    GSYM LEFT_FORALL_IMP_THM,
    COND_PROP___EQUIV_REWRITE,
    var_res_prop___REWRITE] THEN
STRIP_TAC THEN FULL_SIMP_TAC std_ss [] THEN
Q.EXISTS_TAC `sfb_rest`  THEN
ASM_REWRITE_TAC[] THEN
STRIP_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
`?sst sh. s = (sst,sh)` by (Cases_on `s` THEN SIMP_TAC std_ss []) THEN
FULL_SIMP_TAC (std_ss++CONJ_ss) [COND_PROP___STRONG_IMP_def,
            var_res_prop___REWRITE] THEN
Q.PAT_ASSUM `X ==> !s s1 s2. Y s s1 s2` MP_TAC THEN
ASM_SIMP_TAC std_ss [GSYM LEFT_EXISTS_IMP_THM] THEN
Q.EXISTS_TAC `s` THEN
Q.EXISTS_TAC `s1` THEN
Q.EXISTS_TAC `s2` THEN
ASM_SIMP_TAC std_ss [] THEN
METIS_TAC[]);





val VAR_RES_FRAME_SPLIT___COND_PROP_STRONG_EQUIV =
store_thm ("VAR_RES_FRAME_SPLIT___COND_PROP_STRONG_EQUIV",
``!f wpb rpb wpb' sfb_context  sfb_split sfb_imp
                sfb_context' sfb_split' sfb_imp' sfb_restP sr.

((COND_PROP___STRONG_EQUIV (var_res_prop f (wpb,rpb) sfb_context)
                        (var_res_prop f (wpb,rpb) sfb_context')) /\
(COND_PROP___STRONG_EQUIV (var_res_prop f (wpb,rpb) sfb_split)
                        (var_res_prop f (wpb,rpb) sfb_split')) /\
(COND_PROP___STRONG_EQUIV (var_res_prop f (wpb,rpb) sfb_imp)
                        (var_res_prop f (wpb,rpb) sfb_imp'))) ==>

((VAR_RES_FRAME_SPLIT f sr (wpb,rpb) wpb'
   sfb_context' sfb_split' sfb_imp' sfb_restP) =
(VAR_RES_FRAME_SPLIT f sr (wpb,rpb) wpb'
   sfb_context sfb_split sfb_imp sfb_restP))``,

REPEAT STRIP_TAC THEN
FULL_SIMP_TAC std_ss [COND_PROP___STRONG_EQUIV_def] THEN
EQ_TAC THEN
MATCH_MP_TAC VAR_RES_FRAME_SPLIT___COND_PROP_STRONG_IMP THEN
ASM_REWRITE_TAC[]);



val VAR_RES_FRAME_SPLIT___asl_star___context =
store_thm ("VAR_RES_FRAME_SPLIT___asl_star___context",
``!f f' P1 P2 wpb rpb wpb' sfb_context  sfb_split sfb_imp sfb_restP sr.

(IS_VAR_RES_COMBINATOR f /\ (GET_VAR_RES_COMBINATOR f = f') /\
(VAR_RES_IS_STACK_IMPRECISE___USED_VARS (SET_OF_BAG (BAG_UNION wpb rpb)) P1) /\
(VAR_RES_IS_STACK_IMPRECISE___USED_VARS (SET_OF_BAG (BAG_UNION wpb rpb)) P2)) ==>

((VAR_RES_FRAME_SPLIT f' sr (wpb,rpb) wpb'
   (BAG_INSERT (asl_star f P1 P2) sfb_context) sfb_split sfb_imp sfb_restP) =
(VAR_RES_FRAME_SPLIT f' sr (wpb,rpb) wpb'
   (BAG_INSERT P1 (BAG_INSERT P2 sfb_context)) sfb_split sfb_imp sfb_restP))``,

REPEAT STRIP_TAC THEN
MATCH_MP_TAC VAR_RES_FRAME_SPLIT___COND_PROP_STRONG_EQUIV THEN
ASM_SIMP_TAC std_ss [COND_PROP___STRONG_EQUIV___REFL,
   var_res_prop___asl_star]);



val VAR_RES_FRAME_SPLIT___asl_star___imp =
store_thm ("VAR_RES_FRAME_SPLIT___asl_star___imp",
``!f f' P1 P2 wpb rpb wpb' sfb_context  sfb_split sfb_imp sfb_restP sr.

(IS_VAR_RES_COMBINATOR f /\ (GET_VAR_RES_COMBINATOR f = f') /\
(VAR_RES_IS_STACK_IMPRECISE___USED_VARS (SET_OF_BAG (BAG_UNION wpb rpb)) P1) /\
(VAR_RES_IS_STACK_IMPRECISE___USED_VARS (SET_OF_BAG (BAG_UNION wpb rpb)) P2)) ==>

((VAR_RES_FRAME_SPLIT f' sr (wpb,rpb) wpb' sfb_context sfb_split
   (BAG_INSERT (asl_star f P1 P2) sfb_imp) sfb_restP) =
 (VAR_RES_FRAME_SPLIT f' sr (wpb,rpb) wpb' sfb_context sfb_split
   (BAG_INSERT P1 (BAG_INSERT P2 sfb_imp)) sfb_restP))``,

REPEAT STRIP_TAC THEN
MATCH_MP_TAC VAR_RES_FRAME_SPLIT___COND_PROP_STRONG_EQUIV THEN
ASM_SIMP_TAC std_ss [COND_PROP___STRONG_EQUIV___REFL,
   var_res_prop___asl_star]);




val VAR_RES_FRAME_SPLIT___asl_star___split =
store_thm ("VAR_RES_FRAME_SPLIT___asl_star___split",
``!f f' P1 P2 wpb rpb wpb' sfb_context  sfb_split sfb_imp sfb_restP sr.

(IS_VAR_RES_COMBINATOR f /\ (GET_VAR_RES_COMBINATOR f = f') /\
(VAR_RES_IS_STACK_IMPRECISE___USED_VARS (SET_OF_BAG (BAG_UNION wpb rpb)) P1) /\
(VAR_RES_IS_STACK_IMPRECISE___USED_VARS (SET_OF_BAG (BAG_UNION wpb rpb)) P2)) ==>

((VAR_RES_FRAME_SPLIT f' sr (wpb,rpb) wpb' sfb_context
   (BAG_INSERT (asl_star f P1 P2) sfb_split) sfb_imp sfb_restP) =
 (VAR_RES_FRAME_SPLIT f' sr (wpb,rpb) wpb' sfb_context
   (BAG_INSERT P1 (BAG_INSERT P2 sfb_split)) sfb_imp sfb_restP))``,

REPEAT STRIP_TAC THEN
MATCH_MP_TAC VAR_RES_FRAME_SPLIT___COND_PROP_STRONG_EQUIV THEN
ASM_SIMP_TAC std_ss [COND_PROP___STRONG_EQUIV___REFL,
   var_res_prop___asl_star]);




val VAR_RES_FRAME_SPLIT___COND_PROP___STRONG_EXISTS___imp =
store_thm ("VAR_RES_FRAME_SPLIT___COND_PROP___STRONG_EXISTS___imp",
``!f wpb rpb wpb' sfb_context sfb_split sfb_imp sfb_imp' sfb_restP sr.

(COND_PROP___STRONG_IMP
   (var_res_prop f (wpb, rpb) sfb_imp)
   (COND_PROP___STRONG_EXISTS (\x. var_res_prop f (wpb, rpb) (sfb_imp' x)))) ==>

(?x. (VAR_RES_FRAME_SPLIT f sr (wpb,rpb) wpb' sfb_context sfb_split
     (sfb_imp' x) sfb_restP)) ==>
(VAR_RES_FRAME_SPLIT f sr (wpb,rpb) wpb' sfb_context sfb_split
   sfb_imp sfb_restP)
``,

SIMP_TAC std_ss [VAR_RES_FRAME_SPLIT_EXPAND,
   var_res_prop___COND_UNION,  var_res_prop___COND_INSERT,
   COND_PROP___STRONG_EXISTS_def,
   COND_PROP___STRONG_IMP_def,
   var_res_prop___REWRITE] THEN
REPEAT STRIP_TAC THEN
FULL_SIMP_TAC std_ss [] THEN
Q.EXISTS_TAC `sfb_rest` THEN
ASM_REWRITE_TAC[] THEN
REPEAT STRIP_TAC THEN
FULL_SIMP_TAC std_ss [] THEN
Q.PAT_ASSUM `!x. var_res_prop___COND f X Y` ASSUME_TAC THEN
FULL_SIMP_TAC std_ss [] THEN
Q.PAT_ASSUM `!s. X ==> Y` (MP_TAC o Q.SPEC `s`) THEN
ASM_SIMP_TAC (std_ss++CONJ_ss) [var_res_prop___PROP_UNION,
   var_res_prop___COND_UNION] THEN
SIMP_TAC std_ss [IN_ABS, asl_bool_EVAL] THEN
METIS_TAC[]);



val VAR_RES_FRAME_SPLIT___asl_exists___imp =
store_thm ("VAR_RES_FRAME_SPLIT___asl_exists___imp",
``!f P wpb rpb wpb' sfb_context  sfb_split sfb_imp sfb_restP sr.

(!y. VAR_RES_IS_STACK_IMPRECISE___USED_VARS (SET_OF_BAG (BAG_UNION wpb rpb)) (P y)) ==>

((?y. (VAR_RES_FRAME_SPLIT f sr (wpb,rpb) wpb' sfb_context sfb_split
   (BAG_INSERT (P y) sfb_imp) sfb_restP)) ==>
(VAR_RES_FRAME_SPLIT f sr (wpb,rpb) wpb' sfb_context sfb_split
   (BAG_INSERT (asl_exists y. P y) sfb_imp) sfb_restP))``,

REPEAT GEN_TAC THEN STRIP_TAC THEN
HO_MATCH_MP_TAC VAR_RES_FRAME_SPLIT___COND_PROP___STRONG_EXISTS___imp THEN
ASM_SIMP_TAC std_ss [var_res_prop___asl_exists,
      COND_PROP___STRONG_IMP___REFL]);



val VAR_RES_FRAME_SPLIT___COND_PROP___STRONG_IMP_EXISTS___split =
store_thm ("VAR_RES_FRAME_SPLIT___COND_PROP___STRONG_IMP_EXISTS___split",
``!f wpb rpb wpb' sfb_context sfb_split sfb_split' sfb_imp sfb_restP sr.

(COND_PROP___STRONG_IMP
   (var_res_prop f (wpb, rpb) sfb_split)
   (COND_PROP___STRONG_EXISTS (\x. var_res_prop f (wpb, rpb) (sfb_split' x)))) ==>

(!x. (VAR_RES_FRAME_SPLIT f sr (wpb,rpb) wpb' sfb_context
     (sfb_split' x) sfb_imp sfb_restP)) ==>
(VAR_RES_FRAME_SPLIT f sr (wpb,rpb) wpb' sfb_context sfb_split
   sfb_imp sfb_restP)
``,

SIMP_TAC std_ss [VAR_RES_FRAME_SPLIT_def,
   var_res_prop___COND_UNION,  var_res_prop___COND_INSERT,
   COND_PROP___STRONG_EXISTS_def,
   COND_PROP___STRONG_IMP_def,
   var_res_prop___REWRITE] THEN
REPEAT STRIP_TAC THEN
FULL_SIMP_TAC std_ss [] THEN

Tactical.REVERSE (Cases_on `var_res_prop___COND f (wpb,rpb) sfb_context /\
          var_res_prop___COND f (wpb,rpb) sfb_split /\
          var_res_prop___COND f (wpb,rpb) sfb_imp`) THEN1 (
    FULL_SIMP_TAC std_ss [] THEN PROVE_TAC[]) THEN
FULL_SIMP_TAC std_ss [] THEN
Q.PAT_ASSUM `!x. var_res_prop___COND f X Y` ASSUME_TAC THEN

`!s. var_res_prop___PROP f (wpb,rpb) (sfb_split + sfb_context) s =
     ?x. var_res_prop___PROP f (wpb,rpb) (sfb_split' x + sfb_context) s` by ALL_TAC THEN1 (
   FULL_SIMP_TAC std_ss [var_res_prop___COND_UNION,
      var_res_prop___PROP_UNION,
      GSYM LEFT_FORALL_IMP_THM, asl_bool_EVAL,
      GSYM RIGHT_EXISTS_AND_THM, GSYM LEFT_EXISTS_AND_THM] THEN
   METIS_TAC[]
) THEN
FULL_SIMP_TAC std_ss [GSYM LEFT_FORALL_IMP_THM] THEN

Q.PAT_ASSUM `!x. ?sfb_rest. X` (MP_TAC o CONV_RULE SKOLEM_CONV) THEN
ASM_SIMP_TAC std_ss [FORALL_AND_THM] THEN

REPEAT STRIP_TAC THEN
Q.EXISTS_TAC `{| asl_exists x. var_res_bigstar f (sfb_rest x) |}` THEN
CONJ_TAC THEN1 (
   METIS_TAC [VAR_RES_FRAME_SPLIT___sfb_restP_OK___asl_exists_IMP]
) THEN
MATCH_MP_TAC (prove (``(A /\ (A ==> B)) ==> (A /\ B)``, METIS_TAC[])) THEN
CONJ_TAC THEN1 (
   FULL_SIMP_TAC std_ss [var_res_prop___COND___REWRITE,
      BAG_IN_BAG_INSERT, NOT_IN_EMPTY_BAG, FINITE_BAG_THM,
      FORALL_AND_THM] THEN
   HO_MATCH_MP_TAC VAR_RES_IS_STACK_IMPRECISE___USED_VARS___asl_exists_direct THEN
   GEN_TAC THEN
   HO_MATCH_MP_TAC (MP_CANON VAR_RES_IS_STACK_IMPRECISE___USED_VARS___var_res_bigstar) THEN
   ASM_SIMP_TAC std_ss [BAG_EVERY] THEN
   METIS_TAC[]
) THEN
REPEAT STRIP_TAC THEN
`IS_SEPARATION_COMBINATOR f` by FULL_SIMP_TAC std_ss [var_res_prop___COND___REWRITE] THEN
Q.PAT_ASSUM `!x s. X` (MP_TAC o Q.SPECL [`x`, `s`]) THEN
ASM_SIMP_TAC (std_ss++CONJ_ss) [
      var_res_prop___PROP___REWRITE,
      var_res_bigstar_UNION, var_res_bigstar_REWRITE,
      GSYM asl_exists___asl_star_THM,
      asl_bool_EVAL, var_res_bigstar___var_res_prop_stack_true___asl_star_ELIM] THEN
REPEAT STRIP_TAC THEN
Q.EXISTS_TAC `x` THEN
ASM_REWRITE_TAC[]);




val VAR_RES_FRAME_SPLIT___COND_PROP___EQ_EXISTS___split =
store_thm ("VAR_RES_FRAME_SPLIT___COND_PROP___EQ_EXISTS___split",
``!f wpb rpb wpb' sfb_context sfb_split sfb_split' sfb_imp sfb_restP sr.

 ((!x. var_res_prop___COND f (wpb,rpb) (sfb_split' x) =
      var_res_prop___COND f (wpb,rpb) sfb_split) /\

 (var_res_prop___COND f (wpb,rpb) sfb_split ==>
 (var_res_prop___PROP f (wpb, rpb) sfb_split =
  asl_exists x. var_res_prop___PROP f (wpb,rpb) (sfb_split' x)))) ==>

 ((VAR_RES_FRAME_SPLIT f sr (wpb,rpb) wpb' sfb_context sfb_split
   sfb_imp sfb_restP) =
 (!x. (VAR_RES_FRAME_SPLIT f sr (wpb,rpb) wpb' sfb_context
     (sfb_split' x) sfb_imp sfb_restP)))``,

REPEAT STRIP_TAC THEN
Tactical.REVERSE EQ_TAC THEN1 (
   MATCH_MP_TAC VAR_RES_FRAME_SPLIT___COND_PROP___STRONG_IMP_EXISTS___split THEN
   ASM_SIMP_TAC std_ss [COND_PROP___STRONG_IMP_def, COND_PROP___STRONG_EXISTS_def,
      var_res_prop___REWRITE]
) THEN
FULL_SIMP_TAC std_ss [VAR_RES_FRAME_SPLIT_EXPAND,
   var_res_prop___COND_UNION,  var_res_prop___COND_INSERT,
   var_res_prop___REWRITE] THEN
REPEAT STRIP_TAC THEN
FULL_SIMP_TAC std_ss [] THEN
Q.EXISTS_TAC `sfb_rest` THEN
ASM_SIMP_TAC std_ss [] THEN
REPEAT STRIP_TAC THEN
FULL_SIMP_TAC std_ss [] THEN
Q.PAT_ASSUM `!x. X s ==> Y s` MATCH_MP_TAC THEN
Q.PAT_ASSUM `var_res_prop___PROP f (wpb,rpb) X s` MP_TAC THEN

ASM_SIMP_TAC std_ss [var_res_prop___PROP_UNION,
   var_res_prop___COND_UNION, asl_bool_EVAL] THEN
METIS_TAC[]);



val VAR_RES_FRAME_SPLIT___asl_exists___split =
store_thm ("VAR_RES_FRAME_SPLIT___asl_exists___split",
``!f P wpb rpb wpb' sfb_context  sfb_split sfb_imp sfb_restP sr.

(!y. VAR_RES_IS_STACK_IMPRECISE___USED_VARS (SET_OF_BAG (BAG_UNION wpb rpb)) (P y)) ==>

((VAR_RES_FRAME_SPLIT f sr (wpb,rpb) wpb' sfb_context
   (BAG_INSERT (asl_exists y. P y) sfb_split) sfb_imp sfb_restP) =
(!y. (VAR_RES_FRAME_SPLIT f sr (wpb,rpb) wpb' sfb_context
   (BAG_INSERT (P y) sfb_split) sfb_imp sfb_restP)))
``,


REPEAT STRIP_TAC THEN
Tactical.REVERSE (Cases_on `var_res_prop___COND f (wpb,rpb) sfb_split`) THEN1 (
   ASM_SIMP_TAC std_ss [VAR_RES_FRAME_SPLIT_def,
      var_res_prop___COND_UNION, var_res_prop___COND_INSERT]
) THEN
HO_MATCH_MP_TAC VAR_RES_FRAME_SPLIT___COND_PROP___EQ_EXISTS___split THEN
`IS_SEPARATION_COMBINATOR f` by FULL_SIMP_TAC std_ss [var_res_prop___COND___REWRITE] THEN
ASM_SIMP_TAC std_ss [var_res_prop___COND_INSERT,
   var_res_prop___PROP___asl_exists] THEN
MATCH_MP_TAC VAR_RES_IS_STACK_IMPRECISE___USED_VARS___asl_exists_direct THEN
ASM_SIMP_TAC std_ss []);







val VAR_RES_FRAME_SPLIT___CONST_INTRO = store_thm ("VAR_RES_FRAME_SPLIT___CONST_INTRO",
``!e f wpb rpb wpb' sfb_context sfb_split sfb_imp sfb_restP sr.
(VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET (SET_OF_BAG (BAG_UNION wpb rpb)) e) ==>
((VAR_RES_FRAME_SPLIT f sr (wpb,rpb) wpb' sfb_context
   sfb_split sfb_imp sfb_restP) =
 (!c. ((VAR_RES_FRAME_SPLIT f sr (wpb,rpb) wpb'
   sfb_context
   (BAG_INSERT
      (var_res_prop_equal f e (var_res_exp_const c)) sfb_split)
   sfb_imp) sfb_restP)))``,

REPEAT STRIP_TAC THEN
HO_MATCH_MP_TAC VAR_RES_FRAME_SPLIT___COND_PROP___EQ_EXISTS___split THEN
SIMP_TAC (std_ss++CONJ_ss++EQUIV_EXTRACT_ss) [
   asl_bool_EVAL,
   var_res_prop___COND_INSERT,
   var_res_prop___PROP_INSERT] THEN
REPEAT STRIP_TAC THEN1 (
   ASM_SIMP_TAC std_ss [VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET___VAR_CONST_EVAL,
       VAR_RES_IS_STACK_IMPRECISE___USED_VARS___var_res_prop_equal,
       VAR_RES_IS_STACK_IMPRECISE___USED_VARS___asl_exists_direct]
) THEN

`?uf. IS_SEPARATION_COMBINATOR_NEUTRAL_ELEMENT_FUNCTION___WITH_COMBINATOR f uf` by
   PROVE_TAC[IS_SEPARATION_COMBINATOR_NEUTRAL_ELEMENT_FUNCTION_IMP,
      var_res_prop___COND___REWRITE] THEN
FULL_SIMP_TAC std_ss [IS_SEPARATION_COMBINATOR_NEUTRAL_ELEMENT_FUNCTION___WITH_COMBINATOR_THM] THEN
ASM_SIMP_TAC (std_ss++CONJ_ss) [var_res_prop_equal_unequal_EXPAND,
   IN_ABS, asl_emp_def, var_res_exp_const_def,
   IS_SOME_EXISTS, GSYM LEFT_EXISTS_AND_THM, GSYM RIGHT_EXISTS_AND_THM,
   EXTENSION, asl_bool_EVAL] THEN
QUANT_INSTANTIATE_TAC[] THEN

SIMP_TAC (std_ss++EQUIV_EXTRACT_ss) [GSYM IS_SOME_EXISTS] THEN
REPEAT STRIP_TAC THEN
MATCH_MP_TAC VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET___IS_SOME_IMPL THEN
Q.EXISTS_TAC `SET_OF_BAG (BAG_UNION wpb rpb)` THEN
METIS_TAC [var_res_prop___PROP___VARS])





val VAR_RES_FRAME_SPLIT___COND_PROP___STRONG_EXISTS___context =
store_thm ("VAR_RES_FRAME_SPLIT___COND_PROP___STRONG_EXISTS___context",
``!f wpb rpb wpb' sfb_context sfb_context' sfb_split sfb_imp sfb_restP sr.

(COND_PROP___STRONG_IMP
   (var_res_prop f (wpb, rpb) sfb_context)
   (COND_PROP___STRONG_EXISTS (\x. var_res_prop f (wpb, rpb) (sfb_context' x)))) ==>

(!x. (VAR_RES_FRAME_SPLIT f sr (wpb,rpb) wpb'
     (sfb_context' x) sfb_split sfb_imp sfb_restP)) ==>
(VAR_RES_FRAME_SPLIT f sr (wpb,rpb) wpb' sfb_context sfb_split
   sfb_imp sfb_restP)
``,

ONCE_REWRITE_TAC [VAR_RES_FRAME_SPLIT___ELIM_CONTEXT] THEN
REPEAT STRIP_TAC THEN
`!sfb. COND_PROP___STRONG_IMP
    (var_res_prop f (wpb,rpb) (sfb_context + sfb))
    (COND_PROP___STRONG_EXISTS
       (\x. var_res_prop f (wpb,rpb)
             ((\x. sfb_context' x + sfb) x)))` by ALL_TAC THEN1 (
   FULL_SIMP_TAC std_ss [COND_PROP___STRONG_IMP_def,
      var_res_prop___REWRITE, COND_PROP___STRONG_EXISTS_def,
      var_res_prop___COND_UNION, IN_ABS,
      var_res_prop___PROP_UNION, asl_exists_def, GSYM RIGHT_EXISTS_AND_THM,
      GSYM LEFT_EXISTS_AND_THM] THEN
   METIS_TAC[]
) THEN

HO_MATCH_MP_TAC (MP_CANON VAR_RES_FRAME_SPLIT___COND_PROP___STRONG_IMP_EXISTS___split) THEN
Q.EXISTS_TAC `\x. BAG_UNION (sfb_context' x) sfb_split` THEN
ASM_SIMP_TAC std_ss [] THEN GEN_TAC THEN

HO_MATCH_MP_TAC (MP_CANON VAR_RES_FRAME_SPLIT___COND_PROP___STRONG_EXISTS___imp) THEN
Q.EXISTS_TAC `\x. BAG_UNION (sfb_context' x) sfb_imp` THEN
ASM_SIMP_TAC std_ss [] THEN
Q.EXISTS_TAC `x` THEN
ASM_SIMP_TAC std_ss []);




val VAR_RES_FRAME_SPLIT___asl_exists___context =
store_thm ("VAR_RES_FRAME_SPLIT___asl_exists___context",
``!f P wpb rpb wpb' sfb_context  sfb_split sfb_imp sfb_restP sr.

(!y. VAR_RES_IS_STACK_IMPRECISE___USED_VARS (SET_OF_BAG (BAG_UNION wpb rpb)) (P y)) ==>

(!y. (VAR_RES_FRAME_SPLIT f sr (wpb,rpb) wpb'
   (BAG_INSERT (P y) sfb_context) sfb_split sfb_imp sfb_restP)) ==>
(VAR_RES_FRAME_SPLIT f sr (wpb,rpb) wpb'
   (BAG_INSERT (asl_exists y. P y) sfb_context) sfb_split sfb_imp sfb_restP)``,

REPEAT GEN_TAC THEN STRIP_TAC THEN
HO_MATCH_MP_TAC VAR_RES_FRAME_SPLIT___COND_PROP___STRONG_EXISTS___context THEN
ASM_SIMP_TAC std_ss [var_res_prop___asl_exists,
   COND_PROP___STRONG_IMP___REFL]);


val VAR_RES_FRAME_SPLIT___REWRITE_OK___stack_true =
store_thm ("VAR_RES_FRAME_SPLIT___REWRITE_OK___stack_true",
``
(VAR_RES_FRAME_SPLIT___REWRITE_OK f (wpb,rpb)
   (BAG_INSERT (var_res_prop_stack_true f) sfb_context)  sfb_split  sfb_imp =
 VAR_RES_FRAME_SPLIT___REWRITE_OK f (wpb,rpb)
   sfb_context  sfb_split  sfb_imp) /\

(VAR_RES_FRAME_SPLIT___REWRITE_OK f (wpb,rpb)
   sfb_context  (BAG_INSERT (var_res_prop_stack_true f) sfb_split) sfb_imp =
 VAR_RES_FRAME_SPLIT___REWRITE_OK f (wpb,rpb)
   sfb_context  sfb_split  sfb_imp) /\

(VAR_RES_FRAME_SPLIT___REWRITE_OK f (wpb,rpb)
   sfb_context  sfb_split  (BAG_INSERT (var_res_prop_stack_true f) sfb_imp) =
 VAR_RES_FRAME_SPLIT___REWRITE_OK f (wpb,rpb)
   sfb_context  sfb_split  sfb_imp) /\

(VAR_RES_FRAME_SPLIT___REWRITE_OK f (wpb,rpb)
   sfb_context  sfb_split  sfb_imp
   (BAG_INSERT (var_res_prop_stack_true f) sfb_context') sfb_split' sfb_imp' =
 VAR_RES_FRAME_SPLIT___REWRITE_OK f (wpb,rpb)
   sfb_context  sfb_split  sfb_imp
   sfb_context' sfb_split' sfb_imp') /\

(VAR_RES_FRAME_SPLIT___REWRITE_OK f (wpb,rpb)
   sfb_context  sfb_split  sfb_imp
   sfb_context' (BAG_INSERT (var_res_prop_stack_true f) sfb_split') sfb_imp' =
 VAR_RES_FRAME_SPLIT___REWRITE_OK f (wpb,rpb)
   sfb_context  sfb_split  sfb_imp
   sfb_context' sfb_split' sfb_imp') /\

(VAR_RES_FRAME_SPLIT___REWRITE_OK f (wpb,rpb)
   sfb_context  sfb_split  sfb_imp
   sfb_context' sfb_split' (BAG_INSERT (var_res_prop_stack_true f) sfb_imp') =
 VAR_RES_FRAME_SPLIT___REWRITE_OK f (wpb,rpb)
   sfb_context  sfb_split  sfb_imp
   sfb_context' sfb_split' sfb_imp')``,


SIMP_TAC std_ss [FUN_EQ_THM, VAR_RES_FRAME_SPLIT___REWRITE_OK___REWRITE,
   var_res_prop___COND_INSERT, BAG_UNION_INSERT,
   VAR_RES_IS_STACK_IMPRECISE___USED_VARS___var_res_prop_stack_true,
   var_res_prop___PROP___var_res_prop_stack_true]);





val VAR_RES_FRAME_SPLIT___stack_true =
store_thm ("VAR_RES_FRAME_SPLIT___stack_true",
``(!f wpb rpb wpb' sfb_context  sfb_split  sfb_imp sfb_restP sr.
((VAR_RES_FRAME_SPLIT f sr (wpb,rpb) wpb'
   sfb_context sfb_split (BAG_INSERT (var_res_prop_stack_true f) sfb_imp) sfb_restP) =
(VAR_RES_FRAME_SPLIT f sr (wpb,rpb) wpb' sfb_context sfb_split sfb_imp sfb_restP))) /\

(!f wpb rpb wpb' sfb_context  sfb_split  sfb_imp sfb_restP sr.
((VAR_RES_FRAME_SPLIT f sr (wpb,rpb) wpb'
   sfb_context (BAG_INSERT (var_res_prop_stack_true f) sfb_split) sfb_imp sfb_restP) =
(VAR_RES_FRAME_SPLIT f sr (wpb,rpb) wpb' sfb_context sfb_split sfb_imp sfb_restP))) /\

(!f wpb rpb wpb' sfb_context  sfb_split  sfb_imp sfb_restP sr.
((VAR_RES_FRAME_SPLIT f sr (wpb,rpb) wpb'
   (BAG_INSERT (var_res_prop_stack_true f) sfb_context) sfb_split sfb_imp sfb_restP) =
(VAR_RES_FRAME_SPLIT f sr (wpb,rpb) wpb' sfb_context sfb_split sfb_imp sfb_restP)))
``,

REPEAT STRIP_TAC THEN
MATCH_MP_TAC VAR_RES_FRAME_SPLIT___COND_PROP_STRONG_EQUIV THEN
ONCE_REWRITE_TAC[COND_PROP___STRONG_EQUIV___SYM] THEN
REWRITE_TAC [COND_PROP___STRONG_EQUIV___var_res_prop_stack_true,
             COND_PROP___STRONG_EQUIV___REFL]);


val VAR_RES_FRAME_SPLIT___stack_true___context =
   save_thm ("VAR_RES_FRAME_SPLIT___stack_true___context",
   el 3 (CONJUNCTS VAR_RES_FRAME_SPLIT___stack_true));

val VAR_RES_FRAME_SPLIT___stack_true___split =
   save_thm ("VAR_RES_FRAME_SPLIT___stack_true___split",
   el 2 (CONJUNCTS VAR_RES_FRAME_SPLIT___stack_true));

val VAR_RES_FRAME_SPLIT___stack_true___imp =
   save_thm ("VAR_RES_FRAME_SPLIT___stack_true___imp",
   el 1 (CONJUNCTS VAR_RES_FRAME_SPLIT___stack_true));


val VAR_RES_FRAME_SPLIT___SOLVE = store_thm ("VAR_RES_FRAME_SPLIT___SOLVE",
``!rfc f wpb rpb wpb' sfb_context sfb_split sfb_restP.
(BAG_EVERY (VAR_RES_IS_STACK_IMPRECISE___USED_VARS (SET_OF_BAG
           (BAG_DIFF (BAG_UNION wpb rpb) wpb'))) sfb_split) ==>
(~(VAR_RES_PROP_IS_EQUIV_FALSE (SND rfc) f (wpb,rpb) (BAG_UNION sfb_context sfb_split)) ==>
  (sfb_restP sfb_split)) ==>
VAR_RES_FRAME_SPLIT f rfc (wpb,rpb) wpb' sfb_context sfb_split EMPTY_BAG sfb_restP``,

REPEAT STRIP_TAC THEN
`VAR_RES_FRAME_SPLIT f rfc (wpb,rpb) wpb' sfb_context sfb_split
                {|var_res_prop_stack_true f|} sfb_restP` by
   METIS_TAC[REWRITE_RULE [var_res_bool_proposition_TF] (SPEC ``T`` VAR_RES_FRAME_SPLIT___SOLVE___bool_prop)] THEN
FULL_SIMP_TAC std_ss [VAR_RES_FRAME_SPLIT___stack_true]);


val VAR_RES_FRAME_SPLIT___SOLVE_WEAK = store_thm ("VAR_RES_FRAME_SPLIT___SOLVE_WEAK",
``!rfc f wpb rpb wpb' sfb_context sfb_split sfb_restP.
(BAG_EVERY (VAR_RES_IS_STACK_IMPRECISE___USED_VARS (SET_OF_BAG
           (BAG_DIFF (BAG_UNION wpb rpb) wpb'))) sfb_split) ==>
(sfb_restP sfb_split ==>
VAR_RES_FRAME_SPLIT f rfc (wpb,rpb) wpb' sfb_context sfb_split EMPTY_BAG sfb_restP)``,
SIMP_TAC std_ss [VAR_RES_FRAME_SPLIT___SOLVE]);


val VAR_RES_FRAME_SPLIT___asl_false___context =
store_thm ("VAR_RES_FRAME_SPLIT___asl_false___context",
``!f strong_rest wpb rpb wpb' sfb_context sfb_split sfb_imp sfb_restP.
  VAR_RES_FRAME_SPLIT f strong_rest (wpb,rpb) wpb'
     (BAG_INSERT asl_false sfb_context)  sfb_split sfb_imp sfb_restP``,
SIMP_TAC std_ss [
   VAR_RES_FRAME_SPLIT_EXPAND, BAG_UNION_INSERT, var_res_prop___COND_UNION,
   var_res_prop___COND_INSERT, var_res_prop___PROP_INSERT,
   asl_bool_EVAL, VAR_RES_FRAME_SPLIT___sfb_restP_OK_def]);



val VAR_RES_FRAME_SPLIT___asl_false___split =
store_thm ("VAR_RES_FRAME_SPLIT___asl_false___split",
``!f strong_rest wpb rpb wpb' sfb_context sfb_split sfb_imp sfb_restP.
  VAR_RES_FRAME_SPLIT f strong_rest (wpb,rpb) wpb' sfb_context
     (BAG_INSERT asl_false sfb_split) sfb_imp sfb_restP``,
SIMP_TAC std_ss [
   VAR_RES_FRAME_SPLIT_EXPAND, BAG_UNION_INSERT, var_res_prop___COND_UNION,
   var_res_prop___COND_INSERT, var_res_prop___PROP_INSERT,
   asl_bool_EVAL, VAR_RES_FRAME_SPLIT___sfb_restP_OK_def]);



val VAR_RES_FRAME_SPLIT___bool_proposition___context =
store_thm ("VAR_RES_FRAME_SPLIT___bool_proposition___context",
``!f wpb rpb wpb' sfb_context  sfb_split  sfb_imp sfb_restP c sr.

((VAR_RES_FRAME_SPLIT f sr (wpb,rpb) wpb'
   (BAG_INSERT (var_res_bool_proposition f c) sfb_context) sfb_split sfb_imp sfb_restP) =
 (c ==> (VAR_RES_FRAME_SPLIT f sr (wpb,rpb) wpb' sfb_context sfb_split sfb_imp sfb_restP)))
``,

Cases_on `c` THENL [
   SIMP_TAC std_ss [var_res_bool_proposition_TF,
      VAR_RES_FRAME_SPLIT___stack_true],
   SIMP_TAC std_ss [var_res_bool_proposition_TF,
      VAR_RES_FRAME_SPLIT___asl_false___context]
]);


val VAR_RES_FRAME_SPLIT___bool_proposition___split =
store_thm ("VAR_RES_FRAME_SPLIT___bool_proposition___split",
``!f wpb rpb wpb' sfb_context  sfb_split  sfb_imp sfb_restP c sr.

((VAR_RES_FRAME_SPLIT f sr (wpb,rpb) wpb'
   sfb_context (BAG_INSERT (var_res_bool_proposition f c) sfb_split) sfb_imp sfb_restP) =
 (c ==> (VAR_RES_FRAME_SPLIT f sr (wpb,rpb) wpb' sfb_context sfb_split sfb_imp sfb_restP)))
``,

Cases_on `c` THENL [
   SIMP_TAC std_ss [var_res_bool_proposition_TF,
      VAR_RES_FRAME_SPLIT___stack_true],
   SIMP_TAC std_ss [var_res_bool_proposition_TF,
      VAR_RES_FRAME_SPLIT___asl_false___split]
]);


val VAR_RES_FRAME_SPLIT___bool_proposition___imp =
store_thm ("VAR_RES_FRAME_SPLIT___bool_proposition___imp",
``!f wpb rpb wpb' sfb_context  sfb_split  sfb_imp sfb_restP c1 c2 sr.

((VAR_RES_FRAME_SPLIT f sr (wpb,rpb) wpb'
   sfb_context sfb_split
    (BAG_INSERT (var_res_bool_proposition f c1)
        (BAG_INSERT (var_res_bool_proposition f c2) sfb_imp)) sfb_restP) =
 (VAR_RES_FRAME_SPLIT f sr (wpb,rpb) wpb' sfb_context sfb_split
    (BAG_INSERT (var_res_bool_proposition f (c1 /\ c2)) sfb_imp) sfb_restP))
``,

Cases_on `c1` THEN
SIMP_TAC std_ss [var_res_bool_proposition_TF,
   VAR_RES_FRAME_SPLIT___stack_true___imp] THEN

SIMP_TAC std_ss [VAR_RES_FRAME_SPLIT_def,
   var_res_prop___PROP___asl_false,
   BAG_UNION_INSERT, asl_bool_EVAL,
   var_res_prop___COND_INSERT,
   VAR_RES_IS_STACK_IMPRECISE___USED_VARS___asl_false,
   VAR_RES_IS_STACK_IMPRECISE___USED_VARS___var_res_bool_proposition]);



val VAR_RES_FRAME_SPLIT___trivial_cond___context =
store_thm ("VAR_RES_FRAME_SPLIT___trivial_cond___context",
``!f wpb rpb wpb' sfb_context  sfb_split  sfb_imp sfb_restP c P sr.

((VAR_RES_FRAME_SPLIT f sr (wpb,rpb) wpb'
   (BAG_INSERT (asl_trivial_cond c P) sfb_context) sfb_split sfb_imp sfb_restP) =
 (c ==> (VAR_RES_FRAME_SPLIT f sr (wpb,rpb) wpb'
   (BAG_INSERT P sfb_context) sfb_split sfb_imp sfb_restP)))
``,

Cases_on `c` THEN
SIMP_TAC std_ss [asl_trivial_cond_TF,
   VAR_RES_FRAME_SPLIT___asl_false___context])


val VAR_RES_FRAME_SPLIT___trivial_cond___split =
store_thm ("VAR_RES_FRAME_SPLIT___trivial_cond___split",
``!f wpb rpb wpb' sfb_context  sfb_split  sfb_imp sfb_restP c P sr.

((VAR_RES_FRAME_SPLIT f sr (wpb,rpb) wpb' sfb_context
   (BAG_INSERT (asl_trivial_cond c P) sfb_split) sfb_imp sfb_restP) =
 (c ==> (VAR_RES_FRAME_SPLIT f sr (wpb,rpb) wpb' sfb_context
   (BAG_INSERT P sfb_split) sfb_imp sfb_restP)))
``,

Cases_on `c` THEN
SIMP_TAC std_ss [asl_trivial_cond_TF,
   VAR_RES_FRAME_SPLIT___asl_false___split])


val VAR_RES_FRAME_SPLIT___trivial_cond___imp =
store_thm ("VAR_RES_FRAME_SPLIT___trivial_cond___imp",
``!f wpb rpb wpb' sfb_context  sfb_split  sfb_imp sfb_restP c P sr.

VAR_RES_IS_STACK_IMPRECISE___USED_VARS (SET_OF_BAG (wpb + rpb)) P ==>

((VAR_RES_FRAME_SPLIT f sr (wpb,rpb) wpb' sfb_context sfb_split
   (BAG_INSERT (asl_trivial_cond c P) sfb_imp) sfb_restP) =
 (VAR_RES_FRAME_SPLIT f sr (wpb,rpb) wpb' sfb_context sfb_split
   (BAG_INSERT (var_res_bool_proposition f c) (BAG_INSERT P sfb_imp)) sfb_restP))
``,

Cases_on `c` THEN
SIMP_TAC std_ss [asl_trivial_cond_TF,
   var_res_bool_proposition_TF,
   VAR_RES_FRAME_SPLIT___stack_true___imp] THEN
SIMP_TAC std_ss [VAR_RES_FRAME_SPLIT_def,
   var_res_prop___PROP___asl_false, BAG_UNION_INSERT,
   var_res_prop___COND_INSERT,
   VAR_RES_IS_STACK_IMPRECISE___USED_VARS___asl_false,
   asl_bool_EVAL]);



val VAR_RES_FRAME_SPLIT___JUST_COND___GUESS = store_thm (
"VAR_RES_FRAME_SPLIT___JUST_COND___GUESS",
``((c /\
VAR_RES_FRAME_SPLIT f strong_rest (wpb,rpb) wpb' sfb_context
       sfb_split {||} sfb_restP) ==>

VAR_RES_FRAME_SPLIT f strong_rest (wpb,rpb) wpb' sfb_context
       sfb_split {|var_res_bool_proposition f c|} sfb_restP) /\

((VAR_RES_FRAME_SPLIT f strong_rest (wpb,rpb) wpb' sfb_context
       sfb_split (BAG_INSERT (var_res_bool_proposition f c1)
                 (BAG_INSERT (var_res_bool_proposition f c2) sfb_imp))
       sfb_restP) =
VAR_RES_FRAME_SPLIT f strong_rest (wpb,rpb) wpb' sfb_context
       sfb_split (BAG_INSERT (var_res_bool_proposition f (c1 /\ c2))
                  sfb_imp) sfb_restP)``,

SIMP_TAC (std_ss++CONJ_ss) [
   VAR_RES_FRAME_SPLIT_EXPAND, BAG_UNION_EMPTY, BAG_UNION_INSERT,
   var_res_prop___COND_INSERT, var_res_prop___COND_UNION,
   VAR_RES_IS_STACK_IMPRECISE___USED_VARS___var_res_bool_proposition,
   var_res_prop___PROP___var_res_bool_proposition, IN_ABS] THEN
SIMP_TAC std_ss [IN_DEF, CONJ_ASSOC]);



val VAR_RES_PROP_IS_EQUIV_FALSE___ELIM =
store_thm ("VAR_RES_PROP_IS_EQUIV_FALSE___ELIM",
``F ==> VAR_RES_PROP_IS_EQUIV_FALSE c f (wpb,rpb) sfb``,
SIMP_TAC std_ss[]);



(*******************************************************
 * Implies unequal
 ******************************************************)


val var_res_implies_unequal_def = Define `
  var_res_implies_unequal f b e1 e2 =
  (!s. IS_SOME (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS e1) /\
       IS_SOME (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS e2) /\
       IS_SEPARATION_COMBINATOR f /\
       (s IN (var_res_bigstar f b)) ==>
       s IN var_res_prop_weak_unequal e1 e2)`;

val var_res_implies_unequal_SYM = store_thm ("var_res_implies_unequal_SYM",
``!f b e1 e2.
  var_res_implies_unequal f b e1 e2 =
  var_res_implies_unequal f b e2 e1``,

SIMP_TAC std_ss [var_res_implies_unequal_def] THEN
PROVE_TAC[ var_res_prop_weak_unequal_symmetric]);


val var_res_implies_unequal___SUB_BAG = store_thm (
"var_res_implies_unequal___SUB_BAG",
``!f sfb1 sfb2 e1 e2.
  (SUB_BAG sfb1 sfb2 /\
   var_res_implies_unequal f sfb1 e1 e2) ==>
   var_res_implies_unequal f sfb2 e1 e2``,

SIMP_TAC std_ss [var_res_implies_unequal_def,
   SUB_BAG_EXISTS, GSYM LEFT_EXISTS_AND_THM,
   GSYM RIGHT_EXISTS_AND_THM,
   GSYM LEFT_FORALL_IMP_THM,
   BAG_UNION_EMPTY] THEN
REPEAT STRIP_TAC THEN
Q.PAT_ASSUM `IS_SEPARATION_COMBINATOR f` ASSUME_TAC THEN
FULL_SIMP_TAC std_ss [var_res_bigstar_UNION,
   asl_star_def, IN_ABS,
   VAR_RES_COMBINATOR_REWRITE] THEN
`p IN var_res_prop_weak_unequal e1 e2` by PROVE_TAC[] THEN
POP_ASSUM MP_TAC THEN
SIMP_TAC std_ss [var_res_prop_equal_unequal_EXPAND,
   IN_ABS] THEN
Tactical.REVERSE (`
   (IS_SOME (e1 (FST p)) /\ IS_SOME (e2 (FST p))) ==>
   ((e1 (FST p) = e1 (FST s)) /\ (e2 (FST p) = e2 (FST s)))` by ALL_TAC) THEN1 (
   METIS_TAC[]
) THEN

CONSEQ_REWRITE_TAC ([], [
   IS_SOME___VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS___SUBSTATE_LEFT],
   []) THEN
ASM_SIMP_TAC std_ss [] THEN
METIS_TAC[VAR_RES_STACK_IS_SUBSTATE_INTRO]);




val var_res_implies_unequal___asl_exists = store_thm (
"var_res_implies_unequal___asl_exists",
``!f b P e1 e2. IS_SEPARATION_COMBINATOR f ==>
  (var_res_implies_unequal f (BAG_INSERT (asl_exists x. P x) b) e1 e2 =
  !x. var_res_implies_unequal f (BAG_INSERT (P x) b) e1 e2)``,

SIMP_TAC std_ss [var_res_implies_unequal_def,
   BAG_INSERT_NOT_EMPTY,
   var_res_bigstar_REWRITE_EXT,
   GSYM asl_exists___asl_star_THM, asl_bool_EVAL] THEN
PROVE_TAC[]);



val var_res_implies_unequal___trivial_context =
store_thm ("var_res_implies_unequal___trivial_context",
``!f b c1 c2. ~(c1 = c2) ==>
  var_res_implies_unequal f b (var_res_exp_const c1) (var_res_exp_const c2)``,

SIMP_TAC std_ss [var_res_implies_unequal_def,
   var_res_prop_equal_unequal_EXPAND,
   var_res_exp_const_def, IN_ABS]);


val var_res_implies_unequal___trivial_unequal =
store_thm ("var_res_implies_unequal___trivial_unequal",
``!f b e1 e2.
  BAG_IN (var_res_prop_unequal f e1 e2) b ==>
  var_res_implies_unequal f b e1 e2``,

REPEAT STRIP_TAC THEN
IMP_RES_TAC BAG_DECOMPOSE THEN
ASM_SIMP_TAC (std_ss++CONJ_ss) [var_res_implies_unequal_def,
   var_res_bigstar_REWRITE_EXT] THEN
REPEAT STRIP_TAC THEN
FULL_SIMP_TAC std_ss [asl_star_def,
   IN_ABS, VAR_RES_COMBINATOR_REWRITE,
   var_res_prop_equal_unequal_EXPAND] THEN
Tactical.REVERSE (`(e1 (FST s) = e1 (FST p)) /\ (e2 (FST s) = e2 (FST p))` by ALL_TAC) THEN1 (
   ASM_SIMP_TAC std_ss []
) THEN
CONSEQ_REWRITE_TAC ([],[
   IS_SOME___VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS___SUBSTATE_RIGHT], []) THEN
ASM_SIMP_TAC std_ss [] THEN
METIS_TAC[VAR_RES_STACK_IS_SUBSTATE_INTRO]);



val var_res_prop_implies_eq_def = Define `
   var_res_prop_implies_eq f (wpb,rpb) sfb sfb1 sfb1' =
   (var_res_prop f (wpb,rpb) (BAG_UNION sfb sfb1)=
    var_res_prop f (wpb,rpb) (BAG_UNION sfb sfb1'))`

val var_res_prop_implies_def = Define `
   var_res_prop_implies f (wpb,rpb) sfb sfb' =
   (var_res_prop_implies_eq f (wpb,rpb) sfb EMPTY_BAG sfb')`

val var_res_prop_implies_REWRITE = store_thm ("var_res_prop_implies_REWRITE",
``!f wpb rpb sfb sfb'.
   var_res_prop_implies f (wpb,rpb) sfb sfb' =
   (var_res_prop f (wpb,rpb) sfb =
    var_res_prop f (wpb,rpb) (BAG_UNION sfb sfb'))``,
SIMP_TAC std_ss [var_res_prop_implies_eq_def,
   var_res_prop_implies_def, BAG_UNION_EMPTY]);


(*
val var_res_prop_implies___VAR_RES_FRAME_SPLIT = store_thm ("var_res_prop_implies___VAR_RES_FRAME_SPLIT"
``!sr f wpb rpb sfb sfb'.
   var_res_prop_implies f (wpb,rpb) sfb sfb' =
   VAR_RES_FRAME_SPLIT f sr (wpb,rpb) EMPTY_BAG EMPTY_BAG sfb sfb' (K T)``,

SIMP_TAC std_ss [var_res_prop_implies_REWRITE,
   var_res_prop___EQ, VAR_RES_FRAME_SPLIT_def,
   BAG_UNION_EMPTY, BAG_DIFF_EMPTY] THEN
REPEAT STRIP_TAC THEN
Cases_on `var_res_prop___PROP___asl_false
   var_res_prop_implies_def, BAG_UNION_EMPTY]);
*)

val var_res_prop_implies_eq___SUB_BAG = store_thm (
"var_res_prop_implies_eq___SUB_BAG",
``!f wpb rpb sfb1 sfb2 sfb sfb'.
  (SUB_BAG sfb1 sfb2 /\
   var_res_prop_implies_eq f (wpb,rpb) sfb1 sfb sfb') ==>
   var_res_prop_implies_eq f (wpb,rpb) sfb2 sfb sfb'``,

SIMP_TAC std_ss [var_res_prop_implies_eq_def,
   SUB_BAG_EXISTS, GSYM LEFT_EXISTS_AND_THM,
   GSYM LEFT_FORALL_IMP_THM,
   var_res_prop___REWRITE,
   var_res_prop___COND_UNION] THEN
SIMP_TAC (std_ss++EQUIV_EXTRACT_ss) [] THEN
REPEAT STRIP_TAC THEN
Tactical.REVERSE (Cases_on `var_res_prop___COND f (wpb,rpb) sfb1`) THEN (
   FULL_SIMP_TAC std_ss []
) THEN
Tactical.REVERSE (Cases_on `var_res_prop___COND f (wpb,rpb) sfb`) THEN (
   FULL_SIMP_TAC std_ss []
) THEN
Q.PAT_ASSUM `var_res_prop___COND f X sfb'` ASSUME_TAC THEN
FULL_SIMP_TAC std_ss [COND_RAND, COND_RATOR] THEN
STRIP_TAC THEN
Q.ABBREV_TAC `sfb1a = sfb1 + sfb` THEN
Q.ABBREV_TAC `sfb1b = sfb1 + sfb'` THEN
`sfb1 + b + sfb = sfb1a + b` by
   PROVE_TAC[COMM_BAG_UNION, ASSOC_BAG_UNION] THEN
`sfb1 + b + sfb' = sfb1b + b` by
   PROVE_TAC[COMM_BAG_UNION, ASSOC_BAG_UNION] THEN
ASM_REWRITE_TAC[] THEN
`var_res_prop___COND f (wpb,rpb) sfb1a /\
 var_res_prop___COND f (wpb,rpb) sfb1b` by ALL_TAC THEN1 (
   Q.UNABBREV_TAC `sfb1a` THEN
   Q.UNABBREV_TAC `sfb1b` THEN
   ASM_SIMP_TAC std_ss [var_res_prop___COND_UNION]
) THEN
ASM_SIMP_TAC std_ss [var_res_prop___PROP_UNION,
   var_res_prop___COND_UNION]);


val var_res_prop_implies___SUB_BAG = store_thm (
"var_res_prop_implies___SUB_BAG",
``!f wpb rpb sfb1 sfb2 sfb'.
  (SUB_BAG sfb1 sfb2 /\
   var_res_prop_implies f (wpb,rpb) sfb1 sfb') ==>
   var_res_prop_implies f (wpb,rpb) sfb2 sfb'``,

SIMP_TAC std_ss [var_res_prop_implies_def] THEN
PROVE_TAC[var_res_prop_implies_eq___SUB_BAG])


val var_res_prop_implies___UNION = store_thm (
"var_res_prop_implies___UNION",
``!f wpb rpb sfb sfb' sfb''.
   var_res_prop_implies f (wpb,rpb) sfb sfb' /\
   var_res_prop_implies f (wpb,rpb) sfb sfb'' ==>
   var_res_prop_implies f (wpb,rpb) sfb (BAG_UNION sfb' sfb'')``,

   REPEAT STRIP_TAC THEN
   `var_res_prop_implies f (wpb, rpb) (BAG_UNION sfb sfb') sfb''` by ALL_TAC THEN1 (
       MATCH_MP_TAC var_res_prop_implies___SUB_BAG THEN
       Q.EXISTS_TAC `sfb` THEN
       ASM_SIMP_TAC std_ss [SUB_BAG_UNION_MONO]
   ) THEN
   FULL_SIMP_TAC std_ss [var_res_prop_implies_REWRITE,
    ASSOC_BAG_UNION]);




val var_res_implies_unequal___var_res_prop___PROP =
store_thm ("var_res_implies_unequal___var_res_prop___PROP",
``!f e1 e2 wpb rpb sfb s.
 (var_res_implies_unequal f sfb e1 e2 /\
 IS_SOME (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS e1) /\
 IS_SOME (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS e2) /\
 IS_SEPARATION_COMBINATOR f /\
 s IN var_res_prop___PROP f (wpb,rpb) sfb) ==>
 s IN var_res_prop_weak_unequal e1 e2``,

SIMP_TAC (std_ss++CONJ_ss) [var_res_implies_unequal_def,
   var_res_prop___PROP___REWRITE, IN_ABS]);




val var_res_implies_unequal___prop_implies =
store_thm ("var_res_implies_unequal___prop_implies",
``!f e1 e2 wpb rpb sfb.
 (var_res_implies_unequal f sfb e1 e2) ==>
 ((VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET
         (SET_OF_BAG (BAG_UNION wpb rpb)) e1) /\
  (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET
         (SET_OF_BAG (BAG_UNION wpb rpb)) e2)) ==>

  (var_res_prop_implies f (wpb,rpb) sfb {|var_res_prop_unequal f e1 e2|})``,


SIMP_TAC std_ss [var_res_prop___REWRITE,
   var_res_prop___COND_INSERT,
   VAR_RES_IS_STACK_IMPRECISE___USED_VARS___var_res_prop_unequal,
   COND_EQ_REWRITE, var_res_prop___PROP_INSERT,
   var_res_prop_implies_REWRITE, BAG_UNION_INSERT,
   BAG_UNION_EMPTY] THEN

SIMP_TAC std_ss [var_res_prop_equal_unequal_EXPAND,
   IN_ABS, asl_emp_def, GSYM RIGHT_EXISTS_AND_THM,
   GSYM LEFT_EXISTS_AND_THM,
   var_res_implies_unequal_def,
   var_res_prop___COND___EXPAND] THEN
REPEAT STRIP_TAC THEN
`?uf. IS_SEPARATION_COMBINATOR_NEUTRAL_ELEMENT_FUNCTION f uf` by
   PROVE_TAC[IS_SEPARATION_COMBINATOR_HALF_EXPAND_THM] THEN
POP_ASSUM (MP_TAC) THEN
FULL_SIMP_TAC std_ss [IS_SEPARATION_COMBINATOR_NEUTRAL_ELEMENT_FUNCTION_THM] THEN
ONCE_REWRITE_TAC[EXTENSION] THEN
QUANT_INSTANTIATE_TAC[] THEN
REPEAT STRIP_TAC THEN
SIMP_TAC (std_ss++EQUIV_EXTRACT_ss) [IN_ABS] THEN
FULL_SIMP_TAC std_ss [var_res_prop___PROP___REWRITE, IN_ABS,
   VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET_def]);



val VAR_RES_COND_INFERENCE___prop_implies =
store_thm ("VAR_RES_COND_INFERENCE___prop_implies",
``!f wpb rpb sfb sfb' prog post.
 (var_res_prop_implies f (wpb,rpb) sfb sfb') ==>

 (VAR_RES_COND_HOARE_TRIPLE f
   (var_res_prop f (wpb,rpb) sfb) prog post =
  VAR_RES_COND_HOARE_TRIPLE f
   (var_res_prop f (wpb,rpb) (BAG_UNION sfb sfb'))
        prog post)``,
PROVE_TAC[var_res_prop_implies_REWRITE]);



val VAR_RES_COND_INFERENCE___prop_implies_eq =
store_thm ("VAR_RES_COND_INFERENCE___prop_implies_eq",
``!f wpb rpb sfb sfb' prog post.
 (var_res_prop_implies_eq f (wpb,rpb) {||} sfb sfb') ==>

 (VAR_RES_COND_HOARE_TRIPLE f
   (var_res_prop f (wpb,rpb) sfb) prog post =
  VAR_RES_COND_HOARE_TRIPLE f
   (var_res_prop f (wpb,rpb) sfb')
        prog post)``,
SIMP_TAC std_ss [var_res_prop_implies_eq_def,
   BAG_UNION_EMPTY]);


val VAR_RES_FRAME_SPLIT___var_res_prop_implies_eq___split = store_thm (
  "VAR_RES_FRAME_SPLIT___var_res_prop_implies_eq___split",
``!f sr wpb wpb' rpb sfb_context sfb_split sfb_split' sfb_imp sfb_restP.
 (var_res_prop_implies_eq f (wpb,rpb) sfb_context sfb_split sfb_split') ==>

  (VAR_RES_FRAME_SPLIT f sr (wpb, rpb) wpb' sfb_context sfb_split sfb_imp sfb_restP =
  (VAR_RES_FRAME_SPLIT f sr (wpb, rpb) wpb' sfb_context
      sfb_split' sfb_imp sfb_restP))``,

REPEAT STRIP_TAC THEN
FULL_SIMP_TAC (std_ss++EQUIV_EXTRACT_ss) [VAR_RES_FRAME_SPLIT_EXPAND,
   var_res_prop___COND_INSERT,
   var_res_prop___COND_UNION,
   var_res_prop_implies_eq_def,
   var_res_prop___REWRITE] THEN
REPEAT STRIP_TAC THEN
CONSEQ_CONV_TAC (K EXISTS_EQ___CONSEQ_CONV) THEN
ASM_SIMP_TAC (std_ss++EQUIV_EXTRACT_ss) [] THEN
REPEAT STRIP_TAC THEN
CONSEQ_CONV_TAC (K FORALL_EQ___CONSEQ_CONV) THEN
ASM_SIMP_TAC (std_ss++EQUIV_EXTRACT_ss) [] THEN
GEN_TAC THEN
MATCH_MP_TAC (prove (``X ==> (Y ==> X)``, SIMP_TAC std_ss [])) THEN

FULL_SIMP_TAC std_ss [] THEN
Q.PAT_ASSUM `var_res_prop___COND f X sfb_split` ASSUME_TAC THEN
FULL_SIMP_TAC std_ss [] THEN
METIS_TAC [COMM_BAG_UNION, ASSOC_BAG_UNION]);


val VAR_RES_FRAME_SPLIT___var_res_prop_implies_eq___imp = store_thm (
  "VAR_RES_FRAME_SPLIT___var_res_prop_implies_eq___imp",
``!f sr wpb wpb' rpb sfb_context sfb_split sfb_imp sfb_imp' sfb_restP.
 (var_res_prop_implies_eq f (wpb,rpb) sfb_context sfb_imp sfb_imp') ==>

  (VAR_RES_FRAME_SPLIT f sr (wpb, rpb) wpb' sfb_context sfb_split sfb_imp sfb_restP =
  (VAR_RES_FRAME_SPLIT f sr (wpb, rpb) wpb' sfb_context
      sfb_split sfb_imp' sfb_restP))``,

REPEAT STRIP_TAC THEN
FULL_SIMP_TAC (std_ss++EQUIV_EXTRACT_ss) [VAR_RES_FRAME_SPLIT_EXPAND,
   var_res_prop___COND_INSERT,
   var_res_prop___COND_UNION,
   var_res_prop___REWRITE] THEN
REPEAT STRIP_TAC THEN
CONSEQ_CONV_TAC (K EXISTS_EQ___CONSEQ_CONV) THEN
ASM_SIMP_TAC (std_ss++EQUIV_EXTRACT_ss) [] THEN
REPEAT STRIP_TAC THEN
`var_res_prop_implies_eq f (wpb, rpb) (BAG_UNION sfb_context sfb_rest) sfb_imp sfb_imp'` by ALL_TAC THEN1 (
   MATCH_MP_TAC var_res_prop_implies_eq___SUB_BAG THEN
   Q.EXISTS_TAC `sfb_context` THEN
   ASM_SIMP_TAC std_ss [SUB_BAG_UNION_MONO]
) THEN
REPEAT (Q.PAT_ASSUM `var_res_prop_implies_eq f (wpb, rpb) X Y Z` MP_TAC) THEN
ASM_SIMP_TAC (std_ss++EQUIV_EXTRACT_ss) [var_res_prop_implies_eq_def,
   var_res_prop___REWRITE, var_res_prop___COND_UNION] THEN
Cases_on `var_res_prop___COND f (wpb, rpb) sfb_rest` THEN (
   ASM_SIMP_TAC std_ss []
) THEN
REPEAT STRIP_TAC THEN
FULL_SIMP_TAC std_ss [] THEN
METIS_TAC [COMM_BAG_UNION, ASSOC_BAG_UNION]);




val VAR_RES_FRAME_SPLIT___var_res_prop_implies___split = store_thm (
  "VAR_RES_FRAME_SPLIT___var_res_prop_implies___split",
``!sfb f sr wpb wpb' rpb sfb_context sfb_split sfb_imp sfb_restP.
 (var_res_prop_implies f (wpb,rpb) (BAG_UNION sfb_context sfb_split) sfb) ==>

  (VAR_RES_FRAME_SPLIT f sr (wpb, rpb) wpb' sfb_context sfb_split sfb_imp sfb_restP =
  (VAR_RES_FRAME_SPLIT f sr (wpb, rpb) wpb' sfb_context
      (BAG_UNION sfb sfb_split) sfb_imp sfb_restP))``,

REPEAT STRIP_TAC THEN
MATCH_MP_TAC VAR_RES_FRAME_SPLIT___var_res_prop_implies_eq___split THEN
FULL_SIMP_TAC std_ss [var_res_prop_implies_eq_def,
   var_res_prop_implies_def, BAG_UNION_EMPTY] THEN
METIS_TAC[COMM_BAG_UNION, ASSOC_BAG_UNION]);



val VAR_RES_FRAME_SPLIT___var_res_prop_implies___imp = store_thm (
  "VAR_RES_FRAME_SPLIT___var_res_prop_implies___imp",
``!f sr wpb wpb' rpb sfb_context sfb_split sfb sfb_imp sfb_restP.
 ((var_res_prop_implies f (wpb,rpb) (BAG_UNION sfb_context sfb_imp) sfb) ==>

  (VAR_RES_FRAME_SPLIT f sr (wpb, rpb) wpb' sfb_context sfb_split sfb_imp sfb_restP =
  (VAR_RES_FRAME_SPLIT f sr (wpb, rpb) wpb' sfb_context
      sfb_split (BAG_UNION sfb sfb_imp) sfb_restP)))``,

REPEAT STRIP_TAC THEN
MATCH_MP_TAC VAR_RES_FRAME_SPLIT___var_res_prop_implies_eq___imp THEN
FULL_SIMP_TAC std_ss [var_res_prop_implies_eq_def,
   var_res_prop_implies_def, BAG_UNION_EMPTY] THEN
METIS_TAC[COMM_BAG_UNION, ASSOC_BAG_UNION]);



(*******************************************************
 * Local Variables
 ******************************************************)

val var_res_new_var_init_action_def = Define `
   var_res_new_var_init_action v e s =
      let e_opt = e (FST s) in
      if (IS_NONE e_opt) then NONE else
      (if (v IN FDOM (FST s)) then SOME {} else
       (SOME {var_res_ext_state_var_update (v, (THE e_opt)) s}))`;



val var_res_new_var_init_action___best_local_action_THM = store_thm (
"var_res_new_var_init_action___best_local_action_THM",
``!f v e vs.
   IS_SEPARATION_COMBINATOR f /\
   (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS e = SOME vs) ==>

   (fasl_action_order (var_res_new_var_init_action v e)
    (var_res_cond_best_local_action (VAR_RES_COMBINATOR f)
      (var_res_prop f (EMPTY_BAG, BAG_OF_SET vs) EMPTY_BAG)
      (var_res_prop f ({|v|}, BAG_OF_SET (vs DELETE v))
        {|var_res_prop_equal f (var_res_exp_var v) e|})))``,


SIMP_TAC std_ss [fasl_action_order_POINTWISE_DEF] THEN
REPEAT STRIP_TAC THEN
`VAR_RES_IS_STACK_IMPRECISE___USED_VARS (v INSERT vs)
      (var_res_prop_equal f (var_res_exp_var v) e)` by ALL_TAC THEN1 (
   MATCH_MP_TAC VAR_RES_IS_STACK_IMPRECISE___USED_VARS___var_res_prop_equal THEN
   SIMP_TAC std_ss [VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET___VAR_CONST_EVAL] THEN
   ASM_SIMP_TAC std_ss [VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET_def,
                        SUBSET_DEF, IN_INSERT]
) THEN
`VAR_RES_IS_STACK_IMPRECISE
      (var_res_prop_equal f (var_res_exp_var v) e)` by
   METIS_TAC[VAR_RES_IS_STACK_IMPRECISE___USED_VARS_def] THEN
FULL_SIMP_TAC std_ss [
   var_res_new_var_init_action_def,
   VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_THM,
   VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_REL___EXPAND,
   LET_THM,
   var_res_best_local_action_def,
   quant_best_local_action_def,
   var_res_cond_best_local_action_def,
   var_res_prop___REWRITE,
   var_res_prop___COND___REWRITE,
   FINITE_BAG_THM, NOT_IN_EMPTY_BAG, BAG_ALL_DISTINCT_BAG_UNION,
   BAG_ALL_DISTINCT_THM, BAG_DISJOINT_BAG_INSERT,
   BAG_DISJOINT_EMPTY, BAG_IN_BAG_INSERT,
   SET_BAG_I, BAG_IN_BAG_OF_SET,
   BAG_ALL_DISTINCT_BAG_OF_SET, SET_OF_BAG_INSERT,
   BAG_UNION_INSERT, BAG_UNION_EMPTY, IN_DELETE, INSERT_DELETE_2] THEN
ASM_SIMP_TAC (std_ss++CONJ_ss) [
   var_res_prop___PROP___REWRITE, IN_ABS,
   var_res_bigstar_REWRITE_EXT,
   asl_star___var_res_prop_stack_true___STACK_IMPRECISE___COMM] THEN
ASM_SIMP_TAC (std_ss++CONJ_ss) [
   NOT_IN_EMPTY_BAG, BAG_IN_BAG_INSERT, BAG_IN_BAG_OF_SET,
   var_res_sl___has_read_permission_def, var_res_sl___has_write_permission_def,
   IN_DELETE, GSYM SUBSET_DEF, LET_THM,
   var_res_prop_equal_def, var_res_prop_binexpression_def,
   var_res_stack_proposition_def, IN_ABS, var_res_exp_var_def] THEN
Tactical.REVERSE (Cases_on `vs SUBSET FDOM (FST s)`) THEN1 (
   FULL_SIMP_TAC std_ss [
      fasl_order_THM, NONE___INF_fasl_action_order, IN_ABS,
      GSYM LEFT_FORALL_IMP_THM,
      NONE___best_local_action, bagTheory.NOT_IN_EMPTY_BAG,
      BAG_IN_BAG_OF_SET, var_res_prop_stack_true_def,
      var_res_bool_proposition_REWRITE, asl_emp_def,
      IS_SEPARATION_COMBINATOR_EXPAND_THM,
      GSYM LEFT_EXISTS_AND_THM, GSYM RIGHT_EXISTS_AND_THM,
      VAR_RES_COMBINATOR_REWRITE,
      var_res_sl___has_read_permission_def,
      SOME___VAR_RES_STACK_COMBINE] THEN
   CCONTR_TAC THEN
   FULL_SIMP_TAC std_ss [] THEN
   FULL_SIMP_TAC std_ss [FMERGE_DEF, SUBSET_DEF, IN_UNION]
) THEN
ASM_SIMP_TAC std_ss [COND_NONE_SOME_REWRITES, fasl_order_THM2] THEN
Cases_on `v IN FDOM (FST s)` THEN ASM_REWRITE_TAC[EMPTY_SUBSET] THEN
SIMP_TAC std_ss [SOME___INF_fasl_action_order, IN_ABS, GSYM RIGHT_EXISTS_AND_THM,
   GSYM LEFT_EXISTS_AND_THM, SUBSET_DEF, IN_BIGINTER, IN_SING, IN_IMAGE, IN_INTER,
   IS_SOME_EXISTS, GSYM LEFT_FORALL_IMP_THM] THEN
REPEAT GEN_TAC THEN DISCH_TAC THEN POP_ASSUM (K ALL_TAC) THEN
FULL_SIMP_TAC (std_ss++CONJ_ss) [
   IS_SEPARATION_COMBINATOR_EXPAND_THM,
   GSYM LEFT_EXISTS_AND_THM, GSYM RIGHT_EXISTS_AND_THM,
   SOME___best_local_action, IN_ABS,
   var_res_prop_stack_true_def, var_res_bool_proposition_REWRITE,
   asl_emp_def, IN_BIGINTER, VAR_RES_COMBINATOR_REWRITE,
   GSYM SUBSET_DEF, PAIR_EXISTS_THM, IN_IMAGE,
   GSYM LEFT_FORALL_IMP_THM, PAIR_FORALL_THM] THEN
QUANT_INSTANTIATE_TAC [] THEN
REPEAT GEN_TAC THEN STRIP_TAC THEN Q.PAT_ASSUM `X = SOME (FST s)` (K ALL_TAC) THEN
ASM_SIMP_TAC std_ss [asl_star_def, IN_ABS, IN_SING,
   VAR_RES_COMBINATOR_REWRITE, var_res_ext_state_var_update_def,
   PAIR_EXISTS_THM, GSYM RIGHT_EXISTS_IMP_THM] THEN
QUANT_INSTANTIATE_TAC [] THEN
SIMP_TAC std_ss [VAR_RES_STACK_COMBINE___COMM] THEN
GEN_TAC THEN
Q.EXISTS_TAC `var_res_state_var_update v (THE (e (FST s))) x1` THEN
ASM_SIMP_TAC std_ss [SOME___VAR_RES_STACK_COMBINE,
   var_res_state_var_update_def, FAPPLY_FUPDATE_THM,
   FDOM_FUPDATE, IN_INSERT, VAR_RES_STACK_IS_SEPARATE_def] THEN
STRIP_TAC THEN
FULL_SIMP_TAC std_ss [FMERGE_DEF, IN_UNION] THEN
REPEAT STRIP_TAC THENL [
   METIS_TAC[],
   METIS_TAC[],
   `~(x = v)` by METIS_TAC[] THEN ASM_SIMP_TAC std_ss [],
   `~(x = v)` by METIS_TAC[] THEN ASM_SIMP_TAC std_ss [],

   SIMP_TAC (std_ss++EQUIV_EXTRACT_ss) [
      GSYM fmap_EQ_THM, EXTENSION, FMERGE_DEF,
      FDOM_FUPDATE, IN_UNION, IN_INSERT] THEN
   GEN_TAC THEN Cases_on `x = v` THEN (
      ASM_SIMP_TAC std_ss [FAPPLY_FUPDATE_THM, FMERGE_DEF]
   ),


   FULL_SIMP_TAC std_ss [SUBSET_DEF, IN_INSERT],

   AP_TERM_TAC THEN
   Q.PAT_ASSUM `!st1 st2. X st1 st2` MATCH_MP_TAC THEN
   FULL_SIMP_TAC std_ss [FMERGE_DEF, FDOM_FUPDATE, SUBSET_DEF, IN_INSERT,
      FAPPLY_FUPDATE_THM, VAR_RES_STACK_COMBINE___MERGE_FUNC_def] THEN
   REPEAT STRIP_TAC THEN
   `~(v' = v)` by METIS_TAC[] THEN
   ASM_SIMP_TAC std_ss [COND_RAND, COND_RATOR],


   ASM_SIMP_TAC (std_ss++CONJ_ss) [VAR_RES_STACK___IS_EQUAL_UPTO_VALUES_def,
      FDOM_FUPDATE, FAPPLY_FUPDATE_THM, IN_INSERT] THEN
   METIS_TAC[]
]);




val ASL_IS_LOCAL_ACTION___var_res_new_var_init_action = store_thm (
"ASL_IS_LOCAL_ACTION___var_res_new_var_init_action",
``!f e v.
IS_SOME (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS e) ==>
ASL_IS_LOCAL_ACTION (VAR_RES_COMBINATOR f) (var_res_new_var_init_action v e)``,

SIMP_TAC std_ss [ASL_IS_LOCAL_ACTION___ALTERNATIVE_EXT_DEF,
   var_res_new_var_init_action_def, LET_THM, COND_NONE_SOME_REWRITES,
   VAR_RES_COMBINATOR_REWRITE, SOME___VAR_RES_STACK_COMBINE,
   IS_SOME___VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS___REWRITE,
   VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_REL___EXPAND,
   GSYM LEFT_FORALL_IMP_THM, FMERGE_DEF] THEN
SIMP_TAC std_ss [COND_RAND, COND_RATOR, NOT_IN_EMPTY, IN_SING,
                 var_res_ext_state_var_update_def, SUBSET_DEF, IN_UNION] THEN
REPEAT STRIP_TAC THENL [
   FULL_SIMP_TAC std_ss [var_res_state_var_update_def,
      VAR_RES_STACK_IS_SEPARATE_def, FDOM_FUPDATE, IN_INSERT,
      FAPPLY_FUPDATE_THM] THEN
   GEN_TAC THEN
   Cases_on `x IN FDOM (FST s2)` THEN ASM_REWRITE_TAC[] THEN
   `~(x = v)` by METIS_TAC[] THEN
   ASM_SIMP_TAC std_ss [],


   SIMP_TAC (std_ss++EQUIV_EXTRACT_ss) [
      GSYM fmap_EQ_THM, var_res_state_var_update_def, FAPPLY_FUPDATE_THM,
      FMERGE_DEF, FDOM_FUPDATE, IN_INSERT, IN_UNION, EXTENSION] THEN
   GEN_TAC THEN Cases_on `x = v` THEN1 (
      ASM_SIMP_TAC std_ss [] THEN
      AP_TERM_TAC THEN
      Q.PAT_ASSUM `!st1 st2. X st1 st2` MATCH_MP_TAC THEN
      ASM_SIMP_TAC std_ss [FMERGE_DEF, IN_UNION,
         VAR_RES_STACK_COMBINE___MERGE_FUNC_def, COND_REWRITES]
   ) THEN
   FULL_SIMP_TAC std_ss [VAR_RES_STACK_IS_SEPARATE_def]
]);



val var_res_prog_new_var_init_def = Define `
var_res_prog_new_var_init v e =
asl_prog_prim_command (asl_pc_shallow_command (K (var_res_new_var_init_action v e)))`;

val var_res_prog_new_var_def = Define `
var_res_prog_new_var v = asl_prog_ndet (\p. ?c. p = var_res_prog_new_var_init v (var_res_exp_const c))`;


val var_res_dispose_var_action_def = Define `
   var_res_dispose_var_action v s =
      if ~(var_res_sl___has_write_permission v (FST s)) then NONE else
      (SOME {(FST s \\ v, SND s)})`


val var_res_dispose_var_action___best_local_action_THM = store_thm (
"var_res_dispose_var_action___best_local_action_THM",
``!f v.
   IS_SEPARATION_COMBINATOR f ==>
   (fasl_action_order (var_res_dispose_var_action v)
    (var_res_cond_best_local_action (VAR_RES_COMBINATOR f)
      (var_res_prop f ({|v|}, EMPTY_BAG) EMPTY_BAG)
      (var_res_prop f (EMPTY_BAG, EMPTY_BAG) EMPTY_BAG)))``,

SIMP_TAC std_ss [fasl_action_order_POINTWISE_DEF,
   var_res_dispose_var_action_def, var_res_cond_best_local_action_def,
   var_res_prop___REWRITE, var_res_prop___COND___REWRITE,
   FINITE_BAG_THM, BAG_UNION_EMPTY, BAG_ALL_DISTINCT_THM,
   NOT_IN_EMPTY_BAG, var_res_prop___PROP___REWRITE,
   var_res_bigstar_REWRITE_EXT,
   var_res_best_local_action_def, IN_ABS] THEN
SIMP_TAC std_ss [COND_RAND, COND_RATOR,
   fasl_order_THM2, NONE___quant_best_local_action,
   SOME___quant_best_local_action, IN_ABS, COND_EXPAND_IMP] THEN
SIMP_TAC std_ss [BAG_IN_BAG_INSERT, NOT_IN_EMPTY_BAG] THEN
REPEAT GEN_TAC THEN STRIP_TAC THEN GEN_TAC THEN CONJ_TAC THENL [
   REPEAT STRIP_TAC THEN CCONTR_TAC THEN
   Q.PAT_ASSUM `~(var_res_sl___has_write_permission v (FST s))` MP_TAC THEN
   FULL_SIMP_TAC std_ss [SOME___VAR_RES_STACK_COMBINE,
      VAR_RES_COMBINATOR_REWRITE,
      var_res_sl___has_write_permission_def, FMERGE_DEF,
      IN_UNION, VAR_RES_STACK_IS_SEPARATE_def] THEN
   Q.PAT_ASSUM `!x'. X x'` (MP_TAC o Q.SPEC `v`) THEN
   ASM_SIMP_TAC std_ss [var_res_permission_THM2],


   DISCH_TAC THEN DISCH_TAC THEN (POP_ASSUM (K ALL_TAC)) THEN
   ASM_SIMP_TAC std_ss [SUBSET_DEF, IN_SING, IN_ABS, asl_star_def] THEN
   REPEAT STRIP_TAC THEN
   `!p. VAR_RES_COMBINATOR f (SOME p) (SOME s0) =
        VAR_RES_COMBINATOR f (SOME s0) (SOME p)` by
      METIS_TAC[IS_SEPARATION_COMBINATOR___VAR_RES_COMBINATOR,
                IS_SEPARATION_COMBINATOR_def, COMM_DEF] THEN
   ASM_REWRITE_TAC[] THEN POP_ASSUM (K ALL_TAC) THEN
   FULL_SIMP_TAC std_ss [SOME___VAR_RES_STACK_COMBINE,
      VAR_RES_COMBINATOR_REWRITE, var_res_sl___has_write_permission_def,
      FMERGE_DEF, IN_UNION] THEN
   Q.EXISTS_TAC `(FST x' \\ v, SND x')` THEN
   FULL_SIMP_TAC std_ss [var_res_prop_stack_true_def,
      var_res_bool_proposition_REWRITE, IN_ABS,
      VAR_RES_STACK_IS_SEPARATE_def, FDOM_DOMSUB,
      IN_DELETE, DOMSUB_FAPPLY_NEQ, VAR_RES_STACK___IS_EQUAL_UPTO_VALUES_def] THEN
   ASM_SIMP_TAC (std_ss++CONJ_ss) [] THEN
   `~(v IN FDOM (FST s0))` by ALL_TAC THEN1 (
      Q.PAT_ASSUM `!x. X x` (MP_TAC o Q.SPEC `v`) THEN
      ASM_SIMP_TAC std_ss [var_res_permission_THM2]
   ) THEN
   ASM_SIMP_TAC std_ss [
     GSYM fmap_EQ_THM, FMERGE_DEF,
     FDOM_DOMSUB, EXTENSION, IN_UNION, IN_DELETE,
     DOMSUB_FAPPLY_NEQ] THEN
   METIS_TAC[]
]);



val ASL_IS_LOCAL_ACTION___var_res_dispose_var_action = store_thm (
"ASL_IS_LOCAL_ACTION___var_res_dispose_var_action",
``!f v. ASL_IS_LOCAL_ACTION (VAR_RES_COMBINATOR f) (var_res_dispose_var_action v)``,

SIMP_TAC std_ss [ASL_IS_LOCAL_ACTION___ALTERNATIVE_EXT_DEF,
   var_res_dispose_var_action_def, COND_NONE_SOME_REWRITES,
   IN_SING] THEN
SIMP_TAC std_ss [VAR_RES_COMBINATOR_REWRITE,
   var_res_sl___has_write_permission_def,
   SOME___VAR_RES_STACK_COMBINE, FMERGE_DEF, IN_UNION,
   VAR_RES_STACK_IS_SEPARATE_def, FDOM_DOMSUB,
   DOMSUB_FAPPLY_NEQ, IN_DELETE] THEN
REPEAT GEN_TAC THEN STRIP_TAC THEN
`~(v IN FDOM (FST s2))` by ALL_TAC THEN1 (
   Q.PAT_ASSUM `!x. X x` (MP_TAC o Q.SPEC `v`) THEN
   ASM_SIMP_TAC std_ss [var_res_permission_THM2]
) THEN
ASM_SIMP_TAC std_ss [GSYM fmap_EQ_THM,
   FMERGE_DEF, FDOM_DOMSUB, EXTENSION, IN_DELETE,
   IN_UNION, IN_DELETE, DOMSUB_FAPPLY_NEQ] THEN
METIS_TAC[]);





val var_res_prog_dispose_var_def = Define `
var_res_prog_dispose_var v = asl_prog_prim_command (asl_pc_shallow_command
   (K (var_res_dispose_var_action v)))`



val var_res_prog_call_by_value_arg_def = Define `var_res_prog_call_by_value_arg prog_body c =
   (asl_prog_forall (\x. asl_prog_seq
       (var_res_prog_new_var_init x (var_res_exp_const c))
       (asl_prog_seq (prog_body x) (var_res_prog_dispose_var x))))`;


val var_res_prog_local_var_def = Define `var_res_prog_local_var prog_body =
   asl_prog_ndet (\p. ?c. p = $var_res_prog_call_by_value_arg prog_body c)`



val VAR_RES_PROGRAM_IS_ABSTRACTION___var_res_prog_call_by_value_arg = store_thm (
"VAR_RES_PROGRAM_IS_ABSTRACTION___var_res_prog_call_by_value_arg",
``!f c body.
IS_SEPARATION_COMBINATOR f ==>
(VAR_RES_PROGRAM_IS_ABSTRACTION f
       (var_res_prog_call_by_value_arg body c)
       (asl_prog_forall (\v.
       (asl_prog_block [
          (var_res_prog_cond_best_local_action
             ((var_res_prop f (EMPTY_BAG,EMPTY_BAG) EMPTY_BAG):(bool # ('c,'b,'a) var_res_proposition))
             (var_res_prop f ({|v|},EMPTY_BAG)
                 {|var_res_prop_equal f (var_res_exp_var v) (var_res_exp_const c)|}));
          (body v);
          (var_res_prog_cond_best_local_action
             (var_res_prop f ({|v|},EMPTY_BAG) EMPTY_BAG)
             (var_res_prop f (EMPTY_BAG,EMPTY_BAG) EMPTY_BAG))]))))``,

SIMP_TAC std_ss [var_res_prog_call_by_value_arg_def,
   VAR_RES_PROGRAM_IS_ABSTRACTION_def, asl_prog_block_def] THEN
REPEAT STRIP_TAC THEN
MATCH_MP_TAC ASL_PROGRAM_IS_ABSTRACTION___forall THEN
GEN_TAC THEN SIMP_TAC std_ss [] THEN
CONSEQ_REWRITE_TAC ([ASL_PROGRAM_IS_ABSTRACTION___seq], [], []) THEN
REWRITE_TAC [ASL_PROGRAM_IS_ABSTRACTION___REFL] THEN
ASM_SIMP_TAC std_ss [ASL_PROGRAM_IS_ABSTRACTION_def,
   var_res_prog_cond_best_local_action_REWRITE,
   var_res_prog_dispose_var_def, var_res_prog_new_var_init_def,
   ASL_PROGRAM_SEM___prim_command,
   IS_SEPARATION_COMBINATOR___VAR_RES_COMBINATOR,
   ASL_ATOMIC_ACTION_SEM_def, EVAL_asl_prim_command_THM,
   ASL_IS_LOCAL_ACTION___var_res_cond_best_local_action,
   ASL_IS_LOCAL_ACTION___var_res_dispose_var_action,
   ASL_IS_LOCAL_ACTION___var_res_new_var_init_action,
   IS_SOME___VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS___VAR_CONST_EVAL] THEN
ASM_SIMP_TAC std_ss [var_res_dispose_var_action___best_local_action_THM] THEN
MP_TAC (Q.SPECL [`f`, `arg`, `var_res_exp_const c`]
        var_res_new_var_init_action___best_local_action_THM) THEN
ASM_SIMP_TAC std_ss [VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS___var_res_exp_const,
   EMPTY_DELETE, SET_OF_EMPTY]);




val ASL_PROGRAM_IS_ABSTRACTION___var_res_prog_call_by_value_arg___CONG = store_thm (
"ASL_PROGRAM_IS_ABSTRACTION___var_res_prog_call_by_value_arg___CONG",
``!xenv penv c body body'.
(!v. ASL_PROGRAM_IS_ABSTRACTION xenv penv (body v) (body' v)) ==>
ASL_PROGRAM_IS_ABSTRACTION xenv penv
       (var_res_prog_call_by_value_arg body c)
       (var_res_prog_call_by_value_arg body' c)``,

REPEAT STRIP_TAC THEN
SIMP_TAC std_ss [var_res_prog_call_by_value_arg_def] THEN
MATCH_MP_TAC ASL_PROGRAM_IS_ABSTRACTION___forall THEN
SIMP_TAC std_ss [] THEN
CONSEQ_REWRITE_TAC ([ASL_PROGRAM_IS_ABSTRACTION___seq], [], []) THEN
ASM_SIMP_TAC std_ss [ASL_PROGRAM_IS_ABSTRACTION___REFL]);





val VAR_RES_PROGRAM_IS_ABSTRACTION___var_res_prog_local_var = store_thm (
"VAR_RES_PROGRAM_IS_ABSTRACTION___var_res_prog_local_var",
``!f body.
IS_SEPARATION_COMBINATOR f ==>
(VAR_RES_PROGRAM_IS_ABSTRACTION f
       (var_res_prog_local_var body)
       (asl_prog_forall (\v.
       (asl_prog_block [
          (var_res_prog_cond_best_local_action
             ((var_res_prop f (EMPTY_BAG,EMPTY_BAG) EMPTY_BAG):(bool # ('c,'b,'a) var_res_proposition))
             (var_res_prop f ({|v|},EMPTY_BAG) EMPTY_BAG));
          (body v);
          (var_res_prog_cond_best_local_action
             (var_res_prop f ({|v|},EMPTY_BAG) EMPTY_BAG)
             (var_res_prop f (EMPTY_BAG,EMPTY_BAG) EMPTY_BAG))]))))``,

SIMP_TAC std_ss [var_res_prog_local_var_def, VAR_RES_PROGRAM_IS_ABSTRACTION_def] THEN
REPEAT STRIP_TAC THEN
MATCH_MP_TAC ASL_PROGRAM_IS_ABSTRACTION___ndet_1 THEN
SIMP_TAC std_ss [IN_ABS, GSYM LEFT_FORALL_IMP_THM] THEN
GEN_TAC THEN
MATCH_MP_TAC (SIMP_RULE std_ss [AND_IMP_INTRO] ASL_PROGRAM_IS_ABSTRACTION___TRANSITIVE) THEN
MP_TAC (Q.SPECL [`f`, `c`, `body`]
   VAR_RES_PROGRAM_IS_ABSTRACTION___var_res_prog_call_by_value_arg) THEN
ASM_REWRITE_TAC[VAR_RES_PROGRAM_IS_ABSTRACTION_def] THEN
Q.MATCH_ABBREV_TAC `
   ASL_PROGRAM_IS_ABSTRACTION xenv penv prog1 prog2 ==>
   ?p2. ASL_PROGRAM_IS_ABSTRACTION xenv penv prog1 p2 /\
        ASL_PROGRAM_IS_ABSTRACTION xenv penv p2 prog3` THEN
REPEAT STRIP_TAC THEN
Q.EXISTS_TAC `prog2` THEN
ASM_REWRITE_TAC[] THEN
Q.UNABBREV_TAC `prog2` THEN
Q.UNABBREV_TAC `prog3` THEN
MATCH_MP_TAC ASL_PROGRAM_IS_ABSTRACTION___forall THEN
GEN_TAC THEN SIMP_TAC std_ss [asl_prog_block_def] THEN
CONSEQ_REWRITE_TAC ([ASL_PROGRAM_IS_ABSTRACTION___seq], [], []) THEN
REWRITE_TAC [ASL_PROGRAM_IS_ABSTRACTION___REFL] THEN
ASM_SIMP_TAC std_ss [var_res_prog_cond_best_local_action_def,
   var_res_prop___REWRITE, var_res_prop___COND___REWRITE,
   NOT_IN_EMPTY_BAG, FINITE_BAG_THM, BAG_UNION_EMPTY,
   BAG_ALL_DISTINCT_THM, SET_OF_BAG_INSERT,
   BAG_OF_EMPTY, BAG_IN_BAG_INSERT,
   VAR_RES_IS_STACK_IMPRECISE___USED_VARS___var_res_prop_equal,
   VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET___VAR_CONST_EVAL,
   IN_SING] THEN
SIMP_TAC std_ss [var_res_prog_best_local_action_def] THEN
`IS_SEPARATION_COMBINATOR (FST xenv)` by ALL_TAC THEN1 (
   Q.UNABBREV_TAC `xenv` THEN
   ASM_SIMP_TAC std_ss [IS_SEPARATION_COMBINATOR___VAR_RES_COMBINATOR]
) THEN
ASM_SIMP_TAC std_ss [ASL_PROGRAM_IS_ABSTRACTION___quant_best_local_action] THEN
GEN_TAC THEN
Q.HO_MATCH_ABBREV_TAC `ASL_PROGRAM_HOARE_TRIPLE xenv penv (P x)
   (asl_prog_quant_best_local_action (\x. P x) (\x. Q' x)) (Q x)` THEN
MATCH_MP_TAC ASL_INFERENCE_STRENGTHEN THEN
Q.EXISTS_TAC `P x` THEN
Q.EXISTS_TAC `Q' x` THEN
ASM_SIMP_TAC std_ss [ASL_INFERENCE_prog_quant_best_local_action, SUBSET_REFL] THEN
Q.UNABBREV_TAC `Q'` THEN
Q.UNABBREV_TAC `Q` THEN
ASM_SIMP_TAC std_ss [SUBSET_DEF, IN_ABS,
   var_res_prop___PROP___REWRITE, NOT_IN_EMPTY_BAG,
   BAG_IN_BAG_INSERT,
   var_res_bigstar_REWRITE_EXT,
   asl_star___var_res_prop_stack_true___STACK_IMPRECISE___COMM,
   VAR_RES_IS_STACK_IMPRECISE___var_res_prop_equal,
   IS_SOME___VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS___VAR_CONST_EVAL] THEN
SIMP_TAC std_ss [var_res_prop_stack_true_REWRITE,
   IN_ABS, var_res_prop_equal_unequal_EXPAND]);






val ASL_PROGRAM_IS_ABSTRACTION___var_res_prog_local_var___CONG = store_thm (
"ASL_PROGRAM_IS_ABSTRACTION___var_res_prog_local_var___CONG",
``!xenv penv body body'.
(!v. ASL_PROGRAM_IS_ABSTRACTION xenv penv (body v) (body' v)) ==>
ASL_PROGRAM_IS_ABSTRACTION xenv penv
       (var_res_prog_local_var body)
       (var_res_prog_local_var body')``,

REPEAT STRIP_TAC THEN
SIMP_TAC std_ss [var_res_prog_local_var_def] THEN
MATCH_MP_TAC ASL_PROGRAM_IS_ABSTRACTION___ndet THEN
SIMP_TAC std_ss [IN_ABS, GSYM LEFT_EXISTS_AND_THM,
   GSYM LEFT_FORALL_IMP_THM] THEN
REPEAT STRIP_TAC THEN
Q.EXISTS_TAC `c` THEN
ASM_SIMP_TAC std_ss [ASL_PROGRAM_IS_ABSTRACTION___var_res_prog_call_by_value_arg___CONG]);





val VAR_RES_COND_INFERENCE___prog_seq_skip_INTRO = store_thm (
"VAR_RES_COND_INFERENCE___prog_seq_skip_INTRO",
``!f P prog Q.
  VAR_RES_COND_HOARE_TRIPLE f P prog Q =
  VAR_RES_COND_HOARE_TRIPLE f P (asl_prog_seq prog asl_prog_skip) Q``,

SIMP_TAC std_ss [VAR_RES_COND_HOARE_TRIPLE_def,
   VAR_RES_HOARE_TRIPLE_def, ASL_PROGRAM_HOARE_TRIPLE_def,
   HOARE_TRIPLE_def, ASL_PROGRAM_SEM___prog_seq,
   ASL_PROGRAM_SEM___skip, asla_seq_skip]);


val VAR_RES_COND_INFERENCE___prog_block_INTRO = store_thm (
"VAR_RES_COND_INFERENCE___prog_block_INTRO",
``!f P prog Q.
  VAR_RES_COND_HOARE_TRIPLE f P prog Q =
  VAR_RES_COND_HOARE_TRIPLE f P (asl_prog_block [prog]) Q``,
SIMP_TAC std_ss [asl_prog_block_def]);



val VAR_RES_COND_INFERENCE___prog_seq_skip_ELIM = store_thm (
"VAR_RES_COND_INFERENCE___prog_seq_skip_ELIM",
``!f P prog Q.
  VAR_RES_COND_HOARE_TRIPLE f P (asl_prog_seq asl_prog_skip prog) Q =
  VAR_RES_COND_HOARE_TRIPLE f P prog Q``,


SIMP_TAC std_ss [VAR_RES_COND_HOARE_TRIPLE_def,
   VAR_RES_HOARE_TRIPLE_def, ASL_PROGRAM_HOARE_TRIPLE_def,
   HOARE_TRIPLE_def, ASL_PROGRAM_SEM___prog_seq,
   ASL_PROGRAM_SEM___skip, asla_seq_skip]);


val VAR_RES_COND_INFERENCE___prog_block_skip_ELIM = store_thm (
"VAR_RES_COND_INFERENCE___prog_block_skip_ELIM",
``!f P progL Q.
  VAR_RES_COND_HOARE_TRIPLE f P (asl_prog_block (asl_prog_skip::progL)) Q =
  VAR_RES_COND_HOARE_TRIPLE f P (asl_prog_block progL) Q``,
SIMP_TAC std_ss [VAR_RES_COND_INFERENCE___prog_block,
   VAR_RES_COND_INFERENCE___prog_seq_skip_ELIM]);



val VAR_RES_COND_INFERENCE___prog_seq_diverge = store_thm (
"VAR_RES_COND_INFERENCE___prog_seq_diverge",
``!f P prog Q.
  VAR_RES_COND_HOARE_TRIPLE f P (asl_prog_seq asl_prog_diverge prog) Q``,

SIMP_TAC std_ss [VAR_RES_COND_HOARE_TRIPLE_def,
   VAR_RES_HOARE_TRIPLE_def, ASL_PROGRAM_HOARE_TRIPLE_def,
   HOARE_TRIPLE_def, ASL_PROGRAM_SEM___prog_seq,
   asla_seq_diverge, ASL_PROGRAM_SEM___diverge] THEN
SIMP_TAC std_ss [asla_diverge_def, fasl_order_THM2, EMPTY_SUBSET]);


val VAR_RES_COND_INFERENCE___prog_block_diverge = store_thm (
"VAR_RES_COND_INFERENCE___prog_block_diverge",
``!f P progL Q.
  VAR_RES_COND_HOARE_TRIPLE f P (asl_prog_block (asl_prog_diverge::progL)) Q``,
SIMP_TAC std_ss [VAR_RES_COND_INFERENCE___prog_block,
   VAR_RES_COND_INFERENCE___prog_seq_diverge]);


val VAR_RES_COND_INFERENCE___prog_local_var = store_thm (
   "VAR_RES_COND_INFERENCE___prog_local_var",
``!f wpb rpb sfb sfb' body.

(!v. VAR_RES_COND_HOARE_TRIPLE f (var_res_prop f (BAG_INSERT v wpb,rpb) sfb)
         (body v) (COND_PROP___STRONG_EXISTS (\x'. var_res_prop f (BAG_INSERT v wpb,rpb)
         (sfb' x')))) ==>

(VAR_RES_COND_HOARE_TRIPLE f (var_res_prop f (wpb,rpb) sfb)
   (var_res_prog_local_var body)
   (COND_PROP___STRONG_EXISTS (\x'. var_res_prop f (wpb,rpb) (sfb' x'))))``,

REPEAT STRIP_TAC THEN
MATCH_MP_TAC VAR_RES_COND_HOARE_TRIPLE___PROGRAM_ABSTRACTION THEN
Tactical.REVERSE (Cases_on `
   (var_res_prop___COND f (wpb,rpb) sfb) /\
   (!x'. var_res_prop___COND f (wpb,rpb) (sfb' x'))`) THEN1 (
   ASM_SIMP_TAC std_ss [VAR_RES_COND_HOARE_TRIPLE_def, var_res_prop___REWRITE,
      VAR_RES_PROGRAM_IS_ABSTRACTION_def, COND_PROP___STRONG_EXISTS_def] THEN
   PROVE_TAC[ASL_PROGRAM_IS_ABSTRACTION___REFL]
) THEN
Cases_on `IS_SEPARATION_COMBINATOR f` THEN ASM_SIMP_TAC std_ss [] THEN
Q.EXISTS_TAC `(asl_prog_forall (\v.
             asl_prog_block
               [var_res_prog_cond_best_local_action
                  (var_res_prop f ({||},{||}) {||})
                  (var_res_prop f ({|v|},{||}) {||}); body v;
                var_res_prog_cond_best_local_action
                  (var_res_prop f ({|v|},{||}) {||})
                  (var_res_prop f ({||},{||}) {||})]))` THEN

ASM_SIMP_TAC std_ss [VAR_RES_PROGRAM_IS_ABSTRACTION___var_res_prog_local_var] THEN
MATCH_MP_TAC VAR_RES_COND_INFERENCE___prog_forall THEN
SIMP_TAC std_ss [] THEN GEN_TAC THEN
MATCH_MP_TAC
  (MP_CANON VAR_RES_COND_INFERENCE___var_res_prog_cond_best_local_action___VAR_CHANGE) THEN
SIMP_TAC std_ss [BAG_OF_EMPTY, EMPTY_SUBSET, BAG_DIFF_EMPTY,
   BAG_UNION_EMPTY, BAG_UNION_INSERT, VAR_RES_FRAME_SPLIT_NORMALISE] THEN
MATCH_MP_TAC (MP_CANON VAR_RES_FRAME_SPLIT___SOLVE) THEN
CONJ_TAC THEN1 (
   FULL_SIMP_TAC std_ss [var_res_prop___COND___REWRITE,
      BAG_EVERY, BAG_DIFF_EMPTY]
) THEN
SIMP_TAC std_ss [BAG_UNION_EMPTY] THEN REPEAT STRIP_TAC THEN

Tactical.REVERSE (Cases_on `BAG_ALL_DISTINCT (BAG_UNION (BAG_INSERT d wpb) rpb)`) THEN1 (
   ASM_SIMP_TAC std_ss [VAR_RES_COND_HOARE_TRIPLE_def, var_res_prop___REWRITE,
      var_res_prop___COND___REWRITE]
) THEN
SIMP_TAC std_ss [VAR_RES_COND_INFERENCE___prog_block] THEN
MATCH_MP_TAC VAR_RES_COND_INFERENCE___prog_seq THEN
Q.EXISTS_TAC `COND_PROP___STRONG_EXISTS (\x'.
   var_res_prop f (BAG_INSERT d wpb,rpb) (sfb' x'))` THEN

ASM_REWRITE_TAC[] THEN
CONJ_TAC THEN1 (
   SIMP_TAC std_ss [var_res_prop___COND___REWRITE,
      var_res_prop___REWRITE, BAG_ALL_DISTINCT_BAG_UNION,
      COND_PROP___STRONG_EXISTS_def, FORALL_AND_THM] THEN
   REPEAT STRIP_TAC THEN
   MATCH_MP_TAC VAR_RES_IS_STACK_IMPRECISE___USED_VARS___SUBSET THEN
   Q.EXISTS_TAC `SET_OF_BAG (BAG_UNION wpb rpb)` THEN
   ASM_SIMP_TAC std_ss [SUBSET_DEF, IN_SET_OF_BAG, BAG_IN_BAG_UNION,
      BAG_IN_BAG_INSERT, DISJ_IMP_THM] THEN
   RES_TAC
) THEN

MATCH_MP_TAC VAR_RES_COND_INFERENCE___STRONG_COND_EXISTS_PRE THEN
GEN_TAC THEN
MATCH_MP_TAC VAR_RES_COND_INFERENCE___STRONG_COND_EXISTS_POST THEN
Q.EXISTS_TAC `x` THEN
SIMP_TAC std_ss [] THEN
MATCH_MP_TAC (MP_CANON VAR_RES_COND_INFERENCE___var_res_prog_cond_best_local_action___VAR_CHANGE) THEN
SIMP_TAC std_ss [VAR_RES_FRAME_SPLIT_NORMALISE] THEN
CONJ_TAC THEN1 (
   SIMP_TAC std_ss [SUBSET_DEF, IN_SET_OF_BAG, NOT_IN_EMPTY_BAG,
      BAG_IN_BAG_INSERT]
) THEN

MATCH_MP_TAC (MP_CANON VAR_RES_FRAME_SPLIT___SOLVE) THEN
ASM_SIMP_TAC std_ss [BAG_UNION_EMPTY, BAG_DIFF_EMPTY,
   BAG_DIFF_INSERT_same, BAG_UNION_INSERT] THEN
CONJ_TAC THEN1 (
   FULL_SIMP_TAC std_ss [BAG_EVERY, var_res_prop___COND___REWRITE] THEN
   REPEAT STRIP_TAC THEN
   MATCH_MP_TAC VAR_RES_IS_STACK_IMPRECISE___USED_VARS___SUBSET THEN
   Q.EXISTS_TAC `(SET_OF_BAG (BAG_UNION wpb rpb))` THEN
   ASM_SIMP_TAC std_ss [SUBSET_DEF, IN_SET_OF_BAG, BAG_IN_BAG_UNION,
     IN_UNION, IN_DIFF, BAG_IN_BAG_INSERT, NOT_IN_EMPTY_BAG] THEN
   FULL_SIMP_TAC std_ss [BAG_ALL_DISTINCT_BAG_UNION, BAG_DISJOINT_BAG_INSERT,
      BAG_ALL_DISTINCT_THM] THEN
   METIS_TAC[]
) THEN
STRIP_TAC THEN

SIMP_TAC std_ss [VAR_RES_COND_HOARE_TRIPLE_def,
  VAR_RES_HOARE_TRIPLE_def, ASL_PROGRAM_HOARE_TRIPLE_def,
  var_res_prop___REWRITE, ASL_PROGRAM_SEM___skip, HOARE_TRIPLE_def,
  IN_ABS, fasl_order_THM, asl_prog_block_def] THEN
SIMP_TAC std_ss [asla_skip_def, SUBSET_DEF, IN_ABS, IN_SING,
  VAR_RES_STACK___IS_EQUAL_UPTO_VALUES___REFL]);





val VAR_RES_COND_INFERENCE___prog_call_by_value_arg = store_thm (
   "VAR_RES_COND_INFERENCE___prog_call_by_value_arg",
``!f wpb rpb sfb sfb' body c.

(!v. VAR_RES_COND_HOARE_TRIPLE f (var_res_prop f (BAG_INSERT v wpb,rpb)
         (BAG_INSERT (var_res_prop_equal f (var_res_exp_var v) (var_res_exp_const c)) sfb))
         (body v) (COND_PROP___STRONG_EXISTS
            (\x'. var_res_prop f (BAG_INSERT v wpb,rpb) (sfb' x')))) ==>

(VAR_RES_COND_HOARE_TRIPLE f (var_res_prop f (wpb,rpb) sfb)
   (var_res_prog_call_by_value_arg body c)
   (COND_PROP___STRONG_EXISTS (\x'. var_res_prop f (wpb,rpb) (sfb' x'))))``,

REPEAT STRIP_TAC THEN
MATCH_MP_TAC VAR_RES_COND_HOARE_TRIPLE___PROGRAM_ABSTRACTION THEN
Tactical.REVERSE (Cases_on `
   (var_res_prop___COND f (wpb,rpb) sfb) /\
   (!x'. (var_res_prop___COND f (wpb,rpb) (sfb' x')))`) THEN1 (
   ASM_SIMP_TAC std_ss [VAR_RES_COND_HOARE_TRIPLE_def, var_res_prop___REWRITE,
      VAR_RES_PROGRAM_IS_ABSTRACTION_def, COND_PROP___STRONG_EXISTS_def] THEN
   PROVE_TAC[ASL_PROGRAM_IS_ABSTRACTION___REFL]
) THEN
Cases_on `IS_SEPARATION_COMBINATOR f` THEN FULL_SIMP_TAC std_ss [var_res_prop___COND___REWRITE] THEN

Q.EXISTS_TAC `asl_prog_forall
          (\v.
             asl_prog_block
               [var_res_prog_cond_best_local_action
                  (var_res_prop f ({||},{||}) {||})
                  (var_res_prop f ({|v|},{||})
                     {|var_res_prop_equal f (var_res_exp_var v)
                         (var_res_exp_const c)|}); body v;
                var_res_prog_cond_best_local_action
                  (var_res_prop f ({|v|},{||}) {||})
                  (var_res_prop f ({||},{||}) {||})])` THEN
ASM_SIMP_TAC std_ss [VAR_RES_PROGRAM_IS_ABSTRACTION___var_res_prog_call_by_value_arg] THEN
MATCH_MP_TAC VAR_RES_COND_INFERENCE___prog_forall THEN
SIMP_TAC std_ss [] THEN GEN_TAC THEN
MATCH_MP_TAC
  (MP_CANON VAR_RES_COND_INFERENCE___var_res_prog_cond_best_local_action___VAR_CHANGE) THEN
SIMP_TAC std_ss [BAG_OF_EMPTY, EMPTY_SUBSET, BAG_DIFF_EMPTY,
   BAG_UNION_EMPTY, BAG_UNION_INSERT, VAR_RES_FRAME_SPLIT_NORMALISE] THEN
MATCH_MP_TAC (MP_CANON VAR_RES_FRAME_SPLIT___SOLVE) THEN
CONJ_TAC THEN1 (
   FULL_SIMP_TAC std_ss [var_res_prop___COND___REWRITE, BAG_EVERY,
      BAG_DIFF_EMPTY]
) THEN
SIMP_TAC std_ss [BAG_UNION_EMPTY] THEN STRIP_TAC THEN

Tactical.REVERSE (Cases_on `BAG_ALL_DISTINCT (BAG_UNION (BAG_INSERT d wpb) rpb)`) THEN1 (
   ASM_SIMP_TAC std_ss [VAR_RES_COND_HOARE_TRIPLE_def, var_res_prop___REWRITE,
      var_res_prop___COND___REWRITE]
) THEN
SIMP_TAC std_ss [VAR_RES_COND_INFERENCE___prog_block] THEN
MATCH_MP_TAC VAR_RES_COND_INFERENCE___prog_seq THEN
Q.EXISTS_TAC `COND_PROP___STRONG_EXISTS (\x'. var_res_prop f (BAG_INSERT d wpb,rpb) (sfb' x'))` THEN

ASM_REWRITE_TAC[] THEN
CONJ_TAC THEN1 (
   SIMP_TAC std_ss [var_res_prop___COND___REWRITE,
      var_res_prop___REWRITE, BAG_ALL_DISTINCT_BAG_UNION,
      COND_PROP___STRONG_EXISTS_def, FORALL_AND_THM] THEN
   REPEAT STRIP_TAC THEN
   MATCH_MP_TAC VAR_RES_IS_STACK_IMPRECISE___USED_VARS___SUBSET THEN
   Q.EXISTS_TAC `SET_OF_BAG (BAG_UNION wpb rpb)` THEN
   ASM_SIMP_TAC std_ss [SUBSET_DEF, IN_SET_OF_BAG, BAG_IN_BAG_UNION,
      BAG_IN_BAG_INSERT, DISJ_IMP_THM] THEN
   RES_TAC
) THEN

MATCH_MP_TAC VAR_RES_COND_INFERENCE___STRONG_COND_EXISTS_PRE THEN
GEN_TAC THEN
MATCH_MP_TAC VAR_RES_COND_INFERENCE___STRONG_COND_EXISTS_POST THEN
Q.EXISTS_TAC `x` THEN
SIMP_TAC std_ss [] THEN

MATCH_MP_TAC (MP_CANON VAR_RES_COND_INFERENCE___var_res_prog_cond_best_local_action___VAR_CHANGE) THEN
SIMP_TAC std_ss [SUBSET_DEF, IN_SET_OF_BAG, NOT_IN_EMPTY_BAG,
      BAG_IN_BAG_INSERT, VAR_RES_FRAME_SPLIT_NORMALISE] THEN
MATCH_MP_TAC (MP_CANON VAR_RES_FRAME_SPLIT___SOLVE) THEN
ASM_SIMP_TAC std_ss [BAG_UNION_EMPTY, BAG_DIFF_EMPTY,
   BAG_DIFF_INSERT_same, BAG_UNION_INSERT] THEN
CONJ_TAC THEN1 (
   FULL_SIMP_TAC std_ss [BAG_EVERY, var_res_prop___COND___REWRITE] THEN
   REPEAT STRIP_TAC THEN
   MATCH_MP_TAC VAR_RES_IS_STACK_IMPRECISE___USED_VARS___SUBSET THEN
   Q.EXISTS_TAC `(SET_OF_BAG (BAG_UNION wpb rpb))` THEN
   ASM_SIMP_TAC std_ss [SUBSET_DEF, IN_SET_OF_BAG, BAG_IN_BAG_UNION,
     IN_UNION, IN_DIFF, BAG_IN_BAG_INSERT, NOT_IN_EMPTY_BAG] THEN
   FULL_SIMP_TAC std_ss [BAG_ALL_DISTINCT_BAG_UNION, BAG_DISJOINT_BAG_INSERT,
      BAG_ALL_DISTINCT_THM] THEN
   METIS_TAC[]
) THEN
SIMP_TAC std_ss [VAR_RES_COND_HOARE_TRIPLE_def,
  VAR_RES_HOARE_TRIPLE_def, ASL_PROGRAM_HOARE_TRIPLE_def,
  var_res_prop___REWRITE, ASL_PROGRAM_SEM___skip, HOARE_TRIPLE_def,
  IN_ABS, fasl_order_THM, asl_prog_block_def] THEN
SIMP_TAC std_ss [asla_skip_def, SUBSET_DEF, IN_ABS, IN_SING,
  VAR_RES_STACK___IS_EQUAL_UPTO_VALUES___REFL]);





(*******************************************************
 * Assignments
 ******************************************************)


val var_res_assign_action_def = Define `
   (var_res_assign_action v e) s =
      let ev_opt = e (FST s) in
      if ((var_res_sl___has_write_permission v (FST s)) /\ (IS_SOME ev_opt)) then
         SOME {(var_res_ext_state_var_update (v, (THE ev_opt))) s} else
      NONE`

val ASL_IS_LOCAL_ACTION___var_res_assign_action = store_thm (
"ASL_IS_LOCAL_ACTION___var_res_assign_action",
``!f e v.
IS_SOME (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS e) ==>
ASL_IS_LOCAL_ACTION (VAR_RES_COMBINATOR f) (var_res_assign_action v e)``,

SIMP_TAC std_ss [ASL_IS_LOCAL_ACTION___ALTERNATIVE_EXT_DEF,
   var_res_assign_action_def, LET_THM, COND_NONE_SOME_REWRITES,
   IN_SING, VAR_RES_COMBINATOR_REWRITE,
   var_res_ext_state_var_update_def,
   IS_SOME___VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS___REWRITE,
   GSYM LEFT_FORALL_IMP_THM, VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_REL___REWRITE,
   SOME___VAR_RES_STACK_COMBINE,
   FMERGE_DEF, var_res_sl___has_write_permission_def] THEN
REPEAT GEN_TAC THEN STRIP_TAC THEN
REPEAT GEN_TAC THEN STRIP_TAC THEN
`vs SUBSET FDOM (FST s1) UNION FDOM (FST s2)` by
   FULL_SIMP_TAC std_ss [IN_UNION, SUBSET_DEF] THEN
`~(v IN FDOM (FST s2))` by ALL_TAC THEN1 (
   Q.PAT_ASSUM `VAR_RES_STACK_IS_SEPARATE (FST s1) (FST s2)` MP_TAC THEN
   ASM_SIMP_TAC std_ss [VAR_RES_STACK_IS_SEPARATE_def,
     GSYM LEFT_EXISTS_IMP_THM] THEN
   Q.EXISTS_TAC `v` THEN
   ASM_SIMP_TAC std_ss [var_res_permission_THM2]
) THEN
`?c. (e (FST s1) = SOME c) /\ (e (FMERGE VAR_RES_STACK_COMBINE___MERGE_FUNC (FST s1) (FST s2)) = SOME c)` by ALL_TAC THEN1 (
   Tactical.REVERSE (Cases_on `IS_SOME (e (FST s1))`) THEN1 (
      POP_ASSUM MP_TAC THEN
      ASM_REWRITE_TAC[]
   ) THEN
   FULL_SIMP_TAC std_ss [IS_SOME_EXISTS] THEN
   POP_ASSUM (fn thm => REWRITE_TAC[GSYM thm]) THEN
   Q.PAT_ASSUM `!st1 st2. X ==> (e st1 = e st2)` MATCH_MP_TAC THEN
   ASM_SIMP_TAC std_ss [FMERGE_DEF] THEN
   FULL_SIMP_TAC std_ss [SUBSET_DEF, VAR_RES_STACK_COMBINE___MERGE_FUNC_def,
      COND_REWRITES]
) THEN
ASM_SIMP_TAC std_ss [var_res_state_var_update_def, IN_UNION] THEN
CONJ_TAC THENL [
   FULL_SIMP_TAC std_ss [VAR_RES_STACK_IS_SEPARATE_def,
     FDOM_FUPDATE, IN_INSERT, FAPPLY_FUPDATE_THM] THEN
   GEN_TAC THEN Cases_on `x = v` THEN
   ASM_SIMP_TAC std_ss [],


   SIMP_TAC std_ss [GSYM fmap_EQ_THM, FMERGE_DEF, FDOM_FUPDATE,
      EXTENSION, IN_UNION, IN_INSERT, FAPPLY_FUPDATE_THM] THEN
   SIMP_TAC (std_ss++EQUIV_EXTRACT_ss) [] THEN
   GEN_TAC THEN Cases_on `x = v` THEN
   ASM_SIMP_TAC std_ss []
]);


val var_res_prog_assign_def = Define `var_res_prog_assign v e =
  asl_prog_prim_command (asl_pc_shallow_command (\f. (var_res_assign_action v e)))`;


val VAR_RES_PROGRAM_IS_ABSTRACTION___var_res_prog_assign = store_thm (
"VAR_RES_PROGRAM_IS_ABSTRACTION___var_res_prog_assign",
``!f v c e vs.
   IS_SEPARATION_COMBINATOR f /\
   (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS e = SOME vs) ==>

   (VAR_RES_PROGRAM_IS_ABSTRACTION f
    (var_res_prog_assign v e)
    (var_res_prog_cond_best_local_action
      (var_res_prop f ({|v|}, BAG_OF_SET (vs DELETE v))
        {|var_res_prop_equal f (var_res_exp_var v) (var_res_exp_const c)|})
      (var_res_prop f ({|v|}, BAG_OF_SET (vs DELETE v))
        {|var_res_prop_equal f (var_res_exp_var v) (var_res_exp_var_update (v, c) e)|})))``,


SIMP_TAC std_ss [ASL_PROGRAM_IS_ABSTRACTION_def,
   VAR_RES_PROGRAM_IS_ABSTRACTION_def,
   ASL_PROGRAM_SEM___prim_command,
   var_res_prog_assign_def,
   var_res_prog_cond_best_local_action_REWRITE,
   ASL_ATOMIC_ACTION_SEM_def, EVAL_asl_prim_command_THM,
   ASL_IS_LOCAL_ACTION___var_res_assign_action,
   ASL_IS_LOCAL_ACTION___var_res_cond_best_local_action,
   IS_SEPARATION_COMBINATOR___VAR_RES_COMBINATOR,
   fasl_action_order_POINTWISE_DEF] THEN
REPEAT STRIP_TAC THEN
`VAR_RES_IS_STACK_IMPRECISE___USED_VARS (v INSERT vs) (var_res_prop_equal f (var_res_exp_var v) e) /\
 VAR_RES_IS_STACK_IMPRECISE___USED_VARS (v INSERT vs) (var_res_prop_equal f (var_res_exp_var v) (var_res_exp_const c)) /\
 VAR_RES_IS_STACK_IMPRECISE___USED_VARS (v INSERT vs) (var_res_prop_equal f (var_res_exp_var v) (var_res_exp_var_update (v, c) e))` by ALL_TAC THEN1 (
   CONSEQ_REWRITE_TAC([VAR_RES_IS_STACK_IMPRECISE___USED_VARS___var_res_prop_equal],[],[]) THEN
   SIMP_TAC (std_ss++CONJ_ss) [
      VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET___VAR_CONST_EVAL, IN_INSERT,
      VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET___var_res_exp_var_update] THEN
   ASM_SIMP_TAC std_ss [VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET_def,
                        SUBSET_DEF, IN_INSERT]
) THEN
`(VAR_RES_IS_STACK_IMPRECISE (var_res_prop_equal f (var_res_exp_var v) e)) /\
 (VAR_RES_IS_STACK_IMPRECISE (var_res_prop_equal f (var_res_exp_var v) (var_res_exp_const c))) /\
 (VAR_RES_IS_STACK_IMPRECISE (var_res_prop_equal f (var_res_exp_var v) (var_res_exp_var_update (v, c) e)))` by
   FULL_SIMP_TAC std_ss [VAR_RES_IS_STACK_IMPRECISE___USED_VARS_def] THEN

FULL_SIMP_TAC std_ss [
   var_res_assign_action_def,
   VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_THM,
   VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_REL___EXPAND,
   LET_THM,
   var_res_best_local_action_def,
   quant_best_local_action_def,
   var_res_cond_best_local_action_def,
   var_res_prop___REWRITE,
   var_res_prop___COND___REWRITE,
   FINITE_BAG_THM, NOT_IN_EMPTY_BAG, BAG_ALL_DISTINCT_BAG_UNION,
   BAG_ALL_DISTINCT_THM, BAG_DISJOINT_BAG_INSERT,
   BAG_DISJOINT_EMPTY, BAG_IN_BAG_INSERT,
   SET_BAG_I, BAG_IN_BAG_OF_SET,
   BAG_ALL_DISTINCT_BAG_OF_SET, SET_OF_BAG_INSERT,
   BAG_UNION_INSERT, BAG_UNION_EMPTY, IN_DELETE, INSERT_DELETE_2] THEN
ASM_SIMP_TAC (std_ss++CONJ_ss) [
   var_res_prop___PROP___REWRITE, IN_ABS,
   var_res_bigstar_REWRITE_EXT,
   asl_star___var_res_prop_stack_true___STACK_IMPRECISE___COMM] THEN
ASM_SIMP_TAC (std_ss++CONJ_ss) [
   NOT_IN_EMPTY_BAG, BAG_IN_BAG_INSERT, BAG_IN_BAG_OF_SET,
   var_res_sl___has_read_permission_def, var_res_sl___has_write_permission_def,
   IN_DELETE, GSYM SUBSET_DEF, LET_THM,
   var_res_prop_equal_def, var_res_prop_binexpression_def,
   var_res_stack_proposition_def, IN_ABS, var_res_exp_var_def] THEN
Q.ABBREV_TAC `fail_cond =
   (v IN FDOM (FST s) /\
   (SND (FST s ' v) = var_res_write_permission)) /\
   vs SUBSET FDOM (FST s)` THEN
Tactical.REVERSE (Cases_on `fail_cond=T`) THEN1 (
   POP_ASSUM MP_TAC THEN
   FULL_SIMP_TAC std_ss [
      fasl_order_THM, NONE___INF_fasl_action_order, IN_ABS,
      GSYM LEFT_FORALL_IMP_THM,
      NONE___best_local_action,
      var_res_prop_stack_true_def,
      var_res_bool_proposition_REWRITE, asl_emp_def,
      IS_SEPARATION_COMBINATOR_EXPAND_THM,
      GSYM LEFT_EXISTS_AND_THM, GSYM RIGHT_EXISTS_AND_THM,
      VAR_RES_COMBINATOR_REWRITE,
      SOME___VAR_RES_STACK_COMBINE,
      PAIR_FORALL_THM] THEN
   QUANT_INSTANTIATE_TAC [] THEN
   DISCH_TAC THEN CCONTR_TAC THEN
   Q.PAT_ASSUM `~fail_cond` MP_TAC THEN
   Q.UNABBREV_TAC `fail_cond` THEN
   FULL_SIMP_TAC std_ss [FMERGE_DEF, IN_UNION, SUBSET_DEF,
      VAR_RES_STACK_COMBINE___MERGE_FUNC_def, COND_REWRITES,
      VAR_RES_STACK_IS_SEPARATE_def] THEN
   Q.PAT_ASSUM `!x. x IN FDOM x1' /\ x IN Y ==> Z` (MP_TAC o Q.SPEC `v`) THEN
   ASM_SIMP_TAC std_ss [var_res_permission_THM2] THEN
   METIS_TAC[]
) THEN
Q.UNABBREV_TAC `fail_cond` THEN
FULL_SIMP_TAC std_ss [COND_NONE_SOME_REWRITES, fasl_order_THM2] THEN
SIMP_TAC std_ss [SOME___INF_fasl_action_order, IN_ABS, GSYM RIGHT_EXISTS_AND_THM,
   GSYM LEFT_EXISTS_AND_THM, SUBSET_DEF, IN_BIGINTER, IN_SING, IN_IMAGE, IN_INTER,
   IS_SOME_EXISTS, GSYM LEFT_FORALL_IMP_THM] THEN
REPEAT GEN_TAC THEN STRIP_TAC THEN POP_ASSUM (K ALL_TAC) THEN
FULL_SIMP_TAC (std_ss++CONJ_ss) [
   IS_SEPARATION_COMBINATOR_EXPAND_THM,
   GSYM LEFT_EXISTS_AND_THM, GSYM RIGHT_EXISTS_AND_THM,
   SOME___best_local_action, IN_ABS,
   var_res_prop_stack_true_def, var_res_bool_proposition_REWRITE,
   asl_emp_def, IN_BIGINTER, VAR_RES_COMBINATOR_REWRITE,
   GSYM SUBSET_DEF, PAIR_EXISTS_THM, IN_IMAGE,
   GSYM LEFT_FORALL_IMP_THM, PAIR_FORALL_THM,
   var_res_exp_const_def] THEN
QUANT_INSTANTIATE_TAC [] THEN
REPEAT STRIP_TAC THEN
Q.PAT_ASSUM `VAR_RES_STACK_COMBINE (SOME x1') (SOME x1) = SOME (FST s)` (K ALL_TAC) THEN
FULL_SIMP_TAC std_ss [var_res_ext_state_var_update_def,
   asl_star_def, IN_ABS, IN_SING, VAR_RES_COMBINATOR_REWRITE,
   PAIR_EXISTS_THM] THEN
`?c2. (e (FST s) = SOME c2)` by ALL_TAC THEN1 (
   ASM_SIMP_TAC std_ss [GSYM IS_SOME_EXISTS]
) THEN
Q.EXISTS_TAC `var_res_state_var_update v c2 x1` THEN
ONCE_REWRITE_TAC[VAR_RES_STACK_COMBINE___COMM] THEN
QUANT_INSTANTIATE_TAC [] THEN
FULL_SIMP_TAC std_ss [SOME___VAR_RES_STACK_COMBINE,
   var_res_state_var_update_def, FDOM_FUPDATE, FMERGE_DEF,
   FAPPLY_FUPDATE_THM, IN_INSERT,
   VAR_RES_STACK_IS_SEPARATE_def, VAR_RES_STACK___IS_EQUAL_UPTO_VALUES_def,
   VAR_RES_STACK_COMBINE___MERGE_FUNC_def,
   var_res_permission_THM2, COND_REWRITES,
   GSYM fmap_EQ_THM] THEN
`~(v IN FDOM x1''')` by ALL_TAC THEN1 (
   Q.PAT_ASSUM `!x. x IN FDOM x1''' /\ x IN FDOM x1 ==> Z`
      (MP_TAC o Q.SPEC `v`) THEN
   ASM_SIMP_TAC std_ss [var_res_permission_THM2]
) THEN
Q.PAT_ASSUM `FDOM (FST s) = X` ASSUME_TAC THEN
FULL_SIMP_TAC (std_ss++CONJ_ss) [IN_UNION] THEN
REPEAT CONJ_TAC THENL [
   GEN_TAC THEN
   Q.PAT_ASSUM `!x. X x` (MP_TAC o Q.SPEC `x`) THEN
   Cases_on `x = v` THEN ASM_SIMP_TAC std_ss [],

   SIMP_TAC (std_ss++EQUIV_EXTRACT_ss) [
     EXTENSION, IN_INSERT, IN_UNION],

   GEN_TAC THEN
   Q.PAT_ASSUM `!x. X x` (MP_TAC o Q.SPEC `x`) THEN
   Cases_on `x = v` THEN ASM_SIMP_TAC std_ss [COND_REWRITES],


   SIMP_TAC std_ss [var_res_exp_var_update_def,
      var_res_state_var_update_def, FUPDATE_EQ] THEN
   Tactical.REVERSE (`e (x1 |+ (v,c,var_res_write_permission)) = e (FST s)` by ALL_TAC) THEN1 (
      ASM_SIMP_TAC std_ss []
   ) THEN
   Q.PAT_ASSUM `!st1 st2. X ==> (e st1 = e st2)` MATCH_MP_TAC THEN
   ASM_SIMP_TAC std_ss [FAPPLY_FUPDATE_THM, SUBSET_DEF, FDOM_FUPDATE, IN_INSERT, IN_UNION] THEN
   REPEAT STRIP_TAC THENL [
      METIS_TAC[],
      METIS_TAC[],


      Q.PAT_ASSUM `!x. X x` (MP_TAC o Q.SPEC `v'`) THEN
      `v' IN FDOM x1` by METIS_TAC[] THEN
      ASM_SIMP_TAC std_ss [COND_REWRITES]
   ]
]);



val VAR_RES_COND_INFERENCE___var_res_prog_assign =
store_thm ("VAR_RES_COND_INFERENCE___var_res_prog_assign",
``
!f wpb rpb v e c sfb progL Q.
((BAG_IN v wpb) /\
(VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET (SET_OF_BAG (BAG_UNION wpb rpb)) e)) ==>

((VAR_RES_COND_HOARE_TRIPLE f
   (var_res_prop f (wpb,rpb)
      (BAG_INSERT (var_res_prop_equal f (var_res_exp_var v)
                                        (var_res_exp_varlist_update [(v, c)] e))
      (BAG_IMAGE (var_res_prop_varlist_update [(v, c)]) sfb)))
    (asl_prog_block progL) Q) ==>


(VAR_RES_COND_HOARE_TRIPLE f
   (var_res_prop f (wpb,rpb)
      (BAG_INSERT (var_res_prop_equal f (var_res_exp_var v) (var_res_exp_const c))
       sfb))
   (asl_prog_block ((var_res_prog_assign v e)::progL)) Q))``,

REPEAT STRIP_TAC THEN
SIMP_TAC std_ss [VAR_RES_COND_INFERENCE___prog_block] THEN
MATCH_MP_TAC VAR_RES_COND_HOARE_TRIPLE___PROGRAM_ABSTRACTION_first THEN
FULL_SIMP_TAC std_ss [VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET___REWRITE,
   GSYM VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_THM] THEN
Tactical.REVERSE (Cases_on `(var_res_prop___COND f (wpb,rpb)
    (BAG_INSERT  (var_res_prop_equal f (var_res_exp_var v)
                 (var_res_exp_const c)) sfb))`) THEN1 (
   ASM_SIMP_TAC std_ss [VAR_RES_COND_HOARE_TRIPLE_def,
     var_res_prop___REWRITE, VAR_RES_PROGRAM_IS_ABSTRACTION_def] THEN
   PROVE_TAC[ASL_PROGRAM_IS_ABSTRACTION___REFL]
) THEN
Cases_on `IS_SEPARATION_COMBINATOR f` THEN FULL_SIMP_TAC std_ss [] THEN
IMP_RES_TAC VAR_RES_PROGRAM_IS_ABSTRACTION___var_res_prog_assign THEN
POP_ASSUM (fn thm => let
      val thm0 = Q.SPECL [`v`, `c`] thm;
      val prog' = rand (concl thm0);
   in
      EXISTS_TAC prog' THEN MP_TAC thm0
   end) THEN
SIMP_TAC std_ss [] THEN DISCH_TAC THEN POP_ASSUM (K ALL_TAC) THEN
SIMP_TAC std_ss [GSYM VAR_RES_COND_INFERENCE___prog_block] THEN
HO_MATCH_MP_TAC
  (MP_CANON VAR_RES_COND_INFERENCE___var_res_prog_cond_best_local_action) THEN
SIMP_TAC std_ss [VAR_RES_FRAME_SPLIT_NORMALISE] THEN
CONJ_TAC THEN1 (
   FULL_SIMP_TAC std_ss [SUBSET_DEF, IN_SET_OF_BAG,
      BAG_IN_BAG_INSERT, NOT_IN_EMPTY_BAG, BAG_IN_BAG_OF_SET,
      IN_DELETE]
) THEN
SIMP_TAC std_ss [VAR_RES_FRAME_SPLIT___FRAME] THEN
MATCH_MP_TAC VAR_RES_FRAME_SPLIT___equal_const___context_SING THEN
FULL_SIMP_TAC std_ss [BAG_IMAGE_EMPTY, IN_SET_OF_BAG, BAG_IN_BAG_UNION,
   var_res_prop_varlist_update_SING, var_res_exp_varlist_update_SING] THEN
MATCH_MP_TAC (MP_CANON VAR_RES_FRAME_SPLIT___SOLVE) THEN

FULL_SIMP_TAC std_ss [BAG_UNION_INSERT, BAG_UNION_EMPTY, BAG_EVERY,
   BAG_IN_FINITE_BAG_IMAGE, var_res_prop___COND___REWRITE, FINITE_BAG_THM,
   BAG_IN_BAG_INSERT, DISJ_IMP_THM, FORALL_AND_THM,
   GSYM LEFT_FORALL_IMP_THM] THEN
REPEAT STRIP_TAC  THEN
MATCH_MP_TAC VAR_RES_IS_STACK_IMPRECISE___USED_VARS___var_res_prop_var_update___INSERT THEN
MATCH_MP_TAC VAR_RES_IS_STACK_IMPRECISE___USED_VARS___SUBSET THEN
Q.EXISTS_TAC `SET_OF_BAG (BAG_UNION wpb rpb)` THEN
ASM_SIMP_TAC std_ss [] THEN
ASM_SIMP_TAC std_ss [
   SUBSET_DEF, IN_SET_OF_BAG, IN_INSERT, IN_DIFF, IN_UNION,
   BAG_IN_BAG_UNION, DISJ_IMP_THM, FORALL_AND_THM, BAG_IN_BAG_INSERT,
   NOT_IN_EMPTY_BAG, BAG_IN_BAG_DIFF_ALL_DISTINCT]);





(*******************************************************
 * procedure calls
 ******************************************************)


val var_res_prog_eval_expressions_def = Define `
var_res_prog_eval_expressions prog (expL:('a, 'b,'c) var_res_expression list) =
asl_prog_choose_constants prog (MAP (\e s. e (FST s)) expL)`


val var_res_prog_procedure_call_def = Define `
var_res_prog_procedure_call name (ref, expL:('a, 'b,'c) var_res_expression list) =
asl_prog_ext_procedure_call name (ref, (MAP (\e s. e (FST s)) expL))`


val var_res_prog_procedure_call_THM =
store_thm ("var_res_prog_procedure_call_THM",
``var_res_prog_procedure_call name (ref, expL) =
var_res_prog_eval_expressions
  (\constL. asl_prog_procedure_call name (ref,constL)) expL``,

SIMP_TAC std_ss [var_res_prog_procedure_call_def,
   var_res_prog_eval_expressions_def, asl_prog_ext_procedure_call_def]);


val var_res_prog_parallel_procedure_call_def = Define `
var_res_prog_parallel_procedure_call name1 (ref1, expL1:('a, 'b,'c) var_res_expression list)
name2 (ref2, expL2:('a, 'b,'c) var_res_expression list)=
asl_prog_ext_parallel_procedure_call
name1 (ref1, (MAP (\e s. e (FST s)) expL1))
name2 (ref2, (MAP (\e s. e (FST s)) expL2))`


val var_res_prog_parallel_procedure_call_THM =
store_thm ("var_res_prog_parallel_procedure_call_THM",
``var_res_prog_parallel_procedure_call name1 (ref1, expL1:('a, 'b,'c) var_res_expression list)
name2 (ref2, expL2:('a, 'b,'c) var_res_expression list) =

var_res_prog_eval_expressions
  (\constL1. var_res_prog_eval_expressions (\constL2.
      asl_prog_parallel
          (asl_prog_procedure_call name1 (ref1,constL1))
          (asl_prog_procedure_call name2 (ref2,constL2))) expL2) expL1``,

SIMP_TAC std_ss [var_res_prog_parallel_procedure_call_def,
   var_res_prog_eval_expressions_def, asl_prog_ext_parallel_procedure_call_def]);



val ASL_PROGRAM_IS_ABSTRACTION___var_res_prog_eval_expressions = store_thm (
"ASL_PROGRAM_IS_ABSTRACTION___var_res_prog_eval_expressions",
``!xenv penv expL prog prog'.
(!constL. ASL_PROGRAM_IS_ABSTRACTION xenv penv (prog constL) (prog' constL)) ==>
ASL_PROGRAM_IS_ABSTRACTION xenv penv
       (var_res_prog_eval_expressions prog  expL)
       (var_res_prog_eval_expressions prog' expL)``,

REPEAT STRIP_TAC THEN
SIMP_TAC std_ss [var_res_prog_eval_expressions_def,
   asl_prog_choose_constants_def] THEN
MATCH_MP_TAC ASL_PROGRAM_IS_ABSTRACTION___ndet THEN
SIMP_TAC list_ss [IN_ABS, GSYM LEFT_EXISTS_AND_THM,
   GSYM LEFT_FORALL_IMP_THM, IN_IMAGE] THEN
REPEAT STRIP_TAC THEN
Q.EXISTS_TAC `constL` THEN
CONSEQ_REWRITE_TAC ([ASL_PROGRAM_IS_ABSTRACTION___seq], [], []) THEN
ASM_SIMP_TAC std_ss [ASL_PROGRAM_IS_ABSTRACTION___REFL]);



val ASL_PROGRAM_IS_ABSTRACTION___var_res_prog_procedure_call = store_thm (
"ASL_PROGRAM_IS_ABSTRACTION___var_res_prog_procedure_call",
``!xenv penv name arg prog'.
(!arg. ASL_PROGRAM_IS_ABSTRACTION xenv penv (
   asl_prog_procedure_call name arg) (prog' arg)) ==>
ASL_PROGRAM_IS_ABSTRACTION xenv penv
       (var_res_prog_procedure_call name arg)
       (var_res_prog_eval_expressions
        (\constL. prog' (FST arg, constL)) (SND arg))``,

REPEAT STRIP_TAC THEN
`?ref expL. arg = (ref, expL)` by (Cases_on `arg` THEN SIMP_TAC std_ss []) THEN
ASM_SIMP_TAC std_ss [var_res_prog_procedure_call_THM] THEN
MATCH_MP_TAC ASL_PROGRAM_IS_ABSTRACTION___var_res_prog_eval_expressions THEN
ASM_SIMP_TAC std_ss []);



val VAR_RES_STACK___IS_EQUAL_UPTO_VALUES___VAR_RES_STACK_COMBINE =
store_thm ("VAR_RES_STACK___IS_EQUAL_UPTO_VALUES___VAR_RES_STACK_COMBINE",
``!st1 st2 st11 st12 st21 st22.
(VAR_RES_STACK_COMBINE (SOME st11) (SOME st12) = SOME st1) /\
(VAR_RES_STACK_COMBINE (SOME st21) (SOME st22) = SOME st2) /\
VAR_RES_STACK___IS_EQUAL_UPTO_VALUES st11 st21 /\
VAR_RES_STACK___IS_EQUAL_UPTO_VALUES st12 st22 ==>
VAR_RES_STACK___IS_EQUAL_UPTO_VALUES st1 st2``,


SIMP_TAC std_ss [VAR_RES_STACK___IS_EQUAL_UPTO_VALUES_def,
   SOME___VAR_RES_STACK_COMBINE, FMERGE_DEF, IN_UNION,
   VAR_RES_STACK_IS_SEPARATE_def, GSYM FORALL_AND_THM] THEN
REPEAT GEN_TAC THEN
HO_MATCH_MP_TAC (prove (``(!x. (P x ==> Q x)) ==> ((!x. P x) ==> (!x. Q x))``,
                        PROVE_TAC[])) THEN
GEN_TAC THEN
Cases_on `x IN FDOM st11` THEN Cases_on `x IN FDOM st12` THEN
Cases_on `x IN FDOM st21` THEN Cases_on `x IN FDOM st22` THEN
ASM_SIMP_TAC (std_ss++CONJ_ss) [VAR_RES_STACK_COMBINE___MERGE_FUNC_def,
   var_res_permission_THM2]);




val ASL_PROGRAM_IS_ABSTRACTION___var_res_prog_parallel_procedure_call = store_thm (
"ASL_PROGRAM_IS_ABSTRACTION___var_res_prog_parallel_procedure_call",
``!xenv penv arg1 arg2 name1 name2.
(IS_VAR_RES_COMBINATOR (FST xenv)) ==>  !qP1 qP2 qQ1 qQ2.
(!arg. ASL_PROGRAM_IS_ABSTRACTION xenv penv (
   asl_prog_procedure_call name1 arg)
   (var_res_prog_quant_best_local_action (qP1 arg) (qQ1 arg))) /\
(!arg. ASL_PROGRAM_IS_ABSTRACTION xenv penv (
   asl_prog_procedure_call name2 arg)
   (var_res_prog_quant_best_local_action (qP2 arg) (qQ2 arg))) ==>
ASL_PROGRAM_IS_ABSTRACTION xenv penv
       (var_res_prog_parallel_procedure_call name1 arg1 name2 arg2)
       (var_res_prog_eval_expressions (\constL1.
        var_res_prog_eval_expressions (\constL2.

           var_res_prog_quant_best_local_action
              (\ (arg1', arg2'). asl_star (FST xenv)
                                     (qP1 ((FST arg1), constL1) arg1')
                                     (qP2 ((FST arg2), constL2) arg2'))
              (\ (arg1', arg2'). asl_star (FST xenv)
                                     (qQ1 ((FST arg1), constL1) arg1')
                                     (qQ2 ((FST arg2), constL2) arg2')))

        (SND arg2)) (SND arg1))``,


REPEAT STRIP_TAC THEN
`IS_SEPARATION_COMBINATOR (FST xenv)` by PROVE_TAC[IS_SEPARATION_COMBINATOR___IS_VAR_RES_COMBINATOR] THEN
`?ref1 expL1. arg1 = (ref1, expL1)` by (Cases_on `arg1` THEN SIMP_TAC std_ss []) THEN
`?ref2 expL2. arg2 = (ref2, expL2)` by (Cases_on `arg2` THEN SIMP_TAC std_ss []) THEN
ASM_SIMP_TAC std_ss [var_res_prog_parallel_procedure_call_THM] THEN
MATCH_MP_TAC ASL_PROGRAM_IS_ABSTRACTION___var_res_prog_eval_expressions THEN
ASM_SIMP_TAC std_ss [] THEN GEN_TAC THEN
MATCH_MP_TAC ASL_PROGRAM_IS_ABSTRACTION___var_res_prog_eval_expressions THEN
ASM_SIMP_TAC std_ss [] THEN GEN_TAC THEN

Q.PAT_ASSUM `!arg. ASL_PROGRAM_IS_ABSTRACTION xenv penv
                   (asl_prog_procedure_call name1 arg) prog'`
             (MP_TAC o Q.SPEC `(ref1, constL)`) THEN
Q.PAT_ASSUM `!arg. ASL_PROGRAM_IS_ABSTRACTION xenv penv
                   (asl_prog_procedure_call name2 arg) prog'`
             (MP_TAC o Q.SPEC `(ref2, constL')`) THEN

SIMP_TAC std_ss [var_res_prog_quant_best_local_action_def] THEN
Q.MATCH_ABBREV_TAC `
ASL_PROGRAM_IS_ABSTRACTION xenv penv p2
   (asl_prog_quant_best_local_action qP2' qQ2') ==>
ASL_PROGRAM_IS_ABSTRACTION xenv penv p1
   (asl_prog_quant_best_local_action qP1' qQ1') ==>
ASL_PROGRAM_IS_ABSTRACTION xenv penv
   (asl_prog_parallel p1 p2) prog'` THEN


REPEAT STRIP_TAC THEN
Tactical.REVERSE (`
   ASL_PROGRAM_IS_ABSTRACTION xenv penv
   (asl_prog_quant_best_local_action
              (\ (a1,a2). asl_star (FST xenv) (qP1' a1) (qP2' a2))
              (\ (a1,a2). asl_star (FST xenv) (qQ1' a1) (qQ2' a2))) prog'`
   by ALL_TAC) THEN1 (

   POP_ASSUM MP_TAC THEN
   MATCH_MP_TAC ASL_PROGRAM_IS_ABSTRACTION___TRANSITIVE THEN
   ASM_SIMP_TAC std_ss [] THEN
   MATCH_MP_TAC ASL_PROGRAM_IS_ABSTRACTION___parallel THEN
   ASM_SIMP_TAC std_ss []
) THEN


UNABBREV_ALL_TAC THEN
REPEAT (Q.PAT_ASSUM `ASL_PROGRAM_IS_ABSTRACTION x y z zz` (K ALL_TAC)) THEN

ASM_SIMP_TAC std_ss [ASL_PROGRAM_IS_ABSTRACTION___quant_best_local_action,
   ASL_PROGRAM_HOARE_TRIPLE_def, HOARE_TRIPLE_def,
   IN_ABS] THEN
GEN_TAC THEN
`?a1 a2 s. x = ((a1,a2),s)` by ALL_TAC THEN1 (
    Cases_on `x` THEN Cases_on `q` THEN
    SIMP_TAC std_ss []
) THEN
`?f lock_env. xenv = (VAR_RES_COMBINATOR f, lock_env)` by ALL_TAC THEN1 (
   Cases_on `xenv` THEN
   FULL_SIMP_TAC std_ss [IS_VAR_RES_COMBINATOR_def] THEN
   PROVE_TAC[]
) THEN
FULL_SIMP_TAC std_ss [
   fasl_order_THM2,
   asl_prog_quant_best_local_action_def,
   ASL_PROGRAM_SEM___prim_command,
   ASL_ATOMIC_ACTION_SEM_def,
   EVAL_asl_prim_command_THM,
   quant_best_local_action_THM] THEN

SIMP_TAC std_ss [SUBSET_DEF, SOME___quant_best_local_action,
   IN_ABS, asl_star_def, IN_ABS, IN_SING] THEN
STRIP_TAC THEN
`?uff. IS_SEPARATION_COMBINATOR_NEUTRAL_ELEMENT_FUNCTION (VAR_RES_COMBINATOR f) uff` by
  PROVE_TAC [IS_SEPARATION_COMBINATOR_HALF_EXPAND_THM] THEN
POP_ASSUM MP_TAC THEN ASM_SIMP_TAC std_ss [IS_SEPARATION_COMBINATOR_NEUTRAL_ELEMENT_FUNCTION_THM] THEN
STRIP_TAC THEN
CONJ_TAC THEN1 (
   Q.EXISTS_TAC `((a1, p), (a2, q))` THEN
   Q.EXISTS_TAC `uff s` THEN
   Q.EXISTS_TAC `s` THEN
   ASM_SIMP_TAC std_ss [IN_ABS]
) THEN
SIMP_TAC std_ss [FUN_EQ_THM] THEN
CONV_TAC (DEPTH_CONV pairLib.GEN_BETA_CONV) THEN
SIMP_TAC std_ss [IN_ABS, GSYM LEFT_EXISTS_IMP_THM] THEN

GEN_TAC THEN
Q.EXISTS_TAC `((a1,p),(a2,q))` THEN
Q.EXISTS_TAC `uff s` THEN
Q.EXISTS_TAC `s` THEN

ASM_SIMP_TAC std_ss [] THEN
REPEAT STRIP_TAC THEN1 (
   Q.EXISTS_TAC `p''` THEN
   Q.EXISTS_TAC `q'` THEN
   ASM_SIMP_TAC std_ss []
) THEN


MATCH_MP_TAC VAR_RES_STACK___IS_EQUAL_UPTO_VALUES___VAR_RES_STACK_COMBINE THEN
Q.EXISTS_TAC `FST p` THEN
Q.EXISTS_TAC `FST q` THEN
Q.EXISTS_TAC `FST p''` THEN
Q.EXISTS_TAC `FST q'` THEN

FULL_SIMP_TAC std_ss [VAR_RES_COMBINATOR_REWRITE]);






val VAR_RES_COND_INFERENCE___eval_expressions___NIL =
store_thm ("VAR_RES_COND_INFERENCE___eval_expressions___NIL",
``!f P prog progL Q.
(VAR_RES_COND_HOARE_TRIPLE f P
    (asl_prog_block ((var_res_prog_eval_expressions prog [])::progL)) Q =
 VAR_RES_COND_HOARE_TRIPLE f P (asl_prog_block ((prog [])::progL)) Q)``,

SIMP_TAC std_ss [VAR_RES_COND_INFERENCE___prog_block] THEN
SIMP_TAC list_ss [var_res_prog_eval_expressions_def,
   VAR_RES_COND_HOARE_TRIPLE_def, VAR_RES_HOARE_TRIPLE_def,
   ASL_INFERENCE___choose_constants___NIL,
   IS_SEPARATION_COMBINATOR___VAR_RES_COMBINATOR]);



val VAR_RES_COND_INFERENCE___eval_expressions___ONE =
store_thm ("VAR_RES_COND_INFERENCE___eval_expressions___ONE",
``!f wpb rpb sfb e L c prog progL Q.
BAG_IN (var_res_prop_equal f e (var_res_exp_const c)) sfb  ==>

(VAR_RES_COND_HOARE_TRIPLE f (var_res_prop f (wpb,rpb) sfb)
   (asl_prog_block ((var_res_prog_eval_expressions prog (e::L))::progL)) Q =
 VAR_RES_COND_HOARE_TRIPLE f (var_res_prop f (wpb,rpb) sfb)
   (asl_prog_block ((var_res_prog_eval_expressions (\L. prog (c::L)) L)::progL)) Q)``,

SIMP_TAC std_ss [VAR_RES_COND_INFERENCE___prog_block] THEN
SIMP_TAC std_ss [VAR_RES_COND_HOARE_TRIPLE_def, VAR_RES_HOARE_TRIPLE_def,
   var_res_prop___REWRITE, var_res_prog_eval_expressions_def] THEN
SIMP_TAC (list_ss++EQUIV_EXTRACT_ss) [] THEN
REPEAT STRIP_TAC THEN
CONSEQ_CONV_TAC (K FORALL_EQ___CONSEQ_CONV) THEN
GEN_TAC THEN
HO_MATCH_MP_TAC ASL_INFERENCE___choose_constants___ONE THEN
ASM_SIMP_TAC std_ss [IN_ABS, IS_SEPARATION_COMBINATOR___VAR_RES_COMBINATOR] THEN

`?sfb'. sfb =  BAG_INSERT (var_res_prop_equal f e (var_res_exp_const c)) sfb'` by
  PROVE_TAC[BAG_DECOMPOSE] THEN
FULL_SIMP_TAC std_ss [BAG_IN_BAG_INSERT, IN_ABS,
   var_res_prop___COND_INSERT, IN_SET_OF_BAG, var_res_prop___PROP_INSERT] THEN
Q.PAT_ASSUM `VAR_RES_IS_STACK_IMPRECISE___USED_VARS X Y` MP_TAC THEN
FULL_SIMP_TAC std_ss [IS_SEPARATION_COMBINATOR_EXPAND_THM] THEN
ASM_SIMP_TAC std_ss [
   VAR_RES_IS_STACK_IMPRECISE___USED_VARS_def,
   VAR_RES_IS_STACK_IMPRECISE_def,
   var_res_prop_equal_def, var_res_prop_binexpression_def,
   var_res_stack_proposition_def, IN_ABS, var_res_exp_const_def,
   IN_SET_OF_BAG, LET_THM, asl_emp_def, GSYM RIGHT_EXISTS_AND_THM,
   GSYM LEFT_EXISTS_AND_THM, VAR_RES_STACK_IS_SUBSTATE_def,
   ASL_IS_SUBSTATE___PRODUCT_SEPARATION_COMBINATOR,
   VAR_RES_COMBINATOR_def] THEN
SIMP_TAC (std_ss++CONJ_ss) [
   PAIR_FORALL_THM, PAIR_EXISTS_THM,
   GSYM LEFT_FORALL_IMP_THM, IS_SOME_EXISTS,
   GSYM LEFT_EXISTS_AND_THM, GSYM RIGHT_EXISTS_AND_THM] THEN
REPEAT STRIP_TAC THEN
METIS_TAC[]);





val VAR_RES_COND_INFERENCE___eval_expressions___LIST =
store_thm ("VAR_RES_COND_INFERENCE___eval_expressions___LIST",
``!f wpb rpb sfb eL cL prog progL Q L.
(LENGTH cL = LENGTH eL) /\
EVERY (\ (e,c). BAG_IN (var_res_prop_equal f e (var_res_exp_const c)) sfb) (ZIP (eL,cL))  ==>

(VAR_RES_COND_HOARE_TRIPLE f (var_res_prop f (wpb,rpb) sfb)
   (asl_prog_block ((var_res_prog_eval_expressions prog (eL++L))::progL)) Q =
 VAR_RES_COND_HOARE_TRIPLE f (var_res_prop f (wpb,rpb) sfb)
   (asl_prog_block ((var_res_prog_eval_expressions (\L. prog (cL++L)) L)::progL)) Q)``,


Induct_on `eL` THEN1 (
   SIMP_TAC list_ss [LENGTH_NIL, ETA_THM]
) THEN
REPEAT STRIP_TAC THEN
Cases_on `cL` THEN FULL_SIMP_TAC list_ss [] THEN
SIMP_TAC list_ss [] THEN
MP_TAC (Q.SPECL [`f`, `wpb`, `rpb`, `sfb`, `h`, `eL++L`, `h'`, `prog`, `progL`, `Q`]
  VAR_RES_COND_INFERENCE___eval_expressions___ONE
) THEN
ASM_SIMP_TAC std_ss [] THEN ASM_REWRITE_TAC[] THEN
SIMP_TAC std_ss [] THEN
DISCH_TAC THEN (POP_ASSUM (K ALL_TAC)) THEN

Q.PAT_ASSUM `!f wpb rpb. X` (MP_TAC o Q.SPECL [`f`,` wpb`, `rpb`, `sfb`, `t`]) THEN
ASM_REWRITE_TAC[] THEN
SIMP_TAC std_ss []);




val VAR_RES_COND_INFERENCE___eval_expressions =
store_thm ("VAR_RES_COND_INFERENCE___eval_expressions",
``!f wpb rpb sfb eL cL prog progL Q.
(LENGTH cL = LENGTH eL) /\
EVERY (\ (e,c). BAG_IN (var_res_prop_equal f e (var_res_exp_const c)) sfb) (ZIP (eL,cL))  ==>

(VAR_RES_COND_HOARE_TRIPLE f (var_res_prop f (wpb,rpb) sfb)
   (asl_prog_block ((var_res_prog_eval_expressions prog eL)::progL)) Q =
 VAR_RES_COND_HOARE_TRIPLE f (var_res_prop f (wpb,rpb) sfb)
   (asl_prog_block ((prog cL)::progL)) Q)``,


REPEAT STRIP_TAC THEN
MP_TAC (Q.SPECL [`f`, `wpb`, `rpb`, `sfb`, `eL`, `cL`, `prog`, `progL`, `Q`, `[]`] VAR_RES_COND_INFERENCE___eval_expressions___LIST) THEN
ASM_SIMP_TAC list_ss [VAR_RES_COND_INFERENCE___eval_expressions___NIL]);



(*******************************************************
 * locks
 ******************************************************)

val var_res_prog_aquire_lock_input_def = Define `
var_res_prog_aquire_lock_input f c wp P =
asl_prog_aquire_lock c (var_res_lock_invariant f wp P)`

val var_res_prog_release_lock_input_def = Define `
var_res_prog_release_lock_input f wp P =
asl_prog_release_lock (var_res_lock_invariant f wp P)`;


val ASL_PROGRAM_IS_ABSTRACTION___asl_prog_cond_critical_section___lock_decls_env = store_thm (
   "ASL_PROGRAM_IS_ABSTRACTION___asl_prog_cond_critical_section___lock_decls_env",
``!f f' lock_decls penv l c prog wpL P.
 (IS_VAR_RES_COMBINATOR f') /\ (GET_VAR_RES_COMBINATOR f' = f) /\
 (ALL_DISTINCT (MAP FST lock_decls) /\ MEM (l,wpL,P) lock_decls) ==>

 ASL_PROGRAM_IS_ABSTRACTION (f',LIST_TO_FUN (VAR_RES_LOCK_ENV_MAP f lock_decls)) penv
      (asl_prog_cond_critical_section l c prog)
      (asl_prog_block
         [var_res_prog_aquire_lock_input f c (LIST_TO_SET wpL) P;
          prog;
          var_res_prog_release_lock_input f (LIST_TO_SET wpL) P])``,

SIMP_TAC (std_ss++CONJ_ss) [IS_VAR_RES_COMBINATOR_def, GET_VAR_RES_COMBINATOR_THM,
   GSYM LEFT_EXISTS_AND_THM, GSYM RIGHT_EXISTS_AND_THM, GSYM LEFT_FORALL_IMP_THM] THEN
REPEAT STRIP_TAC THEN
REWRITE_TAC [var_res_prog_release_lock_input_def,
             var_res_prog_aquire_lock_input_def] THEN
MATCH_MP_TAC ASL_PROGRAM_IS_ABSTRACTION___asl_prog_cond_critical_section THEN
ASM_SIMP_TAC std_ss [IS_SEPARATION_COMBINATOR___VAR_RES_COMBINATOR,
   VAR_RES_LOCK_ENV_MAP_def] THEN
MATCH_MP_TAC EQ_SYM THEN
MATCH_MP_TAC (
   SIMP_RULE std_ss [PAIR_FORALL_THM] LIST_TO_FUN_DISTINCT_THM) THEN
ASM_SIMP_TAC list_ss [MEM_MAP, PAIR_EXISTS_THM, MAP_MAP_o,
   combinTheory.o_DEF, ETA_THM] THEN
PROVE_TAC[]);




val var_res_prog_aquire_lock_internal_def =
Define `var_res_prog_aquire_lock_internal f c wp P =
  if (~FST P) then asl_prog_diverge else
    var_res_prog_aquire_lock_input f c wp (SND P)`

val var_res_prog_aquire_lock_def =
Define `var_res_prog_aquire_lock f c wpb sfb =
        var_res_prog_aquire_lock_internal f c (SET_OF_BAG wpb)
           (var_res_prop f (wpb,EMPTY_BAG) sfb)`;


val var_res_prog_release_lock_internal_def =
Define `var_res_prog_release_lock_internal f wp P =
  if (~FST P) then asl_prog_diverge else
    var_res_prog_release_lock_input f wp (SND P)`;

val var_res_prog_release_lock_def =
Define `var_res_prog_release_lock f wpb sfb =
        var_res_prog_release_lock_internal f (SET_OF_BAG wpb)
           (var_res_prop f (wpb,EMPTY_BAG) sfb)`;



val var_res_lock_invariant___prop_input = store_thm (
"var_res_lock_invariant___prop_input",
``IS_SEPARATION_COMBINATOR f ==>
  (var_res_lock_invariant f wp (var_res_prop_input_ap f (wp,{}) P) =
   var_res_lock_invariant f wp P)``,

ONCE_REWRITE_TAC[EXTENSION] THEN
SIMP_TAC (std_ss++EQUIV_EXTRACT_ss) [var_res_lock_invariant_def, IN_ABS,
   var_res_prop_input_ap_def, var_res_prop_input_ap_distinct_def,
   asl_bool_REWRITES, ALL_DISTINCT,
   var_res_prop_internal___PROP_def, NOT_IN_EMPTY_BAG,
   var_res_sl___has_write_permission_def, NOT_IN_EMPTY] THEN
REPEAT STRIP_TAC THEN
ASM_SIMP_TAC list_ss [var_res_bigstar_REWRITE] THEN
Q.HO_MATCH_ABBREV_TAC `x IN asl_star f' Q
              (\s. perm s /\ s IN P'') = x IN P'` THEN
`P'' = P'` by ALL_TAC THEN1 (
   MAP_EVERY Q.UNABBREV_TAC [`P''`, `P'`, `f'`] THEN
   METIS_TAC[IS_SEPARATION_COMBINATOR___VAR_RES_COMBINATOR,
      asl_star___PROPERTIES, COMM_DEF]
) THEN
Tactical.REVERSE (
`x IN asl_star f' Q (\s. perm s /\ s IN P') =
 x IN asl_star f' Q P'` by ALL_TAC) THEN1 (
   ASM_SIMP_TAC std_ss [] THEN
   UNABBREV_ALL_TAC THEN
   ASM_SIMP_TAC std_ss [asl_star___var_res_prop_stack_true___IDEM_2]
) THEN

UNABBREV_ALL_TAC THEN
ASM_SIMP_TAC std_ss [asl_star___var_res_prop_stack_true___IDEM_2] THEN
Q.ABBREV_TAC `P' = asl_star (VAR_RES_COMBINATOR f) (var_res_prop_stack_true f) P` THEN
EQ_TAC THENL [
   REPEAT STRIP_TAC THEN
   Tactical.REVERSE (`x IN
          asl_star (VAR_RES_COMBINATOR f) (var_res_prop_stack_true f) P'` by ALL_TAC) THEN1 (
      POP_ASSUM MP_TAC THEN
      Q.UNABBREV_TAC `P'` THEN
      ASM_SIMP_TAC std_ss [asl_star___var_res_prop_stack_true___IDEM_2]
   ) THEN
   FULL_SIMP_TAC std_ss [asl_star_def, IN_ABS] THEN
   METIS_TAC[],

   SIMP_TAC std_ss [asl_star_def, IN_ABS, VAR_RES_COMBINATOR_REWRITE,
      PAIR_EXISTS_THM] THEN
   FULL_SIMP_TAC std_ss [IS_SEPARATION_COMBINATOR_EXPAND_THM,
      var_res_prop_stack_true_def, var_res_bool_proposition_REWRITE,
      IN_ABS, asl_emp_def, GSYM RIGHT_EXISTS_AND_THM,
      GSYM LEFT_EXISTS_AND_THM] THEN
   QUANT_INSTANTIATE_TAC [] THEN
   REPEAT STRIP_TAC THEN
   Q.EXISTS_TAC `FEMPTY` THEN
   ASM_SIMP_TAC std_ss [VAR_RES_STACK_COMBINE_REWRITE]
]);


val var_res_lock_invariant___var_res_prop =
store_thm ("var_res_lock_invariant___var_res_prop",
``!f wpb sfb. IS_SEPARATION_COMBINATOR f ==>
  (var_res_lock_invariant f (SET_OF_BAG wpb)
         (var_res_prop___PROP f (wpb,{||}) sfb) =
    var_res_lock_invariant f (SET_OF_BAG wpb)
  (var_res_bigstar f sfb))``,

REPEAT STRIP_TAC THEN
`(var_res_prop___PROP f (wpb,{||}) sfb) =
var_res_prop_input_ap f (SET_OF_BAG wpb,EMPTY)
   (var_res_bigstar f sfb)` by ALL_TAC THEN1 (
   ASM_SIMP_TAC list_ss [var_res_prop_input_ap_def,
      var_res_prop_input_ap_distinct_def,
      var_res_prop___PROP___REWRITE, NOT_IN_EMPTY_BAG,
      ALL_DISTINCT, asl_bool_REWRITES,
      var_res_prop_internal___PROP_def,
      NOT_IN_EMPTY, IS_SEPARATION_COMBINATOR___VAR_RES_COMBINATOR,
      IN_SET_OF_BAG, var_res_bigstar_REWRITE_EXT]
) THEN
ASM_SIMP_TAC std_ss [var_res_lock_invariant___prop_input]);



val var_res_prog_aquire_release_lock_input___REWRITE =
store_thm ("var_res_prog_aquire_release_lock_input___REWRITE",
``!f c wp P.
 IS_SEPARATION_COMBINATOR f ==>

 ((var_res_prog_aquire_lock_input f c wp P) =
    (var_res_prog_aquire_lock_internal f c wp
        (var_res_prop_input f (wp, EMPTY) P))) /\
    ((var_res_prog_release_lock_input f wp P) =
     (var_res_prog_release_lock_internal f wp
        (var_res_prop_input f (wp, EMPTY) P)))``,

SIMP_TAC std_ss [var_res_prog_release_lock_internal_def,
   var_res_prog_aquire_lock_internal_def,
   var_res_prop_input_def, var_res_prop_input_distinct_def,
   ALL_DISTINCT] THEN
SIMP_TAC std_ss [var_res_prog_aquire_lock_input_def,
   var_res_lock_invariant___prop_input, GSYM var_res_prop_input_ap_def,
   var_res_prog_release_lock_input_def]);


val ASL_PROGRAM_IS_ABSTRACTION___asl_prog_cond_critical_section___lock_decls_env___INTERNAL = store_thm (
   "ASL_PROGRAM_IS_ABSTRACTION___asl_prog_cond_critical_section___lock_decls_env___INTERNAL",

``!f f' lock_decls penv l c prog wpL P.
 (IS_VAR_RES_COMBINATOR f') /\ (GET_VAR_RES_COMBINATOR f' = f) ==>
 (ALL_DISTINCT (MAP FST lock_decls) /\ MEM (l,wpL,P) lock_decls) ==>

 ASL_PROGRAM_IS_ABSTRACTION (f',LIST_TO_FUN (VAR_RES_LOCK_ENV_MAP f lock_decls)) penv
      (asl_prog_cond_critical_section l c prog)
      (asl_prog_block
         [var_res_prog_aquire_lock_internal f c (LIST_TO_SET wpL)
          (var_res_prop_input f ((LIST_TO_SET wpL),{}) P);
          prog;
          var_res_prog_release_lock_internal f (LIST_TO_SET wpL)
          (var_res_prop_input f ((LIST_TO_SET wpL),{}) P)])``,

REPEAT STRIP_TAC THEN
`IS_SEPARATION_COMBINATOR f` by ALL_TAC THEN1 (
   FULL_SIMP_TAC std_ss [IS_VAR_RES_COMBINATOR_def] THEN
   `f = f''` by METIS_TAC[GET_VAR_RES_COMBINATOR_THM] THEN
   ASM_REWRITE_TAC[]
) THEN
METIS_TAC[var_res_prog_aquire_release_lock_input___REWRITE,
   ASL_PROGRAM_IS_ABSTRACTION___asl_prog_cond_critical_section___lock_decls_env]);


val var_res_prog_aquire_lock___INTRO =
store_thm ("var_res_prog_aquire_lock___INTRO",
``!f c wpb wp sfb.
     (SET_OF_BAG wpb = wp) ==>
     ((var_res_prog_aquire_lock_internal f c wp
         (var_res_prop f (wpb, EMPTY_BAG) sfb)) =
     (var_res_prog_aquire_lock f c wpb sfb))``,
SIMP_TAC std_ss [var_res_prog_aquire_lock_def]);


val var_res_prog_release_lock___INTRO =
store_thm ("var_res_prog_release_lock___INTRO",
``!f wpb wp sfb.
     (SET_OF_BAG wpb = wp) ==>
     ((var_res_prog_release_lock_internal f wp
         (var_res_prop f (wpb, EMPTY_BAG) sfb)) =
     (var_res_prog_release_lock f wpb sfb)) ``,
SIMP_TAC std_ss [var_res_prog_release_lock_def]);


val ASL_PROGRAM_IS_ABSTRACTION___var_res_prog_aquire_lock =
store_thm ("ASL_PROGRAM_IS_ABSTRACTION___var_res_prog_aquire_lock",
``!f lenv penv c wpb sfb.
IS_SEPARATION_COMBINATOR f ==>
ASL_PROGRAM_IS_ABSTRACTION (VAR_RES_COMBINATOR f, lenv) penv
     (var_res_prog_aquire_lock f c wpb sfb)
     (asl_prog_seq
        (var_res_prog_cond_best_local_action
            (var_res_prop f (EMPTY_BAG, EMPTY_BAG) EMPTY_BAG)
            (var_res_prop f (wpb, EMPTY_BAG) sfb))
        (asl_prog_assume c))``,

SIMP_TAC std_ss [
   var_res_prog_cond_best_local_action_REWRITE,
   var_res_prog_aquire_lock_def,
   asl_prog_aquire_lock_def,
   GSYM asl_prog_assume_def,
   var_res_prog_aquire_lock_internal_def,
   var_res_prog_aquire_lock_input_def,
   var_res_prop___REWRITE] THEN
REPEAT STRIP_TAC THEN
Cases_on `var_res_prop___COND f (wpb,{||}) sfb` THEN (
   ASM_SIMP_TAC std_ss [ASL_PROGRAM_IS_ABSTRACTION___diverge]
) THEN
MATCH_MP_TAC ASL_PROGRAM_IS_ABSTRACTION___seq THEN
ASM_REWRITE_TAC [ASL_PROGRAM_IS_ABSTRACTION___REFL] THEN
ASM_SIMP_TAC std_ss [ASL_PROGRAM_IS_ABSTRACTION_def,
   ASL_PROGRAM_SEM___prim_command,
   ASL_ATOMIC_ACTION_SEM_def,
   EVAL_asl_prim_command_THM,
   ASL_IS_LOCAL_ACTION___materialisation_annihilation,
   IS_SEPARATION_COMBINATOR___VAR_RES_COMBINATOR,
   ASL_IS_LOCAL_ACTION___var_res_cond_best_local_action] THEN
ASM_SIMP_TAC std_ss [
   IS_SEPARATION_COMBINATOR___VAR_RES_COMBINATOR,
   var_res_cond_best_local_action_def,
   var_res_best_local_action_def,
   var_res_prop___COND___REWRITE, FINITE_BAG_THM,
   NOT_IN_EMPTY_BAG, BAG_UNION_EMPTY, BAG_ALL_DISTINCT_THM,
   var_res_lock_invariant___var_res_prop] THEN

MATCH_MP_TAC fasl_action_order____quant_best_local_action THEN

ASM_SIMP_TAC std_ss [IS_SEPARATION_COMBINATOR___VAR_RES_COMBINATOR,
   HOARE_TRIPLE_def, ASL_IS_LOCAL_ACTION___materialisation_annihilation,
   IN_ABS, fasl_order_THM2] THEN
ASM_SIMP_TAC std_ss [asla_materialisation_THM,
   IS_SEPARATION_COMBINATOR___VAR_RES_COMBINATOR,
   var_res_prop___PROP___REWRITE, NOT_IN_EMPTY_BAG,
   var_res_bigstar_REWRITE_EXT,
   IN_ABS, SUBSET_DEF] THEN
REPEAT (GEN_TAC ORELSE DISCH_TAC) THEN
Q.PAT_ASSUM `x' IN X` MP_TAC THEN
SIMP_TAC std_ss [asl_star_def] THEN
ASM_SIMP_TAC std_ss [IN_SING, IN_ABS,
   var_res_lock_invariant_def, IN_SET_OF_BAG,
   VAR_RES_COMBINATOR_REWRITE,
   SOME___VAR_RES_STACK_COMBINE,
   var_res_bigstar___var_res_prop_stack_true___asl_star_ELIM] THEN
STRIP_TAC THEN
`SND p = SND x'` by ALL_TAC THEN1 (
   Q.PAT_ASSUM `f (SOME X) (SOME Y) = (SOME Z)` MP_TAC THEN
   Q.PAT_ASSUM `x IN Z` MP_TAC THEN
   FULL_SIMP_TAC std_ss [IS_SEPARATION_COMBINATOR_EXPAND_THM,
      var_res_prop_stack_true_def, var_res_bool_proposition_REWRITE,
      IN_ABS, asl_emp_def, GSYM LEFT_FORALL_IMP_THM]
) THEN
`!v. BAG_IN v wpb ==> ~(v IN FDOM (FST x))` by ALL_TAC THEN1 (
   FULL_SIMP_TAC std_ss [VAR_RES_STACK_IS_SEPARATE_def,
      IN_SET_OF_BAG, var_res_permission_THM2] THEN
   METIS_TAC[]
) THEN
REPEAT STRIP_TAC THENL [
   ASM_SIMP_TAC std_ss [var_res_sl___has_write_permission_def,
      FMERGE_DEF, IN_UNION, IN_SET_OF_BAG],


   `VAR_RES_IS_STACK_IMPRECISE (var_res_bigstar f sfb)` by ALL_TAC THEN1 (
      FULL_SIMP_TAC std_ss [var_res_prop___COND___EXPAND,
         VAR_RES_IS_STACK_IMPRECISE___USED_VARS_def]
   ) THEN
   FULL_SIMP_TAC std_ss [VAR_RES_IS_STACK_IMPRECISE___ALTERNATIVE_DEF_2] THEN
   POP_ASSUM MATCH_MP_TAC  THEN
   Q.EXISTS_TAC `p` THEN
   ASM_SIMP_TAC std_ss [SUBSET_DEF, IN_SET_OF_BAG,
      FMERGE_DEF, IN_UNION],


   ASM_SIMP_TAC std_ss [VAR_RES_STACK___IS_EQUAL_UPTO_VALUES_def,
      FMERGE_DEF, IN_UNION, IN_SET_OF_BAG] THEN
   METIS_TAC[]
]);


val VAR_RES_COND_INFERENCE___var_res_prog_aquire_lock = store_thm (
"VAR_RES_COND_INFERENCE___var_res_prog_aquire_lock",
``!f wpb rpb sfb wpb' c sfb' progL Q.
   IS_SEPARATION_COMBINATOR f ==>

((VAR_RES_COND_HOARE_TRIPLE f
    (var_res_prop f (BAG_UNION wpb wpb',rpb) (BAG_UNION sfb' sfb))
    (asl_prog_block (
        (asl_prog_assume c)::
        progL))
    Q) ==>

  VAR_RES_COND_HOARE_TRIPLE f
    (var_res_prop f (wpb,rpb) sfb)
    (asl_prog_block (
        (var_res_prog_aquire_lock f c wpb' sfb')::
        progL))
    Q)``,


REPEAT STRIP_TAC THEN
Tactical.REVERSE (Cases_on `var_res_prop___COND f (wpb,rpb) sfb`) THEN1 (
   ASM_SIMP_TAC std_ss [VAR_RES_COND_HOARE_TRIPLE_def,
      var_res_prop___REWRITE]
) THEN
SIMP_TAC std_ss [VAR_RES_COND_INFERENCE___prog_block] THEN
MATCH_MP_TAC VAR_RES_COND_HOARE_TRIPLE___PROGRAM_ABSTRACTION_first THEN
Q.EXISTS_TAC `asl_prog_seq
        (var_res_prog_cond_best_local_action
            (var_res_prop f (EMPTY_BAG, EMPTY_BAG) EMPTY_BAG)
            (var_res_prop f (wpb', EMPTY_BAG) sfb')) (asl_prog_assume c)` THEN
ASM_SIMP_TAC std_ss [VAR_RES_PROGRAM_IS_ABSTRACTION_def,
   ASL_PROGRAM_IS_ABSTRACTION___var_res_prog_aquire_lock,
   GSYM VAR_RES_COND_INFERENCE___prog_block,
   VAR_RES_COND_INFERENCE___prog_block2] THEN
MATCH_MP_TAC (MP_CANON VAR_RES_COND_INFERENCE___var_res_prog_cond_best_local_action___VAR_CHANGE) THEN
Q.EXISTS_TAC `rfc` THEN
ASM_SIMP_TAC std_ss [BAG_OF_EMPTY, EMPTY_SUBSET] THEN
MATCH_MP_TAC (MP_CANON VAR_RES_FRAME_SPLIT___SOLVE) THEN
FULL_SIMP_TAC std_ss [BAG_DIFF_EMPTY,
   var_res_prop___COND___EXPAND, BAG_EVERY]);



val ASL_PROGRAM_IS_ABSTRACTION___var_res_prog_release_lock =
store_thm ("ASL_PROGRAM_IS_ABSTRACTION___var_res_prog_release_lock",
``!f lenv penv wpb sfb.
IS_SEPARATION_COMBINATOR f ==>
ASL_PROGRAM_IS_ABSTRACTION (VAR_RES_COMBINATOR f, lenv) penv
     (var_res_prog_release_lock f wpb sfb)
     (var_res_prog_cond_best_local_action
         (var_res_prop f (wpb, EMPTY_BAG) sfb)
         (var_res_prop f (EMPTY_BAG, EMPTY_BAG) EMPTY_BAG))``,

ASM_SIMP_TAC std_ss [
   var_res_prog_cond_best_local_action_REWRITE,
   var_res_prog_release_lock_def,
   var_res_prog_release_lock_internal_def,
   var_res_prog_release_lock_input_def,
   asl_prog_release_lock_def,
   COND_RAND, COND_RATOR,
   ASL_PROGRAM_IS_ABSTRACTION_def,
   ASL_PROGRAM_SEM___prim_command,
   ASL_PROGRAM_SEM___diverge,
   ASL_ATOMIC_ACTION_SEM_def,
   EVAL_asl_prim_command_THM,
   ASL_IS_LOCAL_ACTION___materialisation_annihilation,
   IS_SEPARATION_COMBINATOR___VAR_RES_COMBINATOR,
   ASL_IS_LOCAL_ACTION___var_res_cond_best_local_action] THEN
REPEAT STRIP_TAC THEN
Cases_on `~FST (var_res_prop f (wpb,{||}) sfb)` THEN1 (
   ASM_SIMP_TAC std_ss [fasl_order_THM2, asla_diverge_def,
      EMPTY_SUBSET, fasl_action_order_POINTWISE_DEF]
) THEN
ASM_SIMP_TAC std_ss [] THEN STRIP_TAC THEN
`var_res_prop___COND f ({||}:'c -> num,{||}:'c -> num)
      ({||}:('d, 'c, 'a) var_res_proposition -> num)` by ALL_TAC THEN1 (
   ASM_SIMP_TAC std_ss [var_res_prop___COND___REWRITE,
      NOT_IN_EMPTY_BAG, FINITE_BAG_THM, BAG_UNION_EMPTY,
      BAG_ALL_DISTINCT_THM]
) THEN
FULL_SIMP_TAC list_ss [
   var_res_cond_best_local_action_def,
   var_res_prop___REWRITE, var_res_best_local_action_def] THEN

MATCH_MP_TAC fasl_action_order____quant_best_local_action THEN

ASM_SIMP_TAC std_ss [IS_SEPARATION_COMBINATOR___VAR_RES_COMBINATOR,
   ASL_IS_LOCAL_ACTION___materialisation_annihilation,
   HOARE_TRIPLE_def, IN_ABS, fasl_order_THM2,
   var_res_lock_invariant___var_res_prop,
   asla_annihilation_THM, SUBSET_DEF,
   COND_NONE_SOME_REWRITES] THEN

GEN_TAC THEN STRIP_TAC THEN
Tactical.REVERSE (`?s0 s1.
 s1 IN
 var_res_lock_invariant f (SET_OF_BAG wpb)
   (var_res_bigstar f sfb) /\
 (SOME x = VAR_RES_COMBINATOR f (SOME s0) (SOME s1)) /\
  s0 IN var_res_prop___PROP f ({||},{||}) {||} /\
  VAR_RES_STACK___IS_EQUAL_UPTO_VALUES (FST x) (FST s0)` by ALL_TAC) THEN1 (
   METIS_TAC[]
) THEN

`?uf. IS_SEPARATION_COMBINATOR_NEUTRAL_ELEMENT_FUNCTION f uf` by
   METIS_TAC[IS_SEPARATION_COMBINATOR_HALF_EXPAND_THM] THEN
POP_ASSUM MP_TAC THEN
ASM_SIMP_TAC std_ss [IS_SEPARATION_COMBINATOR_NEUTRAL_ELEMENT_FUNCTION_THM] THEN
STRIP_TAC THEN
Q.EXISTS_TAC `(DRESTRICT (FST x) (COMPL (SET_OF_BAG wpb)),
               uf (SND x))` THEN
Q.EXISTS_TAC `(DRESTRICT (FST x) (SET_OF_BAG wpb),
               SND x)` THEN
Q.PAT_ASSUM `x IN Y` MP_TAC THEN
FULL_SIMP_TAC std_ss [var_res_lock_invariant_def,
   IN_ABS, DRESTRICT_DEF, IN_SET_OF_BAG, EXTENSION,
   IN_INTER, var_res_prop___PROP___REWRITE,
   NOT_IN_EMPTY_BAG, VAR_RES_COMBINATOR_REWRITE,
   var_res_sl___has_write_permission_def,
   var_res_bigstar_REWRITE_EXT,
   var_res_prop_stack_true_REWRITE,
   asl_emp_def,
   VAR_RES_STACK___IS_EQUAL_UPTO_VALUES_def,
   IN_COMPL] THEN
STRIP_TAC THEN
SIMP_TAC (std_ss++EQUIV_EXTRACT_ss++CONJ_ss) [] THEN
REPEAT STRIP_TAC THENL [
   METIS_TAC[],

   `VAR_RES_IS_STACK_IMPRECISE___USED_VARS (SET_OF_BAG wpb) (var_res_bigstar f sfb)` by
       FULL_SIMP_TAC std_ss [var_res_prop___COND___EXPAND,
           BAG_UNION_EMPTY] THEN
   POP_ASSUM (MATCH_MP_TAC o REWRITE_RULE[VAR_RES_IS_STACK_IMPRECISE___USED_VARS___ALTERNATIVE_DEF]) THEN
   Q.EXISTS_TAC `x` THEN
   ASM_SIMP_TAC std_ss [DRESTRICT_DEF, SUBSET_REFL,
      IN_SET_OF_BAG, IN_INTER],

   SIMP_TAC (std_ss++CONJ_ss) [SOME___VAR_RES_STACK_COMBINE,
      FMERGE_DEF, VAR_RES_STACK_IS_SEPARATE_def,
      DRESTRICT_DEF, IN_COMPL, IN_INTER, GSYM fmap_EQ_THM] THEN
   SIMP_TAC std_ss [EXTENSION, IN_INTER, IN_UNION, IN_COMPL,
      IN_SET_OF_BAG] THEN
   METIS_TAC[],

   METIS_TAC[],
   METIS_TAC[]
]);


val VAR_RES_COND_INFERENCE___var_res_prog_release_lock = store_thm (
"VAR_RES_COND_INFERENCE___var_res_prog_release_lock",
``!rfc f wpb rpb sfb wpb' sfb' progL Q.
   IS_SEPARATION_COMBINATOR f /\
   ((SET_OF_BAG wpb') SUBSET (SET_OF_BAG wpb)) ==>

( VAR_RES_FRAME_SPLIT f rfc (wpb,rpb) wpb' EMPTY_BAG sfb sfb'
  (\sfb'''. VAR_RES_COND_HOARE_TRIPLE f
    (var_res_prop f ((BAG_DIFF wpb wpb'),rpb) sfb''')
       (asl_prog_block progL) Q) ==>

  VAR_RES_COND_HOARE_TRIPLE f
    (var_res_prop f (wpb,rpb) sfb)
    (asl_prog_block (
        (var_res_prog_release_lock f wpb' sfb')::
        progL))
    Q)``,


REPEAT STRIP_TAC THEN
SIMP_TAC std_ss [VAR_RES_COND_INFERENCE___prog_block] THEN
MATCH_MP_TAC VAR_RES_COND_HOARE_TRIPLE___PROGRAM_ABSTRACTION_first THEN
Q.EXISTS_TAC `var_res_prog_cond_best_local_action
   (var_res_prop f (wpb', EMPTY_BAG) sfb')
   (var_res_prop f (EMPTY_BAG, EMPTY_BAG) EMPTY_BAG)` THEN
ASM_SIMP_TAC std_ss [VAR_RES_PROGRAM_IS_ABSTRACTION_def,
   ASL_PROGRAM_IS_ABSTRACTION___var_res_prog_release_lock,
   GSYM VAR_RES_COND_INFERENCE___prog_block] THEN
MATCH_MP_TAC (MP_CANON VAR_RES_COND_INFERENCE___var_res_prog_cond_best_local_action___VAR_CHANGE) THEN
Q.EXISTS_TAC `rfc` THEN
ASM_SIMP_TAC std_ss [BAG_OF_EMPTY, EMPTY_SUBSET,
  BAG_UNION_EMPTY]);




(*******************************************************
 * assume, conditions, loops
 ******************************************************)


val VAR_RES_COND_INFERENCE___prog_cond =
store_thm ("VAR_RES_COND_INFERENCE___prog_cond",
``!f P c pTrue pFalse prog Q.
VAR_RES_COND_HOARE_TRIPLE f P
   (asl_prog_block ((asl_prog_assume c)::pTrue::prog)) Q /\
VAR_RES_COND_HOARE_TRIPLE f P
   (asl_prog_block ((asl_prog_assume (asl_pred_neg c))::pFalse::prog)) Q ==>
VAR_RES_COND_HOARE_TRIPLE f P (asl_prog_block ((asl_prog_cond c pTrue pFalse)::prog)) Q``,

SIMP_TAC std_ss [VAR_RES_COND_INFERENCE___prog_block] THEN
SIMP_TAC std_ss [VAR_RES_COND_HOARE_TRIPLE_def, VAR_RES_HOARE_TRIPLE_def] THEN
REPEAT STRIP_TAC THEN
FULL_SIMP_TAC std_ss [] THEN
MATCH_MP_TAC ASL_INFERENCE_prog_cond_seq THEN
FULL_SIMP_TAC std_ss [ASL_PROGRAM_HOARE_TRIPLE_def,
   ASL_PROGRAM_SEM___prog_block, ASL_PROGRAM_SEM___prog_seq]);


val VAR_RES_COND_INFERENCE___prog_cond_block =
store_thm ("VAR_RES_COND_INFERENCE___prog_cond_block",
``!f P c bTrue bFalse prog Q.
VAR_RES_COND_HOARE_TRIPLE f P
   (asl_prog_block ((asl_prog_assume c)::(bTrue++prog))) Q /\
VAR_RES_COND_HOARE_TRIPLE f P
   (asl_prog_block ((asl_prog_assume (asl_pred_neg c))::
        (bFalse++prog))) Q ==>
VAR_RES_COND_HOARE_TRIPLE f P (asl_prog_block ((asl_prog_cond c (asl_prog_block bTrue) (asl_prog_block bFalse))::prog)) Q``,

REPEAT STRIP_TAC THEN
MATCH_MP_TAC VAR_RES_COND_INFERENCE___prog_cond THEN
ASM_SIMP_TAC std_ss [VAR_RES_COND_INFERENCE___prog_block3]);


val VAR_RES_INFERENCE___prog_kleene_star = store_thm ("VAR_RES_INFERENCE___prog_kleene_star",
``!xenv penv P prog.
     VAR_RES_HOARE_TRIPLE xenv penv P prog P ==>
     VAR_RES_HOARE_TRIPLE xenv penv P (asl_prog_kleene_star prog) P``,

SIMP_TAC std_ss [VAR_RES_HOARE_TRIPLE_def,
   ASL_PROGRAM_HOARE_TRIPLE_def,
   ASL_PROGRAM_SEM___prog_kleene_star,
   HOARE_TRIPLE_def, IN_ABS, fasl_order_THM] THEN
SIMP_TAC std_ss [SUBSET_DEF,
   SOME___SUP_fasl_action_order, IN_IMAGE, IN_BIGUNION, IN_UNIV,
   GSYM RIGHT_EXISTS_AND_THM, GSYM LEFT_FORALL_IMP_THM, IN_ABS] THEN
REPEAT GEN_TAC THEN STRIP_TAC THEN
REPEAT GEN_TAC THEN STRIP_TAC THEN
HO_MATCH_MP_TAC (prove (``
   (!n. (X n) /\ (!x'. X n ==> Y x' n)) ==>
   ((!n. X n) /\ (!x' n. Y x' n))``, METIS_TAC[])) THEN
Induct_on `n` THEN1 (
   ASM_SIMP_TAC std_ss [ASL_PROGRAM_SEM___prog_repeat, asla_skip_def, IN_SING,
      VAR_RES_STACK___IS_EQUAL_UPTO_VALUES___REFL]
) THEN
FULL_SIMP_TAC std_ss [ASL_PROGRAM_SEM___prog_repeat___asla_repeat, IS_SOME_EXISTS,
   GSYM LEFT_FORALL_IMP_THM, asla_repeat___SYM_DEF] THEN
SIMP_TAC std_ss [SOME___asla_seq, GSYM LEFT_FORALL_IMP_THM,
  IN_BIGUNION, IN_IMAGE, GSYM RIGHT_EXISTS_AND_THM] THEN
CONJ_TAC THEN1 (
   Q.EXISTS_TAC `y` THEN
   METIS_TAC[option_CLAUSES]
) THEN
REPEAT GEN_TAC THEN STRIP_TAC THEN
GEN_TAC THEN STRIP_TAC THEN
`x'' IN P /\ VAR_RES_STACK___IS_EQUAL_UPTO_VALUES (FST x) (FST x'')` by METIS_TAC[] THEN
Q.PAT_ASSUM `!x. x IN P ==> X x` (MP_TAC o Q.SPEC `x''`) THEN
ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
FULL_SIMP_TAC std_ss [] THEN
METIS_TAC[VAR_RES_STACK___IS_EQUAL_UPTO_VALUES___TRANS]);



val VAR_RES_COND_INFERENCE___prog_while =
store_thm ("VAR_RES_COND_INFERENCE___prog_while",
``!f P wp rp d LI c pL prog Q.
(FST P ==> ALL_DISTINCT d) ==>
((!x. VAR_RES_COND_HOARE_TRIPLE f
        (var_res_prop_input_distinct f (wp,rp) d (LI x))
        (asl_prog_block ((asl_prog_assume c)::pL))
        (var_res_prop_input_distinct f (wp,rp) d (LI x))) /\

?x. VAR_RES_COND_HOARE_TRIPLE f P
   (asl_prog_block (
       (var_res_prog_cond_best_local_action
            (var_res_prop_input_distinct f (wp,rp) d (LI x))
            (var_res_prop_input_distinct f (wp,rp) d (LI x)))::
       (asl_prog_assume (asl_pred_neg c))::prog)) Q) ==>

VAR_RES_COND_HOARE_TRIPLE f P (asl_prog_block (
(asl_comment_loop_invariant (\x. var_res_prop_input_ap_distinct f (wp,rp) d (LI x))
   (asl_prog_while c (asl_prog_block pL)))::prog)) Q``,

REWRITE_TAC [asl_comment_loop_invariant_def,
  asl_prog_while_def, VAR_RES_COND_INFERENCE___prog_block2] THEN
REPEAT STRIP_TAC THEN

Tactical.REVERSE (Cases_on `IS_SEPARATION_COMBINATOR f /\ FST P`) THEN1 (
   FULL_SIMP_TAC std_ss [VAR_RES_COND_HOARE_TRIPLE_def]
) THEN
FULL_SIMP_TAC std_ss [VAR_RES_COND_INFERENCE___prog_block] THEN
MATCH_MP_TAC (MP_CANON VAR_RES_COND_HOARE_TRIPLE___PROGRAM_ABSTRACTION_first) THEN

Q.EXISTS_TAC `var_res_prog_cond_quant_best_local_action
                 (\x. var_res_prop_input_distinct f (wp,rp) d (LI x))
                 (\x. var_res_prop_input_distinct f (wp,rp) d (LI x))` THEN

ASM_REWRITE_TAC [GSYM asl_prog_assume_def] THEN
Tactical.REVERSE CONJ_TAC THEN1 (
   FULL_SIMP_TAC std_ss [GSYM VAR_RES_COND_INFERENCE___prog_block] THEN
   MATCH_MP_TAC VAR_RES_COND_INFERENCE___var_res_prog_cond_quant_best_local_action THEN
   Q.EXISTS_TAC `x` THEN
   ASM_SIMP_TAC std_ss []
) THEN

Q.PAT_ASSUM `!x. X` MP_TAC THEN
ASM_SIMP_TAC std_ss [VAR_RES_COND_HOARE_TRIPLE_def,
   var_res_prog_cond_quant_best_local_action_def,
   VAR_RES_PROGRAM_IS_ABSTRACTION_def,
   var_res_prop_input_distinct_def] THEN

Q.HO_MATCH_ABBREV_TAC `
   (!x. VAR_RES_HOARE_TRIPLE xenv FEMPTY (PP x) p (PP x)) ==>
   ASL_PROGRAM_IS_ABSTRACTION xenv FEMPTY
      (asl_prog_kleene_star p)
      (var_res_prog_quant_best_local_action PP PP)` THEN

REPEAT STRIP_TAC THEN
`IS_VAR_RES_COMBINATOR (FST xenv)` by ALL_TAC THEN1 (
   Q.UNABBREV_TAC `xenv` THEN
   ASM_SIMP_TAC std_ss [IS_VAR_RES_COMBINATOR_def] THEN
   METIS_TAC[]
) THEN
ASM_SIMP_TAC std_ss [ASL_PROGRAM_IS_ABSTRACTION___var_res_quant_best_local_action,
   VAR_RES_INFERENCE___prog_kleene_star]);



val VAR_RES_COND_INFERENCE___block_spec =
store_thm ("VAR_RES_COND_INFERENCE___block_spec",
``!f P wp rp d P' Q' p prog Q.
(FST P ==> ALL_DISTINCT d) ==>
((!x. VAR_RES_COND_HOARE_TRIPLE f
        (var_res_prop_input_distinct f (wp,rp) d (P' x))
        p
        (var_res_prop_input_distinct f (wp,rp) d (Q' x))) /\

?x. VAR_RES_COND_HOARE_TRIPLE f P
   (asl_prog_block (
       (var_res_prog_cond_best_local_action
            (var_res_prop_input_distinct f (wp,rp) d (P' x))
            (var_res_prop_input_distinct f (wp,rp) d (Q' x)))::
       prog)) Q) ==>

VAR_RES_COND_HOARE_TRIPLE f P (asl_prog_block (
(asl_comment_block_spec ((\x. var_res_prop_input_ap_distinct f (wp,rp) d (P' x)),
                          (\x. var_res_prop_input_ap_distinct f (wp,rp) d (Q' x)))
                         p)::prog)) Q``,

REPEAT STRIP_TAC THEN
Tactical.REVERSE (Cases_on `FST P /\ IS_SEPARATION_COMBINATOR f /\ FST Q`) THEN1 (
   FULL_SIMP_TAC std_ss [VAR_RES_COND_HOARE_TRIPLE_def]
) THEN
MATCH_MP_TAC (MP_CANON VAR_RES_COND_HOARE_TRIPLE___PROGRAM_ABSTRACTION_first_block_simple) THEN
SIMP_TAC std_ss [asl_comment_block_spec_def] THEN
Q.EXISTS_TAC `var_res_prog_cond_best_local_action
              (var_res_prop_input_distinct f (wp,rp) d (P' x))
              (var_res_prop_input_distinct f (wp,rp) d (Q' x))` THEN
FULL_SIMP_TAC std_ss [] THEN
Q.PAT_ASSUM `ALL_DISTINCT d` ASSUME_TAC THEN
`IS_VAR_RES_COMBINATOR (VAR_RES_COMBINATOR f)` by METIS_TAC[IS_VAR_RES_COMBINATOR_def] THEN
FULL_SIMP_TAC std_ss [VAR_RES_PROGRAM_IS_ABSTRACTION_def,
   var_res_prog_cond_best_local_action_def, COND_RAND,
   COND_RATOR, var_res_prop_input_distinct_def,
   ASL_PROGRAM_IS_ABSTRACTION___var_res_best_local_action,
   VAR_RES_COND_HOARE_TRIPLE_def]);



val VAR_RES_COND_INFERENCE___loop_spec =
store_thm ("VAR_RES_COND_INFERENCE___loop_spec",
``!f P wp rp d P' Q' p prog1 prog2 c Q.
(FST P ==> ALL_DISTINCT d) ==>
((!x. VAR_RES_COND_HOARE_TRIPLE f
        (var_res_prop_input_distinct f (wp,rp) d (P' x))
        (asl_prog_block (asl_prog_assume (asl_pred_neg c)::prog1))
        (var_res_prop_input_distinct f (wp,rp) d (Q' x))) /\

(!x. VAR_RES_COND_HOARE_TRIPLE f (var_res_prop_input_distinct f (wp,rp) d (P' x))
  (asl_prog_block [asl_prog_assume c;p;
      (var_res_prog_cond_quant_best_local_action
           (\x. (var_res_prop_input_distinct f (wp,rp) d (P' x)))
           (\x. (var_res_prop_input_distinct f (wp,rp) d (Q' x))))])
    (var_res_prop_input_distinct f (wp,rp) d (Q' x))) /\

?x. VAR_RES_COND_HOARE_TRIPLE f P
   (asl_prog_block (
       (var_res_prog_cond_best_local_action
            (var_res_prop_input_distinct f (wp,rp) d (P' x))
            (var_res_prop_input_distinct f (wp,rp) d (Q' x)))::
       prog2)) Q) ==>

VAR_RES_COND_HOARE_TRIPLE f P (asl_prog_block (
   (asl_comment_loop_spec ((\x. var_res_prop_input_ap_distinct f (wp,rp) d (P' x)),
                            (\x. var_res_prop_input_ap_distinct f (wp,rp) d (Q' x)))
   (asl_prog_block ((asl_prog_while c p)::prog1)))::prog2)) Q``,



REPEAT STRIP_TAC THEN
Tactical.REVERSE (Cases_on `FST P /\ IS_SEPARATION_COMBINATOR f /\ FST Q`) THEN1 (
   FULL_SIMP_TAC std_ss [VAR_RES_COND_HOARE_TRIPLE_def]
) THEN

REWRITE_TAC [prove (``asl_comment_loop_spec = asl_comment_block_spec``,
   SIMP_TAC std_ss [FUN_EQ_THM, asl_comment_block_spec_def,
       asl_comment_loop_spec_def])] THEN
MATCH_MP_TAC (MP_CANON VAR_RES_COND_INFERENCE___block_spec) THEN
ASM_REWRITE_TAC[] THEN
Tactical.REVERSE CONJ_TAC THEN1 METIS_TAC[] THEN

FULL_SIMP_TAC std_ss [VAR_RES_COND_HOARE_TRIPLE_def,
   var_res_prop_input_distinct_def, VAR_RES_HOARE_TRIPLE_def] THEN
Q.PAT_ASSUM `ALL_DISTINCT d` ASSUME_TAC THEN
SIMP_TAC std_ss [GSYM pairTheory.ELIM_PFORALL] THEN
HO_MATCH_MP_TAC ASL_INFERENCE_prog_while_frame THEN

FULL_SIMP_TAC std_ss [GSYM VAR_RES_HOARE_TRIPLE_def,
   var_res_prog_cond_quant_best_local_action_def,
   GSYM var_res_prog_quant_best_local_action_def,
   IS_SEPARATION_COMBINATOR___VAR_RES_COMBINATOR,
   pairTheory.ELIM_PFORALL]
);


val VAR_RES_COND_INFERENCE___while_unroll =
store_thm ("VAR_RES_COND_INFERENCE___while_unroll",
``!f c p prog P Q.

VAR_RES_COND_HOARE_TRIPLE f P
   (asl_prog_block ((asl_prog_assume (asl_pred_neg c))::prog)) Q /\
VAR_RES_COND_HOARE_TRIPLE f P
   (asl_prog_block ((asl_prog_assume c)::p::(asl_prog_while c p)::prog)) Q ==>
VAR_RES_COND_HOARE_TRIPLE f P
   (asl_prog_block ((asl_prog_while c p)::prog)) Q``,


SIMP_TAC std_ss [VAR_RES_COND_HOARE_TRIPLE_def,
   VAR_RES_HOARE_TRIPLE_def] THEN
REPEAT STRIP_TAC THEN
HO_MATCH_MP_TAC ASL_INFERENCE_prog_while_unroll THEN
FULL_SIMP_TAC std_ss [IS_SEPARATION_COMBINATOR___VAR_RES_COMBINATOR]);


val VAR_RES_COND_INFERENCE___while_unroll___invariant =
store_thm ("VAR_RES_COND_INFERENCE___while_unroll___invariant",
``!i f c p prog P Q.

VAR_RES_COND_HOARE_TRIPLE f P
   (asl_prog_block ((asl_prog_assume (asl_pred_neg c))::prog)) Q /\
VAR_RES_COND_HOARE_TRIPLE f P
   (asl_prog_block ((asl_prog_assume c)::p::(asl_comment_loop_invariant i (asl_prog_while c p))::prog)) Q ==>

VAR_RES_COND_HOARE_TRIPLE f P
   (asl_prog_block ((asl_comment_loop_invariant i
           (asl_prog_while c p))::prog)) Q``,

SIMP_TAC std_ss [VAR_RES_COND_INFERENCE___while_unroll,
   asl_comment_loop_invariant_def]);


val VAR_RES_COND_INFERENCE___while_unroll___loop_spec =
store_thm ("VAR_RES_COND_INFERENCE___while_unroll___loop_spec",
``!f c (p :('a, 'b, 'c, ('d, 'e, 'f) var_res_ext_state) asl_program) 
   sp prog1 prog2 P Q.

VAR_RES_COND_HOARE_TRIPLE f P
   (asl_prog_block ((asl_prog_assume (asl_pred_neg c))::(prog1 ++ prog2))) Q /\
VAR_RES_COND_HOARE_TRIPLE f P
   (asl_prog_block ((asl_prog_assume c)::p::(asl_comment_loop_spec sp 
       (asl_prog_block ((asl_prog_while c p)::prog1)))::prog2)) Q ==>

VAR_RES_COND_HOARE_TRIPLE f P
   (asl_prog_block ((asl_comment_loop_spec sp
           (asl_prog_block ((asl_prog_while c p)::prog1))::prog2))) Q``,

SIMP_TAC std_ss [asl_comment_loop_spec_def] THEN
REPEAT GEN_TAC THEN
Tactical.REVERSE (
`!(c1 :('a, 'b, 'c, ('d, 'e, 'f) var_res_ext_state) asl_program)  c2 c3 L1 L2.
  (VAR_RES_COND_HOARE_TRIPLE f P
    (asl_prog_block
       (c1::c2::asl_prog_block (c3::L1)::L2)) Q =
   VAR_RES_COND_HOARE_TRIPLE f P
    (asl_prog_block (c1::c2::c3::(L1 ++ L2))) Q) /\
  (VAR_RES_COND_HOARE_TRIPLE f P
    (asl_prog_block (asl_prog_block (c1::L1)::L2)) Q =
   VAR_RES_COND_HOARE_TRIPLE f P
     (asl_prog_block (c1::(L1++L2))) Q)` by ALL_TAC) THEN1 (
   FULL_SIMP_TAC std_ss [VAR_RES_COND_INFERENCE___while_unroll]
) THEN

REPEAT GEN_TAC THEN
`(asl_prog_block (c1::L1)::L2 = [] ++ asl_prog_block (c1::L1)::L2) /\
 (c1::c2::asl_prog_block (c3::L1)::L2 = [c1;c2] ++ asl_prog_block (c3::L1)::L2)` by SIMP_TAC list_ss [] THEN

ONCE_ASM_REWRITE_TAC[] THEN
SIMP_TAC std_ss [ASL_PROGRAM_SEM___block_flatten,
   VAR_RES_PROGRAM_SEM_def, VAR_RES_COND_HOARE_TRIPLE_REWRITE] THEN
SIMP_TAC list_ss []);





val VAR_RES_COND_INFERENCE___prog_assume_true =
store_thm ("VAR_RES_COND_INFERENCE___prog_assume_true",
``!f P progL Q.
VAR_RES_COND_HOARE_TRIPLE f P (asl_prog_block progL) Q ==>
VAR_RES_COND_HOARE_TRIPLE f P
   (asl_prog_block ((asl_prog_assume asl_pred_true)::progL)) Q``,
SIMP_TAC std_ss [VAR_RES_COND_INFERENCE___prog_block_skip_ELIM,
   asl_prog_assume_true]);


val VAR_RES_COND_INFERENCE___prog_assume_false =
store_thm ("VAR_RES_COND_INFERENCE___prog_assume_false",
``!f P progL Q.
T ==>
VAR_RES_COND_HOARE_TRIPLE f P
   (asl_prog_block ((asl_prog_assume asl_pred_false)::progL)) Q``,
SIMP_TAC std_ss [VAR_RES_COND_INFERENCE___prog_block_diverge,
   asl_prog_assume_false]);


val VAR_RES_COND_INFERENCE___prog_assume_neg_false =
store_thm ("VAR_RES_COND_INFERENCE___prog_assume_neg_false",
``!f P progL Q.
VAR_RES_COND_HOARE_TRIPLE f P (asl_prog_block progL) Q ==>
VAR_RES_COND_HOARE_TRIPLE f P
   (asl_prog_block ((asl_prog_assume (asl_pred_neg asl_pred_false))::progL)) Q``,
SIMP_TAC std_ss [VAR_RES_COND_HOARE_TRIPLE_def,
   VAR_RES_HOARE_TRIPLE_def, ASL_PROGRAM_HOARE_TRIPLE_def,
   ASL_PROGRAM_SEM___prog_block,
   ASL_PROGRAM_SEM___prog_assume___neg_false,
   IS_SEPARATION_COMBINATOR___VAR_RES_COMBINATOR,
   asla_seq_skip]);


val VAR_RES_COND_INFERENCE___prog_assume_neg_true =
store_thm ("VAR_RES_COND_INFERENCE___prog_assume_neg_true",
``!f P progL Q. T ==>
VAR_RES_COND_HOARE_TRIPLE f P
   (asl_prog_block ((asl_prog_assume (asl_pred_neg asl_pred_true))::progL)) Q``,
SIMP_TAC std_ss [VAR_RES_COND_HOARE_TRIPLE_def,
   VAR_RES_HOARE_TRIPLE_def, ASL_PROGRAM_HOARE_TRIPLE_def,
   ASL_PROGRAM_SEM___prog_block,
   ASL_PROGRAM_SEM___prog_assume___neg_true,
   IS_SEPARATION_COMBINATOR___VAR_RES_COMBINATOR,
   asla_seq_diverge] THEN
SIMP_TAC std_ss [HOARE_TRIPLE_def,
  asla_diverge_def, fasl_order_THM, EMPTY_SUBSET]);



val VAR_RES_COND_INFERENCE___prog_assume_and =
store_thm ("VAR_RES_COND_INFERENCE___prog_assume_and",
``!f P1 P2 P progL Q.
VAR_RES_COND_HOARE_TRIPLE f P
   (asl_prog_block (
         (asl_prog_assume P1)::
         (asl_prog_assume P2)::progL)) Q ==>
VAR_RES_COND_HOARE_TRIPLE f P
   (asl_prog_block ((asl_prog_assume (asl_pred_and P1 P2))::progL)) Q``,

REPEAT STRIP_TAC THEN
SIMP_TAC std_ss [VAR_RES_COND_INFERENCE___prog_block] THEN
MATCH_MP_TAC VAR_RES_COND_HOARE_TRIPLE___PROGRAM_ABSTRACTION_first THEN
Q.EXISTS_TAC `asl_prog_seq (asl_prog_assume P1) (asl_prog_assume P2)` THEN
REPEAT STRIP_TAC THENL [
   SIMP_TAC std_ss [VAR_RES_PROGRAM_IS_ABSTRACTION_def] THEN
   MATCH_MP_TAC ASL_PROGRAM_IS_ABSTRACTION___assume_and THEN
   ASM_SIMP_TAC std_ss [IS_SEPARATION_COMBINATOR___VAR_RES_COMBINATOR],

   FULL_SIMP_TAC std_ss [VAR_RES_COND_HOARE_TRIPLE_def,
      VAR_RES_HOARE_TRIPLE_def, ASL_PROGRAM_HOARE_TRIPLE_def,
      ASL_PROGRAM_SEM___prog_seq, ASL_PROGRAM_SEM___prog_block] THEN
   METIS_TAC[asla_seq___ASSOC, ASSOC_DEF]
]);


val VAR_RES_COND_INFERENCE___prog_assume_or =
store_thm ("VAR_RES_COND_INFERENCE___prog_assume_or",
``!f P1 P2 P progL Q.
VAR_RES_COND_HOARE_TRIPLE f P
   (asl_prog_block ((asl_prog_assume P1)::progL)) Q /\
VAR_RES_COND_HOARE_TRIPLE f P
   (asl_prog_block ((asl_prog_assume P2)::progL)) Q ==>
VAR_RES_COND_HOARE_TRIPLE f P
   (asl_prog_block (asl_prog_assume (asl_pred_or P1 P2)::progL)) Q``,

SIMP_TAC std_ss [VAR_RES_COND_INFERENCE___prog_block] THEN
REPEAT STRIP_TAC THEN
MATCH_MP_TAC VAR_RES_COND_HOARE_TRIPLE___PROGRAM_ABSTRACTION_first THEN
Q.EXISTS_TAC `asl_prog_choice (asl_prog_assume P1) (asl_prog_assume P2)` THEN
REPEAT STRIP_TAC THENL [
   SIMP_TAC std_ss [VAR_RES_PROGRAM_IS_ABSTRACTION_def] THEN
   MATCH_MP_TAC ASL_PROGRAM_IS_ABSTRACTION___assume_or THEN
   ASM_SIMP_TAC std_ss [IS_SEPARATION_COMBINATOR___VAR_RES_COMBINATOR],

   FULL_SIMP_TAC std_ss [VAR_RES_COND_HOARE_TRIPLE_def,
      VAR_RES_HOARE_TRIPLE_def, asl_prog_seq_choice] THEN
   REPEAT STRIP_TAC THEN
   MATCH_MP_TAC ASL_INFERENCE_prog_choice THEN
   ASM_SIMP_TAC std_ss []
]);



val VAR_RES_COND_INFERENCE___prog_assume_neg_neg =
store_thm ("VAR_RES_COND_INFERENCE___prog_assume_neg_neg",
``!f p P progL Q.
VAR_RES_COND_HOARE_TRIPLE f P
   (asl_prog_block ((asl_prog_assume p)::progL)) Q ==>
VAR_RES_COND_HOARE_TRIPLE f P
   (asl_prog_block ((asl_prog_assume (asl_pred_neg (asl_pred_neg p)))::progL)) Q``,

SIMP_TAC std_ss [VAR_RES_COND_INFERENCE___prog_block] THEN
REPEAT STRIP_TAC THEN
MATCH_MP_TAC VAR_RES_COND_HOARE_TRIPLE___PROGRAM_ABSTRACTION_first THEN
Q.EXISTS_TAC `asl_prog_assume p` THEN
REPEAT STRIP_TAC THENL [
   SIMP_TAC std_ss [VAR_RES_PROGRAM_IS_ABSTRACTION_def] THEN
   MATCH_MP_TAC ASL_PROGRAM_IS_ABSTRACTION___assume_neg_neg THEN
   ASM_SIMP_TAC std_ss [IS_SEPARATION_COMBINATOR___VAR_RES_COMBINATOR],

   ASM_REWRITE_TAC[]
]);



val VAR_RES_COND_INFERENCE___prog_assume_neg_and =
store_thm ("VAR_RES_COND_INFERENCE___prog_assume_neg_and",
``!f P1 P2 P progL Q.
VAR_RES_COND_HOARE_TRIPLE f P
   (asl_prog_block ((asl_prog_assume (asl_pred_or (asl_pred_neg P1) (asl_pred_neg P2)))::progL)) Q ==>
VAR_RES_COND_HOARE_TRIPLE f P
   (asl_prog_block ((asl_prog_assume (asl_pred_neg (asl_pred_and P1 P2)))::progL)) Q``,

SIMP_TAC std_ss [VAR_RES_COND_INFERENCE___prog_block] THEN
REPEAT STRIP_TAC THEN
MATCH_MP_TAC VAR_RES_COND_HOARE_TRIPLE___PROGRAM_ABSTRACTION_first THEN
Q.EXISTS_TAC `asl_prog_assume (asl_pred_or (asl_pred_neg P1) (asl_pred_neg P2))` THEN
REPEAT STRIP_TAC THENL [
   SIMP_TAC std_ss [VAR_RES_PROGRAM_IS_ABSTRACTION_def] THEN
   MATCH_MP_TAC ASL_PROGRAM_IS_ABSTRACTION___assume_neg_and THEN
   ASM_SIMP_TAC std_ss [IS_SEPARATION_COMBINATOR___VAR_RES_COMBINATOR],

   ASM_REWRITE_TAC[]
]);



val VAR_RES_COND_INFERENCE___prog_assume_neg_or =
store_thm ("VAR_RES_COND_INFERENCE___prog_assume_neg_or",
``!f P1 P2 P progL Q.
VAR_RES_COND_HOARE_TRIPLE f P
   (asl_prog_block ((asl_prog_assume (asl_pred_and (asl_pred_neg P1) (asl_pred_neg P2)))::progL)) Q ==>
VAR_RES_COND_HOARE_TRIPLE f P
   (asl_prog_block ((asl_prog_assume (asl_pred_neg (asl_pred_or P1 P2)))::progL)) Q``,

SIMP_TAC std_ss [VAR_RES_COND_INFERENCE___prog_block] THEN
REPEAT STRIP_TAC THEN
MATCH_MP_TAC VAR_RES_COND_HOARE_TRIPLE___PROGRAM_ABSTRACTION_first THEN
Q.EXISTS_TAC `asl_prog_assume (asl_pred_and (asl_pred_neg P1) (asl_pred_neg P2))` THEN
REPEAT STRIP_TAC THENL [
   SIMP_TAC std_ss [VAR_RES_PROGRAM_IS_ABSTRACTION_def] THEN
   MATCH_MP_TAC ASL_PROGRAM_IS_ABSTRACTION___assume_neg_or THEN
   ASM_SIMP_TAC std_ss [IS_SEPARATION_COMBINATOR___VAR_RES_COMBINATOR],

   ASM_REWRITE_TAC[]
]);


val ASL_IS_INTUITIONISTIC___weak_expression =
store_thm ("ASL_IS_INTUITIONISTIC___weak_expression",
``!f p el.
IS_SEPARATION_COMBINATOR f /\
EVERY (\e. IS_SOME (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS e)) el ==>
ASL_IS_INTUITIONISTIC (VAR_RES_COMBINATOR f)
         (var_res_prop_weak_expression p el)``,

SIMP_TAC std_ss [ASL_IS_INTUITIONISTIC___REWRITE, EVERY_MEM,
   IS_SEPARATION_COMBINATOR___VAR_RES_COMBINATOR,
   var_res_prop_weak_expression_def, IN_ABS, LET_THM,
   var_res_prop_expression_def, var_res_stack_proposition_def] THEN
REPEAT (GEN_TAC ORELSE DISCH_TAC) THEN
Tactical.REVERSE (`EVERY (\e. (e (FST s2) = e (FST s1))) el` by ALL_TAC) THEN1 (
   Tactical.REVERSE (`MAP (\e. (e (FST s2))) el = MAP (\e. (e (FST s1))) el` by ALL_TAC) THEN1 (
      ASM_REWRITE_TAC[]
   ) THEN
   POP_ASSUM MP_TAC THEN
   REPEAT (POP_ASSUM (K ALL_TAC)) THEN
   Induct_on `el` THEN
   ASM_SIMP_TAC list_ss []
) THEN
FULL_SIMP_TAC std_ss [VAR_RES_COMBINATOR_def,
   ASL_IS_SUBSTATE___PRODUCT_SEPARATION_COMBINATOR,
   GSYM VAR_RES_STACK_IS_SUBSTATE_def, EVERY_MEM, MEM_MAP,
   GSYM LEFT_FORALL_IMP_THM] THEN
METIS_TAC[IS_SOME___VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS___SUBSTATE_LEFT]);


val ASL_IS_INTUITIONISTIC___weak_binexpression =
store_thm ("ASL_IS_INTUITIONISTIC___weak_binexpression",
``!f p e1 e2.
IS_SEPARATION_COMBINATOR f /\
IS_SOME (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS e1) /\
IS_SOME (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS e2) ==>
ASL_IS_INTUITIONISTIC (VAR_RES_COMBINATOR f)
         (var_res_prop_weak_binexpression p e1 e2)``,

SIMP_TAC std_ss [var_res_prop_weak_binexpression_def,
   var_res_prop_binexpression___ALTERNATIVE_DEF,
   GSYM var_res_prop_weak_expression_def] THEN
REPEAT STRIP_TAC THEN
MATCH_MP_TAC ASL_IS_INTUITIONISTIC___weak_expression THEN
ASM_SIMP_TAC list_ss []);



val var_res_pred_def = Define `
var_res_pred p el =
   asl_pred_prim (\f. var_res_prop_weak_expression p el)`;

val var_res_pred_bin_def = Define `
var_res_pred_bin p e1 e2 =
   asl_pred_prim (\f. var_res_prop_weak_binexpression p e1 e2)`;


val var_res_pred_bin___ALTERNATIVE_DEF = store_thm ("var_res_pred_bin___ALTERNATIVE_DEF",
``var_res_pred_bin p e1 e2 =
  var_res_pred (\l. p (HD l) (HD (TL l))) [e1;e2]``,
SIMP_TAC std_ss [var_res_pred_bin_def, var_res_pred_def,
  var_res_prop_weak_expression_def, var_res_prop_weak_binexpression_def,
  var_res_prop_binexpression___ALTERNATIVE_DEF]);


val VAR_RES_COND_INFERENCE___prog_assume_pred =
store_thm ("VAR_RES_COND_INFERENCE___prog_assume_pred",
``!f wpb rpb sfb p el progL Q.

EVERY (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET
   (SET_OF_BAG (BAG_UNION wpb rpb))) el ==>

(VAR_RES_COND_HOARE_TRIPLE f (var_res_prop f (wpb, rpb)
   (BAG_INSERT (var_res_prop_expression f T p el) sfb))
   (asl_prog_block progL) Q ==>

VAR_RES_COND_HOARE_TRIPLE f (var_res_prop f (wpb, rpb) sfb)
   (asl_prog_block ((asl_prog_assume (var_res_pred p el))::progL)) Q)``,

SIMP_TAC std_ss [VAR_RES_COND_INFERENCE___prog_block,
   var_res_pred_def] THEN
SIMP_TAC std_ss [VAR_RES_COND_HOARE_TRIPLE_def,
   VAR_RES_HOARE_TRIPLE_def, var_res_prop___REWRITE,
   asl_prog_assume_def] THEN
REPEAT STRIP_TAC THEN
MATCH_MP_TAC ASL_INFERENCE_assume_seq THEN
REPEAT STRIP_TAC THENL [
   ASM_SIMP_TAC std_ss [IS_SEPARATION_COMBINATOR___VAR_RES_COMBINATOR],

   ASM_SIMP_TAC std_ss [asl_predicate_IS_DECIDED_def, IN_ABS,
      EVAL_asl_predicate_def] THEN
   `ASL_IS_INTUITIONISTIC (VAR_RES_COMBINATOR f)
           (var_res_prop_weak_expression p el)` by ALL_TAC THEN1 (
      MATCH_MP_TAC ASL_IS_INTUITIONISTIC___weak_expression THEN
      FULL_SIMP_TAC std_ss [EVERY_MEM,
         VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET_def]
   ) THEN
   ASM_SIMP_TAC std_ss [var_res_prop_weak_expression_def,
     ASL_INTUITIONISTIC_NEGATION_REWRITE, IN_ABS,
     var_res_prop_expression_def, var_res_stack_proposition_def,
     LET_THM, VAR_RES_COMBINATOR_def, ASL_IS_SUBSTATE___PRODUCT_SEPARATION_COMBINATOR,
     GSYM VAR_RES_STACK_IS_SUBSTATE_def] THEN
   REPEAT STRIP_TAC THEN
   `EVERY IS_SOME (MAP (\e. e (FST x)) el)` by ALL_TAC THEN1 (
      SIMP_TAC std_ss [EVERY_MEM, MEM_MAP, GSYM LEFT_FORALL_IMP_THM] THEN
      CONSEQ_REWRITE_TAC ([VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET___IS_SOME_IMPL], [], []) THEN
      METIS_TAC [var_res_prop___PROP___VARS, EVERY_MEM]
   ) THEN
   Cases_on `p (MAP THE (MAP (\e. e (FST x)) el))` THEN (
     ASM_REWRITE_TAC[]
   ) THEN
   REPEAT STRIP_TAC THEN
   Tactical.REVERSE (`MAP (\e. e (FST s2)) el =
                      MAP (\e. e (FST x)) el` by ALL_TAC) THEN1 (
       ASM_REWRITE_TAC[]
   ) THEN
   FULL_SIMP_TAC std_ss [MAP_EQ_f, EVERY_MEM, VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET_def,
      MEM_MAP, GSYM LEFT_FORALL_IMP_THM] THEN
   METIS_TAC[IS_SOME___VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS___SUBSTATE_LEFT],


   `VAR_RES_IS_STACK_IMPRECISE___USED_VARS
            (SET_OF_BAG (BAG_UNION wpb rpb))
            (var_res_prop_expression f T p el)` by ALL_TAC THEN1 (
      ASM_SIMP_TAC std_ss [VAR_RES_IS_STACK_IMPRECISE___USED_VARS___var_res_prop_expression]
   ) THEN
   FULL_SIMP_TAC std_ss [var_res_prop___COND_INSERT, ASL_PROGRAM_HOARE_TRIPLE_def,
      HOARE_TRIPLE_def, asl_bool_EVAL, IN_ABS] THEN
   REPEAT STRIP_TAC THEN
   Q.PAT_ASSUM `!x. X` MATCH_MP_TAC THEN
   Q.PAT_ASSUM `x IN var_res_prop___PROP f X Y` MP_TAC THEN
   FULL_SIMP_TAC std_ss [var_res_prop___PROP_INSERT, IN_ABS,
      var_res_prop___COND_INSERT,
      EVAL_asl_predicate_def, COND_RAND, COND_RATOR, asl_bool_EVAL] THEN
   FULL_SIMP_TAC std_ss [asl_star_def, var_res_prop_weak_expression_def,
      var_res_prop_expression_def, var_res_stack_proposition_def,
      IN_ABS, LET_THM, asl_emp_def, IS_SEPARATION_COMBINATOR_EXPAND_THM,
      GSYM RIGHT_EXISTS_AND_THM, GSYM LEFT_EXISTS_AND_THM,
      VAR_RES_COMBINATOR_REWRITE, PAIR_EXISTS_THM] THEN
   PROVE_TAC[]
]);




val VAR_RES_COND_INFERENCE___prog_assume_pred_bin =
store_thm ("VAR_RES_COND_INFERENCE___prog_assume_pred_bin",
``!f wpb rpb sfb p e1 e2 progL Q.

VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET
   (SET_OF_BAG (BAG_UNION wpb rpb)) e1 /\
VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET
   (SET_OF_BAG (BAG_UNION wpb rpb)) e2 ==>

(VAR_RES_COND_HOARE_TRIPLE f (var_res_prop f (wpb, rpb)
   (BAG_INSERT (var_res_prop_binexpression f T p e1 e2) sfb))
   (asl_prog_block progL) Q ==>

VAR_RES_COND_HOARE_TRIPLE f (var_res_prop f (wpb, rpb) sfb)
   (asl_prog_block ((asl_prog_assume (var_res_pred_bin p e1 e2))::progL)) Q)``,

SIMP_TAC std_ss [var_res_pred_bin___ALTERNATIVE_DEF,
   var_res_prop_binexpression___ALTERNATIVE_DEF] THEN
REPEAT STRIP_TAC THEN
MATCH_MP_TAC (MP_CANON VAR_RES_COND_INFERENCE___prog_assume_pred) THEN
ASM_SIMP_TAC list_ss []);



val VAR_RES_COND_INFERENCE___prog_assert_pred =
store_thm ("VAR_RES_COND_INFERENCE___prog_assert_pred",
``!sr f wpb rpb sfb p el progL Q.

EVERY (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET
   (SET_OF_BAG (BAG_UNION wpb rpb))) el ==>

((VAR_RES_FRAME_SPLIT f sr (wpb,rpb) EMPTY_BAG EMPTY_BAG sfb 
  {|var_res_prop_expression f T p el|}) (K T) /\
(VAR_RES_COND_HOARE_TRIPLE f (var_res_prop f (wpb, rpb)
   (BAG_INSERT (var_res_prop_expression f T p el) sfb))
   (asl_prog_block progL) Q) ==>

VAR_RES_COND_HOARE_TRIPLE f (var_res_prop f (wpb, rpb) sfb)
   (asl_prog_block ((asl_prog_assert (var_res_pred p el))::progL)) Q)``,


SIMP_TAC std_ss [VAR_RES_COND_INFERENCE___prog_block,
   var_res_pred_def] THEN
SIMP_TAC std_ss [VAR_RES_COND_HOARE_TRIPLE_def,
   VAR_RES_HOARE_TRIPLE_def, var_res_prop___REWRITE,
   asl_prog_assert_def] THEN
REPEAT STRIP_TAC THEN
MATCH_MP_TAC ASL_INFERENCE_assert_seq THEN

`ASL_IS_INTUITIONISTIC (VAR_RES_COMBINATOR f)
        (var_res_prop_weak_expression p el)` by ALL_TAC THEN1 (
   MATCH_MP_TAC ASL_IS_INTUITIONISTIC___weak_expression THEN
   FULL_SIMP_TAC std_ss [EVERY_MEM,
      VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET_def]
) THEN
`VAR_RES_IS_STACK_IMPRECISE___USED_VARS (SET_OF_BAG (wpb + rpb))
        (var_res_prop_expression f T p el)` by ALL_TAC THEN1 (
   MATCH_MP_TAC VAR_RES_IS_STACK_IMPRECISE___USED_VARS___var_res_prop_expression THEN
   ASM_REWRITE_TAC[]
) THEN
FULL_SIMP_TAC std_ss [IS_SEPARATION_COMBINATOR___VAR_RES_COMBINATOR,
   IN_ABS, EVAL_asl_predicate_def,
   var_res_prop___COND_INSERT] THEN
`!s. s IN var_res_prop___PROP f (wpb,rpb) sfb ==>
     s IN var_res_prop_weak_expression p el` by ALL_TAC THEN1 (

   `VAR_RES_FRAME_SPLIT___sfb_restP_OK f (wpb,rpb) (K T)` by ALL_TAC THEN1 (
      FULL_SIMP_TAC std_ss [VAR_RES_FRAME_SPLIT___sfb_restP_OK_def] THEN
      METIS_TAC[]
   ) THEN
   FULL_SIMP_TAC std_ss [VAR_RES_FRAME_SPLIT_def, BAG_UNION_EMPTY, BAG_DIFF_EMPTY,
      BAG_UNION_INSERT, var_res_prop___COND_INSERT, IN_DEF] THEN
   REPEAT STRIP_TAC THEN
   Q.PAT_ASSUM `!s. X s ==> Y s` (MP_TAC o Q.SPEC `s`) THEN
   ASM_SIMP_TAC std_ss [var_res_prop___PROP_INSERT, var_res_prop___COND_INSERT,
      var_res_prop_weak_expression_def,
      var_res_prop_expression_def, var_res_stack_proposition_def, IN_ABS,
      LET_THM, GSYM LEFT_FORALL_IMP_THM]
) THEN
ASM_SIMP_TAC std_ss [] THEN
Tactical.REVERSE (`(asl_and (\s. s IN var_res_prop___PROP f (wpb,rpb) sfb /\ (s = x))
     (var_res_prop_weak_expression p el)) = (\s.    s IN
             var_res_prop___PROP f (wpb,rpb)     (BAG_INSERT (var_res_prop_expression f T p el) sfb) /\
             (s = x))` by ALL_TAC) THEN1 (
   ASM_SIMP_TAC std_ss []
) THEN

ASM_SIMP_TAC std_ss [FUN_EQ_THM, asl_bool_EVAL, IN_ABS,
   var_res_prop___PROP_INSERT, var_res_prop___COND_INSERT,
   var_res_prop_expression_REWRITE, var_res_prop_weak_expression_def,
   LET_THM] THEN
FULL_SIMP_TAC std_ss [IS_SEPARATION_COMBINATOR_EXPAND_THM, asl_emp_def, IN_ABS,
   GSYM RIGHT_EXISTS_AND_THM, GSYM LEFT_EXISTS_AND_THM] THEN
METIS_TAC[]);



val VAR_RES_COND_INFERENCE___comment_assert =
store_thm ("VAR_RES_COND_INFERENCE___comment_assert",
``!f wpb rpb sfb progL qP Q.

(?x. VAR_RES_COND_HOARE_TRIPLE f (var_res_prop f (wpb, rpb) sfb)
   (asl_prog_block (
       (var_res_prog_cond_best_local_action 
          (var_res_prop_internal f (EMPTY_BAG, BAG_UNION wpb rpb) (EMPTY, EMPTY) T EMPTY_BAG (qP x))
          (var_res_prop_internal f (EMPTY_BAG, BAG_UNION wpb rpb) (EMPTY, EMPTY) T EMPTY_BAG (qP x)))::
       progL)) Q) ==>

VAR_RES_COND_HOARE_TRIPLE f (var_res_prop f (wpb, rpb) sfb)
   (asl_prog_block ((asl_comment_assert qP)::progL)) Q``,


SIMP_TAC std_ss [GSYM LEFT_FORALL_IMP_THM] THEN
REPEAT GEN_TAC THEN
Tactical.REVERSE (Cases_on `var_res_prop___COND f (wpb,rpb) sfb`) THEN1 (
   ASM_SIMP_TAC std_ss [VAR_RES_COND_HOARE_TRIPLE_def,
      var_res_prop___REWRITE]
) THEN
MATCH_MP_TAC (VAR_RES_COND_HOARE_TRIPLE___PROGRAM_ABSTRACTION_first_block_simple) THEN
`IS_SEPARATION_COMBINATOR f /\ BAG_ALL_DISTINCT (BAG_UNION wpb rpb)` by ALL_TAC THEN1 (
   FULL_SIMP_TAC std_ss [var_res_prop___COND___EXPAND]
) THEN
ASM_SIMP_TAC std_ss [VAR_RES_PROGRAM_IS_ABSTRACTION_def,
   var_res_prog_cond_best_local_action_def, var_res_prop___REWRITE,
   asl_comment_assert_def, var_res_prop_internal_def,
   var_res_prop_internal___COND_def, FINITE_BAG_THM,
   NOT_IN_EMPTY_BAG, BAG_UNION_EMPTY] THEN
MATCH_MP_TAC (EQ_IMP_RULE_CANON ASL_PROGRAM_IS_ABSTRACTION___var_res_best_local_action) THEN
ASM_SIMP_TAC std_ss [VAR_RES_HOARE_TRIPLE_def, ASL_PROGRAM_HOARE_TRIPLE_def,
   ASL_PROGRAM_SEM___skip, HOARE_TRIPLE_def, IN_ABS,
   asla_skip_def, fasl_order_THM, SUBSET_DEF, IN_SING,
   VAR_RES_STACK___IS_EQUAL_UPTO_VALUES___REFL] THEN
FULL_SIMP_TAC std_ss [var_res_prop___COND___REWRITE,
   IS_VAR_RES_COMBINATOR_def] THEN
METIS_TAC[]);


(*
val VAR_RES_COND_INFERENCE___comment_assert =
store_thm ("VAR_RES_COND_INFERENCE___comment_assert",
``!rfc f wpb rpb sfb progL P Q.

VAR_RES_IS_STACK_IMPRECISE___USED_VARS (SET_OF_BAG (BAG_UNION wpb rpb)) P ==>

(VAR_RES_FRAME_SPLIT f rfc (wpb,rpb) EMPTY_BAG EMPTY_BAG sfb {|P|}
(\sfb'''. VAR_RES_COND_HOARE_TRIPLE f
    (var_res_prop f (wpb,rpb) (BAG_INSERT P sfb'''))
       (asl_prog_block progL) Q)) ==>

VAR_RES_COND_HOARE_TRIPLE f (var_res_prop f (wpb, rpb) sfb)
   (asl_prog_block ((asl_comment_assert P)::progL)) Q``,


REPEAT STRIP_TAC THEN
Tactical.REVERSE (Cases_on `var_res_prop___COND f (wpb,rpb) sfb`) THEN1 (
   ASM_SIMP_TAC std_ss [VAR_RES_COND_HOARE_TRIPLE_def,
      var_res_prop___REWRITE]
) THEN
MATCH_MP_TAC (MP_CANON VAR_RES_COND_HOARE_TRIPLE___PROGRAM_ABSTRACTION_first_block_simple) THEN
Q.EXISTS_TAC `var_res_prog_cond_best_local_action 
   (var_res_prop f (EMPTY_BAG, BAG_UNION wpb rpb) {|P|})
   (var_res_prop f (EMPTY_BAG, BAG_UNION wpb rpb) {|P|})` THEN
Tactical.REVERSE CONJ_TAC THEN1 (
   MATCH_MP_TAC (MP_CANON VAR_RES_COND_INFERENCE___var_res_prog_cond_best_local_action) THEN
   Q.EXISTS_TAC `rfc` THEN
   ASM_SIMP_TAC std_ss [BAG_UNION_INSERT, BAG_UNION_EMPTY, SUBSET_DEF,
      IN_SET_OF_BAG, NOT_IN_EMPTY_BAG]
) THEN
`var_res_prop___COND f ({||},wpb + rpb) {|P|}` by ALL_TAC THEN1 (
   FULL_SIMP_TAC std_ss [var_res_prop___COND___REWRITE,
      BAG_IN_BAG_INSERT, NOT_IN_EMPTY_BAG, BAG_UNION_EMPTY,
      FINITE_BAG_THM]
) THEN
ASM_SIMP_TAC std_ss [VAR_RES_PROGRAM_IS_ABSTRACTION_def,
   var_res_prog_cond_best_local_action_def, var_res_prop___REWRITE,
   asl_comment_assert_def] THEN
MATCH_MP_TAC (EQ_IMP_RULE_CANON ASL_PROGRAM_IS_ABSTRACTION___var_res_best_local_action) THEN

ASM_SIMP_TAC std_ss [VAR_RES_HOARE_TRIPLE_def, ASL_PROGRAM_HOARE_TRIPLE_def,
   ASL_PROGRAM_SEM___skip, HOARE_TRIPLE_def, IN_ABS,
   asla_skip_def, fasl_order_THM, SUBSET_DEF, IN_SING,
   VAR_RES_STACK___IS_EQUAL_UPTO_VALUES___REFL] THEN

FULL_SIMP_TAC std_ss [var_res_prop___COND___REWRITE,
   IS_VAR_RES_COMBINATOR_def] THEN
METIS_TAC[]);
*)


val ASL_INTUITIONISTIC_NEGATION___weak_prop_expression =
store_thm ("ASL_INTUITIONISTIC_NEGATION___weak_prop_expression",
``!el f s p.
(IS_SEPARATION_COMBINATOR f /\
 EVERY (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET (FDOM (FST s))) el) ==>

(ASL_INTUITIONISTIC_NEGATION (VAR_RES_COMBINATOR f)
   (var_res_prop_weak_expression p el) s =
(var_res_prop_weak_expression (\l. ~(p l)) el) s)``,


SIMP_TAC std_ss [ASL_INTUITIONISTIC_NEGATION_def, EXTENSION,
  IN_ABS, ASL_IS_SEPARATE_def, GSYM LEFT_FORALL_IMP_THM,
  IS_SOME_EXISTS, var_res_prop_weak_expression_def] THEN
REPEAT STRIP_TAC THEN
FULL_SIMP_TAC std_ss [IS_SEPARATION_COMBINATOR_EXPAND_THM] THEN
ASM_SIMP_TAC std_ss [var_res_prop_expression_def,
  var_res_stack_proposition_def, LET_THM, IN_ABS] THEN
`EVERY IS_SOME (MAP (\e. e (FST s)) el)` by ALL_TAC THEN1 (
   FULL_SIMP_TAC std_ss [VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET___REWRITE,
      VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_REL___REWRITE,
      EVERY_MEM, MEM_MAP, GSYM LEFT_FORALL_IMP_THM] THEN
   METIS_TAC[]
) THEN
ASM_REWRITE_TAC[] THEN
EQ_TAC THENL [
   SIMP_TAC std_ss [GSYM LEFT_EXISTS_IMP_THM,
      VAR_RES_COMBINATOR_REWRITE] THEN
   Q.EXISTS_TAC `(FEMPTY, uf (SND s))` THEN
   Q.EXISTS_TAC `s` THEN
   FULL_SIMP_TAC std_ss [VAR_RES_STACK_COMBINE_REWRITE,
      IS_SOME_EXISTS],


   REPEAT (GEN_TAC ORELSE DISCH_TAC) THEN
   Tactical.REVERSE (`MAP (\e. e (FST y)) el =
                      MAP (\e. e (FST s)) el` by ALL_TAC) THEN1 (
       ASM_REWRITE_TAC[]
   ) THEN
   FULL_SIMP_TAC std_ss [VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET_def,
      VAR_RES_COMBINATOR_REWRITE, MAP_EQ_f, EVERY_MEM, MEM_MAP, GSYM LEFT_FORALL_IMP_THM] THEN
   METIS_TAC[IS_SOME___VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS___SUBSTATE_RIGHT,
      VAR_RES_STACK_IS_SUBSTATE_INTRO]
]);






val ASL_INTUITIONISTIC_NEGATION___weak_prop_binexpression =
store_thm ("ASL_INTUITIONISTIC_NEGATION___weak_prop_binexpression",
``!e1 e2 f s p.
(IS_SEPARATION_COMBINATOR f /\
 VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET (FDOM (FST s)) e1 /\
 VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET (FDOM (FST s)) e2) ==>

(ASL_INTUITIONISTIC_NEGATION (VAR_RES_COMBINATOR f)
   (var_res_prop_weak_binexpression p e1 e2) s =
(var_res_prop_weak_binexpression (\x1 x2. ~(p x1 x2)) e1 e2) s)``,

SIMP_TAC std_ss [var_res_prop_weak_binexpression___ALTERNATIVE_DEF] THEN
REPEAT STRIP_TAC THEN
HO_MATCH_MP_TAC ASL_INTUITIONISTIC_NEGATION___weak_prop_expression THEN
ASM_SIMP_TAC list_ss []);



val VAR_RES_COND_INFERENCE___prog_assume_neg_pred =
store_thm ("VAR_RES_COND_INFERENCE___prog_assume_neg_pred",
``!f wpb rpb sfb p el progL Q.

EVERY (VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET
   (SET_OF_BAG (BAG_UNION wpb rpb))) el ==>

(VAR_RES_COND_HOARE_TRIPLE f (var_res_prop f (wpb, rpb)
   (BAG_INSERT (var_res_prop_expression f T (\l. ~(p l)) el) sfb))
   (asl_prog_block progL) Q ==>

VAR_RES_COND_HOARE_TRIPLE f (var_res_prop f (wpb, rpb) sfb)
   (asl_prog_block ((asl_prog_assume (asl_pred_neg (
      var_res_pred p el)))::progL)) Q)``,


REPEAT STRIP_TAC THEN
MP_TAC (Q.SPECL [`f`, `wpb`, `rpb`, `sfb`, `\l. ~(p l)`, `el`,
                 `progL`, `Q`]
        VAR_RES_COND_INFERENCE___prog_assume_pred) THEN
ASM_SIMP_TAC std_ss [] THEN

SIMP_TAC std_ss [VAR_RES_COND_INFERENCE___prog_block, var_res_pred_def] THEN
SIMP_TAC std_ss [VAR_RES_COND_HOARE_TRIPLE_def, VAR_RES_HOARE_TRIPLE_def,
   ASL_PROGRAM_HOARE_TRIPLE_def, ASL_PROGRAM_SEM___prog_seq,
   HOARE_TRIPLE_def, IN_ABS, var_res_prop___REWRITE,
   ASL_PROGRAM_SEM___assume, IS_SEPARATION_COMBINATOR___VAR_RES_COMBINATOR,
   EVAL_asl_predicate_def] THEN
REPEAT STRIP_TAC THEN
`!p. ASL_IS_INTUITIONISTIC (VAR_RES_COMBINATOR f)
    (var_res_prop_weak_expression p el)` by ALL_TAC THEN1 (
   GEN_TAC THEN
   MATCH_MP_TAC ASL_IS_INTUITIONISTIC___weak_expression THEN
   FULL_SIMP_TAC std_ss [VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET_def,
      EVERY_MEM]
) THEN
FULL_SIMP_TAC std_ss [] THEN
Q.PAT_ASSUM `!x'. x' IN X ==> Z` (MP_TAC o Q.SPEC `x`) THEN
ASM_SIMP_TAC std_ss [] THEN
Q.MATCH_ABBREV_TAC `fasl_order ((asla_seq A2 psem) x) (SOME qset) ==>
                    fasl_order ((asla_seq A1 psem) x) (SOME qset)` THEN
Tactical.REVERSE (`A1 x = A2 x` by ALL_TAC) THEN1 (
   ASM_SIMP_TAC std_ss [fasl_order_THM2, asla_seq_def]
) THEN
Q.UNABBREV_TAC `A1` THEN Q.UNABBREV_TAC `A2` THEN
SIMP_TAC std_ss [asla_assume_def] THEN

Q.ABBREV_TAC `P1 = ASL_INTUITIONISTIC_NEGATION (VAR_RES_COMBINATOR f)
         (var_res_prop_weak_expression p el)` THEN
Q.ABBREV_TAC `P2 = var_res_prop_weak_expression (\l. ~p l) el` THEN
Tactical.REVERSE (`!s. ASL_IS_SUBSTATE (VAR_RES_COMBINATOR f) x s ==> (s IN P1 = s IN P2)` by ALL_TAC) THEN1 (
   `x IN P1 = x IN P2` by ALL_TAC THEN1 (
      PROVE_TAC[ASL_IS_SUBSTATE___REFL, IS_SEPARATION_COMBINATOR___VAR_RES_COMBINATOR]
   ) THEN
   `x IN ASL_INTUITIONISTIC_NEGATION (VAR_RES_COMBINATOR f) P1 =
    x IN ASL_INTUITIONISTIC_NEGATION (VAR_RES_COMBINATOR f) P2` by ALL_TAC THEN1 (
      FULL_SIMP_TAC std_ss [ASL_INTUITIONISTIC_NEGATION_REWRITE, IN_ABS]
   ) THEN
   ASM_SIMP_TAC std_ss []
) THEN
REPEAT STRIP_TAC THEN
Q.UNABBREV_TAC `P1` THEN
Q.UNABBREV_TAC `P2` THEN
SIMP_TAC std_ss [IN_DEF] THEN
MATCH_MP_TAC ASL_INTUITIONISTIC_NEGATION___weak_prop_expression THEN

FULL_SIMP_TAC std_ss [VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET___REWRITE,
   VAR_RES_COMBINATOR_def, ASL_IS_SUBSTATE___PRODUCT_SEPARATION_COMBINATOR, EVERY_MEM] THEN
FULL_SIMP_TAC std_ss [ASL_IS_SUBSTATE_def, SOME___VAR_RES_STACK_COMBINE, FMERGE_DEF] THEN
`SET_OF_BAG (BAG_UNION wpb rpb) SUBSET FDOM (FST x)` by
   PROVE_TAC[var_res_prop___PROP___VARS] THEN
REPEAT STRIP_TAC THEN
RES_TAC THEN
Q.EXISTS_TAC `vs'` THEN
FULL_SIMP_TAC std_ss [SUBSET_DEF, IN_UNION]);



val VAR_RES_COND_INFERENCE___prog_assume_neg_pred_bin =
store_thm ("VAR_RES_COND_INFERENCE___prog_assume_neg_pred_bin",
``!f wpb rpb sfb p e1 e2 progL Q.

VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET
   (SET_OF_BAG (BAG_UNION wpb rpb)) e1 /\
VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET
   (SET_OF_BAG (BAG_UNION wpb rpb)) e2 ==>

(VAR_RES_COND_HOARE_TRIPLE f (var_res_prop f (wpb, rpb)
   (BAG_INSERT (var_res_prop_binexpression f T (\x1 x2. ~(p x1 x2)) e1 e2) sfb))
   (asl_prog_block progL) Q ==>

VAR_RES_COND_HOARE_TRIPLE f (var_res_prop f (wpb, rpb) sfb)
   (asl_prog_block ((asl_prog_assume (asl_pred_neg (
      var_res_pred_bin p e1 e2)))::progL)) Q)``,


SIMP_TAC std_ss [var_res_pred_bin___ALTERNATIVE_DEF,
   var_res_prop_binexpression___ALTERNATIVE_DEF] THEN
REPEAT STRIP_TAC THEN
MATCH_MP_TAC (MP_CANON VAR_RES_COND_INFERENCE___prog_assume_neg_pred) THEN
ASM_SIMP_TAC list_ss []);



val VAR_RES_COND_INFERENCE___prog_assume_pred_equiv =
store_thm ("VAR_RES_COND_INFERENCE___prog_assume_pred_equiv",
``!f P pred1 pred2 progL Q.

EQUIV_asl_predicate (VAR_RES_COMBINATOR f) pred1 pred2 ==>

(VAR_RES_COND_HOARE_TRIPLE f P
   (asl_prog_block ((asl_prog_assume pred1)::progL)) Q =
VAR_RES_COND_HOARE_TRIPLE f P
   (asl_prog_block ((asl_prog_assume pred2)::progL)) Q)``,

SIMP_TAC std_ss [EQUIV_asl_predicate_def,
  VAR_RES_COND_HOARE_TRIPLE_REWRITE,
  VAR_RES_PROGRAM_SEM_def,
  ASL_PROGRAM_SEM___prog_block,
  COND_HOARE_TRIPLE_REWRITE,
  IS_SEPARATION_COMBINATOR___VAR_RES_COMBINATOR,
  ASL_PROGRAM_SEM___assume]);



val VAR_RES_COND_INFERENCE___prog_assume_and___NO_EQUIV_COUNTER_EXAMPLE =
store_thm ("VAR_RES_COND_INFERENCE___prog_assume_and___NO_EQUIV_COUNTER_EXAMPLE",
``(IS_SEPARATION_COMBINATOR f ==>
  ~(VAR_RES_COND_HOARE_TRIPLE f (T, asl_true)
   (asl_prog_seq
         (asl_prog_assume (var_res_pred (\vl. HD vl = 0) [var_res_exp_var v]))
         (asl_prog_assume asl_pred_false)) 
   (T, asl_true))) /\
  
   (VAR_RES_COND_HOARE_TRIPLE f (T, asl_true)
   (asl_prog_assume (asl_pred_and (var_res_pred (\vl. HD vl = 0) [var_res_exp_var v])
                                  asl_pred_false)) (T, asl_true))``,


SIMP_TAC (std_ss++CONJ_ss) [EQUIV_asl_predicate_def,
  VAR_RES_COND_HOARE_TRIPLE_REWRITE,
  VAR_RES_PROGRAM_SEM_def,
  ASL_PROGRAM_SEM___prog_block,
  COND_HOARE_TRIPLE_REWRITE,
  ASL_PROGRAM_SEM___prog_seq,
  var_res_prop___REWRITE,
  IS_SEPARATION_COMBINATOR___VAR_RES_COMBINATOR,
  ASL_PROGRAM_SEM___assume, asl_bool_EVAL] THEN

SIMP_TAC std_ss [
  EVAL_asl_predicate_def, asl_bool_EVAL,
  asl_bool_REWRITES, asla_assume_def, HOARE_TRIPLE_def, IN_ABS,
  NOT_IN_asl_false, ASL_INTUITIONISTIC_NEGATION_REWRITE,
  EMPTY_SUBSET, fasl_order_THM2, var_res_pred_def] THEN
ASM_SIMP_TAC (list_ss++CONJ_ss) [ASL_IS_INTUITIONISTIC___weak_expression,
   IS_SEPARATION_COMBINATOR___VAR_RES_COMBINATOR,
   IS_SOME___VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS___VAR_CONST_EVAL,
   SOME___asla_seq] THEN
REPEAT STRIP_TAC THEN
Q.EXISTS_TAC `(FEMPTY, x2)` THEN
SIMP_TAC (list_ss++CONJ_ss) [var_res_prop_weak_expression_def,
   var_res_prop_expression_REWRITE, IN_ABS, LET_THM,
   var_res_exp_var_def, FDOM_FEMPTY, NOT_IN_EMPTY,
   IMAGE_EMPTY, BIGUNION_EMPTY, EMPTY_SUBSET] THEN
Q.EXISTS_TAC `(FEMPTY |+ (v, (0,ARB)), x2)` THEN
SIMP_TAC std_ss [ASL_IS_SUBSTATE_def,
   VAR_RES_COMBINATOR_REWRITE, FDOM_FUPDATE, FDOM_FEMPTY,
   IN_INSERT, NOT_IN_EMPTY, FAPPLY_FUPDATE_THM,
   VAR_RES_STACK_COMBINE_REWRITE] THEN
FULL_SIMP_TAC std_ss [IS_SEPARATION_COMBINATOR_EXPAND_THM] THEN
Q.EXISTS_TAC `(FEMPTY |+ (v,0,ARB), uf x2)` THEN
SIMP_TAC std_ss []);



(*******************************************************
 * PROCCALL FREE
 ******************************************************)


val asl_prog_IS_RESOURCE_AND_PROCCALL_FREE___var_res_bla =
store_thm ("asl_prog_IS_RESOURCE_AND_PROCCALL_FREE___var_res_bla",
``asl_prog_IS_RESOURCE_AND_PROCCALL_FREE (var_res_prog_best_local_action P Q) /\
  asl_prog_IS_RESOURCE_AND_PROCCALL_FREE (var_res_prog_cond_best_local_action xP xQ) /\
  asl_prog_IS_RESOURCE_AND_PROCCALL_FREE (var_res_prog_quant_best_local_action qP qQ) /\
  asl_prog_IS_RESOURCE_AND_PROCCALL_FREE (var_res_prog_cond_quant_best_local_action xqP xqQ)``,

REWRITE_TAC[asl_prog_IS_RESOURCE_AND_PROCCALL_FREE___SIMPLE_REWRITES,
   var_res_prog_best_local_action_def, var_res_prog_cond_best_local_action_def,
   var_res_prog_quant_best_local_action_def,
   var_res_prog_cond_quant_best_local_action_def,
   COND_RAND, COND_RATOR, COND_EXPAND_IMP]);


val asl_prog_IS_RESOURCE_AND_PROCCALL_FREE___VAR_RES_SIMPLE_REWRITES =
store_thm ("asl_prog_IS_RESOURCE_AND_PROCCALL_FREE___VAR_RES_SIMPLE_REWRITES",
``asl_prog_IS_RESOURCE_AND_PROCCALL_FREE (var_res_prog_release_lock f wpb sfb) /\
  asl_prog_IS_RESOURCE_AND_PROCCALL_FREE (var_res_prog_release_lock_input f wp P) /\
  asl_prog_IS_RESOURCE_AND_PROCCALL_FREE (var_res_prog_release_lock_internal f wp PP) /\
  asl_prog_IS_RESOURCE_AND_PROCCALL_FREE (var_res_prog_aquire_lock f c wpb sfb) /\
  asl_prog_IS_RESOURCE_AND_PROCCALL_FREE (var_res_prog_aquire_lock_input f c wp P) /\
  asl_prog_IS_RESOURCE_AND_PROCCALL_FREE (var_res_prog_aquire_lock_internal f c wp PP) /\

  asl_prog_IS_RESOURCE_AND_PROCCALL_FREE (var_res_prog_new_var_init v e) /\
  asl_prog_IS_RESOURCE_AND_PROCCALL_FREE (var_res_prog_dispose_var v) /\
  asl_prog_IS_RESOURCE_AND_PROCCALL_FREE (var_res_prog_assign v e)
``,

SIMP_TAC std_ss [var_res_prog_aquire_lock_internal_def,
                 var_res_prog_aquire_lock_def,
                 var_res_prog_aquire_lock_input_def,
                 var_res_prog_release_lock_internal_def,
                 var_res_prog_release_lock_def,
                 var_res_prog_release_lock_input_def,
                 var_res_prog_assign_def,
                 var_res_prog_new_var_init_def,
                 var_res_prog_dispose_var_def] THEN
REPEAT STRIP_TAC THEN
SIMP_TAC std_ss [COND_RAND, COND_RATOR,
                 asl_prog_IS_RESOURCE_AND_PROCCALL_FREE___prog_aquire_lock,
                 asl_prog_IS_RESOURCE_AND_PROCCALL_FREE___SIMPLE_REWRITES,
                 asl_prog_IS_RESOURCE_AND_PROCCALL_FREE___prim_command]);


val asl_prog_IS_RESOURCE_AND_PROCCALL_FREE___var_res_prog_new_var =
store_thm ("asl_prog_IS_RESOURCE_AND_PROCCALL_FREE___var_res_prog_new_var",
``!v. asl_prog_IS_RESOURCE_AND_PROCCALL_FREE (var_res_prog_new_var v)``,

SIMP_TAC std_ss [var_res_prog_new_var_def] THEN
GEN_TAC THEN
MATCH_MP_TAC asl_prog_IS_RESOURCE_AND_PROCCALL_FREE___prog_ndet THEN
SIMP_TAC std_ss [IN_ABS, GSYM LEFT_FORALL_IMP_THM,
   asl_prog_IS_RESOURCE_AND_PROCCALL_FREE___VAR_RES_SIMPLE_REWRITES]);






val asl_prog_IS_RESOURCE_AND_PROCCALL_FREE___var_res_prog_call_by_value_arg =
store_thm ("asl_prog_IS_RESOURCE_AND_PROCCALL_FREE___var_res_prog_call_by_value_arg",
``!body c.
  ((!v. asl_prog_IS_RESOURCE_AND_PROCCALL_FREE (body v)) ==>
  asl_prog_IS_RESOURCE_AND_PROCCALL_FREE (var_res_prog_call_by_value_arg body c))``,


SIMP_TAC std_ss [var_res_prog_call_by_value_arg_def] THEN
REPEAT STRIP_TAC THEN
MATCH_MP_TAC asl_prog_IS_RESOURCE_AND_PROCCALL_FREE___prog_forall THEN
SIMP_TAC std_ss [] THEN
GEN_TAC THEN
CONSEQ_REWRITE_TAC ([asl_prog_IS_RESOURCE_AND_PROCCALL_FREE___prog_seq], [], []) THEN
ASM_SIMP_TAC std_ss [asl_prog_IS_RESOURCE_AND_PROCCALL_FREE___VAR_RES_SIMPLE_REWRITES]);




val asl_prog_IS_RESOURCE_AND_PROCCALL_FREE___var_res_prog_local_var =
store_thm ("asl_prog_IS_RESOURCE_AND_PROCCALL_FREE___var_res_prog_local_var",
``!body.
  ((!v. asl_prog_IS_RESOURCE_AND_PROCCALL_FREE (body v)) ==>
  asl_prog_IS_RESOURCE_AND_PROCCALL_FREE (var_res_prog_local_var body))``,


SIMP_TAC std_ss [var_res_prog_local_var_def] THEN
REPEAT STRIP_TAC THEN
MATCH_MP_TAC asl_prog_IS_RESOURCE_AND_PROCCALL_FREE___prog_ndet THEN
ASM_SIMP_TAC std_ss [IN_ABS, GSYM LEFT_FORALL_IMP_THM,
   asl_prog_IS_RESOURCE_AND_PROCCALL_FREE___var_res_prog_call_by_value_arg]);



val asl_prog_IS_RESOURCE_AND_PROCCALL_FREE___var_res_prog_eval_expressions =
store_thm ("asl_prog_IS_RESOURCE_AND_PROCCALL_FREE___var_res_prog_eval_expressions",
``!body expL.
(!argL. asl_prog_IS_RESOURCE_AND_PROCCALL_FREE (body argL)) ==>
asl_prog_IS_RESOURCE_AND_PROCCALL_FREE (var_res_prog_eval_expressions body expL)``,

SIMP_TAC std_ss [var_res_prog_eval_expressions_def] THEN
REPEAT STRIP_TAC THEN
MATCH_MP_TAC asl_prog_IS_RESOURCE_AND_PROCCALL_FREE___prog_choose_constants THEN
ASM_REWRITE_TAC[]);




(*******************************************************
 * Lists of theorems for export
 ******************************************************)

val var_res___varlist_update_NO_VAR_THM =
save_thm ("var_res___varlist_update_NO_VAR_THM",
LIST_CONJ (map GEN_ALL [
   var_res_exp_varlist_update___const_EVAL,
   var_res_exp_varlist_update___var_res_exp_op_EVAL,
   var_res_exp_varlist_update___var_res_exp_binop_EVAL,
   var_res_exp_varlist_update___var_res_exp_binop_const_EVAL,
   var_res_exp_varlist_update___var_res_exp_add_sub_EVAL,
   var_res_prop_varlist_update___var_res_prop_binexpression,
   var_res_prop_varlist_update___var_res_prop_expression,
   var_res_prop_varlist_update___equal_unequal,
   var_res_prop_varlist_update___var_res_exp_is_defined,
   var_res_prop_varlist_update___BOOL,
   var_res_prop_varlist_update___bool_cond,
   var_res_prop_varlist_update___asl_trivial_cond,
   var_res_prop_varlist_update___asl_star,
   var_res_prop_varlist_update___var_res_map,
   var_res_prop_varlist_update___var_res_prop_binexpression_cond]));


val asl_prog_IS_RESOURCE_AND_PROCCALL_FREE___VAR_RES_REWRITES =
  save_thm ("asl_prog_IS_RESOURCE_AND_PROCCALL_FREE___VAR_RES_REWRITES",
  LIST_CONJ (map GEN_ALL [
     asl_prog_IS_RESOURCE_AND_PROCCALL_FREE___var_res_bla,
     asl_prog_IS_RESOURCE_AND_PROCCALL_FREE___VAR_RES_SIMPLE_REWRITES,
     asl_prog_IS_RESOURCE_AND_PROCCALL_FREE___var_res_prog_new_var,
     asl_prog_IS_RESOURCE_AND_PROCCALL_FREE___var_res_prog_call_by_value_arg,
     asl_prog_IS_RESOURCE_AND_PROCCALL_FREE___var_res_prog_local_var,
     asl_prog_IS_RESOURCE_AND_PROCCALL_FREE___var_res_prog_eval_expressions]));


val VAR_RES_IS_STACK_IMPRECISE___USED_VARS___VAR_RES_REWRITES =
  save_thm ("VAR_RES_IS_STACK_IMPRECISE___USED_VARS___VAR_RES_REWRITES",
  LIST_CONJ (map GEN_ALL [
     VAR_RES_IS_STACK_IMPRECISE___USED_VARS___var_res_prop_stack_true,
     VAR_RES_IS_STACK_IMPRECISE___USED_VARS___var_res_bool_proposition,
     VAR_RES_IS_STACK_IMPRECISE___USED_VARS___const,
     VAR_RES_IS_STACK_IMPRECISE___USED_VARS___asl_or,
     VAR_RES_IS_STACK_IMPRECISE___USED_VARS___asl_and,
     VAR_RES_IS_STACK_IMPRECISE___USED_VARS___asl_false,
     VAR_RES_IS_STACK_IMPRECISE___USED_VARS___asl_trivial_cond,
     VAR_RES_IS_STACK_IMPRECISE___USED_VARS___asl_exists_direct,
     VAR_RES_IS_STACK_IMPRECISE___USED_VARS___cond,
     VAR_RES_IS_STACK_IMPRECISE___USED_VARS___asl_star,
     VAR_RES_IS_STACK_IMPRECISE___USED_VARS___var_res_map___SIMPLE,
     VAR_RES_IS_STACK_IMPRECISE___USED_VARS___var_res_exp_is_defined,
     VAR_RES_IS_STACK_IMPRECISE___USED_VARS___var_res_prop_binexpression_cond,
     VAR_RES_IS_STACK_IMPRECISE___USED_VARS___var_res_prop_binexpression,
     VAR_RES_IS_STACK_IMPRECISE___USED_VARS___var_res_prop_expression,
     VAR_RES_IS_STACK_IMPRECISE___USED_VARS___var_res_prop_weak_unequal,
     VAR_RES_IS_STACK_IMPRECISE___USED_VARS___var_res_prop_weak_equal,
     VAR_RES_IS_STACK_IMPRECISE___USED_VARS___var_res_prop_equal,
     VAR_RES_IS_STACK_IMPRECISE___USED_VARS___var_res_prop_unequal,

     IS_SOME___VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS___VAR_CONST_EVAL,
     VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET___VAR_CONST_EVAL,
     VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET___var_res_exp_op,
     VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET___var_res_exp_binop,
     VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET___var_res_exp_binop_const,
     VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS_SUBSET___var_res_exp_add_sub,
     IS_SOME___VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS___var_res_exp_op,
     IS_SOME___VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS___var_res_exp_binop,
     IS_SOME___VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS___var_res_exp_binop_const,
     IS_SOME___VAR_RES_IS_STACK_IMPRECISE_EXPRESSION___USED_VARS___var_res_exp_add_sub]));


val _ = export_theory();
