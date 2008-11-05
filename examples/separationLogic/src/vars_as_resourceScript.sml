open HolKernel Parse boolLib bossLib;

(*
quietdec := true;
loadPath := 
            (concat Globals.HOLDIR "/examples/separationLogic/src") :: 
            !loadPath;

map load ["finite_mapTheory", "relationTheory", "congLib", "sortingTheory",
   "rich_listTheory", "generalHelpersTheory", "latticeTheory", "separationLogicTheory", "realLib"];
show_assums := true;
*)

open generalHelpersTheory finite_mapTheory relationTheory pred_setTheory congLib sortingTheory
   listTheory rich_listTheory arithmeticTheory operatorTheory optionTheory latticeTheory separationLogicTheory;

(*
quietdec := false;
*)

val _ = new_theory "vars_as_resource";

(*
val IS_PERMISSION_STRUCTURE_SUBSET_def = Define `
	IS_PERMISSION_STRUCTURE_SUBSET (s:'a set, f:'a option -> 'a option -> 'a option, total_perm:'a) = 
		(!c1 c2. (~(c1 IN s) \/ ~(c2 IN s)) ==> (f (SOME c1) (SOME c2) = NONE)) /\
		(!c c1 c2. (f (SOME c1) (SOME c2) = (SOME c)) ==> (c IN s)) /\
		ASSOC f /\
		COMM f /\
		OPTION_IS_LEFT_CANCELLATIVE f /\
		(!C. f NONE C = NONE) /\
		(!c. c IN s ==> (?c1 c2. f (SOME c1) (SOME c2) = (SOME c))) /\
		(!c. f (SOME total_perm) (SOME c) = NONE) /\
		(!c1 c2. ~(f (SOME c1) (SOME c2) = (SOME c1)))`
*)

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
``
	IS_PERMISSION_STRUCTURE (f, total_perm) = 
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


val var_res_permission_THM = new_specification
  ("var_res_permission_THM", ["var_res_permission_combine", "var_res_permission_split", "var_res_write_permission"],
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
	]));



val var_res_permission_THM2 = save_thm ("var_res_permission_THM2",
	REWRITE_RULE [IS_PERMISSION_STRUCTURE_THM,
		IS_EQ_SPLIT_PERMISSION_STRUCTURE_THM] var_res_permission_THM)


val var_res_read_permission_THM = new_specification
  ("var_res_read_permission_THM", ["var_res_read_permission"],
   prove (``?var_res_read_permission:var_res_permission.
				     ~(var_res_read_permission = var_res_write_permission)``,
            METIS_TAC[var_res_permission_THM2]));


(*--------------------------------------------------------------------------------------------------*)



val _ = type_abbrev("var_res_state", 
	Type `:('pvars |-> ('data # var_res_permission))`);



val VAR_RES_STACK_IS_SEPARATE_def = Define `
	VAR_RES_STACK_IS_SEPARATE s1 s2 =
	!x. 	((x IN (FDOM s1)) /\ (x IN (FDOM s2))) ==>
		((FST (s1 ' x) = FST (s2 ' x)) /\ 
                 (IS_SOME (var_res_permission_combine (SOME (SND (s1 ' x))) (SOME (SND (s2 ' x))))))`;








val fmerge_exists = prove
(``!m f g. 
     ?merge.
       (FDOM merge = FDOM f UNION FDOM g) /\
       (!x. FAPPLY merge x = if ~(x IN FDOM f) then FAPPLY g x else 
					 if ~(x IN FDOM g) then FAPPLY f x else 
					(m (FAPPLY f x) (FAPPLY g x)))``,
GEN_TAC THEN GEN_TAC THEN
INDUCT_THEN fmap_INDUCT ASSUME_TAC THENL [
	Q.EXISTS_TAC `f` THEN
	SIMP_TAC std_ss [FDOM_FEMPTY, UNION_EMPTY, NOT_IN_EMPTY] THEN
	PROVE_TAC[NOT_FDOM_FAPPLY_FEMPTY],


	FULL_SIMP_TAC std_ss [] THEN
	REPEAT STRIP_TAC THEN
	Cases_on `x IN FDOM f` THENL [
		Q.EXISTS_TAC `merge |+ (x, m (f ' x) y)`,
		Q.EXISTS_TAC `merge |+ (x, y)`
	] THEN (
		ASM_SIMP_TAC std_ss [FDOM_FUPDATE] THEN
		REPEAT STRIP_TAC THEN1 (
			SIMP_TAC std_ss [EXTENSION, IN_INSERT, IN_UNION] THEN
			PROVE_TAC[]
		) THEN
		Cases_on `x' = x` THEN (
			ASM_SIMP_TAC std_ss [FAPPLY_FUPDATE_THM, IN_INSERT]
		)
	)
]);




val FMERGE_DEF = new_specification
  ("FMERGE_DEF", ["FMERGE"],
   CONV_RULE (ONCE_DEPTH_CONV SKOLEM_CONV) fmerge_exists);


val FMERGE_FEMPTY = store_thm ("FMERGE_FEMPTY",
	``(FMERGE m f FEMPTY = f) /\
	   (FMERGE m FEMPTY f = f)``,

SIMP_TAC std_ss [GSYM fmap_EQ_THM] THEN
SIMP_TAC std_ss [FMERGE_DEF, FDOM_FEMPTY, NOT_IN_EMPTY,
	UNION_EMPTY]);


val FMERGE_NO_CHANGE = store_thm ("FMERGE_NO_CHANGE",
``	   ((FMERGE m f1 f2 = f1) = 
		(!x. (x IN FDOM f2) ==> (x IN FDOM f1 /\ (m (f1 ' x) (f2 ' x) = (f1 ' x))))) /\
	   ((FMERGE m f1 f2 = f2) = 
		(!x. (x IN FDOM f1) ==> (x IN FDOM f2 /\ (m (f1 ' x) (f2 ' x) = (f2 ' x)))))``,

SIMP_TAC std_ss [GSYM fmap_EQ_THM] THEN
SIMP_TAC std_ss [EXTENSION, FMERGE_DEF, IN_UNION, GSYM FORALL_AND_THM] THEN
STRIP_TAC THENL [
	HO_MATCH_MP_TAC (prove (``(!x. (P x = Q x)) ==> ((!x. P x) = (!x. Q x))``, METIS_TAC[])) THEN
	GEN_TAC THEN
	Cases_on `x IN FDOM f2` THEN (
		ASM_SIMP_TAC std_ss [] THEN
		METIS_TAC[]
	),

	HO_MATCH_MP_TAC (prove (``(!x. (P x = Q x)) ==> ((!x. P x) = (!x. Q x))``, METIS_TAC[])) THEN
	GEN_TAC THEN
	Cases_on `x IN FDOM f1` THEN (
		ASM_SIMP_TAC std_ss [] THEN
		METIS_TAC[]
	)
]);


val FMERGE_COMM = store_thm ("FMERGE_COMM",
	``COMM (FMERGE m) = COMM m``,

SIMP_TAC std_ss [COMM_DEF, GSYM fmap_EQ_THM] THEN
SIMP_TAC std_ss [FMERGE_DEF] THEN
EQ_TAC THEN REPEAT STRIP_TAC THENL [
	POP_ASSUM MP_TAC THEN
	SIMP_TAC std_ss [GSYM LEFT_EXISTS_IMP_THM] THEN
	Q.EXISTS_TAC `FEMPTY |+ (z, x)` THEN
	Q.EXISTS_TAC `FEMPTY |+ (z, y)` THEN
	
	SIMP_TAC std_ss [FDOM_FUPDATE, FDOM_FEMPTY, IN_UNION] THEN
	SIMP_TAC std_ss [IN_SING, FAPPLY_FUPDATE_THM],


	PROVE_TAC [UNION_COMM],


	FULL_SIMP_TAC std_ss [IN_UNION]
]);



val FMERGE_ASSOC = store_thm ("FMERGE_ASSOC",
	``ASSOC (FMERGE m) = ASSOC m``,

SIMP_TAC std_ss [ASSOC_DEF, GSYM fmap_EQ_THM] THEN
SIMP_TAC std_ss [FMERGE_DEF, UNION_ASSOC, IN_UNION] THEN
EQ_TAC THEN REPEAT STRIP_TAC THENL [
	POP_ASSUM MP_TAC THEN
	SIMP_TAC std_ss [GSYM LEFT_EXISTS_IMP_THM] THEN
	Q.EXISTS_TAC `FEMPTY |+ (e, x)` THEN
	Q.EXISTS_TAC `FEMPTY |+ (e, y)` THEN
	Q.EXISTS_TAC `FEMPTY |+ (e, z)` THEN
	Q.EXISTS_TAC `e` THEN	
	SIMP_TAC std_ss [FDOM_FUPDATE, FDOM_FEMPTY, IN_UNION] THEN
	SIMP_TAC std_ss [IN_SING, FAPPLY_FUPDATE_THM],


	ASM_SIMP_TAC std_ss [] THEN
	METIS_TAC[],

	ASM_SIMP_TAC std_ss [] THEN
	METIS_TAC[],

	ASM_SIMP_TAC std_ss [] THEN
	METIS_TAC[]
]);




val FMERGE_DRESTRICT = store_thm ("FMERGE_DRESTRICT",

``DRESTRICT (FMERGE f st1 st2) vs =
  FMERGE f (DRESTRICT st1 vs) (DRESTRICT st2 vs)``,

SIMP_TAC std_ss [GSYM fmap_EQ_THM, 
		 DRESTRICT_DEF, FMERGE_DEF, EXTENSION,
		 IN_INTER, IN_UNION] THEN
METIS_TAC[]);



val FMERGE_EQ_FEMPTY = store_thm ("FMERGE_EQ_FEMPTY",
	``(FMERGE m f g = FEMPTY) =
          (f = FEMPTY) /\ (g = FEMPTY)``,

SIMP_TAC std_ss [GSYM fmap_EQ_THM] THEN
SIMP_TAC (std_ss++boolSimps.CONJ_ss) [FMERGE_DEF, FDOM_FEMPTY, NOT_IN_EMPTY,
	EMPTY_UNION, IN_UNION]);



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
``
	(!s. VAR_RES_STACK_COMBINE NONE s = NONE) /\
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

	(!s1 s2 s x v1 v2 p1 p2. 
			   ((VAR_RES_STACK_COMBINE (SOME s1) (SOME s2) = (SOME s)) /\
			   (x IN FDOM s1) /\ (x IN FDOM s2)) ==>

			   (((FST (s1 ' x)) = (FST (s ' x))) /\ ((FST (s2 ' x)) = (FST (s ' x))) /\
                            (var_res_permission_combine (SOME (SND (s1 ' x))) (SOME (SND (s2 ' x))) = 
                                                        (SOME (SND (s ' x))))))``,


SIMP_TAC std_ss [VAR_RES_STACK_COMBINE_def, BIN_OPTION_MAP_THM, FMERGE_DEF,
		 VAR_RES_STACK_COMBINE___MERGE_FUNC_def] THEN
SIMP_TAC std_ss [COND_RAND, COND_RATOR] THEN
REPEAT STRIP_TAC THENL [
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


	REWRITE_TAC [FMERGE_DEF],
	ASM_SIMP_TAC std_ss [FMERGE_DEF],
	ASM_SIMP_TAC std_ss [FMERGE_DEF],
	ASM_SIMP_TAC std_ss [FMERGE_DEF],
	FULL_SIMP_TAC std_ss [VAR_RES_STACK_IS_SEPARATE_def, FMERGE_DEF],

	ASM_SIMP_TAC std_ss [FMERGE_DEF] THEN
	FULL_SIMP_TAC std_ss [VAR_RES_STACK_IS_SEPARATE_def] THEN
	RES_TAC THEN
	FULL_SIMP_TAC std_ss [IS_SOME_EXISTS]
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





val asl_emp___VAR_RES_STACK_COMBINE = store_thm ("asl_emp___VAR_RES_STACK_COMBINE",
``asl_emp VAR_RES_STACK_COMBINE = {FEMPTY}``,

SIMP_TAC std_ss [asl_emp_def, EXTENSION, IN_ABS, IN_SING,
	VAR_RES_STACK_COMBINE_REWRITE])





val var_res_sl___star_def = Define `var_res_sl___star = asl_star VAR_RES_STACK_COMBINE`
val _ = temp_overload_on ("*", ``var_res_sl___star``);

val var_res_sl___value_perm_of_def = Define `
	var_res_sl___value_perm_of pvar (value,perm:var_res_permission) =  {FEMPTY |+ (pvar, (value, perm))}`;

val var_res_sl___value_of_def = Define `
	var_res_sl___value_of pvar value = asl_exists perm. var_res_sl___value_perm_of pvar (value, perm)`;

val var_res_sl___own_def = Define `
	var_res_sl___own perm pvar = asl_exists v. var_res_sl___value_perm_of pvar (v, perm)`;



val var_res_sl___value_perm_of___asl_star = store_thm ("var_res_sl___value_perm_of___asl_star",
``!pvar v1 p1 v2 p2.
((var_res_sl___value_perm_of pvar (v1,p1)) * (var_res_sl___value_perm_of pvar (v2,p2))) =
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
(((var_res_sl___value_of pvar v1)) * (var_res_sl___value_of pvar v2)) =
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
(((var_res_sl___own p1 pvar)) * (var_res_sl___own p2 pvar)) =
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
		BIN_OPTION_MAP_THM, COND_RAND, COND_RATOR] THEN
	ASM_SIMP_TAC std_ss [GSYM fmap_EQ_THM, FMERGE_DEF,
		FDOM_FUPDATE, FDOM_FEMPTY, IN_SING] THEN
	REPEAT STRIP_TAC THEN
	MATCH_MP_TAC (prove (``(~B) ==> (~A \/ ~B \/ C)``, METIS_TAC[])) THEN
	CCONTR_TAC THEN
	FULL_SIMP_TAC std_ss [IN_UNION, IN_SING]
]);



val var_res_sl___has_write_permission_THM = store_thm ("var_res_sl___has_read_permission_THM",
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
		Cases_on `v IN FDOM q'` THEN1 (
			Cases_on `q' ' v` THEN
			FULL_SIMP_TAC std_ss []
		) THEN
		Q.PAT_ASSUM `FDOM x = X` ASSUME_TAC THEN
		FULL_SIMP_TAC std_ss [IN_UNION, IN_SING]
	],

	ASM_SIMP_TAC std_ss [VAR_RES_STACK_COMBINE_def,
		BIN_OPTION_MAP_THM, COND_RAND, COND_RATOR] THEN
	ASM_SIMP_TAC std_ss [GSYM fmap_EQ_THM, FMERGE_DEF,
		FDOM_FUPDATE, FDOM_FEMPTY, IN_SING] THEN
	REPEAT STRIP_TAC THEN
	MATCH_MP_TAC (prove (``(~B) ==> (~A \/ ~B \/ C)``, METIS_TAC[])) THEN
	CCONTR_TAC THEN
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



(*








var_res_sl___value_of

DB.find "IS_LOCAL_EVAL_ENV"
FASL_IS_LOCAL_EVAL_ENV_def
ASL_IS_INTUITIONISTIC_def

val var_res_expression_def = Hol_datatype
`var_res_expression = var_res_var of 'pvars
				| var_res_const of 'data`


val EVAL_var_res_expression_def = Define `
	(EVAL_var_res_expression (s:('data, 'pvars) var_res_state) (var_res_var (v:'pvars)) =
		if v IN FDOM s then SOME (FST (s ' v)) else NONE) /\
	(EVAL_var_res_expression s (var_res_const d) = SOME d)`


val EVAL_var_res_expression___SUBSTATE = store_thm ("EVAL_var_res_expression___SUBSTATE",
``!s1 s2 e.
ASL_IS_SUBSTATE VAR_RES_STACK_COMBINE s1 s2 /\
IS_SOME (EVAL_var_res_expression s1 e) ==>
(EVAL_var_res_expression s2 e = EVAL_var_res_expression s1 e)``,

Cases_on `e` THEN (
	SIMP_TAC std_ss [EVAL_var_res_expression_def]
) THEN
SIMP_TAC std_ss [COND_RAND, COND_RATOR] THEN
SIMP_TAC std_ss [ASL_IS_SUBSTATE_def] THEN
REPEAT GEN_TAC THEN STRIP_TAC THEN
`FDOM s2 = FDOM s1 UNION FDOM s1'` by ALL_TAC THEN1 (
	IMP_RES_TAC VAR_RES_STACK_COMBINE_REWRITE
) THEN
FULL_SIMP_TAC std_ss [IN_UNION] THEN
Cases_on `p IN FDOM s1'` THENL [
	`?v1 v2 p1 p2. (s1 ' p = (v1,p1)) /\ (s1'  ' p = (v2,p2))` by ALL_TAC THEN1 (
		Cases_on `s1 ' p` THEN
		Cases_on `s1' ' p` THEN
		SIMP_TAC std_ss []
	) THEN
        `?perm. (v1 = v2) /\ (s2 ' p = (v2,perm))` by ALL_TAC THEN1 (
		IMP_RES_TAC VAR_RES_STACK_COMBINE_REWRITE THEN
		ASM_SIMP_TAC std_ss []
	) THEN
	ASM_SIMP_TAC std_ss [],

	IMP_RES_TAC VAR_RES_STACK_COMBINE_REWRITE THEN
	ASM_SIMP_TAC std_ss []
]);



val var_res_pred_def = Hol_datatype `
	var_res_pred = 
	 var_res_pred___eq of ('data, 'pvars) var_res_expression => ('data, 'pvars) var_res_expression
       | var_res_pred___neq of ('data, 'pvars) var_res_expression => ('data, 'pvars) var_res_expression`

val EVAL_var_res_pred_def = Define `
	(EVAL_var_res_pred f (var_res_pred___eq e1 e2) s =
		let d1 = EVAL_var_res_expression s e1 in
		let d2 = EVAL_var_res_expression s e2 in
		IS_SOME d1 /\ IS_SOME d2 /\ (d1 = d2)) /\
	(EVAL_var_res_pred f (var_res_pred___neq e1 e2) s =
		let d1 = EVAL_var_res_expression s e1 in
		let d2 = EVAL_var_res_expression s e2 in
		IS_SOME d1 /\ IS_SOME d2 /\ ~(d1 = d2))`






!p.
ASL_IS_INTUITIONISTIC VAR_RES_STACK_COMBINE (EVAL_var_res_pred VAR_RES_STACK_COMBINE p)


Cases_on `p` THEN (
	SIMP_TAC std_ss [ASL_IS_INTUITIONISTIC___REWRITE,
		VAR_RES_STACK_COMBINE___IS_SEPARATION_COMBINATOR] THEN
	SIMP_TAC std_ss [IN_DEF, EVAL_var_res_pred_def, LET_THM] THEN
	METIS_TAC[EVAL_var_res_expression___SUBSTATE]
)
*)





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
``  (FDOM (VAR_RES_STACK_SPLIT wp1 wp2 st) =  FDOM st DIFF wp2) /\
    (!v. (v IN FDOM st) /\ ~(v IN wp2) ==>
         ((VAR_RES_STACK_SPLIT wp1 wp2 st) ' v =  (FST (st ' v),
                                                  (if (v IN wp1) then SND (st ' v) else
						  (var_res_permission_split (SND (st ' v)))))))``,


SIMP_TAC std_ss [VAR_RES_STACK_SPLIT_def, FUN_FMAP_DEF, FDOM_FINITE, FINITE_DIFF, IN_DIFF,
		 LET_THM, GSYM PAIR_BETA_THM, COND_RATOR, COND_RAND]);


val VAR_RES_STACK_SPLIT12___REWRITES = store_thm ("VAR_RES_STACK_SPLIT12___REWRITES",
``  (FDOM (VAR_RES_STACK_SPLIT1 wp st) =  FDOM st) /\
    (FDOM (VAR_RES_STACK_SPLIT2 wp st) =  FDOM st DIFF wp) /\ 
    (!v. (v IN FDOM st)  ==>
         ((VAR_RES_STACK_SPLIT1 wp st) ' v =  (FST (st ' v),
                                                  (if (v IN wp) then SND (st ' v) else
						  (var_res_permission_split (SND (st ' v))))))) /\
    (!v. (v IN FDOM st) /\ ~(v IN wp) ==>
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






val _ = export_theory();
