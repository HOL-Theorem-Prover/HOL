open HolKernel Parse boolLib bossLib;

(*
quietdec := true;
loadPath := 
            (concat [Globals.HOLDIR, "/examples/separationLogic/src"]) :: 
            (concat [Globals.HOLDIR, "/examples/separationLogic/src/smallfoot"]) :: 
            !loadPath;

map load ["finite_mapTheory", "relationTheory", "congLib", "sortingTheory",
   "rich_listTheory", "generalHelpersTheory", "latticeTheory", "separationLogicTheory",
   "stringTheory",
   "vars_as_resourceTheory", "containerTheory", "separationLogicLib"];
show_assums := true;
*)

open generalHelpersTheory finite_mapTheory relationTheory pred_setTheory congLib sortingTheory
   listTheory rich_listTheory arithmeticTheory operatorTheory optionTheory latticeTheory separationLogicTheory vars_as_resourceTheory;
open stringTheory separationLogicLib BoolExtractShared ConseqConv

(*
quietdec := false;
*)

val _ = new_theory "smallfoot";


val bool_neg_pair_ss = simpLib.conv_ss BOOL_NEG_PAIR_convdata;
val bool_eq_imp_ss = simpLib.conv_ss BOOL_EQ_IMP_convdata;
val bool_extract_common_terms_ss = simpLib.conv_ss BOOL_EXTRACT_SHARED_convdata;
    

val smallfoot_tag = Hol_datatype `smallfoot_tag =
	smallfoot_tag of string`
val smallfoot_tag_11 = DB.fetch "-" "smallfoot_tag_11";

val smallfoot_var = Hol_datatype `smallfoot_var =
	smallfoot_var of string`
val smallfoot_var_11 = DB.fetch "-" "smallfoot_var_11";



val INFINITE_UNIV_STRING = store_thm ("INFINITE_UNIV_STRING",
   ``INFINITE (UNIV:string set)``,

SIMP_TAC std_ss [INFINITE_UNIV] THEN
Q.EXISTS_TAC `\s. c::s` THEN
SIMP_TAC std_ss [CONS_11] THEN
Q.EXISTS_TAC `""` THEN
SIMP_TAC list_ss []);




val INFINITE_UNIV_SMALLFOOT_TAG = store_thm ("INFINITE_UNIV_SMALLFOOT_TAG",
    ``INFINITE (UNIV:smallfoot_tag set)``,

`UNIV:smallfoot_tag set = IMAGE (smallfoot_tag) UNIV` by ALL_TAC THEN1 (
      SIMP_TAC std_ss [EXTENSION, IN_UNIV, IN_IMAGE] THEN
      Cases_on `x` THEN 
      PROVE_TAC[]
) THEN
METIS_TAC[IMAGE_11_INFINITE, INFINITE_UNIV_STRING, smallfoot_tag_11]);



val INFINITE_UNIV_SMALLFOOT_VAR = store_thm ("INFINITE_UNIV_SMALLFOOT_VAR",
    ``INFINITE (UNIV:smallfoot_var set)``,

`UNIV:smallfoot_var set = IMAGE (smallfoot_var) UNIV` by ALL_TAC THEN1 (
      SIMP_TAC std_ss [EXTENSION, IN_UNIV, IN_IMAGE] THEN
      Cases_on `x` THEN 
      PROVE_TAC[]
) THEN
METIS_TAC[IMAGE_11_INFINITE, INFINITE_UNIV_STRING, smallfoot_var_11]);


val INFINITE_UNIV_NUM = store_thm ("INFINITE_UNIV_NUM",
    ``INFINITE (UNIV:num set)``,

SIMP_TAC std_ss [INFINITE_UNIV] THEN
Q.EXISTS_TAC `SUC` THEN
SIMP_TAC std_ss [] THEN
Q.EXISTS_TAC `0` THEN
SIMP_TAC arith_ss []);




val _ = type_abbrev("smallfoot_heap", Type `:num |-> smallfoot_tag |-> num`)
val _ = type_abbrev("smallfoot_stack", Type `:(num, smallfoot_var) var_res_state`)
val _ = type_abbrev("smallfoot_state", Type `:(smallfoot_stack # smallfoot_heap)`)



val smallfoot_separation_combinator_def = Define `
	smallfoot_separation_combinator =
	(PRODUCT_SEPARATION_COMBINATOR VAR_RES_STACK_COMBINE DISJOINT_FMAP_UNION):	smallfoot_state bin_option_function`;

val IS_SEPARATION_ALGEBRA___smallfoot_separation_combinator =
	store_thm ("IS_SEPARATION_ALGEBRA___smallfoot_separation_combinator",
``IS_SEPARATION_ALGEBRA smallfoot_separation_combinator (FEMPTY, FEMPTY)``,

REWRITE_TAC [smallfoot_separation_combinator_def] THEN
MATCH_MP_TAC PRODUCT_SEPARATION_COMBINATOR___ALGEBRA_THM THEN
REWRITE_TAC[VAR_RES_STACK_COMBINE___IS_SEPARATION_ALGEBRA,
	IS_SEPARATION_ALGEBRA___FINITE_MAP]);



val IS_SEPARATION_COMBINATOR___smallfoot_separation_combinator =
	store_thm ("IS_SEPARATION_COMBINATOR___smallfoot_separation_combinator",
``IS_SEPARATION_COMBINATOR smallfoot_separation_combinator``,

PROVE_TAC[IS_SEPARATION_ALGEBRA___IS_COMBINATOR,
	IS_SEPARATION_ALGEBRA___smallfoot_separation_combinator]);


val IS_SOME___smallfoot_separation_combinator = store_thm 
("IS_SOME___smallfoot_separation_combinator",
``IS_SOME (smallfoot_separation_combinator s s') =
?st1 st2 h1 h2. (s = SOME (st1,h1)) /\ (s' = SOME (st2, h2)) /\
	(DISJOINT (FDOM h1) (FDOM h2)) /\ VAR_RES_STACK_IS_SEPARATE st1 st2``,

SIMP_TAC std_ss [smallfoot_separation_combinator_def] THEN
Cases_on `s` THEN1 SIMP_TAC std_ss [PRODUCT_SEPARATION_COMBINATOR_REWRITE] THEN
Cases_on `x` THEN SIMP_TAC std_ss [] THEN
Cases_on `s'` THEN1 SIMP_TAC std_ss [PRODUCT_SEPARATION_COMBINATOR_REWRITE] THEN
Cases_on `x` THEN SIMP_TAC std_ss [] THEN
SIMP_TAC std_ss [PRODUCT_SEPARATION_COMBINATOR_REWRITE, LET_THM, COND_RAND, COND_RATOR] THEN
SIMP_TAC std_ss [DISJOINT_FMAP_UNION_def, BIN_OPTION_MAP_THM, COND_RAND, COND_RATOR,
	VAR_RES_STACK_COMBINE_REWRITE] THEN
METIS_TAC[])


val smallfoot_separation_combinator___REWRITE_helper = prove (``
!s1 s2. smallfoot_separation_combinator (SOME s1) (SOME s2) = 
           (if (VAR_RES_STACK_IS_SEPARATE (FST s1) (FST s2) /\ (DISJOINT (FDOM (SND s1)) (FDOM (SND s2)))) then
              SOME (THE (VAR_RES_STACK_COMBINE (SOME (FST s1)) (SOME (FST s2))),FUNION (SND s1) (SND s2))
            else
              NONE)``,

Cases_on `s1` THEN Cases_on `s2` THEN
SIMP_TAC std_ss [smallfoot_separation_combinator_def,
	PRODUCT_SEPARATION_COMBINATOR_REWRITE, LET_THM,
	DISJOINT_FMAP_UNION_def, BIN_OPTION_MAP_THM] THEN
SIMP_TAC std_ss [COND_RAND, COND_RATOR] THEN
Cases_on `DISJOINT (FDOM r) (FDOM r')` THEN ASM_REWRITE_TAC[] THEN
SIMP_TAC std_ss [VAR_RES_STACK_COMBINE_REWRITE]);



val smallfoot_separation_combinator___REWRITE =
save_thm ("smallfoot_separation_combinator___REWRITE",

let
	val thm0 = IS_SEPARATION_ALGEBRA___smallfoot_separation_combinator;
	val thm1 = SIMP_RULE std_ss [IS_SEPARATION_ALGEBRA_EXPAND_THM] thm0;
in CONJ thm1 smallfoot_separation_combinator___REWRITE_helper end);



val smallfoot_separation_combinator___asl_emp___REWRITE =
store_thm ("smallfoot_separation_combinator___asl_emp___REWRITE",
``(smallfoot_separation_combinator (SOME (FEMPTY,FEMPTY)) X = X) /\
  (smallfoot_separation_combinator X (SOME (FEMPTY,FEMPTY)) = X)``,

Cases_on `X` THEN
SIMP_TAC std_ss [smallfoot_separation_combinator___REWRITE]);



val SOME___smallfoot_separation_combinator = store_thm ("SOME___smallfoot_separation_combinator",
``(smallfoot_separation_combinator (SOME s1) (SOME s2) = SOME s) =

(DISJOINT (FDOM (SND s1)) (FDOM (SND s2)) /\
(VAR_RES_STACK_COMBINE (SOME (FST s1)) (SOME (FST s2)) = SOME (FST s)) /\
((SND s) = FUNION (SND s1) (SND s2)))``,

				
SIMP_TAC std_ss [smallfoot_separation_combinator___REWRITE, COND_NONE_SOME_REWRITES,
SOME___VAR_RES_STACK_COMBINE] THEN
Cases_on `VAR_RES_STACK_IS_SEPARATE (FST s1) (FST s2)` THEN ASM_REWRITE_TAC[] THEN
Cases_on `s` THEN
ASM_SIMP_TAC std_ss [VAR_RES_STACK_COMBINE_EXPAND] THEN
METIS_TAC[]);




val smallfoot_separation_combinator___asl_emp = store_thm ("smallfoot_separation_combinator___asl_emp",
``asl_emp smallfoot_separation_combinator = {(FEMPTY, FEMPTY)}``,

SIMP_TAC std_ss [asl_emp_def, smallfoot_separation_combinator___REWRITE,
	EXTENSION, IN_ABS, IN_SING]);





val smallfoot_data_type = Hol_datatype `smallfoot_data_type = 
	smallfoot_data_num_TYPE
      | smallfoot_data_var_TYPE
      |	smallfoot_data_num_list_TYPE`;


val smallfoot_data = Hol_datatype `smallfoot_data = 
	smallfoot_data_num of num
      | smallfoot_data_var of smallfoot_var
      |	smallfoot_data_num_list of num list`;


val smallfoot_data_type_distinct = DB.fetch "-" "smallfoot_data_type_distinct";
val smallfoot_data_distinct = DB.fetch "-" "smallfoot_data_distinct";
val smallfoot_data_11 = DB.fetch "-" "smallfoot_data_11";


val _ = type_abbrev("smallfoot_typed_data", Type `:(smallfoot_data_type # smallfoot_data)`)


val smallfoot_data_GET_num_def = Define `
  (smallfoot_data_GET_num (smallfoot_data_num n) = n)`;


val smallfoot_data_GET_var_def = Define `
  (smallfoot_data_GET_var (smallfoot_data_var v) = v)`;


val smallfoot_data_GET_num_list_def = Define `
  (smallfoot_data_GET_num_list (smallfoot_data_num_list nl) = nl)`;



val smallfoot_data_IS_WELL_TYPED_def = Define `
  (smallfoot_data_IS_WELL_TYPED (smallfoot_data_num_TYPE, X) = ?n. X = (smallfoot_data_num n)) /\
  (smallfoot_data_IS_WELL_TYPED (smallfoot_data_var_TYPE, X) = ?v. X = (smallfoot_data_var v)) /\
  (smallfoot_data_IS_WELL_TYPED (smallfoot_data_num_list_TYPE, X) = ?nL. X = (smallfoot_data_num_list nL))`


val smallfoot_data_IS_WELL_TYPED___INFER_TYPE_THM =
store_thm ("smallfoot_data_IS_WELL_TYPED___INFER_TYPE_THM",
``(!t n. smallfoot_data_IS_WELL_TYPED (t, smallfoot_data_num n) = (t = smallfoot_data_num_TYPE)) /\
  (!t v. smallfoot_data_IS_WELL_TYPED (t, smallfoot_data_var v) = (t = smallfoot_data_var_TYPE)) /\
  (!t l. smallfoot_data_IS_WELL_TYPED (t, smallfoot_data_num_list l) = (t = smallfoot_data_num_list_TYPE))``,

REPEAT STRIP_TAC THEN
Cases_on `t` THEN (
   SIMP_TAC std_ss [smallfoot_data_IS_WELL_TYPED_def,
		    smallfoot_data_type_distinct,
               	    smallfoot_data_distinct,
                    smallfoot_data_11]
));



val smallfoot_data_IS_WELL_TYPED___SATISFYABLE___THM =
store_thm ("smallfoot_data_IS_WELL_TYPED___SATISFYABLE___THM",
``(!d. ?t. smallfoot_data_IS_WELL_TYPED (t,d)) /\
  (!t. ?d. smallfoot_data_IS_WELL_TYPED (t,d))``,

REPEAT STRIP_TAC THENL [
   Cases_on `d` THEN
   SIMP_TAC std_ss [smallfoot_data_IS_WELL_TYPED___INFER_TYPE_THM],

   Cases_on `t` THEN
   SIMP_TAC std_ss [smallfoot_data_IS_WELL_TYPED_def]
]);





val smallfoot_data_REWRITES = save_thm ("smallfoot_data_REWRITES",

LIST_CONJ [smallfoot_data_type_distinct,
	   smallfoot_data_distinct,
	   smallfoot_data_11,
           smallfoot_data_GET_num_def,
           smallfoot_data_GET_var_def,
           smallfoot_data_GET_num_list_def,
           smallfoot_data_IS_WELL_TYPED_def,
	   smallfoot_data_IS_WELL_TYPED___SATISFYABLE___THM,
	   smallfoot_data_IS_WELL_TYPED___INFER_TYPE_THM]);


val smallfoot_data_GET_REWRITES = save_thm ("smallfoot_data_GET_REWRITES",

LIST_CONJ [smallfoot_data_GET_num_def,
           smallfoot_data_GET_var_def,
           smallfoot_data_GET_num_list_def]);



val _ = type_abbrev("smallfoot_a_expression", Type `:smallfoot_stack -> num option`)

val smallfoot_ae_var_def = Define `smallfoot_ae_var var = (\stack:smallfoot_stack. 
(if (var IN FDOM stack) then SOME (FST (stack ' var)) else NONE))`;

val smallfoot_ae_const_def = Define `smallfoot_ae_const c = (K (SOME c)):smallfoot_a_expression`;
val smallfoot_ae_null_def = Define `smallfoot_ae_null = smallfoot_ae_const 0`;

val smallfoot_ae_binop_def = Define `
smallfoot_ae_binop (bop:num->num->num) e1 e2 =
	(\s:smallfoot_stack. 
		let no1 = e1 s in
		let no2 = e2 s in
		if ((IS_SOME no1) /\ (IS_SOME no2)) then SOME (bop (THE no1) (THE no2)) else NONE)`



val smallfoot_ae_binop___const_eval = store_thm ("smallfoot_ae_binop___const_eval",
``smallfoot_ae_binop bop (smallfoot_ae_const c1) (smallfoot_ae_const c2) =
  smallfoot_ae_const (bop c1 c2)``,

SIMP_TAC std_ss [smallfoot_ae_binop_def, smallfoot_ae_const_def, 
		 LET_THM, FUN_EQ_THM]);

val smallfoot_ae_binop___null_eval = store_thm ("smallfoot_ae_binop___null_eval",
``(smallfoot_ae_binop bop smallfoot_ae_null (smallfoot_ae_const c2) =
   smallfoot_ae_const (bop 0 c2)) /\
  (smallfoot_ae_binop bop (smallfoot_ae_const c1) smallfoot_ae_null =
   smallfoot_ae_const (bop c1 0)) /\
  (smallfoot_ae_binop bop smallfoot_ae_null smallfoot_ae_null =
   smallfoot_ae_const (bop 0 0))
``,

SIMP_TAC std_ss [smallfoot_ae_null_def, 
		 smallfoot_ae_binop___const_eval]);


val smallfoot_ae_eq_THM = store_thm ("smallfoot_ae_eq_THM",
	``((smallfoot_ae_var v1 = smallfoot_ae_var v2) = (v1 = v2)) /\
	   ((smallfoot_ae_const c1 = smallfoot_ae_const c2) = (c1 = c2)) /\
	   (~(smallfoot_ae_const c = smallfoot_ae_var v))``,

SIMP_TAC std_ss [FUN_EQ_THM, 
	smallfoot_ae_var_def, smallfoot_ae_const_def] THEN
CONJ_TAC THENL [
	EQ_TAC THEN SIMP_TAC std_ss [] THEN
	STRIP_TAC THEN
	CCONTR_TAC THEN
	`?s:smallfoot_stack. s = FEMPTY |+ (v1,(0,var_res_write_permission))` by METIS_TAC[] THEN
	Q.PAT_ASSUM `!x. P x` (MP_TAC o Q.SPEC `s`) THEN
	ASM_SIMP_TAC std_ss [FDOM_FEMPTY, FDOM_FUPDATE,
		IN_SING],

	Q.EXISTS_TAC `FEMPTY` THEN
	SIMP_TAC std_ss [FDOM_FEMPTY, NOT_IN_EMPTY]
]);


val smallfoot_ae_eq_null_THM = store_thm ("smallfoot_ae_eq_null_THM",
	``(~(smallfoot_ae_var v = smallfoot_ae_null)) /\
	   ((smallfoot_ae_const c = smallfoot_ae_null) = (c = 0))``,
SIMP_TAC std_ss [smallfoot_ae_null_def, smallfoot_ae_eq_THM]);


val SOME___smallfoot_ae_const = store_thm ("SOME___smallfoot_ae_const",
``!c c1 X. 
  (smallfoot_ae_const c X = SOME c1) =
  (c = c1)``,

SIMP_TAC std_ss [smallfoot_ae_const_def]);


val smallfoot_ae_is_const_def = Define `
    smallfoot_ae_is_const e = ?n. e = smallfoot_ae_const n`;


val _ = type_abbrev("smallfoot_a_proposition", Type `:smallfoot_state -> bool`);

val smallfoot_ae_is_defined_def = Define `smallfoot_ae_is_defined P ae = 
(!h st. (P:smallfoot_a_proposition) (st,h) ==>
	IS_SOME ((ae st):num option))`;


val smallfoot_ae_is_list_cond_defined_def = Define `
smallfoot_ae_is_list_cond_defined P L =
 ((FST P):bool, \s:smallfoot_state. s IN (SND P) /\ EVERY (\e. IS_SOME ((e (FST s)):num option)) L)`




val smallfoot_ap_implies_readperms_def = Define `smallfoot_ap_implies_readperms P vs = 
(!h st. (P:smallfoot_a_proposition) (st,h) ==>
	vs SUBSET FDOM st)`;


val smallfoot_ap_implies_writeperm_def = Define `smallfoot_ap_implies_writeperm P v = 
(!h st. (P:smallfoot_a_proposition) (st,h) ==>
	var_res_sl___has_write_permission v st)`;


val smallfoot_ae_stack_read_def = Define `smallfoot_ae_stack_read e t (s:smallfoot_state) =
if (?loc. (e (FST s) = SOME loc) /\ ~(loc = 0) /\ (loc IN FDOM (SND s)) /\
	  (t IN FDOM ((SND s) ' loc))) then
  SOME ((SND s) ' (THE (e (FST s))) ' t)
else
  NONE`;


val smallfoot_ap_implies_stack_read_def = Define `smallfoot_ap_implies_stack_read P e t = 
(!s. s IN (P:smallfoot_a_proposition) ==>
        IS_SOME (smallfoot_ae_stack_read e t s))`


val smallfoot_ap_implies_in_heap_def = Define `smallfoot_ap_implies_in_heap P e = 
(!h st. (P:smallfoot_a_proposition) (st,h) ==>
        IS_SOME (e st) /\ ((THE (e st)) IN (FDOM h)) /\ (~((THE (e st)) = 0)))`;





val smallfoot_a_stack_proposition_def = Define `smallfoot_a_stack_proposition emp sp = \state:smallfoot_state. ((SND state = FEMPTY) \/ ~emp) /\ ((sp (FST state)))`

val smallfoot_ap_binexpression_def = Define `
smallfoot_ap_binexpression emp p e1 e2 =
	smallfoot_a_stack_proposition emp (\s. 
		let (no1:num option) = e1 s in
		let (no2:num option) = e2 s in
		((IS_SOME no1) /\ (IS_SOME no2) /\ (p (THE no1) (THE no2))))`


val smallfoot_ap_equal_def = Define `smallfoot_ap_equal p1 p2 =
	smallfoot_ap_binexpression T $= p1 p2`;
val smallfoot_ap_unequal_def = Define `smallfoot_ap_unequal p1 p2 = 
	smallfoot_ap_binexpression T (\n1 n2. ~(n1 = n2)) p1 p2`;

val smallfoot_ap_weak_equal_def = Define `smallfoot_ap_weak_equal p1 p2 = 
	smallfoot_ap_binexpression F $= p1 p2`;
val smallfoot_ap_weak_unequal_def = Define `smallfoot_ap_weak_unequal p1 p2 = 
	smallfoot_ap_binexpression F (\n1 n2. ~(n1 = n2)) p1 p2`;

val smallfoot_ap_less_def = Define `smallfoot_ap_less p1 p2 =
	smallfoot_ap_binexpression T $< p1 p2`;
val smallfoot_ap_lesseq_def = Define `smallfoot_ap_lesseq p1 p2 =
	smallfoot_ap_binexpression T $<= p1 p2`;
val smallfoot_ap_greater_def = Define `smallfoot_ap_greater p1 p2 =
	smallfoot_ap_binexpression T $> p1 p2`;
val smallfoot_ap_greatereq_def = Define `smallfoot_ap_greatereq p1 p2 =
	smallfoot_ap_binexpression T $>= p1 p2`;


val smallfoot_ap_var_write_perm_val_def = Define `smallfoot_ap_var_write_perm_val v e (state:smallfoot_state) =
	(SND state = FEMPTY) /\ (v IN FDOM (FST state)) /\
	(IS_SOME (e (FST state))) /\ ((FST state) ' v = (THE (e (FST state)), var_res_write_permission))`;

val smallfoot_ap_var_write_perm_def = Define `
smallfoot_ap_var_write_perm v = asl_exists e. smallfoot_ap_var_write_perm_val v e`


val smallfoot_ap_true_def = Define `smallfoot_ap_true = 
	asl_true:smallfoot_a_proposition`;
val smallfoot_ap_false_def = Define `smallfoot_ap_false = 
	asl_false:smallfoot_a_proposition`;
val smallfoot_ap_star_def = Define `smallfoot_ap_star = 
	asl_star smallfoot_separation_combinator`;
val smallfoot_ap_bigstar_def = Define `smallfoot_ap_bigstar = 
	asl_bigstar smallfoot_separation_combinator`;
val smallfoot_ap_bigstar_list_def = Define `smallfoot_ap_bigstar_list = 
	asl_bigstar_list smallfoot_separation_combinator`;
val smallfoot_ap_emp_def = Define `smallfoot_ap_emp =
	asl_emp smallfoot_separation_combinator`
val smallfoot_ap_unknown_def = Define `smallfoot_ap_unknown s =
	smallfoot_ap_emp`;


val smallfoot_ap_emp_ALTERNATIVE_DEF = store_thm
    ("smallfoot_ap_emp_ALTERNATIVE_DEF",
     ``smallfoot_ap_emp = \x. (FST x = FEMPTY) /\ (SND x = FEMPTY)``,				
     SIMP_TAC std_ss [smallfoot_ap_emp_def, smallfoot_separation_combinator___asl_emp,
		      EXTENSION, IN_ABS, PAIR_FORALL_THM, IN_SING]);



val smallfoot_ap_bigstar_REWRITE = save_thm ("smallfoot_ap_bigstar_REWRITE",
	let 
		val thm0 = Q.ISPEC `smallfoot_separation_combinator` asl_bigstar_REWRITE;
		val thm1 = SIMP_RULE std_ss
 [IS_SEPARATION_COMBINATOR___smallfoot_separation_combinator,
	GSYM smallfoot_ap_bigstar_def, GSYM smallfoot_ap_emp_def,
	GSYM smallfoot_ap_star_def] thm0;
	in
		thm1
	end);



val smallfoot_ap_bigstar_list_REWRITE = save_thm ("smallfoot_ap_bigstar_list_REWRITE",
	let 
		val thm0 = Q.ISPEC `smallfoot_separation_combinator` asl_bigstar_list_REWRITE;
		val thm1 = SIMP_RULE std_ss
 [GSYM smallfoot_ap_bigstar_list_def, GSYM smallfoot_ap_emp_def,
  GSYM smallfoot_ap_star_def] thm0;
	in
		thm1
	end);

val smallfoot_ap_stack_true_def = Define `
   smallfoot_ap_stack_true:smallfoot_a_proposition = \s. (SND s = FEMPTY)`



val LISTS_TO_FMAP_def = Define `
	(LISTS_TO_FMAP ([], []) = FEMPTY) /\
	(LISTS_TO_FMAP (key::keyL, value::valL) = FUPDATE (LISTS_TO_FMAP (keyL, valL)) (key,value))`;


val FEVERY_LISTS_TO_FMAP = store_thm ("FEVERY_LISTS_TO_FMAP",
``
!P l1 l2.
((LENGTH l1 = LENGTH l2) /\
 (!e. MEM e (ZIP (l1,l2)) ==> P e)) ==>
FEVERY P (LISTS_TO_FMAP (l1,l2))``,

Induct_on `l1` THENL [
  Cases_on `l2` THEN
  SIMP_TAC list_ss [] THEN
  SIMP_TAC std_ss [LISTS_TO_FMAP_def, FEVERY_FEMPTY],


  Cases_on `l2` THEN
  SIMP_TAC list_ss [] THEN
  SIMP_TAC std_ss [LISTS_TO_FMAP_def, FEVERY_FUPDATE,
		   DISJ_IMP_THM, FORALL_AND_THM] THEN
  REPEAT STRIP_TAC THEN
  `FEVERY P (LISTS_TO_FMAP (l1,t))` by RES_TAC THEN
  FULL_SIMP_TAC std_ss [FEVERY_DEF, DRESTRICT_DEF, IN_INTER]
]);


val FMAP_MAP___LISTS_TO_FMAP = store_thm (
"FMAP_MAP___LISTS_TO_FMAP",
``!f l1 l2. (LENGTH l1 = LENGTH l2) ==>
(FMAP_MAP f (LISTS_TO_FMAP (l1,l2)) =
LISTS_TO_FMAP (l1, MAP f l2))``,


GEN_TAC THEN
Induct_on `l1` THENL [
   Cases_on `l2` THEN
   SIMP_TAC list_ss [LISTS_TO_FMAP_def, FMAP_MAP_FEMPTY],

   Cases_on `l2` THEN
   ASM_SIMP_TAC list_ss [LISTS_TO_FMAP_def, FMAP_MAP_FUPDATE]
]);


val smallfoot_ap_points_to_def = Define `
	smallfoot_ap_points_to e1 L = \state:smallfoot_state.
		let (stack,heap) = (FST state, SND state) in 
		let loc_opt = (e1 stack) in (
		IS_SOME (loc_opt) /\
		let (loc = THE loc_opt) in (
		~(loc = 0) /\
		((FDOM heap)= {loc}) /\
		(FEVERY (\(tag,exp).
				(tag IN FDOM (heap ' loc)) /\
				(IS_SOME (exp stack)) /\
				(THE (exp stack) = heap ' loc ' tag)) L)))`;


val smallfoot_ap_tree_seg_num_def = Define `
  smallfoot_ap_tree_seg_num n bal tagL startExp endExp =
  (asl_rec_pred_num smallfoot_separation_combinator bal n (smallfoot_ap_equal endExp) 
      (smallfoot_ap_weak_unequal endExp)
      (MAP (\t e1 e2 s. smallfoot_ae_is_const e2) tagL)
      (\e eL. smallfoot_ap_points_to e (LISTS_TO_FMAP (tagL, eL))) startExp)`;



val smallfoot_ap_tree_seg_num_REWRITE = save_thm ("smallfoot_ap_tree_seg_num_REWRITE",
   let 
      val thm0 = smallfoot_ap_tree_seg_num_def;
      val gsym = GSYM (Drule.RIGHT_ETA (MK_ABS (Q.GEN `startExp` (SPEC_ALL thm0))));
      val thm1 = SIMP_RULE std_ss [asl_rec_pred_num_REWRITE_BOTH,
				   gsym] thm0
      val thm2 = SIMP_RULE list_ss [asl_choose_pred_args_def,
         IS_SEPARATION_COMBINATOR___smallfoot_separation_combinator,
         asl_bool_REWRITES, MAP_MAP_o, combinTheory.o_DEF] thm1;
      val thm3 = SIMP_RULE (list_ss++boolSimps.CONJ_ss) [EVERY_MEM, MEM_ZIP,
			GSYM LEFT_FORALL_IMP_THM, EL_MAP,
	                asl_bigstar_list_REWRITE] thm2
      val thm4 = SIMP_RULE list_ss [GSYM smallfoot_ap_star_def,
                                    GSYM smallfoot_ap_bigstar_list_def] thm3;
   in
      thm4
   end);


val smallfoot_ap_tree_seg_num_REWRITE = save_thm ("smallfoot_ap_tree_seg_num_REWRITE",
   let 
      val thm0 = smallfoot_ap_tree_seg_num_def;
      val gsym = GSYM (Drule.RIGHT_ETA (MK_ABS (Q.GEN `startExp` (SPEC_ALL thm0))));
      val thm1 = SIMP_RULE std_ss [asl_rec_pred_num_REWRITE_BOTH,
				   gsym] thm0
      val thm2 = SIMP_RULE list_ss [asl_choose_pred_args_def,
         IS_SEPARATION_COMBINATOR___smallfoot_separation_combinator,
         asl_bool_REWRITES, MAP_MAP_o, combinTheory.o_DEF] thm1;
      val thm3 = SIMP_RULE (list_ss++boolSimps.CONJ_ss) [EVERY_MEM, MEM_ZIP,
			GSYM LEFT_FORALL_IMP_THM, EL_MAP,
	                asl_bigstar_list_REWRITE] thm2
      val thm4 = SIMP_RULE list_ss [GSYM smallfoot_ap_star_def,
                                    GSYM smallfoot_ap_bigstar_list_def] thm3;
   in
      thm4
   end);


val smallfoot_ap_tree_seg_num_REWRITE_2 = save_thm ("smallfoot_ap_tree_seg_num_REWRITE_2",
   let 
      val thm0 = SIMP_RULE std_ss [] (SPEC ``0:num`` smallfoot_ap_tree_seg_num_REWRITE)

      val thm1a = SIMP_RULE arith_ss [] (SPEC ``SUC n`` smallfoot_ap_tree_seg_num_REWRITE)
      val thm1 = GEN ``n:num`` thm1a 
   in
      CONJ thm0 thm1
   end);



val smallfoot_ap_tree_seg_def = Define `
  smallfoot_ap_tree_seg bal tagL startExp endExp =
  asl_exists n. smallfoot_ap_tree_seg_num n bal tagL startExp endExp`;






val smallfoot_ap_bintree_num_def = Define `
   smallfoot_ap_bintree_num n (lt,rt) startExp =
   smallfoot_ap_tree_seg_num n F [lt;rt] startExp smallfoot_ae_null`;

val smallfoot_ap_bintree_def = Define `
   smallfoot_ap_bintree (lt,rt) startExp =
   asl_exists n. smallfoot_ap_bintree_num n (lt,rt) startExp`;



val smallfoot_ap_bintree_num_REWRITE = save_thm ("smallfoot_ap_bintree_num_REWRITE",
   let 
      val thm0 = smallfoot_ap_bintree_num_def;
      val thm1 = SIMP_RULE list_ss [
         smallfoot_ap_tree_seg_num_def, GSYM asl_rec_pred_def] thm0;
      val gsym = Drule.RIGHT_ETA (GSYM (Drule.RIGHT_ETA (MK_ABS (Q.GEN `startExp` (SPEC_ALL thm1)))));
      val thm2 = SIMP_RULE std_ss [gsym,
         asl_rec_pred_num_REWRITE] thm1;
      val thm3 = SIMP_RULE list_ss [asl_choose_pred_args___2EL,
         IS_SEPARATION_COMBINATOR___smallfoot_separation_combinator,
         asl_bool_REWRITES] thm2;
      val thm4 = SIMP_RULE list_ss [GSYM smallfoot_ap_bintree_def,
         GSYM smallfoot_ap_star_def,LISTS_TO_FMAP_def] thm3;
      val thm5 = SIMP_RULE list_ss [asl_bool_EVAL, asl_exists_def, IN_ABS,
				    smallfoot_ae_is_const_def,
				    GSYM LEFT_EXISTS_AND_THM,
				    GSYM RIGHT_EXISTS_AND_THM] thm4;
      val thm6 = SIMP_RULE list_ss [asl_exists___GSYM_REWRITE,
				    IN_ABS3] thm5;
   in
      thm6
   end);



val smallfoot_ap_bintree_REWRITE = save_thm ("smallfoot_ap_bintree_REWRITE",
   let 
      val thm0 = smallfoot_ap_bintree_def;
      val thm1 = SIMP_RULE list_ss [smallfoot_ap_tree_seg_num_def,
         smallfoot_ap_bintree_num_def] thm0;
      val thm2 = SIMP_RULE list_ss [GSYM asl_rec_pred_def] thm1;
      val gsym = GSYM (Drule.RIGHT_ETA (MK_ABS (Q.GEN `startExp` (SPEC_ALL thm2))));

      val thm2a = SIMP_RULE std_ss [asl_rec_pred_unbalanced___REWRITE,
      IS_SEPARATION_COMBINATOR___smallfoot_separation_combinator, gsym] thm2;


      val thm3 = SIMP_RULE list_ss [asl_choose_pred_args___2EL,
         IS_SEPARATION_COMBINATOR___smallfoot_separation_combinator,
         asl_bool_REWRITES] thm2a;
      val thm4 = SIMP_RULE list_ss [GSYM smallfoot_ap_bintree_def,
         GSYM smallfoot_ap_star_def,LISTS_TO_FMAP_def] thm3;
      val thm5 = SIMP_RULE list_ss [asl_bool_EVAL, asl_exists_def, IN_ABS,
				    smallfoot_ae_is_const_def,
				    GSYM LEFT_EXISTS_AND_THM,
				    GSYM RIGHT_EXISTS_AND_THM] thm4;
      val thm6 = SIMP_RULE list_ss [asl_exists___GSYM_REWRITE,
				    IN_ABS3] thm5;
   in
      thm6
   end);






val SWAP_asl_exists_THM = store_thm ("SWAP_asl_exists_THM",
	``!P. (asl_exists x y. P x y) = (asl_exists y x. P x y)``,

SIMP_TAC std_ss [FUN_EQ_THM, asl_exists_def, IN_ABS] THEN
METIS_TAC[]);


val smallfoot_ap_star___PROPERTIES = save_thm ("smallfoot_ap_star___PROPERTIES",
	let 
		val thm0  = asl_star___PROPERTIES;
		val thm1 = ISPEC ``smallfoot_separation_combinator`` thm0;
		val thm2 = REWRITE_RULE [IS_SEPARATION_COMBINATOR___smallfoot_separation_combinator,
		GSYM smallfoot_ap_star_def, GSYM smallfoot_ap_emp_def] thm1;
	in
		thm2
	end);


val smallfoot_ap_false___smallfoot_ap_star_THM =
save_thm ("smallfoot_ap_false___smallfoot_ap_star_THM",

let
   val thm0 = ISPEC ``smallfoot_separation_combinator``
              (Q.SPEC `x` (GEN_ALL asl_false___asl_star_THM));
   val thm1 = REWRITE_RULE [GSYM smallfoot_ap_star_def,
			    GSYM smallfoot_ap_false_def]
	      thm0
in
  thm1
end);

val asl_exists___smallfoot_ap_star_THM = save_thm ("asl_exists___smallfoot_ap_star_THM",
REWRITE_RULE [GSYM smallfoot_ap_star_def]
(ISPEC ``smallfoot_separation_combinator`` asl_exists___asl_star_THM));


val smallfoot_ap_false___NOT_IN = 
store_thm ("smallfoot_ap_false___NOT_IN",
``!x. ~(x IN smallfoot_ap_false)``,
SIMP_TAC std_ss [smallfoot_ap_false_def, asl_bool_EVAL]);


val smallfoot_ap_star___swap = store_thm ("smallfoot_ap_star___swap",

``smallfoot_ap_star p1 (smallfoot_ap_star p2 p3) =
  smallfoot_ap_star p2 (smallfoot_ap_star p1 p3)``,

METIS_TAC[ASSOC_DEF, COMM_DEF, smallfoot_ap_star___PROPERTIES]);




val smallfoot_ap_star___swap_ap_stack_true = store_thm ("smallfoot_ap_star___swap_ap_stack_true",

``smallfoot_ap_star smallfoot_ap_stack_true (smallfoot_ap_star p1 p2) =
  smallfoot_ap_star p1 (smallfoot_ap_star smallfoot_ap_stack_true p2)``,

METIS_TAC[smallfoot_ap_star___swap]);



val smallfoot_ap_bintree_num___TAG_SYM = store_thm ("smallfoot_ap_bintree_num___TAG_SYM",
``	smallfoot_ap_bintree_num n (lt,rt) = smallfoot_ap_bintree_num n (rt,lt)``,

Cases_on `lt = rt` THEN1 ASM_REWRITE_TAC[] THEN
Induct_on `n` THENL [
	SIMP_TAC std_ss [FUN_EQ_THM] THEN
	ONCE_REWRITE_TAC[smallfoot_ap_bintree_num_REWRITE] THEN
	REWRITE_TAC[],



	SIMP_TAC std_ss [FUN_EQ_THM] THEN
	ONCE_REWRITE_TAC[smallfoot_ap_bintree_num_REWRITE] THEN
	SIMP_TAC arith_ss [] THEN
	STRIP_ASSUME_TAC smallfoot_ap_star___PROPERTIES THEN
	REPEAT GEN_TAC THEN
	AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
	HO_MATCH_MP_TAC (prove (``(!p q. (P p q = Q q p)) ==>
		      ((asl_exists p q. P p q) = (asl_exists p q. Q p q))``,
		      SIMP_TAC std_ss [FUN_EQ_THM, asl_exists_def, IN_ABS] THEN
		      METIS_TAC[])) THEN
	METIS_TAC[COMM_DEF, FUPDATE_COMMUTES]
]);


val smallfoot_ap_bintree___TAG_SYM = store_thm ("smallfoot_ap_bintree___TAG_SYM",
``smallfoot_ap_bintree (lt,rt) = smallfoot_ap_bintree (rt,lt)``,

SIMP_TAC std_ss [smallfoot_ap_bintree_def, FUN_EQ_THM,
	asl_exists_def] THEN
METIS_TAC[smallfoot_ap_bintree_num___TAG_SYM]);





val smallfoot_ap_list_seg_num_def = Define `
   smallfoot_ap_list_seg_num n tl startExp endExp =
   smallfoot_ap_tree_seg_num n T [tl] startExp endExp`;

val smallfoot_ap_list_seg_num_REWRITE = save_thm ("smallfoot_ap_list_seg_num_REWRITE",
   let 
      val thm0 = smallfoot_ap_list_seg_num_def;
      val thm1 = SIMP_RULE list_ss [smallfoot_ap_tree_seg_num_def] thm0;
      val gsym = GSYM (Drule.RIGHT_ETA (MK_ABS (Q.GEN `startExp` (SPEC_ALL thm1))));
      val thm2 = SIMP_RULE std_ss [asl_rec_pred_num_REWRITE, gsym] thm1;
      val thm3 = SIMP_RULE list_ss [asl_choose_pred_args___SING,
         IS_SEPARATION_COMBINATOR___smallfoot_separation_combinator,
         asl_bool_REWRITES, LISTS_TO_FMAP_def] thm2;
      val thm4 = SIMP_RULE list_ss [GSYM smallfoot_ap_star_def] thm3;
      val thm5 = SIMP_RULE list_ss [asl_bool_EVAL, asl_exists_def, IN_ABS,
				    smallfoot_ae_is_const_def,
				    GSYM LEFT_EXISTS_AND_THM,
				    GSYM RIGHT_EXISTS_AND_THM] thm4;
      val thm6 = SIMP_RULE list_ss [asl_exists___GSYM_REWRITE,
				    IN_ABS3] thm5;
   in
      thm6
   end);


val smallfoot_ap_list_seg_num_REWRITE_2 = save_thm ("smallfoot_ap_list_seg_num_REWRITE_2",
   let 
      val thm0 = SIMP_RULE std_ss [] (SPEC ``0:num`` smallfoot_ap_list_seg_num_REWRITE)

      val thm1a = SIMP_RULE arith_ss [] (SPEC ``SUC n`` smallfoot_ap_list_seg_num_REWRITE)
      val thm1 = GEN ``n:num`` thm1a 
   in
      CONJ thm0 thm1
   end);



val smallfoot_ap_list_seg_def = Define `
   smallfoot_ap_list_seg tl startExp endExp =
   asl_exists n. smallfoot_ap_list_seg_num n tl startExp endExp`

val smallfoot_ap_list_def = Define `
   smallfoot_ap_list tl startExp =
   smallfoot_ap_list_seg tl startExp smallfoot_ae_null`


val smallfoot_ap_list_seg_REWRITE = save_thm ("smallfoot_ap_list_seg_REWRITE",
   let 
      val thm0 = smallfoot_ap_list_seg_def;
      val thm1 = SIMP_RULE list_ss [smallfoot_ap_tree_seg_num_def,
         smallfoot_ap_list_seg_num_def] thm0;
      val thm2 = SIMP_RULE std_ss [GSYM asl_rec_sing_pred___BALANCED_UNBALANCED,
         IS_SEPARATION_COMBINATOR___smallfoot_separation_combinator,
         GSYM asl_rec_sing_pred_num_def, GSYM asl_rec_sing_pred_def] thm1;
      val thm3 = SIMP_RULE list_ss [asl_rec_sing_pred_def,
          asl_rec_sing_pred_num_def, GSYM asl_rec_pred_def] thm2;
      val gsym = GSYM (Drule.RIGHT_ETA (MK_ABS (Q.GEN `startExp` (SPEC_ALL thm3))));

      val thm4 = SIMP_RULE std_ss [asl_rec_pred_unbalanced___REWRITE,
      IS_SEPARATION_COMBINATOR___smallfoot_separation_combinator, gsym] thm3;

      val thm5 = SIMP_RULE list_ss [asl_choose_pred_args___SING,
         IS_SEPARATION_COMBINATOR___smallfoot_separation_combinator,
         asl_bool_REWRITES, LISTS_TO_FMAP_def] thm4;
      val thm6 = SIMP_RULE list_ss [GSYM smallfoot_ap_star_def] thm5;

      val thm7 = SIMP_RULE list_ss [asl_bool_EVAL, asl_exists_def, IN_ABS,
				    smallfoot_ae_is_const_def,
				    GSYM LEFT_EXISTS_AND_THM,
				    GSYM RIGHT_EXISTS_AND_THM] thm6;
      val thm8 = SIMP_RULE list_ss [asl_exists___GSYM_REWRITE,
				    IN_ABS3] thm7;

   in
      thm8
   end);


val smallfoot_ap_list_seg___UNBALANCED_DEF = store_thm (
"smallfoot_ap_list_seg___UNBALANCED_DEF",
``smallfoot_ap_list_seg tl startExp endExp =
  smallfoot_ap_tree_seg F [tl] startExp endExp``,

SIMP_TAC list_ss [smallfoot_ap_list_seg_num_def,
		 smallfoot_ap_tree_seg_num_def,
		 smallfoot_ap_list_seg_def,
		 smallfoot_ap_tree_seg_def,
		 GSYM asl_rec_sing_pred_num_def,
		 GSYM asl_rec_sing_pred_def,
		 asl_rec_sing_pred___BALANCED_UNBALANCED,
		 IS_SEPARATION_COMBINATOR___smallfoot_separation_combinator]);




val smallfoot_ap_list_REWRITE = save_thm ("smallfoot_ap_list_REWRITE",
   let 
      val thm0 = smallfoot_ap_list_def;
      val thm1 = ONCE_REWRITE_RULE [smallfoot_ap_list_seg_REWRITE] thm0;
      val thm2 = REWRITE_RULE [GSYM smallfoot_ap_list_def] thm1
   in
      thm2
   end);




val smallfoot_ap_data_list_seg_num_def = Define `
  (smallfoot_ap_data_list_seg_num 0 tl startExp data endExp = 
    (asl_and (smallfoot_ap_equal endExp startExp) 
             (\s. FEVERY (\x. (SND x) = []) data))) /\

  (smallfoot_ap_data_list_seg_num (SUC n) tl startExp data endExp = 
    (asl_and (smallfoot_ap_weak_unequal endExp startExp) 
     (asl_and (\s. FEVERY (\x. ~((SND x) = [])) data)
      asl_exists n'. smallfoot_ap_star
                      (smallfoot_ap_points_to startExp
		         ((FMAP_MAP (\dl. smallfoot_ae_const (HD dl)) data) |+
                                   (tl,smallfoot_ae_const n')))
                      (smallfoot_ap_data_list_seg_num n tl
		         (smallfoot_ae_const n') (FMAP_MAP TL data) endExp)
     )))`;



val smallfoot_ap_data_list_seg_num_REWRITE = store_thm ("smallfoot_ap_data_list_seg_num_REWRITE",
``smallfoot_ap_data_list_seg_num n tl startExp data endExp = 
  if (n = 0) then
    (asl_and (smallfoot_ap_equal endExp startExp) 
             (\s. FEVERY (\x. (SND x) = []) data))
  else
  ((asl_and (smallfoot_ap_weak_unequal endExp startExp) 
     (asl_and (\s. FEVERY (\x. ~((SND x) = [])) data)
      asl_exists n'. smallfoot_ap_star
                      (smallfoot_ap_points_to startExp
		         ((FMAP_MAP (\dl. smallfoot_ae_const (HD dl)) data) |+
                                   (tl,smallfoot_ae_const n')))
                      (smallfoot_ap_data_list_seg_num (PRE n) tl
		         (smallfoot_ae_const n') (FMAP_MAP TL data) endExp)
     )))``,

Cases_on `n` THEN
SIMP_TAC arith_ss [smallfoot_ap_data_list_seg_num_def]);




val smallfoot_ap_data_list_seg_num___NO_DATA =
store_thm ("smallfoot_ap_data_list_seg_num___NO_DATA",

``!n tl startExp endExp.
  smallfoot_ap_data_list_seg_num n tl startExp FEMPTY endExp =
  smallfoot_ap_list_seg_num n tl startExp endExp``,

Induct_on `n` THENL [
   ONCE_REWRITE_TAC[smallfoot_ap_list_seg_num_REWRITE] THEN
   SIMP_TAC std_ss [smallfoot_ap_data_list_seg_num_def,
		    FEVERY_FEMPTY, asl_bool_REWRITES],

   
   ONCE_REWRITE_TAC[smallfoot_ap_list_seg_num_REWRITE] THEN
   ASM_SIMP_TAC arith_ss [smallfoot_ap_data_list_seg_num_def,
		      FMAP_MAP_FEMPTY, FEVERY_FEMPTY,
		      asl_bool_REWRITES]
]);




val smallfoot_ap_data_list_seg_num___DATA_LENGTH =
store_thm ("smallfoot_ap_data_list_seg_num___DATA_LENGTH",

``!n data tl startExp endExp.

  ~(FEVERY (\x. LENGTH (SND x) = n) data) ==>
  (smallfoot_ap_data_list_seg_num n tl startExp data endExp =
   smallfoot_ap_false)``,

Induct_on `n` THENL [
   SIMP_TAC std_ss [FEVERY_FEMPTY, smallfoot_ap_data_list_seg_num_def,
		    LENGTH_NIL, asl_bool_REWRITES, smallfoot_ap_false_def],


   SIMP_TAC std_ss [smallfoot_ap_data_list_seg_num_def] THEN
   REPEAT STRIP_TAC THEN
   Tactical.REVERSE (Cases_on `FEVERY (\x. ~(SND x = [])) data`) THEN (
      ASM_SIMP_TAC std_ss [asl_bool_REWRITES, smallfoot_ap_false_def]
   ) THEN
   Tactical.REVERSE (`~FEVERY (\x. LENGTH (SND x) = n) (FMAP_MAP TL data)` by ALL_TAC) THEN (
      ASM_SIMP_TAC std_ss [asl_bool_REWRITES, 
			   smallfoot_ap_false___smallfoot_ap_star_THM,
			   asl_exists_def, smallfoot_ap_false___NOT_IN]
   ) THEN
   Q.PAT_ASSUM `FEVERY X data` MP_TAC THEN
   Q.PAT_ASSUM `~(FEVERY X Y)` MP_TAC THEN
   REPEAT (POP_ASSUM (K ALL_TAC)) THEN
   Q.SPEC_TAC (`data`, `data`) THEN
   HO_MATCH_MP_TAC fmap_INDUCT THEN
   SIMP_TAC std_ss [FEVERY_FEMPTY, FEVERY_FUPDATE,
		       NOT_FDOM_DRESTRICT,
		       FMAP_MAP_FUPDATE,
		       FMAP_MAP_THM] THEN
   REPEAT STRIP_TAC THENL [
     Cases_on `y` THEN 
     FULL_SIMP_TAC list_ss [],

     METIS_TAC[]
   ]
]);




val smallfoot_ap_data_list_seg_num___ELIM_DATA =
store_thm ("smallfoot_ap_data_list_seg_num___ELIM_DATA",

``!data data' n tl startExp endExp s.
  ((!t. (t IN (FDOM data')) ==> ((t IN (FDOM data)) /\ (data' ' t = data ' t))) /\
  (s IN smallfoot_ap_data_list_seg_num n tl startExp data endExp)) ==>
   s IN smallfoot_ap_data_list_seg_num n tl startExp data' endExp``,

Induct_on `n` THENL [
   SIMP_TAC std_ss [smallfoot_ap_data_list_seg_num_def,
		    asl_bool_EVAL, IN_ABS, FEVERY_DEF],

   
   SIMP_TAC std_ss [smallfoot_ap_data_list_seg_num_def,
		    asl_bool_EVAL, IN_ABS, FEVERY_DEF] THEN
   REPEAT STRIP_TAC THEN
   FULL_SIMP_TAC std_ss [smallfoot_ap_star_def, asl_star_def,
			 IN_ABS] THEN
   Q.EXISTS_TAC `n'` THEN 
   Q.EXISTS_TAC `p` THEN 
   Q.EXISTS_TAC `q` THEN 
   ASM_SIMP_TAC std_ss [] THEN
   CONJ_TAC THENL [
      Q.PAT_ASSUM `p IN X` MP_TAC THEN
      Cases_on `p` THEN
      ASM_SIMP_TAC std_ss [smallfoot_ap_points_to_def,
			   IN_ABS, LET_THM,
			   FEVERY_DEF, FMAP_MAP_THM,
			   FDOM_FUPDATE, FAPPLY_FUPDATE_THM] THEN
      STRIP_TAC THEN GEN_TAC THEN STRIP_TAC THEN
      Q.PAT_ASSUM `!x. X x` (MP_TAC o Q.SPEC `x`) THEN 
      Cases_on `x = tl` THEN (
         FULL_SIMP_TAC std_ss [smallfoot_ae_const_def, IN_INSERT,
			      FMAP_MAP_THM]
      ),



      Q.PAT_ASSUM `!data data'. X data data'` HO_MATCH_MP_TAC THEN
      Q.EXISTS_TAC `FMAP_MAP TL data` THEN
      ASM_SIMP_TAC std_ss [FMAP_MAP_THM]
  ]
]);

      




val smallfoot_ap_data_list_seg_num___ELIM_DATA___COMPLETE =
store_thm ("smallfoot_ap_data_list_seg_num___ELIM_DATA___COMPLETE",

``!data n tl startExp endExp s.  
   s IN smallfoot_ap_data_list_seg_num n tl startExp data endExp ==>
   s IN smallfoot_ap_list_seg_num n tl startExp endExp``,

SIMP_TAC std_ss [GSYM smallfoot_ap_data_list_seg_num___NO_DATA] THEN
REPEAT STRIP_TAC THEN
MATCH_MP_TAC smallfoot_ap_data_list_seg_num___ELIM_DATA THEN
Q.EXISTS_TAC `data` THEN
ASM_SIMP_TAC std_ss [FDOM_FEMPTY, NOT_IN_EMPTY]);







val smallfoot_ap_data_list_seg_def = Define `
   smallfoot_ap_data_list_seg tl startExp data endExp =
   asl_exists n. smallfoot_ap_data_list_seg_num n tl startExp data endExp`


val smallfoot_ap_data_list_seg_REWRITE = store_thm ("smallfoot_ap_data_list_seg_REWRITE",
``smallfoot_ap_data_list_seg tl startExp data endExp = 
  asl_or
    (asl_and (smallfoot_ap_equal endExp startExp) 
             (\s. FEVERY (\x. (SND x) = []) data))
    ((asl_and (smallfoot_ap_weak_unequal endExp startExp) 
     (asl_and (\s. FEVERY (\x. ~((SND x) = [])) data)
      asl_exists n'. smallfoot_ap_star
                      (smallfoot_ap_points_to startExp
		         ((FMAP_MAP (\dl. smallfoot_ae_const (HD dl)) data) |+
                                   (tl,smallfoot_ae_const n')))
                      (smallfoot_ap_data_list_seg tl
		         (smallfoot_ae_const n') (FMAP_MAP TL data) endExp)
     )))``,

SIMP_TAC std_ss [EXTENSION, IN_ABS, asl_bool_EVAL,
                 smallfoot_ap_data_list_seg_def,
                 GSYM asl_exists___smallfoot_ap_star_THM] THEN
REPEAT STRIP_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THENL [
   Cases_on `n` THEN
   FULL_SIMP_TAC std_ss [smallfoot_ap_data_list_seg_num_def,
     asl_bool_EVAL, IN_ABS] THEN
   DISJ2_TAC THEN
   Q.EXISTS_TAC `n''` THEN
   Q.EXISTS_TAC `n'` THEN
   ASM_REWRITE_TAC[],


   Q.EXISTS_TAC `0` THEN
   ASM_SIMP_TAC std_ss [smallfoot_ap_data_list_seg_num_def,
                        asl_bool_EVAL, asl_bool_REWRITES],

   Q.EXISTS_TAC `SUC n` THEN
   ASM_SIMP_TAC std_ss [smallfoot_ap_data_list_seg_num_def,
                        asl_bool_EVAL, asl_bool_REWRITES] THEN
   Q.EXISTS_TAC `n'` THEN
   ASM_REWRITE_TAC[]
]);


val smallfoot_ap_data_list_def = Define `
   smallfoot_ap_data_list tl startExp data =
   smallfoot_ap_data_list_seg tl startExp data smallfoot_ae_null`


val smallfoot_ap_data_list_seg___NO_DATA =
store_thm ("smallfoot_ap_data_list_seg___NO_DATA",

``!tl startExp endExp.
  smallfoot_ap_data_list_seg tl startExp FEMPTY endExp =
  smallfoot_ap_list_seg tl startExp endExp``,

SIMP_TAC std_ss [smallfoot_ap_data_list_seg_def,
		 smallfoot_ap_list_seg_def,
		 smallfoot_ap_data_list_seg_num___NO_DATA]);


val smallfoot_ap_data_list___NO_DATA =
store_thm ("smallfoot_ap_data_list___NO_DATA",

``!tl startExp.
  smallfoot_ap_data_list tl startExp FEMPTY =
  smallfoot_ap_list tl startExp``,

SIMP_TAC std_ss [smallfoot_ap_data_list_def,
		 smallfoot_ap_list_def,
		 smallfoot_ap_data_list_seg___NO_DATA]);



val smallfoot_ap_data_list_seg___DATA_LENGTH =
store_thm ("smallfoot_ap_data_list_seg___DATA_LENGTH",

``!data tl startExp endExp.

  ~(?n. FEVERY (\x. LENGTH (SND x) = n) data) ==>
  (smallfoot_ap_data_list_seg tl startExp data endExp =
   smallfoot_ap_false)``,

SIMP_TAC std_ss [smallfoot_ap_data_list_seg_def, EXTENSION, asl_bool_EVAL] THEN
METIS_TAC[smallfoot_ap_false___NOT_IN, smallfoot_ap_data_list_seg_num___DATA_LENGTH]);


val smallfoot_ap_data_list_seg___NOT_EMPTY_DATA_DEF =
store_thm ("smallfoot_ap_data_list_seg___NOT_EMPTY_DATA_DEF",
``
smallfoot_ap_data_list_seg tl startExp (data |+ (t, tvL)) endExp =
smallfoot_ap_data_list_seg_num (LENGTH tvL) tl startExp (data |+ (t, tvL)) endExp``,

SIMP_TAC std_ss [smallfoot_ap_data_list_seg_def,
		 EXTENSION, asl_bool_EVAL] THEN
REPEAT STRIP_TAC THEN (Tactical.REVERSE EQ_TAC) THEN1 METIS_TAC[] THEN
REPEAT STRIP_TAC THEN
Cases_on `LENGTH tvL = n` THEN ASM_REWRITE_TAC[] THEN
FULL_SIMP_TAC list_ss [smallfoot_ap_data_list_seg_num___DATA_LENGTH,
		       FEVERY_FUPDATE] THEN
FULL_SIMP_TAC std_ss [smallfoot_ap_false___NOT_IN]);



val smallfoot_p_expression = Hol_datatype `smallfoot_p_expression = 
	smallfoot_p_var of smallfoot_var
      | smallfoot_p_const of num 
      |	smallfoot_p_add of smallfoot_p_expression => smallfoot_p_expression
      |	smallfoot_p_sub of smallfoot_p_expression => smallfoot_p_expression`;



val SMALLFOOT_P_EXPRESSION_EVAL_def = Define `
	(SMALLFOOT_P_EXPRESSION_EVAL (smallfoot_p_var v) =
		(smallfoot_ae_var v)) /\
	(SMALLFOOT_P_EXPRESSION_EVAL (smallfoot_p_const c) =
		(smallfoot_ae_const c)) /\
	(SMALLFOOT_P_EXPRESSION_EVAL (smallfoot_p_add p1 p2) =
		(smallfoot_ae_binop (\n1 n2. n1+n2) (SMALLFOOT_P_EXPRESSION_EVAL p1) (SMALLFOOT_P_EXPRESSION_EVAL p2))) /\
	(SMALLFOOT_P_EXPRESSION_EVAL (smallfoot_p_sub p1 p2) =
		(smallfoot_ae_binop (\n1 n2. n1-n2) (SMALLFOOT_P_EXPRESSION_EVAL p1) (SMALLFOOT_P_EXPRESSION_EVAL p2)))`;


val smallfoot_pt_proposition = Hol_datatype `smallfoot_pt_proposition = 
	smallfoot_pt_equal of smallfoot_p_expression => smallfoot_p_expression
      | smallfoot_pt_less of smallfoot_p_expression => smallfoot_p_expression`

val smallfoot_pt_proposition_induction = DB.fetch "-" "smallfoot_pt_proposition_induction";
val _ = type_abbrev("smallfoot_p_proposition", Type `:smallfoot_pt_proposition fasl_predicate`);

 

val nchotomy_thm = prove (``!s.
         (?s' s0. s = smallfoot_pt_equal s' s0) \/
         ?s' s0. s = smallfoot_pt_less s' s0``, 
                        REWRITE_TAC [TypeBase.nchotomy_of ``:smallfoot_pt_proposition``]);

val _ = TypeBase.write [TypeBasePure.put_nchotomy nchotomy_thm (valOf (TypeBase.fetch ``:smallfoot_pt_proposition``))];



val SMALLFOOT_PT_PROPOSITION_pred_map_def = Define `
	(SMALLFOOT_PT_PROPOSITION_pred_map (f:smallfoot_state bin_option_function) (smallfoot_pt_equal e1 e2) =
		(smallfoot_ap_binexpression F $= (SMALLFOOT_P_EXPRESSION_EVAL e1) (SMALLFOOT_P_EXPRESSION_EVAL e2))) /\
	(SMALLFOOT_PT_PROPOSITION_pred_map f (smallfoot_pt_less e1 e2) =
		(smallfoot_ap_binexpression F $< (SMALLFOOT_P_EXPRESSION_EVAL e1) (SMALLFOOT_P_EXPRESSION_EVAL e2)))`









val smallfoot_p_true_def = Define `smallfoot_p_true:smallfoot_p_proposition = fasl_pred_true`;
val smallfoot_p_false_def = Define `smallfoot_p_false:smallfoot_p_proposition = fasl_pred_false`;
val smallfoot_p_neg_def = Define `smallfoot_p_neg = fasl_pred_neg:smallfoot_p_proposition->smallfoot_p_proposition`;
val smallfoot_p_equal_def = Define `smallfoot_p_equal = 
\e1 e2. fasl_pred_prim (smallfoot_pt_equal e1 e2)`;
val smallfoot_p_less_def = Define `smallfoot_p_less = 
\e1 e2. fasl_pred_prim (smallfoot_pt_less e1 e2)`;
val smallfoot_p_unequal_def = Define `smallfoot_p_unequal = 
\e1 e2. fasl_pred_or (smallfoot_p_less e1 e2) (smallfoot_p_less e2 e1)`;
val smallfoot_p_lesseq_def = Define `smallfoot_p_lesseq = 
\e1 e2. fasl_pred_or (smallfoot_p_less e1 e2) (smallfoot_p_equal e1 e2)`;
val smallfoot_p_greater_def = Define `smallfoot_p_greater = 
\e1 e2. smallfoot_p_less e2 e1`;
val smallfoot_p_greatereq_def = Define `smallfoot_p_greatereq = 
\e1 e2. smallfoot_p_lesseq e2 e1`;
val smallfoot_p_and_def = Define `smallfoot_p_and = fasl_pred_and:smallfoot_p_proposition -> smallfoot_p_proposition -> smallfoot_p_proposition`;
val smallfoot_p_or_def = Define `smallfoot_p_or = fasl_pred_or:smallfoot_p_proposition -> smallfoot_p_proposition -> smallfoot_p_proposition`;





val smallfoot_action = Hol_datatype `smallfoot_action = 
	smallfoot_assign of smallfoot_var => smallfoot_p_expression
|       smallfoot_field_lookup of smallfoot_var => smallfoot_p_expression => smallfoot_tag
|       smallfoot_field_assign of smallfoot_p_expression  => smallfoot_tag => smallfoot_p_expression
|       smallfoot_new of smallfoot_var
|       smallfoot_dispose of smallfoot_p_expression
|       smallfoot_new_var_init of smallfoot_var => smallfoot_p_expression
|       smallfoot_dispose_var of smallfoot_var`;


val SMALLFOOT_action_map_def = Define `
	(SMALLFOOT_action_map (f:smallfoot_state bin_option_function) (smallfoot_assign v e) ((st, h):smallfoot_state) =
		let ev_opt = SMALLFOOT_P_EXPRESSION_EVAL e st in 
		if ((var_res_sl___has_write_permission v st) /\ (IS_SOME ev_opt)) then 
			SOME {(st |+ (v, THE (ev_opt), var_res_write_permission), h)} 
		else NONE) /\

	(SMALLFOOT_action_map f (smallfoot_field_lookup v e t) ((st, h):smallfoot_state) =
		let loc_opt = SMALLFOOT_P_EXPRESSION_EVAL e st in
		if (~(var_res_sl___has_write_permission v st) \/ (IS_NONE loc_opt)) then NONE else 
		let loc = (THE loc_opt) in (
		if (~(loc IN FDOM h) \/ (loc = 0)) then NONE else
		(if (~(t IN FDOM (h ' loc))) then 
                SOME (\s:smallfoot_state. ?new_v. (FST s = st |+ (v, new_v,var_res_write_permission)) /\ 
                		  (SND s = h |+ (loc, (h ' loc) |+ (t, new_v)))) else
		SOME {(st |+ (v, (h ' loc ' t), var_res_write_permission), h)}))) /\

	(SMALLFOOT_action_map f (smallfoot_field_assign e1 t e2) ((st, h):smallfoot_state) =
		let e1_opt = SMALLFOOT_P_EXPRESSION_EVAL e1 st in
		let e2_opt = SMALLFOOT_P_EXPRESSION_EVAL e2 st in
		if ((IS_NONE e1_opt) \/ (IS_NONE e2_opt)) then NONE else 
		let e1_v = (THE e1_opt) in 
		let e2_v = (THE e2_opt) in (
		if (~(e1_v IN FDOM h) \/ (e1_v = 0)) then NONE else
		(SOME {(st, h |+ (e1_v, (h ' e1_v) |+ (t, e2_v)))}))) /\

	(SMALLFOOT_action_map f (smallfoot_new v) ((st, h):smallfoot_state) =
		if ~(var_res_sl___has_write_permission v st) then NONE else 
		SOME (\s. ?n X. ~(n = 0) /\ ~(n IN FDOM h) /\ (s = (st |+ (v, n, var_res_write_permission),
			h |+ (n, X))))) /\

	(SMALLFOOT_action_map f (smallfoot_dispose e) ((st, h):smallfoot_state) =
		let loc_opt = SMALLFOOT_P_EXPRESSION_EVAL e st in
		if (IS_NONE loc_opt) then NONE else 
		let loc = (THE loc_opt) in (
		if (~(loc IN FDOM h) \/ (loc = 0)) then NONE else
		(SOME {(st, h \\ loc)}))) /\

	(SMALLFOOT_action_map f (smallfoot_new_var_init v e) ((st, h):smallfoot_state) =
		let e_opt = SMALLFOOT_P_EXPRESSION_EVAL e st in
		if (IS_NONE e_opt) then NONE else
		(if (v IN FDOM st) then SOME {} else 
		(SOME {(st |+ (v, THE e_opt, var_res_write_permission), h)}))) /\

	(SMALLFOOT_action_map f (smallfoot_dispose_var v) ((st, h):smallfoot_state) =
		if ~(var_res_sl___has_write_permission v st) then NONE else 
		(SOME {(st\\v, h)}))`



val SMALLFOOT_IS_SUBSTATE_def = Define 
`SMALLFOOT_IS_SUBSTATE =
 ASL_IS_SUBSTATE smallfoot_separation_combinator`;



val SMALLFOOT_IS_SUBSTATE___IS_PREORDER =
    store_thm ("SMALLFOOT_IS_SUBSTATE___IS_PREORDER",
``PreOrder SMALLFOOT_IS_SUBSTATE``,

PROVE_TAC[SMALLFOOT_IS_SUBSTATE_def, ASL_IS_SUBSTATE___IS_PREORDER,
	  IS_SEPARATION_COMBINATOR___smallfoot_separation_combinator]);



val SMALLFOOT_IS_SUBSTATE___TRANS =
    save_thm ("SMALLFOOT_IS_SUBSTATE___TRANS",
CONJUNCT2 (
REWRITE_RULE[PreOrder, transitive_def] SMALLFOOT_IS_SUBSTATE___IS_PREORDER));

val SMALLFOOT_IS_SUBSTATE___REFL =
    save_thm ("SMALLFOOT_IS_SUBSTATE___REFL",
CONJUNCT1 (
REWRITE_RULE[PreOrder, reflexive_def] SMALLFOOT_IS_SUBSTATE___IS_PREORDER));




val SMALLFOOT_IS_SUBSTATE_INTRO = store_thm ("SMALLFOOT_IS_SUBSTATE_INTRO",
``!x1 x2 x.
   (smallfoot_separation_combinator (SOME x1) (SOME x2) = SOME x) ==>
   (SMALLFOOT_IS_SUBSTATE x1 x /\
    SMALLFOOT_IS_SUBSTATE x2 x)``,

SIMP_TAC std_ss [SMALLFOOT_IS_SUBSTATE_def,
		 ASL_IS_SUBSTATE_def] THEN
ASSUME_TAC IS_SEPARATION_COMBINATOR___smallfoot_separation_combinator THEN
FULL_SIMP_TAC std_ss [IS_SEPARATION_COMBINATOR_def, COMM_DEF] THEN
METIS_TAC[]);





val SMALLFOOT_IS_SUBSTATE_REWRITE = store_thm (
"SMALLFOOT_IS_SUBSTATE_REWRITE",
``
!s1 s2.
SMALLFOOT_IS_SUBSTATE s1 s2 =
VAR_RES_STACK_IS_SUBSTATE (FST s1) (FST s2) /\
ASL_IS_SUBSTATE DISJOINT_FMAP_UNION (SND s1) (SND s2)``,

SIMP_TAC std_ss [SMALLFOOT_IS_SUBSTATE_def,
		 smallfoot_separation_combinator_def,
		 ASL_IS_SUBSTATE___PRODUCT_SEPARATION_COMBINATOR,
		 VAR_RES_STACK_IS_SUBSTATE_def]);


val SMALLFOOT_P_EXPRESSION_EVAL___VAR_RES_SUBSTATE = store_thm ("SMALLFOOT_P_EXPRESSION_EVAL___VAR_RES_SUBSTATE",
``!st1 st2. VAR_RES_STACK_IS_SUBSTATE st1 st2 ==>
(!p. IS_SOME (SMALLFOOT_P_EXPRESSION_EVAL p st1) ==>
(SMALLFOOT_P_EXPRESSION_EVAL p st2 = SMALLFOOT_P_EXPRESSION_EVAL p st1))``,


REPEAT GEN_TAC THEN STRIP_TAC THEN
Induct_on `p` THENL [
	FULL_SIMP_TAC std_ss [VAR_RES_STACK_IS_SUBSTATE_def,
	        ASL_IS_SUBSTATE_def,
		SOME___VAR_RES_STACK_COMBINE,
		SMALLFOOT_P_EXPRESSION_EVAL_def,
	        smallfoot_ae_var_def, FMERGE_DEF] THEN
	GEN_TAC THEN
	Cases_on `s IN FDOM q` THEN ASM_SIMP_TAC std_ss [IN_UNION] THEN
	SIMP_TAC std_ss [COND_RAND, COND_RATOR, VAR_RES_STACK_COMBINE___MERGE_FUNC_def],


	SIMP_TAC std_ss [SMALLFOOT_P_EXPRESSION_EVAL_def, smallfoot_ae_const_def],
	
	SIMP_TAC std_ss [SMALLFOOT_P_EXPRESSION_EVAL_def, smallfoot_ae_binop_def,
		LET_THM, COND_RAND, COND_RATOR] THEN
	METIS_TAC[],

	SIMP_TAC std_ss [SMALLFOOT_P_EXPRESSION_EVAL_def, smallfoot_ae_binop_def,
		LET_THM, COND_RAND, COND_RATOR] THEN
	METIS_TAC[]
]);




val SMALLFOOT_P_EXPRESSION_EVAL___SUBSTATE = store_thm ("SMALLFOOT_P_EXPRESSION_EVAL___SUBSTATE",
``!s1 s2. ASL_IS_SUBSTATE smallfoot_separation_combinator s1 s2 ==>
(!p. IS_SOME (SMALLFOOT_P_EXPRESSION_EVAL p (FST s1)) ==>
(SMALLFOOT_P_EXPRESSION_EVAL p (FST s2) = SMALLFOOT_P_EXPRESSION_EVAL p (FST s1)))``,


REPEAT GEN_TAC THEN STRIP_TAC THEN
MATCH_MP_TAC SMALLFOOT_P_EXPRESSION_EVAL___VAR_RES_SUBSTATE THEN
FULL_SIMP_TAC std_ss [ASL_IS_SUBSTATE_def, VAR_RES_STACK_IS_SUBSTATE_def,
		      SOME___smallfoot_separation_combinator] THEN
METIS_TAC[]);




val SMALLFOOT_SUBSTATE_IMPLS = store_thm ("SMALLFOOT_SUBSTATE_IMPLS",
``!s1 s2. ASL_IS_SUBSTATE smallfoot_separation_combinator s1 s2 ==>
 (((SND s1) SUBMAP (SND s2)) /\
 (!v. (v IN FDOM (FST s1)) ==> (
	(v IN FDOM (FST s2)) /\ (FST ((FST s2) ' v) = (FST ((FST s1) ' v))) /\ 
	(IS_VAR_RES_SUBPERMISSION (SND ((FST s1) ' v)) (SND ((FST s2) ' v))))))``,


SIMP_TAC std_ss [GSYM SMALLFOOT_IS_SUBSTATE_def,
		 SMALLFOOT_IS_SUBSTATE_REWRITE,
		 VAR_RES_STACK_IS_SUBSTATE_REWRITE,
		 ASL_IS_SUBSTATE___DISJOINT_FMAP_UNION,
		 SUBMAP_DEF, SUBSET_DEF]);






val SMALLFOOT_STACK_WRITE_PERM___SUBSTATE = store_thm ("SMALLFOOT_STACK_WRITE_PERM___SUBSTATE",
``!s1 s2 v. (ASL_IS_SUBSTATE smallfoot_separation_combinator s1 s2 /\ var_res_sl___has_write_permission v (FST s1)) ==> var_res_sl___has_write_permission v (FST s2)``,

REPEAT STRIP_TAC THEN
IMP_RES_TAC SMALLFOOT_SUBSTATE_IMPLS THEN
Cases_on `s1` THEN Cases_on `s2` THEN
FULL_SIMP_TAC std_ss [var_res_sl___has_write_permission_def] THEN
RES_TAC THEN
Q.PAT_ASSUM `SND (q ' v) = X` ASSUME_TAC THEN
FULL_SIMP_TAC std_ss [IS_VAR_RES_SUBPERMISSION_THM]);





val SMALLFOOT_STACK_READ_PERM___SUBSTATE = store_thm ("SMALLFOOT_STACK_READ_PERM___SUBSTATE",
``!s1 s2 v. (ASL_IS_SUBSTATE smallfoot_separation_combinator s1 s2 /\ var_res_sl___has_read_permission v (FST s1)) ==> var_res_sl___has_read_permission v (FST s2)``,

REPEAT STRIP_TAC THEN
IMP_RES_TAC SMALLFOOT_SUBSTATE_IMPLS THEN
FULL_SIMP_TAC std_ss [var_res_sl___has_read_permission_def]);





val FASL_IS_LOCAL_ACTION___ALTERNATIVE_EXT_DEF = store_thm ("FASL_IS_LOCAL_ACTION___ALTERNATIVE_EXT_DEF",
	``!f op.
         FASL_IS_LOCAL_ACTION f op =
         !s1 s2 s3 v1.
           (f (SOME s1) (SOME s2) = SOME s3) /\ (ASL_IS_SUBSTATE f s1 s3) /\ (op s1 = SOME v1) ==> (?v3. (op s3 = SOME v3) /\ (!t. t IN v3 ==>
           ?t'. (SOME t = f (SOME t') (SOME s2)) /\ t' IN v1))``,

SIMP_TAC std_ss [FASL_IS_LOCAL_ACTION___ALTERNATIVE_DEF] THEN
REPEAT GEN_TAC THEN
EQ_TAC THEN STRIP_TAC THENL [
	REPEAT STRIP_TAC THEN
	`?v3. op s3 = SOME v3` by PROVE_TAC[IS_SOME_EXISTS] THEN
	ASM_SIMP_TAC std_ss [] THEN
	METIS_TAC[],

	SIMP_TAC std_ss [IS_SOME_EXISTS] THEN
	REPEAT STRIP_TAC THENL [
		`ASL_IS_SUBSTATE f s1 s3` by METIS_TAC[ASL_IS_SUBSTATE_def] THEN
		METIS_TAC[],

		`ASL_IS_SUBSTATE f s1 s3` by METIS_TAC[ASL_IS_SUBSTATE_def] THEN
		METIS_TAC[SOME_11]
	]
]);


val VAR_RES_STACK_IS_SEPARATE___write_perm = store_thm ( "VAR_RES_STACK_IS_SEPARATE___write_perm",

``!st1 st2 s v.
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




val smallfoot_xenv___local_action_assign = prove (``
FASL_IS_LOCAL_ACTION smallfoot_separation_combinator
      (SMALLFOOT_action_map smallfoot_separation_combinator
         (smallfoot_assign v e))``,


	SIMP_TAC std_ss [FASL_IS_LOCAL_ACTION___ALTERNATIVE_EXT_DEF,
		SMALLFOOT_action_map_def, PAIR_FORALL_THM, LET_THM,
		COND_NONE_SOME_REWRITES, IN_SING] THEN
	REPEAT GEN_TAC THEN STRIP_TAC THEN
	`SMALLFOOT_P_EXPRESSION_EVAL e x1'' = 
		SMALLFOOT_P_EXPRESSION_EVAL e x1` by
		METIS_TAC[SMALLFOOT_P_EXPRESSION_EVAL___SUBSTATE,
			pairTheory.FST] THEN
	ASM_SIMP_TAC std_ss [] THEN
	Q.ABBREV_TAC `X = THE (SMALLFOOT_P_EXPRESSION_EVAL e x1)` THEN
	REPEAT STRIP_TAC THENL [
		METIS_TAC[SMALLFOOT_STACK_WRITE_PERM___SUBSTATE,
			pairTheory.FST],

		FULL_SIMP_TAC std_ss [smallfoot_separation_combinator___REWRITE,
			COND_NONE_SOME_REWRITES] THEN
		CONJ_TAC THENL [
			METIS_TAC[VAR_RES_STACK_IS_SEPARATE___UPDATE],
			METIS_TAC[VAR_RES_STACK_IS_SEPARATE___COMBINE_UPDATE]
		]
	]);



val smallfoot_xenv___local_action_field_lookup = prove (``
FASL_IS_LOCAL_ACTION smallfoot_separation_combinator
      (SMALLFOOT_action_map smallfoot_separation_combinator
         (smallfoot_field_lookup v e t))``,


	SIMP_TAC std_ss [FASL_IS_LOCAL_ACTION___ALTERNATIVE_EXT_DEF,
		SMALLFOOT_action_map_def, PAIR_FORALL_THM, LET_THM,
		COND_NONE_SOME_REWRITES, IN_SING, NOT_NONE_IS_SOME] THEN
	REPEAT GEN_TAC THEN STRIP_TAC THEN
	`SMALLFOOT_P_EXPRESSION_EVAL e x1'' = 
  	  SMALLFOOT_P_EXPRESSION_EVAL e x1` by
		METIS_TAC[SMALLFOOT_P_EXPRESSION_EVAL___SUBSTATE,
			pairTheory.FST] THEN
	IMP_RES_TAC SMALLFOOT_SUBSTATE_IMPLS THEN
	FULL_SIMP_TAC std_ss [SUBMAP_DEF] THEN
        CONJ_TAC THEN1 (
           METIS_TAC[SMALLFOOT_STACK_WRITE_PERM___SUBSTATE,
			pairTheory.FST]
        ) THEN
        Cases_on `t IN FDOM (x2'' ' (THE (SMALLFOOT_P_EXPRESSION_EVAL e x1)))` THENL [
           ASM_SIMP_TAC std_ss [IN_SING] THEN
           FULL_SIMP_TAC std_ss [smallfoot_separation_combinator___REWRITE,
			COND_NONE_SOME_REWRITES] THEN
           CONJ_TAC THENL [
			METIS_TAC[VAR_RES_STACK_IS_SEPARATE___UPDATE],
			METIS_TAC[VAR_RES_STACK_IS_SEPARATE___COMBINE_UPDATE]
           ],


	   ASM_SIMP_TAC std_ss [IN_ABS, GSYM LEFT_FORALL_IMP_THM,
			        GSYM RIGHT_EXISTS_AND_THM,
			        PAIR_EXISTS_THM] THEN
           FULL_SIMP_TAC std_ss [smallfoot_separation_combinator___REWRITE,
			COND_NONE_SOME_REWRITES,
		        FDOM_FUPDATE] THEN
           GEN_TAC THEN
	   Q.EXISTS_TAC `new_v` THEN
           REPEAT STRIP_TAC THENL [        
	     METIS_TAC[VAR_RES_STACK_IS_SEPARATE___UPDATE],


             `(THE (SMALLFOOT_P_EXPRESSION_EVAL e x1) INSERT FDOM x2) =
              FDOM x2` by ALL_TAC THEN1 (
                REWRITE_TAC[EXTENSION] THEN
                ASM_SIMP_TAC (std_ss++bool_eq_imp_ss) [IN_INSERT]
             ) THEN
             ASM_REWRITE_TAC[],


	     METIS_TAC[VAR_RES_STACK_IS_SEPARATE___COMBINE_UPDATE],


	     Q.PAT_ASSUM `X = x2''` (ASSUME_TAC o GSYM) THEN
	     ASM_REWRITE_TAC[] THEN
	     SIMP_TAC std_ss [GSYM fmap_EQ_THM, FUNION_DEF,
			      FDOM_FUPDATE, IN_UNION] THEN
	     CONJ_TAC THEN1 (
	        SIMP_TAC (std_ss++bool_eq_imp_ss) [EXTENSION, IN_INSERT, IN_UNION]
             ) THEN
             `((THE (SMALLFOOT_P_EXPRESSION_EVAL e x1) INSERT FDOM x2) =
              FDOM x2)` by ALL_TAC THEN1 (
                REWRITE_TAC[EXTENSION] THEN
                ASM_SIMP_TAC (std_ss++bool_eq_imp_ss) [IN_INSERT]
             ) THEN
             `~(THE (SMALLFOOT_P_EXPRESSION_EVAL e x1) IN FDOM x2')` by ALL_TAC THEN1 (             
               FULL_SIMP_TAC std_ss [DISJOINT_DEF, EXTENSION, NOT_IN_EMPTY, IN_INTER] THEN
               METIS_TAC[]
             ) THEN
	     ASM_SIMP_TAC std_ss [DISJ_IMP_THM, FORALL_AND_THM] THEN
	     CONJ_TAC THENL [
	        GEN_TAC THEN STRIP_TAC THEN
		SIMP_TAC std_ss [FAPPLY_FUPDATE_THM, FUNION_DEF] THEN
		ASM_REWRITE_TAC[],


 	        GEN_TAC THEN STRIP_TAC THEN
                `~(x IN FDOM x2)` by ALL_TAC THEN1 (             
                   FULL_SIMP_TAC std_ss [DISJOINT_DEF, EXTENSION, NOT_IN_EMPTY, IN_INTER] THEN
                   METIS_TAC[]
                ) THEN
                `~(x = THE (SMALLFOOT_P_EXPRESSION_EVAL e x1))` by PROVE_TAC[] THEN
		ASM_REWRITE_TAC[] THEN
		SIMP_TAC std_ss [FAPPLY_FUPDATE_THM, FUNION_DEF] THEN
		ASM_REWRITE_TAC[]
             ]
           ]
	]
);





val smallfoot_xenv___local_action_new = prove (``
FASL_IS_LOCAL_ACTION smallfoot_separation_combinator
      (SMALLFOOT_action_map smallfoot_separation_combinator
         (smallfoot_new v))``,


	SIMP_TAC std_ss [FASL_IS_LOCAL_ACTION___ALTERNATIVE_EXT_DEF,
		SMALLFOOT_action_map_def, PAIR_FORALL_THM, LET_THM,
		COND_NONE_SOME_REWRITES, IN_ABS, IN_SING] THEN
	SIMP_TAC std_ss [GSYM RIGHT_EXISTS_AND_THM, GSYM LEFT_EXISTS_AND_THM] THEN
	REPEAT STRIP_TAC THENL [
		METIS_TAC[SMALLFOOT_STACK_WRITE_PERM___SUBSTATE,
			pairTheory.FST],

		Q.EXISTS_TAC `n` THEN
		Q.EXISTS_TAC `X` THEN
		IMP_RES_TAC SMALLFOOT_SUBSTATE_IMPLS THEN
		FULL_SIMP_TAC std_ss [SUBMAP_DEF, smallfoot_separation_combinator___REWRITE,
			COND_NONE_SOME_REWRITES] THEN
		Q.PAT_ASSUM `Y = x2''` (ASSUME_TAC o GSYM) THEN
		FULL_SIMP_TAC std_ss [FUNION_DEF, IN_UNION, FDOM_FUPDATE, DISJOINT_INSERT] THEN
		REPEAT CONJ_TAC THENL [
			METIS_TAC[VAR_RES_STACK_IS_SEPARATE___UPDATE],
			METIS_TAC[VAR_RES_STACK_IS_SEPARATE___COMBINE_UPDATE],

			SIMP_TAC std_ss [GSYM fmap_EQ_THM, FUNION_DEF,
				FDOM_FUPDATE, IN_UNION, EXTENSION, IN_INSERT,
				DISJ_IMP_THM, FORALL_AND_THM,
				FAPPLY_FUPDATE_THM] THEN
			REPEAT CONJ_TAC THENL [
				PROVE_TAC[],

				GEN_TAC THEN STRIP_TAC THEN
				`~(x = n)` by PROVE_TAC[] THEN
				ASM_SIMP_TAC std_ss []
			]
		]
	]);


val smallfoot_xenv___local_action_dispose = prove (``
FASL_IS_LOCAL_ACTION smallfoot_separation_combinator
      (SMALLFOOT_action_map smallfoot_separation_combinator
         (smallfoot_dispose e))``,


	SIMP_TAC std_ss [FASL_IS_LOCAL_ACTION___ALTERNATIVE_EXT_DEF,
		SMALLFOOT_action_map_def, PAIR_FORALL_THM, LET_THM,
		COND_NONE_SOME_REWRITES, IN_ABS, IN_SING,
		NOT_NONE_IS_SOME] THEN
	REPEAT GEN_TAC THEN STRIP_TAC THEN
	`SMALLFOOT_P_EXPRESSION_EVAL e x1'' = 
	  SMALLFOOT_P_EXPRESSION_EVAL e x1` by
		METIS_TAC[SMALLFOOT_P_EXPRESSION_EVAL___SUBSTATE,
			pairTheory.FST] THEN
	FULL_SIMP_TAC std_ss [smallfoot_separation_combinator___REWRITE,
		COND_NONE_SOME_REWRITES] THEN
	Q.ABBREV_TAC `ev = THE (SMALLFOOT_P_EXPRESSION_EVAL e x1)` THEN
	Q.PAT_ASSUM `X = x2''` (ASSUME_TAC o GSYM) THEN
	REPEAT CONJ_TAC THENL [
		ASM_REWRITE_TAC [FDOM_FUNION, IN_UNION],

		FULL_SIMP_TAC std_ss [DISJOINT_DEF, EXTENSION, IN_DELETE,
			IN_INTER, NOT_IN_EMPTY, FDOM_DOMSUB] THEN
		METIS_TAC[],

		ASM_SIMP_TAC std_ss [GSYM fmap_EQ_THM, FUNION_DEF,
			FDOM_DOMSUB, IN_DELETE, IN_UNION] THEN
		`~(ev IN FDOM x2')` by ALL_TAC THEN1 (
			FULL_SIMP_TAC std_ss [DISJOINT_DEF, EXTENSION, NOT_IN_EMPTY, IN_INTER] THEN
			METIS_TAC[]
		) THEN
		CONJ_TAC THENL [
			SIMP_TAC std_ss [EXTENSION, IN_UNION, IN_DELETE] THEN
			METIS_TAC[],

			GEN_TAC THEN
			Cases_on `x = ev` THEN1 (
				ASM_SIMP_TAC std_ss []
			) THEN
			ASM_SIMP_TAC std_ss [DOMSUB_FAPPLY_THM, FUNION_DEF]
		]
	]	
);




val smallfoot_xenv___local_action_dispose_var = prove (``
FASL_IS_LOCAL_ACTION smallfoot_separation_combinator
      (SMALLFOOT_action_map smallfoot_separation_combinator
         (smallfoot_dispose_var v))``,


	SIMP_TAC std_ss [FASL_IS_LOCAL_ACTION___ALTERNATIVE_EXT_DEF,
		SMALLFOOT_action_map_def, PAIR_FORALL_THM, LET_THM,
		COND_NONE_SOME_REWRITES, IN_ABS, IN_SING,
		NOT_NONE_IS_SOME] THEN
	REPEAT GEN_TAC THEN STRIP_TAC THEN
	CONJ_TAC THEN1 (	
		METIS_TAC[SMALLFOOT_STACK_WRITE_PERM___SUBSTATE, pairTheory.FST]
	) THEN

	FULL_SIMP_TAC std_ss [smallfoot_separation_combinator___REWRITE,
		COND_NONE_SOME_REWRITES] THEN
	Q.PAT_ASSUM `X = x1''` (ASSUME_TAC o GSYM) THEN 
	IMP_RES_TAC VAR_RES_STACK_IS_SEPARATE___write_perm THEN


	MATCH_MP_TAC (prove (``(A /\ (A ==> B)) ==> (A /\ B)``, PROVE_TAC[])) THEN
	CONJ_TAC THEN1 (
		FULL_SIMP_TAC std_ss [VAR_RES_STACK_IS_SEPARATE_def,
			FDOM_DOMSUB, DOMSUB_FAPPLY_THM, IN_DELETE] THEN
		METIS_TAC[]
	) THEN
	STRIP_TAC THEN
	FULL_SIMP_TAC std_ss [var_res_sl___has_write_permission_def,
		var_res_sl___has_read_permission_def] THEN
	ASM_SIMP_TAC std_ss [VAR_RES_STACK_COMBINE_def,
		BIN_OPTION_MAP_THM, GSYM fmap_EQ_THM,
		FMERGE_DEF, EXTENSION, FDOM_DOMSUB, IN_DELETE,
		IN_UNION] THEN
	CONJ_TAC THEN1 METIS_TAC[] THEN
	GEN_TAC THEN
	Cases_on `x = v` THEN ASM_REWRITE_TAC[] THEN
	ASM_SIMP_TAC std_ss [DOMSUB_FAPPLY_THM, FMERGE_DEF]
);





val smallfoot_xenv___local_action_new_var_init = prove (``
FASL_IS_LOCAL_ACTION smallfoot_separation_combinator
      (SMALLFOOT_action_map smallfoot_separation_combinator
         (smallfoot_new_var_init v e))``,


	SIMP_TAC std_ss [FASL_IS_LOCAL_ACTION___ALTERNATIVE_EXT_DEF,
		SMALLFOOT_action_map_def, PAIR_FORALL_THM, LET_THM,
		COND_NONE_SOME_REWRITES, IN_ABS, IN_SING,
		NOT_NONE_IS_SOME] THEN
	REPEAT GEN_TAC THEN STRIP_TAC THEN
	`?ev. SMALLFOOT_P_EXPRESSION_EVAL e x1 = SOME ev` by ALL_TAC THEN1 (
		Cases_on `SMALLFOOT_P_EXPRESSION_EVAL e x1` THEN
		FULL_SIMP_TAC std_ss []
	) THEN
	`SMALLFOOT_P_EXPRESSION_EVAL e x1'' = SOME ev` by
		METIS_TAC[SMALLFOOT_P_EXPRESSION_EVAL___SUBSTATE,
			pairTheory.FST, IS_SOME_DEF] THEN
	FULL_SIMP_TAC std_ss [] THEN
	Cases_on `v IN FDOM x1''` THEN1 (
		ASM_SIMP_TAC std_ss [NOT_IN_EMPTY]
	) THEN
	ASM_SIMP_TAC std_ss [IN_SING] THEN
	FULL_SIMP_TAC std_ss [IN_SING, smallfoot_separation_combinator___REWRITE,
		COND_NONE_SOME_REWRITES] THEN
	Q.PAT_ASSUM `X = x1''` (MP_TAC) THEN
	Q.PAT_ASSUM `X = x2''` (ASSUME_TAC o GSYM) THEN
	ASM_SIMP_TAC std_ss [VAR_RES_STACK_COMBINE_def, BIN_OPTION_MAP_THM] THEN
	STRIP_TAC THEN
	`FDOM x1'' = (FDOM x1) UNION (FDOM x1')` by METIS_TAC[FMERGE_DEF] THEN
	FULL_SIMP_TAC std_ss [IN_UNION] THEN
	Q.PAT_ASSUM `X = v1` (ASSUME_TAC o GSYM) THEN
	ASM_SIMP_TAC std_ss [IN_SING] THEN
	MATCH_MP_TAC (prove (``(A /\ (A ==> B)) ==> (A /\ B)``, PROVE_TAC[])) THEN
	CONJ_TAC THEN1 (
		FULL_SIMP_TAC std_ss [VAR_RES_STACK_IS_SEPARATE_def, FDOM_FUPDATE] THEN
		REPEAT GEN_TAC THEN STRIP_TAC THEN
		`~(x = v)` by PROVE_TAC[] THEN
		FULL_SIMP_TAC std_ss [IN_INSERT, FAPPLY_FUPDATE_THM] THEN
		METIS_TAC[]
	) THEN
	STRIP_TAC THEN
	Q.PAT_ASSUM `X = x1''` (ASSUME_TAC o GSYM) THEN
        ASM_SIMP_TAC std_ss [] THEN
	SIMP_TAC std_ss [GSYM fmap_EQ_THM, FMERGE_DEF, FDOM_FUPDATE, EXTENSION,
		IN_INSERT, IN_UNION] THEN
	CONJ_TAC THEN1 METIS_TAC[] THEN
	GEN_TAC THEN
	Cases_on `x = v` THEN (
		ASM_SIMP_TAC std_ss [FAPPLY_FUPDATE_THM, FMERGE_DEF]
	)
);


val smallfoot_xenv___local_action_field_assign = prove (``
FASL_IS_LOCAL_ACTION smallfoot_separation_combinator
      (SMALLFOOT_action_map smallfoot_separation_combinator
         (smallfoot_field_assign e1 tag e2))``,

	SIMP_TAC std_ss [FASL_IS_LOCAL_ACTION___ALTERNATIVE_EXT_DEF,
		SMALLFOOT_action_map_def, PAIR_FORALL_THM, LET_THM,
		COND_NONE_SOME_REWRITES, IN_ABS, IN_SING,
		NOT_NONE_IS_SOME] THEN
	REPEAT GEN_TAC THEN STRIP_TAC THEN

	`SMALLFOOT_P_EXPRESSION_EVAL e1 x1'' = 
		SMALLFOOT_P_EXPRESSION_EVAL e1 x1` by
		METIS_TAC[SMALLFOOT_P_EXPRESSION_EVAL___SUBSTATE,
			pairTheory.FST] THEN
	`SMALLFOOT_P_EXPRESSION_EVAL e2 x1'' = 
		SMALLFOOT_P_EXPRESSION_EVAL e2 x1` by
		METIS_TAC[SMALLFOOT_P_EXPRESSION_EVAL___SUBSTATE,
			pairTheory.FST] THEN
	Q.ABBREV_TAC `v_e1 = THE (SMALLFOOT_P_EXPRESSION_EVAL e1 x1)` THEN
	Q.ABBREV_TAC `v_e2 = THE (SMALLFOOT_P_EXPRESSION_EVAL e2 x1)` THEN
	ASM_SIMP_TAC std_ss [] THEN


	FULL_SIMP_TAC std_ss [smallfoot_separation_combinator___REWRITE,
		COND_NONE_SOME_REWRITES]  THEN
	Q.PAT_ASSUM `X = x2''` (ASSUME_TAC o GSYM) THEN
	ASM_SIMP_TAC std_ss [FDOM_FUPDATE, DISJOINT_INSERT,
		GSYM fmap_EQ_THM, FUNION_DEF, IN_UNION] THEN
	`~(v_e1 IN FDOM x2')` by ALL_TAC THEN1 (
		FULL_SIMP_TAC std_ss [DISJOINT_DEF, EXTENSION, IN_INTER, NOT_IN_EMPTY] THEN
		METIS_TAC[]
	) THEN
	ASM_SIMP_TAC std_ss [] THEN
	CONJ_TAC THEN1 (
		SIMP_TAC std_ss [EXTENSION, IN_UNION, IN_INSERT] THEN
		METIS_TAC[]
	) THEN
	GEN_TAC THEN
	Cases_on `x = v_e1` THEN (
		ASM_SIMP_TAC std_ss [IN_UNION, IN_INSERT,
			FDOM_FUPDATE, FAPPLY_FUPDATE_THM, FUNION_DEF]
	)
);





val SMALLFOOT_STATE_RESTRICT_def = Define `
    SMALLFOOT_STATE_RESTRICT (s:smallfoot_state) vs = 
    (DRESTRICT (FST s) vs, SND s)`



val smallfoot___has_read_permission_def = Define `
	smallfoot___has_read_permission v = 
	smallfoot_a_stack_proposition T (var_res_sl___has_read_permission v)`;

val smallfoot___has_write_permission_def = Define `
	smallfoot___has_write_permission v = 
	smallfoot_a_stack_proposition T (var_res_sl___has_write_permission v)`;


val smallfoot_prop_bag_add_read_perms_def = Define `
	smallfoot_prop_bag_add_read_perms wp sfb =
	(\p. if (?v. v IN wp /\ (p = smallfoot___has_read_permission v)) then
		SUC (sfb p) else sfb p)`

val smallfoot_prop_bag_add_read_perms___BAG_INSERT = store_thm (
"smallfoot_prop_bag_add_read_perms___BAG_INSERT",
``smallfoot_prop_bag_add_read_perms wp (BAG_INSERT p sfb) =
BAG_INSERT p (smallfoot_prop_bag_add_read_perms wp sfb)``,

ONCE_REWRITE_TAC[FUN_EQ_THM] THEN
SIMP_TAC std_ss [smallfoot_prop_bag_add_read_perms_def,
	bagTheory.BAG_INSERT] THEN
GEN_TAC THEN
Cases_on `x = p` THEN ASM_REWRITE_TAC[] THEN
METIS_TAC[ADD_CLAUSES]);

val smallfoot___has_read_permission_11 = store_thm ("smallfoot___has_read_permission_11",

``(smallfoot___has_read_permission v1 = smallfoot___has_read_permission v2) = (v1 = v2)``,

EQ_TAC THEN SIMP_TAC std_ss [] THEN
ONCE_REWRITE_TAC[FUN_EQ_THM] THEN
SIMP_TAC std_ss [smallfoot___has_read_permission_def,
	smallfoot_a_stack_proposition_def, var_res_sl___has_read_permission_def, PAIR_FORALL_THM] THEN
REPEAT STRIP_TAC THEN
CCONTR_TAC THEN
Q.PAT_ASSUM `!x1 x2. P x1 x2` (MP_TAC o Q.SPECL [`FEMPTY |+ (v1, X)`, `FEMPTY`]) THEN
ASM_SIMP_TAC std_ss [FDOM_FUPDATE, FDOM_FEMPTY, IN_SING]);




val smallfoot_prop_bag_add_read_perms___INSERT = store_thm (
"smallfoot_prop_bag_add_read_perms___INSERT",
``~(v IN wp) ==>
(smallfoot_prop_bag_add_read_perms (v INSERT wp) sfb =
BAG_INSERT (smallfoot___has_read_permission v) (smallfoot_prop_bag_add_read_perms wp sfb))``,

ONCE_REWRITE_TAC[FUN_EQ_THM] THEN
SIMP_TAC std_ss [smallfoot_prop_bag_add_read_perms_def,
	bagTheory.BAG_INSERT, IN_INSERT, smallfoot___has_read_permission_11] THEN
SIMP_TAC std_ss [RIGHT_AND_OVER_OR, EXISTS_OR_THM] THEN
REPEAT STRIP_TAC THEN
Cases_on `x = smallfoot___has_read_permission v` THEN ASM_REWRITE_TAC[] THEN
DECIDE_TAC);



val smallfoot_ap_star___has_read_permission_IMPL = store_thm (
"smallfoot_ap_star___has_read_permission_IMPL",
``smallfoot_ap_star (smallfoot___has_read_permission v) P (x1,x2) ==>
var_res_sl___has_read_permission v x1``,

SIMP_TAC std_ss [var_res_sl___has_read_permission_def,
	smallfoot_ap_star_def, asl_star_def,
	smallfoot_separation_combinator___REWRITE, COND_NONE_SOME_REWRITES,
	smallfoot___has_read_permission_def, smallfoot_a_stack_proposition_def,
	IN_ABS, PAIR_EXISTS_THM, FDOM_FEMPTY, DISJOINT_EMPTY,
	FUNION_FEMPTY_1] THEN
REPEAT STRIP_TAC THEN
Q.PAT_ASSUM `X = x1` (ASSUME_TAC o GSYM) THEN
ASM_SIMP_TAC std_ss [VAR_RES_STACK_COMBINE_def, BIN_OPTION_MAP_THM,
	FMERGE_DEF, IN_UNION]);



val _ = type_abbrev("smallfoot_prog", 
Type `:(smallfoot_action, 
	(smallfoot_var list # num list), (*procedure args*)
	string (*locks*), 
	string, (*procedure names*)
	smallfoot_pt_proposition, (*predicates*)
	unit, (*select predicates*)
	smallfoot_var, (*select data*)
	smallfoot_state (*states*)
   ) fasl_program`);


val smallfoot_env_def = Define `
	smallfoot_env = (smallfoot_separation_combinator, 
                         SMALLFOOT_PT_PROPOSITION_pred_map, 
                         (\f:smallfoot_state bin_option_function. 
			 \x:unit. \v:smallfoot_var. (\s:smallfoot_state. T)), 
                         SMALLFOOT_action_map)`



val SMALLFOOT_PROGRAM_SEM_def = Define `
	SMALLFOOT_PROGRAM_SEM res_env penv prog =
	FASL_PROGRAM_SEM (smallfoot_env,res_env) penv (prog:smallfoot_prog)`;



val FASL_IS_LOCAL_EVAL_ENV___smallfoot_env = store_thm ("FASL_IS_LOCAL_EVAL_ENV___smallfoot_env",
``FASL_IS_LOCAL_EVAL_ENV (smallfoot_env)``,

SIMP_TAC std_ss [FASL_IS_LOCAL_EVAL_ENV_def, smallfoot_env_def] THEN
REPEAT CONJ_TAC THENL [
	SIMP_TAC std_ss [IS_SEPARATION_COMBINATOR___smallfoot_separation_combinator],
	
	HO_MATCH_MP_TAC smallfoot_pt_proposition_induction THEN
	SIMP_TAC std_ss [SMALLFOOT_PT_PROPOSITION_pred_map_def,
		smallfoot_ap_binexpression_def, ASL_IS_INTUITIONISTIC___REWRITE,
		IS_SEPARATION_COMBINATOR___smallfoot_separation_combinator,
		smallfoot_a_stack_proposition_def, IN_ABS, LET_THM] THEN
	METIS_TAC[SMALLFOOT_P_EXPRESSION_EVAL___SUBSTATE],


	SIMP_TAC std_ss [ASL_IS_SELECT_ASSUME_PREDICATE_def, IN_UNIV],


	Cases_on `action` THEN (
		REWRITE_TAC [smallfoot_xenv___local_action_assign,
				       smallfoot_xenv___local_action_field_lookup,
				       smallfoot_xenv___local_action_field_assign,
				       smallfoot_xenv___local_action_new,
				       smallfoot_xenv___local_action_dispose,
				       smallfoot_xenv___local_action_new_var_init,
				       smallfoot_xenv___local_action_dispose_var]
	)
]);




val SMALLFOOT_SEPARATION_COMBINATOR___EXTRACT = store_thm ("SMALLFOOT_SEPARATION_COMBINATOR___EXTRACT",
``(FST (smallfoot_env) = smallfoot_separation_combinator)``,

SIMP_TAC std_ss [smallfoot_env_def]);



val fasl_select_predicate_IS_SATISFIABLE___smallfoot_env = store_thm ("fasl_select_predicate_IS_SATISFIABLE___smallfoot_env",
``!P c.
fasl_select_predicate_IS_SATISFIABLE smallfoot_env P c``,

SIMP_TAC std_ss [fasl_select_predicate_IS_SATISFIABLE_def,
	XEVAL_fasl_select_predicate_def, smallfoot_env_def,
	asl_true_def, IN_ABS]);


val smallfoot_split_ap_def = Define `smallfoot_split_ap (bp, fp:smallfoot_a_proposition) = \s. (bp /\ (fp s))`;




val VAR_RES_STACK___IS_EQUAL_UPTO_VALUES_def = Define `
VAR_RES_STACK___IS_EQUAL_UPTO_VALUES (st1:('a, 'b) var_res_state) (st2:('a, 'b) var_res_state) =
((!x. ((x IN FDOM st1) /\ (x IN FDOM st2)) ==> (SND (st1 ' x) = SND (st2 ' x))) /\
 (!x. ((x IN FDOM st1) /\ ~(x IN FDOM st2)) ==> (SND (st1 ' x) = var_res_write_permission)) /\
 (!x. (~(x IN FDOM st1) /\ (x IN FDOM st2)) ==> (SND (st2 ' x) = var_res_write_permission)))
`;





val SMALLFOOT_HOARE_TRIPLE_def = Define `
	SMALLFOOT_HOARE_TRIPLE res_env (penv:(string |-> ((smallfoot_var list # num list) -> smallfoot_prog))) P prog Q =
        !x. FASL_PROGRAM_HOARE_TRIPLE (smallfoot_env,res_env) penv
				  (\s. s IN P /\ (s = x)) prog (\s. s IN Q /\ (VAR_RES_STACK___IS_EQUAL_UPTO_VALUES (FST x) (FST s)))`

val SMALLFOOT_REL_HOARE_TRIPLE_def = Define `
SMALLFOOT_REL_HOARE_TRIPLE res_env penv P prog =
!s s'. ((s IN P) /\ (SMALLFOOT_PROGRAM_SEM res_env penv prog s = SOME s')) ==>
    (!s2. s2 IN s' ==> VAR_RES_STACK___IS_EQUAL_UPTO_VALUES (FST s) (FST s2))`;


val SMALLFOOT_HOARE_TRIPLE_REWRITE = store_thm ("SMALLFOOT_HOARE_TRIPLE_REWRITE",
``SMALLFOOT_HOARE_TRIPLE res_env penv P prog Q =
  FASL_PROGRAM_HOARE_TRIPLE (smallfoot_env,res_env) penv P prog Q /\
  SMALLFOOT_REL_HOARE_TRIPLE res_env penv P prog``,

SIMP_TAC std_ss [SMALLFOOT_HOARE_TRIPLE_def, SUBSET_DEF,
		 FASL_PROGRAM_HOARE_TRIPLE_def, IN_ABS,
		 SMALLFOOT_REL_HOARE_TRIPLE_def,
		 HOARE_TRIPLE_def, SMALLFOOT_PROGRAM_SEM_def,
		 fasl_order_THM] THEN
METIS_TAC[SOME_11]);


val SMALLFOOT_PROCEDURE_SPEC_def = Define `
	SMALLFOOT_PROCEDURE_SPEC res_env penv specs =
        FASL_PROCEDURE_SPEC (smallfoot_env,res_env) (penv:(string |-> ((smallfoot_var list # num list) -> smallfoot_prog))) 
			    (\name. ((\arg x s. (s IN ((FST (specs name)) arg (FST x))) /\ (s = SND x)),
				     (\arg x s. (s IN ((SND (specs name)) arg (FST x))) /\ 
				             (VAR_RES_STACK___IS_EQUAL_UPTO_VALUES (FST (SND x)) (FST s))
			            )))`

val SMALLFOOT_PROCEDURE_SPEC_REWRITE = store_thm ("SMALLFOOT_PROCEDURE_SPEC_REWRITE",
``!res_env penv specs procs.
         SMALLFOOT_PROCEDURE_SPEC res_env penv specs procs =
         !name.
           name IN procs ==>
           name IN FDOM penv /\
           !arg x.
              SMALLFOOT_HOARE_TRIPLE res_env penv (FST (specs name) arg x)
               (fasl_prog_procedure_call name arg) (SND (specs name) arg x)``,

SIMP_TAC std_ss [SMALLFOOT_PROCEDURE_SPEC_def, FASL_PROCEDURE_SPEC_def,
		 PAIR_FORALL_THM, SMALLFOOT_HOARE_TRIPLE_def]);






val SMALLFOOT_COND_HOARE_TRIPLE_def = Define `
	SMALLFOOT_COND_HOARE_TRIPLE (Pcond,P) prog (Qcond,Q) =
        ((Pcond /\ Qcond) ==> SMALLFOOT_HOARE_TRIPLE (K smallfoot_ap_true) FEMPTY P prog Q)`;


val SMALLFOOT_COND_HOARE_TRIPLE_TRUE = store_thm ("SMALLFOOT_COND_HOARE_TRIPLE_TRUE",
``SMALLFOOT_COND_HOARE_TRIPLE (T,P) prog (T,Q) =
  SMALLFOOT_HOARE_TRIPLE (K smallfoot_ap_true) FEMPTY P prog Q``,
SIMP_TAC std_ss [SMALLFOOT_COND_HOARE_TRIPLE_def]);



val SMALLFOOT_COND_HOARE_TRIPLE_REWRITE = store_thm (
   "SMALLFOOT_COND_HOARE_TRIPLE_REWRITE",

``SMALLFOOT_COND_HOARE_TRIPLE P prog Q =
  ((FST P /\ FST Q) ==> SMALLFOOT_HOARE_TRIPLE (K smallfoot_ap_true) FEMPTY (SND P) prog (SND Q))``,

Cases_on `P` THEN Cases_on `Q` THEN
SIMP_TAC std_ss [SMALLFOOT_COND_HOARE_TRIPLE_def]);



   

val smallfoot_ap_resource_invariant_def =
Define `smallfoot_ap_resource_invariant wp P =
(\s:smallfoot_state. (FDOM (FST s) = wp) /\
                 (!v. v IN wp ==> (SND ((FST s) ' v) = var_res_write_permission)) /\
		 s IN smallfoot_ap_star smallfoot_ap_stack_true P)`


val SMALLFOOT_res_decls_renv_def = Define `
	SMALLFOOT_res_decls_renv  res_decls =
		let (res_names, res_vars, res_invs_body) = 
			(MAP FST res_decls,
                         MAP (FST o SND) res_decls,
			 MAP (SND o SND) res_decls) in 
                let res_invs = MAP (\(wpb,sf). 
			       (smallfoot_ap_resource_invariant (LIST_TO_SET wpb) sf))
                               (ZIP (res_vars, res_invs_body)) in 
		let res_fmap = LISTS_TO_FMAP (res_names, res_invs) in 
                (FAPPLY res_fmap)`;



val SMALLFOOT_proc_specs_penv_def = Define `
	SMALLFOOT_proc_specs_penv  proc_specs =
		LISTS_TO_FMAP (MAP FST proc_specs, MAP (FST o SND) proc_specs)`

val SMALLFOOT_proc_specs_spec_def = Define `
	SMALLFOOT_proc_specs_spec  proc_specs =
		let (pnames, precond, postcond) = 
			(MAP FST proc_specs,
                         MAP (FST o SND o SND) proc_specs,
			 MAP (SND o SND o SND) proc_specs) in
		let conds = ZIP (precond, postcond) in 
		let cond_fmap = LISTS_TO_FMAP (pnames, conds) in 
		(FAPPLY cond_fmap)`

val SMALLFOOT_SPECIFICATION_def = Define `
	SMALLFOOT_SPECIFICATION res_decls proc_specs =
		let (pnames, body, precond, postcond) = 
			(MAP FST proc_specs,
                         MAP (FST o SND) proc_specs,
                         MAP (FST o SND o SND) proc_specs,
			 MAP (SND o SND o SND) proc_specs) in 
		let conds = ZIP (precond, postcond) in 
		let penv = LISTS_TO_FMAP (pnames, body) in
		let cond_fmap = LISTS_TO_FMAP (pnames, conds) in 
		let (res_names, res_vars, res_invs_body) = 
			(MAP FST res_decls,
                         MAP (FST o SND) res_decls,
			 MAP (SND o SND) res_decls) in 
                let res_invs = MAP (\(wpb,sf). smallfoot_ap_resource_invariant (LIST_TO_SET wpb) sf) (ZIP (res_vars, res_invs_body)) in 
		let res_fmap = LISTS_TO_FMAP (res_names, res_invs) in 
		SMALLFOOT_PROCEDURE_SPEC (FAPPLY res_fmap) penv (FAPPLY cond_fmap) (FDOM penv)`


val SMALLFOOT_SPECIFICATION_THM = store_thm ("SMALLFOOT_SPECIFICATION_THM",
``SMALLFOOT_SPECIFICATION res_decls proc_specs = 
SMALLFOOT_PROCEDURE_SPEC (SMALLFOOT_res_decls_renv res_decls) (SMALLFOOT_proc_specs_penv proc_specs) (SMALLFOOT_proc_specs_spec proc_specs) (FDOM (SMALLFOOT_proc_specs_penv proc_specs))``,


SIMP_TAC std_ss [SMALLFOOT_SPECIFICATION_def, LET_THM, SMALLFOOT_proc_specs_penv_def,
SMALLFOOT_proc_specs_spec_def, SMALLFOOT_res_decls_renv_def]);



val FDOM_SMALLFOOT_proc_specs_penv = store_thm ("FDOM_SMALLFOOT_proc_specs_penv",
	``FDOM (SMALLFOOT_proc_specs_penv proc_specs) =
		LIST_TO_SET (MAP FST proc_specs)``,

SIMP_TAC std_ss [SMALLFOOT_proc_specs_penv_def] THEN
Induct_on `proc_specs` THENL [
	SIMP_TAC list_ss [LISTS_TO_FMAP_def, FDOM_FEMPTY],
	ASM_SIMP_TAC list_ss [LISTS_TO_FMAP_def, FDOM_FUPDATE]
]);




val SMALLFOOT_proc_specs_MEM_REWRITES = store_thm ("SMALLFOOT_proc_specs_MEM_REWRITES",
``!proc_specs name fbody pre post.
(ALL_DISTINCT (MAP FST proc_specs) /\
(MEM (name,fbody,pre,post) proc_specs)) ==>

(((SMALLFOOT_proc_specs_spec proc_specs name) = (pre, post)) /\
((SMALLFOOT_proc_specs_penv proc_specs ' name) = fbody))``,


Induct_on `proc_specs` THEN1 (
	SIMP_TAC list_ss []
) THEN
SIMP_TAC list_ss [LEFT_AND_OVER_OR, DISJ_IMP_THM, FORALL_AND_THM] THEN
CONJ_TAC THEN1 (
	REPEAT GEN_TAC THEN STRIP_TAC THEN
	SIMP_TAC list_ss [SMALLFOOT_proc_specs_penv_def,
		SMALLFOOT_proc_specs_spec_def, LET_THM,
		LISTS_TO_FMAP_def, FAPPLY_FUPDATE_THM]
) THEN
REPEAT GEN_TAC THEN STRIP_TAC THEN
`~(FST h = name)` by ALL_TAC THEN1 (
	CCONTR_TAC THEN
	FULL_SIMP_TAC std_ss [MEM_MAP] THEN
	METIS_TAC [pairTheory.FST]
) THEN
RES_TAC THEN NTAC 2 (POP_ASSUM MP_TAC) THEN

ASM_SIMP_TAC list_ss [SMALLFOOT_proc_specs_penv_def, LISTS_TO_FMAP_def, FAPPLY_FUPDATE_THM, SMALLFOOT_proc_specs_spec_def, LET_THM]);








val smallfoot_prog_assign_def = Define
`(smallfoot_prog_assign v e):smallfoot_prog = fasl_prog_prim_command (fasl_pc_local_action (smallfoot_assign v e))`

val smallfoot_prog_field_lookup_def = Define `
(smallfoot_prog_field_lookup v e t):smallfoot_prog = fasl_prog_prim_command (fasl_pc_local_action (smallfoot_field_lookup v e t))`

val smallfoot_prog_field_assign_def = Define `
(smallfoot_prog_field_assign e1 t e2):smallfoot_prog = fasl_prog_prim_command (fasl_pc_local_action (smallfoot_field_assign e1 t e2))`

val smallfoot_prog_new_def = Define `
(smallfoot_prog_new v):smallfoot_prog = fasl_prog_prim_command (fasl_pc_local_action (smallfoot_new v))`

val smallfoot_prog_dispose_def = Define `
(smallfoot_prog_dispose e):smallfoot_prog = fasl_prog_prim_command (fasl_pc_local_action (smallfoot_dispose e))`;

val smallfoot_prog_new_var_init_def = Define `
(smallfoot_prog_new_var_init v e):smallfoot_prog = fasl_prog_prim_command (fasl_pc_local_action (smallfoot_new_var_init v e))`;

val smallfoot_prog_new_var_def = Define `
smallfoot_prog_new_var v = fasl_prog_ndet (\p. ?c. p = smallfoot_prog_new_var_init v (smallfoot_p_const c))`;



val smallfoot_prog_with_resource_def = Define `smallfoot_prog_with_resource r
c (body:smallfoot_prog) = 
fasl_prog_critical_section r (fasl_prog_seq (fasl_prog_prim_command 
                                            (fasl_pc_assume c))
                                             body)`;




val smallfoot_prog_dispose_var_def = Define `
(smallfoot_prog_dispose_var v):smallfoot_prog = fasl_prog_prim_command (fasl_pc_local_action (smallfoot_dispose_var v))`



val smallfoot_prog_choose_constants_def = Define `
(smallfoot_prog_choose_constants prog expL):smallfoot_prog = 

fasl_prog_ndet 
(IMAGE (\constL.
fasl_prog_seq 
   (fasl_prog_prim_command (fasl_pc_assume (fasl_pred_bigand
      (MAP (\x. smallfoot_p_equal (FST x) (smallfoot_p_const (SND x)))
      (ZIP (expL, constL))))))
   (prog constL))
 (\l. LENGTH l = LENGTH expL))`





val smallfoot_prog_procedure_call_def = Define `
(smallfoot_prog_procedure_call name (ref_argL, val_argL)):smallfoot_prog = 

smallfoot_prog_choose_constants
   (\constL.(fasl_prog_procedure_call name (ref_argL, constL)))
   val_argL`;




val smallfoot_prog_parallel_procedure_call_def = Define `
smallfoot_prog_parallel_procedure_call name1 (ref_argL1, val_argL1) 
                                       name2 (ref_argL2, val_argL2) = 

smallfoot_prog_choose_constants
   (\constL1. smallfoot_prog_choose_constants (\constL2.
               (fasl_prog_parallel 
                  (fasl_prog_procedure_call name1 (ref_argL1, constL1))
                  (fasl_prog_procedure_call name2 (ref_argL2, constL2))))
               val_argL2)
   val_argL1`;




val smallfoot_prog_val_arg_def = Define `smallfoot_prog_val_arg prog_body c =
	(fasl_prog_select () (\x. fasl_prog_seq 
				  (smallfoot_prog_new_var_init x (smallfoot_p_const c)) 
                                  (fasl_prog_seq (prog_body x) (smallfoot_prog_dispose_var x))))`;





val smallfoot_prog_local_var_def = Define `smallfoot_prog_local_var prog_body =
	BIGUNION (\p. ?e. p = $smallfoot_prog_val_arg prog_body e)`







val SMALLFOOT_HOARE_TRIPLE_INST_def = Define `
    SMALLFOOT_HOARE_TRIPLE_INST res_env penv pre body post =
!cond_arg arg_refL arg_valL. 
SMALLFOOT_HOARE_TRIPLE res_env penv 
    (pre (arg_refL,arg_valL) cond_arg)
    (body (arg_refL,arg_valL))
    (post (arg_refL,arg_valL) cond_arg)`;

   

			      

val SMALLFOOT_SPECIFICATION___INFERENCE = store_thm ("SMALLFOOT_SPECIFICATION___INFERENCE",
``!res_decls proc_specs. 
(ALL_DISTINCT (MAP FST proc_specs) /\
(!penv. (EVERY (\(name, fbody, pre, post). 
                SMALLFOOT_HOARE_TRIPLE_INST (SMALLFOOT_res_decls_renv res_decls) penv pre (fasl_prog_procedure_call name) post)
               proc_specs) ==>
        (EVERY (\(name, fbody, pre, post).
	(SMALLFOOT_HOARE_TRIPLE_INST (SMALLFOOT_res_decls_renv res_decls) penv pre fbody post)) proc_specs))) ==>

SMALLFOOT_SPECIFICATION res_decls proc_specs``,

SIMP_TAC std_ss [SMALLFOOT_PROCEDURE_SPEC_def, SMALLFOOT_SPECIFICATION_THM,
		 SMALLFOOT_HOARE_TRIPLE_INST_def] THEN
REPEAT STRIP_TAC THEN
MATCH_MP_TAC FASL_INFERENCE___PROCEDURE_SPEC THEN
FULL_SIMP_TAC list_ss [FDOM_SMALLFOOT_proc_specs_penv,
	FASL_PROCEDURE_SPEC_def, SMALLFOOT_HOARE_TRIPLE_def] THEN
REPEAT STRIP_TAC THEN
Q.PAT_ASSUM `!penv. EVERY (P penv) proc_spec ==> X` (fn thm =>
	let
		val thm0 = Q.SPEC `penv'` thm;
		val (t, _) = dest_imp (concl thm0);
	in
		SUBGOAL_THEN t (fn thm => (ASSUME_TAC (MP thm0 thm)))
	end) THEN1 (
	
	SIMP_TAC list_ss [EVERY_MEM] THEN
	GEN_TAC THEN
	`?name fbody pre post. e = (name, fbody, pre, post)` by ALL_TAC THEN1 (
		Cases_on `e` THEN
		Cases_on `r` THEN
		Cases_on `r'` THEN
		SIMP_TAC std_ss []
	) THEN
	ASM_SIMP_TAC std_ss [] THEN
	STRIP_TAC THEN
	Q.PAT_ASSUM `!name. X name` (ASSUME_TAC o Q.SPEC `name`) THEN
	`MEM name (MAP FST proc_specs)` by ALL_TAC THEN1 (
		ASM_SIMP_TAC std_ss [MEM_MAP] THEN
		METIS_TAC[pairTheory.FST]
	) THEN
	FULL_SIMP_TAC std_ss [] THEN
	
	Q.PAT_ASSUM `!arg x. P arg x` MP_TAC THEN
	IMP_RES_TAC SMALLFOOT_proc_specs_MEM_REWRITES THEN
	ASM_SIMP_TAC std_ss [PAIR_FORALL_THM]
) THEN


FULL_SIMP_TAC std_ss [EVERY_MEM] THEN
`?fbody pre post. MEM (proc, fbody, pre, post) proc_specs` by ALL_TAC THEN1 (
	FULL_SIMP_TAC std_ss [MEM_MAP] THEN
	Cases_on `y` THEN
	Cases_on `r` THEN
	Cases_on `r'` THEN
	ASM_SIMP_TAC std_ss [] THEN
	METIS_TAC[]
) THEN
Q.PAT_ASSUM `!e. X e` (MP_TAC o Q.SPEC `(proc, fbody, pre, post)`) THEN
ASM_SIMP_TAC std_ss [] THEN
IMP_RES_TAC SMALLFOOT_proc_specs_MEM_REWRITES THEN
Cases_on `arg` THEN
ASM_SIMP_TAC std_ss []);




val smallfoot_slp_init_var_def = Define `
    smallfoot_slp_init_var v e P =
    \s:smallfoot_state. ?x. (var_res_sl___read v (FST s) = SOME (x, var_res_write_permission)) /\
	                         let st' = (FST s) \\ v in
				     P (st', (SND s)) /\ (e st' = SOME x)`



val smallfoot_slp_new_var_def = Define `
    smallfoot_slp_new_var v P = asl_exists e. smallfoot_slp_init_var v e P`;


val smallfoot_slp_new_var_EXPAND = store_thm ("smallfoot_slp_new_var_EXPAND",
``smallfoot_slp_new_var v P =
    \s:smallfoot_state. ?x. (var_res_sl___read v (FST s) = SOME (x, var_res_write_permission)) /\
	                         let st' = (FST s) \\ v in
				     P (st', (SND s))``,

SIMP_TAC std_ss [smallfoot_slp_new_var_def, smallfoot_slp_init_var_def, FUN_EQ_THM] THEN
SIMP_TAC std_ss [asl_exists_def, IN_ABS, LET_THM] THEN
REPEAT STRIP_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THENL [
   Q.EXISTS_TAC `x'` THEN
   ASM_SIMP_TAC std_ss [],


   Q.EXISTS_TAC `K (SOME x)` THEN
   Q.EXISTS_TAC `x` THEN
   ASM_SIMP_TAC std_ss []
]);



val smallfoot_slp_new_var_ALTERNATIVE_DEF = store_thm ("smallfoot_slp_new_var_ALTERNATIVE_DEF",
``smallfoot_slp_new_var v P = asl_exists c. smallfoot_slp_init_var v (smallfoot_ae_const c) P``,

SIMP_TAC std_ss [smallfoot_slp_init_var_def, smallfoot_ae_const_def, smallfoot_slp_new_var_EXPAND,
		 asl_exists_def, IN_ABS, FUN_EQ_THM] THEN
METIS_TAC[]);






val fasl_slp_opt___smallfoot_prog_new_var_init = store_thm (
"fasl_slp_opt___smallfoot_prog_new_var_init",
``
!res_env penv P v e.

fasl_slp_opt (smallfoot_env, res_env) penv P (smallfoot_prog_new_var_init v e) =
(if smallfoot_ae_is_defined P (SMALLFOOT_P_EXPRESSION_EVAL e) then
SOME (smallfoot_slp_init_var v (SMALLFOOT_P_EXPRESSION_EVAL e) P) else
NONE)``,
	 


SIMP_TAC list_ss [fasl_slp_opt___EXPANDED_DEF,
	smallfoot_prog_new_var_init_def, FASL_PROGRAM_TRACES_IN_THM,
	IN_SING, 
	FASL_TRACE_SEM_def, FASL_ATOMIC_ACTION_SEM_def,
	fasla_big_seq_def, fasla_seq_skip,
	EVAL_fasl_prim_command_def, smallfoot_env_def,
	COND_NONE_SOME_REWRITES,
	COND_NONE_SOME_REWRITES_EQ,
        SMALLFOOT_action_map_def, PAIR_FORALL_THM, LET_THM,
        smallfoot_ae_is_defined_def, PAIR_EXISTS_THM] THEN
REPEAT STRIP_TAC THEN1 (
   SIMP_TAC std_ss [IN_DEF, NOT_NONE_IS_SOME] THEN
   PROVE_TAC[]
) THEN
REWRITE_TAC [EXTENSION] THEN
SIMP_TAC std_ss [IN_ABS, smallfoot_slp_init_var_def, var_res_sl___read_def,
		 COND_NONE_SOME_REWRITES, LET_THM] THEN
Cases_on `x` THEN
SIMP_TAC std_ss [COND_RATOR, COND_RAND, NOT_IN_EMPTY, IN_SING, NOT_NONE_IS_SOME, 
   IS_SOME_EXISTS, GSYM LEFT_EXISTS_AND_THM, GSYM RIGHT_EXISTS_AND_THM] THEN
EQ_TAC THEN STRIP_TAC THENL [
   FULL_SIMP_TAC std_ss [FDOM_FUPDATE, IN_INSERT, FAPPLY_FUPDATE_THM, DOMSUB_FUPDATE_THM] THEN
   `x1 \\ v = x1` by ALL_TAC THEN1 (
      ASM_SIMP_TAC std_ss [GSYM fmap_EQ_THM, FDOM_DOMSUB, EXTENSION, IN_DELETE,
			   DOMSUB_FAPPLY_THM] THEN
      METIS_TAC[]
   ) THEN
   FULL_SIMP_TAC std_ss [IN_DEF],


   Q.EXISTS_TAC `q \\ v` THEN
   ASM_SIMP_TAC std_ss [FDOM_DOMSUB, IN_DELETE] THEN
   ASM_SIMP_TAC std_ss [IN_DEF] THEN
   SIMP_TAC std_ss [GSYM fmap_EQ_THM, FDOM_FUPDATE, FDOM_DOMSUB,
		    IN_INSERT, IN_DELETE,
		    FAPPLY_FUPDATE_THM, DOMSUB_FAPPLY_THM, EXTENSION] THEN
   METIS_TAC[]
]);








val fasl_slp_opt___smallfoot_prog_new_var = store_thm (
"fasl_slp_opt___smallfoot_prog_new_var",
``
!res_env penv P v.

(fasl_slp_opt (smallfoot_env,res_env) penv P (smallfoot_prog_new_var v) =
SOME (smallfoot_slp_new_var v P))``,
	   


SIMP_TAC std_ss [smallfoot_prog_new_var_def, fasl_slp_opt___prog_ndet, IN_ABS,
		 GSYM LEFT_FORALL_IMP_THM, fasl_slp_opt___smallfoot_prog_new_var_init,
		 IMAGE_ABS, GSYM RIGHT_EXISTS_AND_THM,
		 smallfoot_ae_is_defined_def, SMALLFOOT_P_EXPRESSION_EVAL_def,
		 smallfoot_ae_const_def] THEN

REWRITE_TAC [Once EXTENSION] THEN
SIMP_TAC std_ss [smallfoot_slp_new_var_ALTERNATIVE_DEF, IN_BIGUNION, IN_ABS,
		 GSYM RIGHT_EXISTS_AND_THM, asl_exists_def,
		 smallfoot_ae_const_def]);






val fasl_wlp_opt___smallfoot_prog_dispose_var = store_thm (
"fasl_wlp_opt___smallfoot_prog_dispose_var",
``
!res_env penv Q v.

(fasl_wlp_opt (smallfoot_env,res_env) penv (smallfoot_prog_dispose_var v) Q =
SOME (smallfoot_slp_new_var v Q))``,
	   


SIMP_TAC std_ss [fasl_wlp_opt_def, COND_NONE_SOME_REWRITES, 
		 COND_NONE_SOME_REWRITES_EQ, smallfoot_prog_dispose_var_def] THEN
REPEAT STRIP_TAC THEN1 (
    FULL_SIMP_TAC std_ss [EXTENSION, NOT_IN_EMPTY, FASL_PROGRAM_TRACES_IN_THM]
) THEN

SIMP_TAC std_ss [fasl_wlp_def, EXTENSION] THEN
SIMP_TAC list_ss [IN_BIGUNION, IN_ABS, FASL_PROGRAM_HOARE_TRIPLE_REWRITE,
		 FASL_PROGRAM_TRACES_IN_THM, FASL_TRACE_SEM_def,
		 fasla_big_seq_def, fasla_seq_skip, FASL_ATOMIC_ACTION_SEM_def,
	         EVAL_fasl_prim_command_THM, smallfoot_env_def,
		 SMALLFOOT_action_map_def, PAIR_FORALL_THM, PAIR_EXISTS_THM,
		 smallfoot_slp_new_var_EXPAND,
		 COND_NONE_SOME_REWRITES] THEN
REPEAT STRIP_TAC THEN EQ_TAC THEN STRIP_TAC THENL [
   RES_TAC THEN
   FULL_SIMP_TAC std_ss [var_res_sl___has_write_permission_def,
			 var_res_sl___read_def, LET_THM, SUBSET_DEF,
			 IN_SING] THEN
   Cases_on `x1 ' v` THEN
   FULL_SIMP_TAC std_ss [IN_DEF],


   Q.EXISTS_TAC `{(x1,x2)}` THEN
   FULL_SIMP_TAC std_ss [var_res_sl___read_def, IN_SING, LET_THM, SUBSET_DEF,
			 var_res_sl___has_write_permission_def, COND_NONE_SOME_REWRITES] THEN
   ASM_SIMP_TAC std_ss [IN_DEF]
]);




val SMALLFOOT_STACK_UPDATE_VAR_def = Define `
    SMALLFOOT_STACK_UPDATE_VAR v c p (st:smallfoot_stack) = 
       (st |+ (v, c, p))`;




val SMALLFOOT_STATE_UPDATE_VAR_def = Define `
    SMALLFOOT_STATE_UPDATE_VAR v c p (s:smallfoot_state) = 
       (SMALLFOOT_STACK_UPDATE_VAR v c p (FST s), SND s)`;

  

val SMALLFOOT_STATE_UPDATE_HEAP_def = Define `
    SMALLFOOT_STATE_UPDATE_HEAP c1 t c2 (s:smallfoot_state) =
         (FST s, let st = SND s in
	         let old_value = if c1 IN FDOM st then st ' c1 else FEMPTY in
                 let new_value = old_value |+ (t, c2) in
		 st |+ (c1, new_value))`;

val SMALLFOOT_STATE_REMOVE_HEAP_TAG_def = Define `
    SMALLFOOT_STATE_REMOVE_HEAP_TAG c t (s:smallfoot_state) =
         (FST s, let st = SND s in
	         let old_value = if c IN FDOM st then st ' c else FEMPTY in
                 let new_value = old_value \\ t in
		 st |+ (c, new_value))`;



val smallfoot_slp_field_lookup_def = Define `
   smallfoot_slp_field_lookup v e t P = \s. 
       ?c1 c2. (var_res_sl___read v (FST s) = SOME (c1, var_res_write_permission)) /\
	       (let sold = SMALLFOOT_STATE_UPDATE_VAR v c2 var_res_write_permission s in
		   ((smallfoot_ae_stack_read e t sold = SOME c1) /\
                    ((P sold) \/ let e_opt = e (FST sold) in
        	     P (SMALLFOOT_STATE_REMOVE_HEAP_TAG (THE e_opt) t sold))))
`;



val fasl_slp_opt___smallfoot_prog_field_lookup = store_thm ("fasl_slp_opt___smallfoot_prog_field_lookup",
``
!res_env penv P v e t. 
fasl_slp_opt (smallfoot_env,res_env) penv P (smallfoot_prog_field_lookup v e t) =

(if ((smallfoot_ap_implies_writeperm P v) /\ (smallfoot_ap_implies_in_heap P (SMALLFOOT_P_EXPRESSION_EVAL e))) then
SOME (smallfoot_slp_field_lookup v (SMALLFOOT_P_EXPRESSION_EVAL e) t P) else NONE)``,
	   

SIMP_TAC list_ss [fasl_slp_opt___EXPANDED_DEF,
		 smallfoot_prog_field_lookup_def, FASL_PROGRAM_TRACES_IN_THM,
		 FASL_TRACE_SEM_def, fasla_big_seq_def, fasla_seq_skip,
		 smallfoot_env_def,
		 FASL_ATOMIC_ACTION_SEM_def, EVAL_fasl_prim_command_THM,
		 SMALLFOOT_action_map_def, PAIR_FORALL_THM, LET_THM, PAIR_EXISTS_THM,
		 COND_NONE_SOME_REWRITES, IN_SING, COND_NONE_SOME_REWRITES_EQ] THEN
REPEAT GEN_TAC THEN
Q.ABBREV_TAC `ee = SMALLFOOT_P_EXPRESSION_EVAL e` THEN

REPEAT STRIP_TAC THEN1 (
   SIMP_TAC std_ss [smallfoot_ap_implies_writeperm_def,
		    smallfoot_ap_implies_in_heap_def, COND_NONE_SOME_REWRITES,
		    smallfoot_ae_stack_read_def, PAIR_FORALL_THM] THEN
   SIMP_TAC (std_ss++boolSimps.CONJ_ss) [NOT_NONE_IS_SOME, IS_SOME_EXISTS,
		    GSYM RIGHT_EXISTS_AND_THM, GSYM LEFT_EXISTS_AND_THM,
		    IN_DEF] THEN
   METIS_TAC[]
) THEN
ONCE_REWRITE_TAC [EXTENSION] THEN
SIMP_TAC std_ss [smallfoot_slp_field_lookup_def, IN_ABS, LET_THM,
		 var_res_sl___read_def, SMALLFOOT_STATE_UPDATE_VAR_def, COND_NONE_SOME_REWRITES,
		 SMALLFOOT_STACK_UPDATE_VAR_def] THEN
GEN_TAC THEN EQ_TAC THENL [
   STRIP_TAC THEN
   FULL_SIMP_TAC std_ss [smallfoot_ap_implies_stack_read_def,
			 var_res_sl___has_write_permission_def,
			 COND_RAND, COND_RATOR,
			 IN_ABS, IN_SING] THEN
   Cases_on `ee x1` THEN FULL_SIMP_TAC std_ss [] THEN
   `x1 |+ (v,FST (x1 ' v),var_res_write_permission) = x1` by ALL_TAC THEN1 (
         Cases_on `x1 ' v` THEN
         FULL_SIMP_TAC std_ss [GSYM fmap_EQ_THM, FDOM_FUPDATE, IN_INSERT, EXTENSION,
			   DISJ_IMP_THM] THEN
         METIS_TAC[FAPPLY_FUPDATE_THM]
   ) THEN
   Cases_on `t IN FDOM (x2 ' x')` THEN
   FULL_SIMP_TAC std_ss [smallfoot_ae_stack_read_def, COND_NONE_SOME_REWRITES, FDOM_FUPDATE,
			 IN_INSERT, FAPPLY_FUPDATE_THM, FUPDATE_EQ] THEN (
      Q.EXISTS_TAC `FST (x1 ' v)` THEN
      ASM_SIMP_TAC std_ss []
   ) THENL [
      FULL_SIMP_TAC std_ss [IN_DEF],


      SIMP_TAC std_ss [FDOM_FUPDATE, IN_INSERT,
		       FAPPLY_FUPDATE_THM] THEN
      Tactical.REVERSE (`(SMALLFOOT_STATE_REMOVE_HEAP_TAG x' t
         (x1,x2 |+ (x',x2 ' x' |+ (t,new_v)))) = (x1, x2)` by ALL_TAC) THEN1 (
         FULL_SIMP_TAC std_ss [IN_DEF]
      ) THEN
      SIMP_TAC std_ss [SMALLFOOT_STATE_REMOVE_HEAP_TAG_def,
		       LET_THM, FDOM_FUPDATE, IN_INSERT,
		       FAPPLY_FUPDATE_THM,
		       FUPDATE_EQ] THEN
      ASM_SIMP_TAC (std_ss++bool_eq_imp_ss++boolSimps.CONJ_ss) 
                      [GSYM fmap_EQ_THM, FDOM_FUPDATE,
		       EXTENSION, IN_INSERT, DISJ_IMP_THM,
		       FORALL_AND_THM, FAPPLY_FUPDATE_THM,
		       FDOM_DOMSUB, IN_DELETE,
		       DOMSUB_FAPPLY_THM] THEN
      GEN_TAC THEN STRIP_TAC THEN
      Cases_on `x'' = x'` THENL [
         ASM_SIMP_TAC (std_ss++boolSimps.CONJ_ss++bool_eq_imp_ss)
                             [FDOM_FUPDATE, FDOM_DOMSUB,
			      IN_INSERT, IN_DELETE, FAPPLY_FUPDATE_THM,
			      DOMSUB_FAPPLY_THM] THEN
	 REPEAT STRIP_TAC THEN
	 `~(t = x''')` by PROVE_TAC[] THEN
	 ASM_SIMP_TAC std_ss [],


	 ASM_SIMP_TAC std_ss []
      ]
   ],


   STRIP_TAC THENL [
      Q.EXISTS_TAC `FST x |+ (v,c2,var_res_write_permission)` THEN
      Q.EXISTS_TAC `SND x` THEN 
      Cases_on `x` THEN   
      FULL_SIMP_TAC std_ss [smallfoot_ae_stack_read_def, COND_NONE_SOME_REWRITES, FUPDATE_EQ,
			    IN_SING] THEN
      Q.PAT_ASSUM `v IN FDOM q` ASSUME_TAC THEN
      Q.PAT_ASSUM `q ' v = X` ASSUME_TAC THEN
      FULL_SIMP_TAC std_ss [COND_REWRITES] THEN
      REPEAT STRIP_TAC THENL [
         PROVE_TAC[IN_DEF],

         SIMP_TAC std_ss [var_res_sl___has_write_permission_def, FAPPLY_FUPDATE_THM,
		       FDOM_FUPDATE, IN_INSERT],

         SIMP_TAC std_ss [GSYM fmap_EQ_THM, FDOM_FUPDATE, IN_INSERT, FAPPLY_FUPDATE_THM,
		       EXTENSION] THEN
         METIS_TAC[optionTheory.option_CLAUSES]
      ],


      Q.PAT_ASSUM `P X` MP_TAC THEN
      FULL_SIMP_TAC std_ss [SMALLFOOT_STATE_REMOVE_HEAP_TAG_def,
			   LET_THM, smallfoot_ae_stack_read_def,
			   COND_NONE_SOME_REWRITES] THEN
      Q.PAT_ASSUM `X = SOME loc` ASSUME_TAC THEN
      FULL_SIMP_TAC std_ss [] THEN
      STRIP_TAC THEN
      Q.EXISTS_TAC `FST x |+ (v,c2,var_res_write_permission)` THEN
      Q.EXISTS_TAC `SND x |+ (loc,SND x ' loc \\ t)` THEN 
      Cases_on `x` THEN   
      FULL_SIMP_TAC std_ss [FAPPLY_FUPDATE_THM, FDOM_DOMSUB,
			    IN_DELETE, FDOM_FUPDATE, IN_INSERT,
			    IN_ABS] THEN
      REPEAT STRIP_TAC THENL [
         PROVE_TAC[IN_DEF],

         SIMP_TAC std_ss [var_res_sl___has_write_permission_def, FAPPLY_FUPDATE_THM,
		       FDOM_FUPDATE, IN_INSERT],

	 Q.EXISTS_TAC `c1` THEN
         SIMP_TAC std_ss [FUPDATE_EQ] THEN
	 ASM_SIMP_TAC (std_ss++bool_eq_imp_ss) 
                             [GSYM fmap_EQ_THM, EXTENSION,
			      FAPPLY_FUPDATE_THM, FDOM_FUPDATE,
			      IN_INSERT] THEN
	 REPEAT STRIP_TAC THENL [
	    ASM_SIMP_TAC std_ss [COND_RATOR, COND_RAND],


	    ASM_SIMP_TAC std_ss [COND_RATOR, COND_RAND, FDOM_FUPDATE,
				 FDOM_DOMSUB, IN_INSERT, IN_DELETE] THEN
	    Cases_on `x' = t` THEN
	    ASM_SIMP_TAC std_ss [],


	    ASM_SIMP_TAC std_ss [COND_RAND, COND_RATOR,
			     FAPPLY_FUPDATE_THM,
				 DOMSUB_FAPPLY_THM] THEN
	    Cases_on `x' = t` THEN ASM_SIMP_TAC std_ss []
         ]
     ]
   ]
]);






val smallfoot_slp_field_assign_def = Define `
   smallfoot_slp_field_assign e1 t e2 P = \s:smallfoot_state. 
       let e1_opt = e1 (FST s) in 
       let e2_opt = e2 (FST s) in 
       (IS_SOME e1_opt) /\ (IS_SOME e2_opt) /\ 
       (smallfoot_ae_stack_read e1 t s = e2_opt) /\
       ((?c. (P (SMALLFOOT_STATE_UPDATE_HEAP (THE e1_opt) t c s))) \/
             (P (SMALLFOOT_STATE_REMOVE_HEAP_TAG (THE e1_opt) t s)))`;



val fasl_slp_opt___smallfoot_prog_field_assign = store_thm ("fasl_slp_opt___smallfoot_prog_field_assign",
``
!res_env penv P e1 e2 t. 
fasl_slp_opt (smallfoot_env,res_env) penv P (smallfoot_prog_field_assign e1 t e2) =

(if ((smallfoot_ae_is_defined P (SMALLFOOT_P_EXPRESSION_EVAL e2)) /\
     (smallfoot_ap_implies_in_heap P (SMALLFOOT_P_EXPRESSION_EVAL e1))) then
SOME (smallfoot_slp_field_assign (SMALLFOOT_P_EXPRESSION_EVAL e1) t (SMALLFOOT_P_EXPRESSION_EVAL e2) P) else NONE)``,


REPEAT GEN_TAC THEN
Q.ABBREV_TAC `ee1 = SMALLFOOT_P_EXPRESSION_EVAL e1` THEN
Q.ABBREV_TAC `ee2 = SMALLFOOT_P_EXPRESSION_EVAL e2` THEN

ASM_SIMP_TAC list_ss [fasl_slp_opt___EXPANDED_DEF, smallfoot_prog_field_assign_def,
		 FASL_PROGRAM_TRACES_IN_THM, FASL_TRACE_SEM_def,
		 FASL_ATOMIC_ACTION_SEM_def, 
		 smallfoot_env_def, fasla_seq_skip, fasla_big_seq_def,
		 EVAL_fasl_prim_command_THM, SMALLFOOT_action_map_def,
		 PAIR_FORALL_THM, PAIR_EXISTS_THM, LET_THM,
		 COND_NONE_SOME_REWRITES, IN_SING,
                 COND_NONE_SOME_REWRITES_EQ,
		 smallfoot_ae_is_defined_def,
		 smallfoot_ap_implies_in_heap_def] THEN
REPEAT STRIP_TAC THEN1 (
   METIS_TAC[optionTheory.option_CLAUSES, IN_DEF]
) THEN

REWRITE_TAC [EXTENSION] THEN
Cases_on `x` THEN
SIMP_TAC std_ss [smallfoot_slp_field_assign_def, LET_THM, IN_ABS,
		 NOT_NONE_IS_SOME, IS_SOME_EXISTS] THEN
EQ_TAC THEN STRIP_TAC THENL [
   Q.PAT_ASSUM `ee1 q = X` ASSUME_TAC THEN
   Q.PAT_ASSUM `ee2 q = X` ASSUME_TAC THEN
   FULL_SIMP_TAC std_ss [smallfoot_ae_stack_read_def, FDOM_FUPDATE, IN_INSERT,
			 FAPPLY_FUPDATE_THM, SMALLFOOT_STATE_UPDATE_HEAP_def, LET_THM,
			 FUPDATE_EQ, SMALLFOOT_STATE_REMOVE_HEAP_TAG_def,
			 DOMSUB_FUPDATE_THM] THEN
   Cases_on `t IN FDOM (x2 ' y)` THENL [
       DISJ1_TAC THEN
       Q.EXISTS_TAC `x2 ' y ' t` THEN
       Tactical.REVERSE (`x2 |+ (y,x2 ' y |+ (t,x2 ' y ' t)) = x2` by ALL_TAC) THEN1 (
          ASM_REWRITE_TAC [] THEN
          PROVE_TAC[IN_DEF]
       ) THEN
       ASM_SIMP_TAC std_ss [GSYM fmap_EQ_THM, EXTENSION, FDOM_FUPDATE, FDOM_DOMSUB,
			    IN_INSERT, FAPPLY_FUPDATE_THM, COND_RAND, COND_RATOR] THEN
       METIS_TAC[],



       DISJ2_TAC THEN
       Tactical.REVERSE (`x2 |+ (y,x2 ' y \\ t) =x2` by ALL_TAC) THEN1 (
          ASM_REWRITE_TAC [] THEN
          PROVE_TAC[IN_DEF]
       ) THEN
       ASM_SIMP_TAC std_ss [GSYM fmap_EQ_THM, EXTENSION, FDOM_FUPDATE, FDOM_DOMSUB,
			    IN_INSERT, FAPPLY_FUPDATE_THM, COND_RAND, COND_RATOR, IN_DELETE,
			    DOMSUB_FAPPLY_THM] THEN
       METIS_TAC[]
   ],





   Q.PAT_ASSUM `ee1 q = X` ASSUME_TAC THEN
   Q.PAT_ASSUM `ee2 q = X` ASSUME_TAC THEN
   FULL_SIMP_TAC std_ss [smallfoot_ae_stack_read_def, FDOM_FUPDATE, IN_INSERT,
			 FAPPLY_FUPDATE_THM, SMALLFOOT_STATE_UPDATE_HEAP_def, LET_THM,
			 FUPDATE_EQ, SMALLFOOT_STATE_REMOVE_HEAP_TAG_def,
			 DOMSUB_FUPDATE_THM, COND_NONE_SOME_REWRITES] THEN
   Q.EXISTS_TAC `r |+ (y, r ' y |+ (t,c))` THEN
   REPEAT STRIP_TAC THENL [
      METIS_TAC[IN_DEF],

      SIMP_TAC std_ss [FDOM_FUPDATE, IN_INSERT],

      ASM_SIMP_TAC std_ss [GSYM fmap_EQ_THM, EXTENSION, IN_INSERT, FDOM_FUPDATE,
			   FAPPLY_FUPDATE_THM, FUPDATE_EQ, COND_RATOR, COND_RAND] THEN
      METIS_TAC[]
   ],


   Q.PAT_ASSUM `ee1 q = X` ASSUME_TAC THEN
   Q.PAT_ASSUM `ee2 q = X` ASSUME_TAC THEN
   FULL_SIMP_TAC std_ss [smallfoot_ae_stack_read_def, FDOM_FUPDATE, IN_INSERT,
			 FAPPLY_FUPDATE_THM, SMALLFOOT_STATE_UPDATE_HEAP_def, LET_THM,
			 FUPDATE_EQ, SMALLFOOT_STATE_REMOVE_HEAP_TAG_def,
			 DOMSUB_FUPDATE_THM, COND_NONE_SOME_REWRITES] THEN
   Q.EXISTS_TAC `r |+ (y, r ' y \\ t)` THEN
   REPEAT STRIP_TAC THENL [
      METIS_TAC[IN_DEF],

      SIMP_TAC std_ss [FDOM_FUPDATE, IN_INSERT],

      ASM_SIMP_TAC std_ss [GSYM fmap_EQ_THM, EXTENSION, IN_INSERT, FDOM_FUPDATE,
			   FAPPLY_FUPDATE_THM, FUPDATE_EQ, COND_RATOR, COND_RAND,
			   DOMSUB_FAPPLY_THM, FDOM_DOMSUB, IN_DELETE] THEN
      METIS_TAC[]
   ]
]);









val smallfoot_slp_new_def = Define `
   smallfoot_slp_new v P = \s:smallfoot_state. 
       ?c1 c2. (var_res_sl___read v (FST s) = SOME (c1, var_res_write_permission)) /\
               (c1 IN FDOM (SND s)) /\ ~(c1 = 0) /\
               (P ((FST s) |+ (v, c2, var_res_write_permission), (SND s) \\ c1))`;





val fasl_slp_opt___smallfoot_prog_new = store_thm ("fasl_slp_opt___smallfoot_prog_new",
``
!res_env penv v P. 
fasl_slp_opt (smallfoot_env,res_env) penv P (smallfoot_prog_new v) =
(if (smallfoot_ap_implies_writeperm P v) then
SOME (smallfoot_slp_new v P) else NONE)``,



ASM_SIMP_TAC list_ss [fasl_slp_opt___EXPANDED_DEF, smallfoot_prog_new_def,
		 FASL_PROGRAM_TRACES_IN_THM, FASL_TRACE_SEM_def,
		 FASL_ATOMIC_ACTION_SEM_def, 
		 smallfoot_env_def, fasla_seq_skip, fasla_big_seq_def,
		 EVAL_fasl_prim_command_THM, SMALLFOOT_action_map_def,
		 PAIR_FORALL_THM, PAIR_EXISTS_THM, LET_THM,
		 COND_NONE_SOME_REWRITES, IN_SING,
                 COND_NONE_SOME_REWRITES_EQ,
		 smallfoot_ap_implies_writeperm_def] THEN
REPEAT STRIP_TAC THEN1 (
   METIS_TAC[IN_DEF]
) THEN

REWRITE_TAC[EXTENSION] THEN
Cases_on `x` THEN 
SIMP_TAC std_ss [IN_ABS, smallfoot_slp_new_def, var_res_sl___read_def, COND_NONE_SOME_REWRITES,
		 var_res_sl___has_write_permission_def] THEN
EQ_TAC THEN STRIP_TAC THENL [
   ASM_SIMP_TAC std_ss [FDOM_FUPDATE, IN_INSERT, FAPPLY_FUPDATE_THM, FUPDATE_EQ] THEN
   Cases_on `x1 ' v` THEN
   Tactical.REVERSE (`(x1 |+ (v,q',var_res_write_permission) = x1) /\ (x2 |+ (n,X) \\ n = x2)` by ALL_TAC) THEN1 (
      Q.EXISTS_TAC `q'` THEN
      FULL_SIMP_TAC std_ss [IN_DEF]
   ) THEN

   FULL_SIMP_TAC std_ss [GSYM fmap_EQ_THM, FDOM_FUPDATE, IN_INSERT, EXTENSION, FAPPLY_FUPDATE_THM,
		        DOMSUB_FAPPLY_THM, FDOM_DOMSUB, IN_DELETE] THEN
   METIS_TAC[],



   Q.EXISTS_TAC `q |+ (v,c2,var_res_write_permission)` THEN
   Q.EXISTS_TAC `r \\ c1` THEN
   ASM_SIMP_TAC std_ss [FDOM_FUPDATE, IN_INSERT, FAPPLY_FUPDATE_THM, FUPDATE_EQ] THEN
   CONJ_TAC THENL [
      PROVE_TAC[IN_DEF],

      Q.EXISTS_TAC `c1` THEN
      Q.EXISTS_TAC `r ' c1` THEN
      ASM_SIMP_TAC std_ss [GSYM fmap_EQ_THM, FDOM_DOMSUB, FDOM_FUPDATE, IN_INSERT, IN_DELETE,
			   EXTENSION, FAPPLY_FUPDATE_THM, DOMSUB_FAPPLY_THM] THEN
      METIS_TAC[]
   ]
]);















val smallfoot_slp_assign_def = Define `
   smallfoot_slp_assign v e P = \s:smallfoot_state. 
       ?c1 c2. (var_res_sl___read v (FST s) = SOME (c1, var_res_write_permission)) /\
	       let sold = SMALLFOOT_STATE_UPDATE_VAR v c2 var_res_write_permission s in
		   (P sold) /\ (e (FST sold) = SOME c1)`;




val fasl_slp_opt___smallfoot_prog_assign = store_thm ("fasl_slp_opt___smallfoot_prog_assign",
``
!res_env penv v e P. 
fasl_slp_opt (smallfoot_env,res_env) penv P (smallfoot_prog_assign v e) =


(if (smallfoot_ap_implies_writeperm P v) /\
    (smallfoot_ae_is_defined P (SMALLFOOT_P_EXPRESSION_EVAL e)) then
SOME (smallfoot_slp_assign v (SMALLFOOT_P_EXPRESSION_EVAL e) P) else NONE)``,



SIMP_TAC list_ss [fasl_slp_opt___EXPANDED_DEF,
		 smallfoot_prog_assign_def, FASL_PROGRAM_TRACES_IN_THM,
		 FASL_TRACE_SEM_def, fasla_big_seq_def, fasla_seq_skip,
		 smallfoot_env_def,
		 FASL_ATOMIC_ACTION_SEM_def, EVAL_fasl_prim_command_THM,
		 SMALLFOOT_action_map_def, PAIR_FORALL_THM, LET_THM, PAIR_EXISTS_THM,
		 COND_NONE_SOME_REWRITES, IN_SING, COND_NONE_SOME_REWRITES_EQ] THEN
REPEAT GEN_TAC THEN
Q.ABBREV_TAC `ee = SMALLFOOT_P_EXPRESSION_EVAL e` THEN

REPEAT STRIP_TAC THEN1 (
   SIMP_TAC std_ss [smallfoot_ap_implies_writeperm_def,
		    smallfoot_ae_is_defined_def, IN_DEF] THEN
   METIS_TAC[]
) THEN
ONCE_REWRITE_TAC [EXTENSION] THEN
SIMP_TAC std_ss [smallfoot_slp_assign_def, IN_ABS, LET_THM,
		 var_res_sl___read_def, SMALLFOOT_STATE_UPDATE_VAR_def, COND_NONE_SOME_REWRITES,
		 SMALLFOOT_STACK_UPDATE_VAR_def] THEN
GEN_TAC THEN EQ_TAC THEN STRIP_TAC THENL [
   FULL_SIMP_TAC std_ss [var_res_sl___has_write_permission_def,
			 FAPPLY_FUPDATE_THM, FDOM_FUPDATE, IN_INSERT,
			 FUPDATE_EQ, IS_SOME_EXISTS] THEN
   Q.EXISTS_TAC `FST (x1 ' v)` THEN

   `x1 |+ (v,FST (x1 ' v),var_res_write_permission) = x1` by ALL_TAC THEN1 (
      Cases_on `x1 ' v` THEN
      FULL_SIMP_TAC std_ss [GSYM fmap_EQ_THM, FDOM_FUPDATE, IN_INSERT, EXTENSION,
			   DISJ_IMP_THM, FAPPLY_FUPDATE_THM] THEN
      ASM_SIMP_TAC std_ss [COND_RAND, COND_RATOR] THEN
      METIS_TAC[]
   ) THEN
   FULL_SIMP_TAC std_ss [IN_DEF],




   Q.EXISTS_TAC `FST x |+ (v,c2,var_res_write_permission)` THEN
   Q.EXISTS_TAC `SND x` THEN 
   Cases_on `x` THEN
   FULL_SIMP_TAC std_ss [FUPDATE_EQ] THEN
   Q.PAT_ASSUM `v IN FDOM q` ASSUME_TAC THEN
   Q.PAT_ASSUM `q ' v = X` ASSUME_TAC THEN
   FULL_SIMP_TAC std_ss [] THEN
   REPEAT STRIP_TAC THENL [
      PROVE_TAC[IN_DEF],

      SIMP_TAC std_ss [var_res_sl___has_write_permission_def, FAPPLY_FUPDATE_THM,
		       FDOM_FUPDATE, IN_INSERT],

      SIMP_TAC std_ss [GSYM fmap_EQ_THM, FDOM_FUPDATE, IN_INSERT, FAPPLY_FUPDATE_THM,
		       EXTENSION] THEN
      METIS_TAC[]
  ]
]);





val smallfoot_slp_dispose_def = Define `
   smallfoot_slp_dispose e P = \s:smallfoot_state. 
       ?x p. (e (FST s) = SOME p) /\ 
           ~(p IN FDOM (SND s)) /\ ~(p = 0) /\
           (P (FST s, (SND s) |+ (p, x)))`;




val fasl_slp_opt___smallfoot_prog_dispose = store_thm (
"fasl_slp_opt___smallfoot_prog_dispose",
``
!res_env penv e P. 
fasl_slp_opt (smallfoot_env,res_env) penv P (smallfoot_prog_dispose e) =
(if (smallfoot_ap_implies_in_heap P (SMALLFOOT_P_EXPRESSION_EVAL e)) then
SOME (smallfoot_slp_dispose (SMALLFOOT_P_EXPRESSION_EVAL e) P) else NONE)``,


ASM_SIMP_TAC list_ss [fasl_slp_opt___EXPANDED_DEF, smallfoot_prog_dispose_def,
		 FASL_PROGRAM_TRACES_IN_THM, FASL_TRACE_SEM_def,
		 FASL_ATOMIC_ACTION_SEM_def,
		 smallfoot_env_def, fasla_seq_skip, fasla_big_seq_def,
		 EVAL_fasl_prim_command_THM, SMALLFOOT_action_map_def,
		 PAIR_FORALL_THM, PAIR_EXISTS_THM, LET_THM,
		 COND_NONE_SOME_REWRITES, IN_SING,
                 COND_NONE_SOME_REWRITES_EQ,
		 smallfoot_ap_implies_in_heap_def,
		 NOT_NONE_IS_SOME] THEN
REPEAT STRIP_TAC THEN1 (
   METIS_TAC[IN_DEF]
) THEN

REWRITE_TAC[EXTENSION] THEN
Q.ABBREV_TAC `ee = SMALLFOOT_P_EXPRESSION_EVAL e` THEN
Cases_on `x` THEN
SIMP_TAC std_ss [IN_ABS, smallfoot_slp_dispose_def] THEN
EQ_TAC THEN REPEAT STRIP_TAC THENL [
   Q.PAT_ASSUM `IS_SOME X` ASSUME_TAC THEN
   FULL_SIMP_TAC std_ss [IS_SOME_EXISTS, FDOM_DOMSUB, IN_DELETE] THEN
   Q.EXISTS_TAC `x2 ' y` THEN
   FULL_SIMP_TAC std_ss [] THEN
   Tactical.REVERSE (`x2 \\ y |+ (y,x2 ' y) = x2` by ALL_TAC) THEN1 (
      METIS_TAC[IN_DEF]
   ) THEN
   ASM_SIMP_TAC std_ss [GSYM fmap_EQ_THM, EXTENSION, FDOM_DOMSUB,
		        FDOM_FUPDATE, IN_DELETE, IN_INSERT,
		        FAPPLY_FUPDATE_THM, DOMSUB_FAPPLY_THM] THEN
   METIS_TAC[],


   
   Q.EXISTS_TAC `r |+ (p,x)` THEN
   ASM_SIMP_TAC std_ss [DOMSUB_FUPDATE_THM] THEN
   REPEAT STRIP_TAC THENL [
      PROVE_TAC[IN_DEF],

      ASM_SIMP_TAC std_ss [GSYM fmap_EQ_THM, EXTENSION, FDOM_DOMSUB,
			   IN_DELETE, DOMSUB_FAPPLY_THM] THEN
      METIS_TAC[]
   ]
]);






val SMALLFOOT_REL_HOARE_TRIPLE___prog_forall_IMP =
store_thm ("SMALLFOOT_REL_HOARE_TRIPLE___prog_forall_IMP",
``!res_env penv P qprog.
(!x. SMALLFOOT_REL_HOARE_TRIPLE res_env penv P (qprog x)) ==>
SMALLFOOT_REL_HOARE_TRIPLE res_env penv P (fasl_prog_forall qprog)``,


SIMP_TAC std_ss [SMALLFOOT_REL_HOARE_TRIPLE_def,
		 SMALLFOOT_PROGRAM_SEM_def,
		 fasl_prog_forall_def,
		 FASL_PROGRAM_SEM_def,
		 FASL_TRACE_SET_SEM_def,
		 SUP_fasl_action_order_def,
		 SUP_fasl_order_def,
		 COND_NONE_SOME_REWRITES,
		 IN_IMAGE, GSYM RIGHT_EXISTS_AND_THM,
		 IN_BIGUNION,
		 FASL_PROGRAM_TRACES_def, IN_UNIV,
		 GSYM LEFT_FORALL_IMP_THM] THEN
REPEAT STRIP_TAC THEN
Q.PAT_ASSUM `!x s. (X x s) ==> (Y x s)` (MP_TAC o Q.SPECL [`x'''`, `s`]) THEN
ASM_SIMP_TAC std_ss [GSYM LEFT_EXISTS_IMP_THM] THEN
Q.EXISTS_TAC `s2` THEN
Q.EXISTS_TAC `x'` THEN
Q.EXISTS_TAC `x''` THEN
ASM_SIMP_TAC std_ss []);






val SMALLFOOT_INFERENCE___prog_val_arg___GENERAL = store_thm (
   "SMALLFOOT_INFERENCE___prog_val_arg___GENERAL",
``!res_env penv P body Q c.
(!v.
SMALLFOOT_HOARE_TRIPLE res_env penv (smallfoot_slp_init_var v (smallfoot_ae_const c) P)
(body v) (smallfoot_slp_new_var v Q)) ==>
(SMALLFOOT_HOARE_TRIPLE res_env penv P (smallfoot_prog_val_arg (\x. (body x)) c) Q)``,


SIMP_TAC std_ss [smallfoot_prog_val_arg_def, SMALLFOOT_HOARE_TRIPLE_REWRITE,
		 FORALL_AND_THM] THEN
Tactical.REVERSE (REPEAT STRIP_TAC) THENL [
   SIMP_TAC std_ss [fasl_prog_select_def] THEN
   MATCH_MP_TAC SMALLFOOT_REL_HOARE_TRIPLE___prog_forall_IMP THEN
   FULL_SIMP_TAC std_ss [SMALLFOOT_REL_HOARE_TRIPLE_def,
      SMALLFOOT_PROGRAM_SEM_def,
      FASL_PROGRAM_SEM___prog_seq, 
      SOME___fasla_seq, GSYM LEFT_FORALL_IMP_THM,
      GSYM RIGHT_EXISTS_AND_THM,
      IS_SOME___fasla_seq, FASL_ATOMIC_ACTION_SEM_def,
      smallfoot_prog_new_var_init_def, 
      FASL_PROGRAM_SEM___prim_command,
      EVAL_fasl_prim_command_THM,
      fasla_select_assume_def, IN_SING,
      smallfoot_env_def, PAIR_FORALL_THM,
      SMALLFOOT_action_map_def,
      LET_THM, SMALLFOOT_P_EXPRESSION_EVAL_def,
      smallfoot_ae_const_def,
      smallfoot_prog_dispose_var_def,
      COND_NONE_SOME_REWRITES, IN_BIGUNION, IN_IMAGE] THEN
   FULL_SIMP_TAC std_ss [fasla_seq_def, SUP_fasl_order_def,
      COND_NONE_SOME_REWRITES, SMALLFOOT_action_map_def, LET_THM,
      SMALLFOOT_P_EXPRESSION_EVAL_def, smallfoot_ae_const_def,
      IN_IMAGE, PAIR_EXISTS_THM, smallfoot_slp_init_var_def,
      IN_ABS, var_res_sl___read_def] THEN
   REPEAT GEN_TAC THEN STRIP_TAC THEN
   Cases_on `x IN FDOM x1` THEN1 (
      FULL_SIMP_TAC std_ss [NOT_IN_EMPTY, IN_BIGUNION,
         IN_IMAGE, GSYM RIGHT_EXISTS_AND_THM]
   ) THEN
   FULL_SIMP_TAC std_ss [IN_SING] THEN
   `(?x1' x2'. ~var_res_sl___has_write_permission x x1' /\ (x1',x2') IN s1'') = F` by METIS_TAC[] THEN
   ASM_SIMP_TAC std_ss [IN_BIGUNION, IN_IMAGE, IN_SING,
		        GSYM RIGHT_EXISTS_AND_THM,
		        SMALLFOOT_action_map_def,
		        PAIR_EXISTS_THM] THEN
   REPEAT STRIP_TAC THEN
   `var_res_sl___has_write_permission x x1''` by RES_TAC THEN
   FULL_SIMP_TAC std_ss [IN_SING] THEN

   Q.PAT_ASSUM `!v x1 x2 s'. X v x1 x2 s'` (MP_TAC o 
      Q.SPECL [`x`, `x1 |+ (x,c,var_res_write_permission)`, `x2`, `s1''`]) THEN
   ASM_SIMP_TAC std_ss [FDOM_FUPDATE, FAPPLY_FUPDATE_THM, IN_INSERT] THEN
   `x1 |+ (x,c,var_res_write_permission) \\ x= x1` by ALL_TAC THEN1 (
      ASM_SIMP_TAC std_ss [GSYM fmap_EQ_THM, EXTENSION, FDOM_FUPDATE,
			   IN_INSERT, FAPPLY_FUPDATE_THM, FDOM_DOMSUB,
                           IN_DELETE, DOMSUB_FAPPLY_THM] THEN
      METIS_TAC[]
   ) THEN
   `P (x1,x2)` by METIS_TAC[IN_DEF] THEN
   ASM_SIMP_TAC std_ss [GSYM LEFT_EXISTS_IMP_THM] THEN
   Q.EXISTS_TAC `x1''` THEN
   Q.EXISTS_TAC `x2''` THEN
   ASM_SIMP_TAC std_ss [VAR_RES_STACK___IS_EQUAL_UPTO_VALUES_def,
		        DOMSUB_FAPPLY_THM, FDOM_FUPDATE,
		        IN_INSERT, FAPPLY_FUPDATE_THM,
		        FDOM_DOMSUB, IN_DELETE, EXTENSION] THEN
   METIS_TAC[],  


   MATCH_MP_TAC FASL_INFERENCE_prog_select THEN
   SIMP_TAC std_ss [fasl_select_predicate_IS_SATISFIABLE___smallfoot_env,
	FASL_IS_LOCAL_EVAL_ENV___smallfoot_env,
	FASL_IS_LOCAL_EVAL_XENV_def,
	XEVAL_fasl_select_predicate_def] THEN
   SIMP_TAC std_ss [smallfoot_env_def] THEN
   SIMP_TAC std_ss [GSYM smallfoot_env_def] THEN
   SIMP_TAC std_ss [asl_bool_REWRITES] THEN
   GEN_TAC THEN


   MATCH_MP_TAC FASL_INFERENCE_prog_slp___IMP THEN
   ASM_SIMP_TAC std_ss [fasl_slp_opt___smallfoot_prog_new_var_init,
		     SMALLFOOT_P_EXPRESSION_EVAL_def,
		     smallfoot_ae_is_defined_def,
		     smallfoot_ae_const_def] THEN

   MATCH_MP_TAC FASL_INFERENCE_prog_wlp___IMP THEN
   SIMP_TAC std_ss [fasl_wlp_opt___smallfoot_prog_dispose_var] THEN
   FULL_SIMP_TAC std_ss [GSYM SMALLFOOT_HOARE_TRIPLE_def,
		      smallfoot_ae_const_def]
]);




val SMALLFOOT_INFERENCE___prog_local_var___GENERAL = store_thm (
   "SMALLFOOT_INFERENCE___prog_local_var___GENERAL",
``!res_env penv P body Q.
(!v.
SMALLFOOT_HOARE_TRIPLE res_env penv (smallfoot_slp_new_var v P)
(body v) (smallfoot_slp_new_var v Q)) ==>
(SMALLFOOT_HOARE_TRIPLE res_env penv P (smallfoot_prog_local_var (\x. (body x))) Q)``,

SIMP_TAC std_ss [smallfoot_prog_local_var_def,
		 GSYM fasl_prog_ndet_def,
		 SMALLFOOT_HOARE_TRIPLE_def, IN_ABS,
		 fasl_prog_ndet___HOARE_TRIPLE,
		 GSYM LEFT_FORALL_IMP_THM] THEN
REPEAT STRIP_TAC THEN
MATCH_MP_TAC (REWRITE_RULE [SMALLFOOT_HOARE_TRIPLE_def] SMALLFOOT_INFERENCE___prog_val_arg___GENERAL) THEN
FULL_SIMP_TAC std_ss [smallfoot_slp_new_var_def,
		      asl_bool_EVAL, GSYM LEFT_EXISTS_AND_THM,
		      FASL_PROGRAM_HOARE_TRIPLE_REWRITE, SUBSET_DEF,
		      IN_ABS] THEN
METIS_TAC[]);






val SMALLFOOT_AP_PERMISSION_UNIMPORTANT_def = Define `
    SMALLFOOT_AP_PERMISSION_UNIMPORTANT (P:smallfoot_a_proposition) =
    (!st1 st2 h. (VAR_RES_STACK___IS_EQUAL_UPTO_PERMISSIONS EMPTY st1 st2) ==>
	       ((st1,h) IN P = (st2,h) IN P)) /\
    (!st1 st2 h. (VAR_RES_STACK_IS_SUBSTATE st1 st2 /\ (st1,h) IN P) ==>
                 (st2,h) IN P) `;






val SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS_def = Define `
    SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS exS (P:smallfoot_a_proposition) =
    ((!s. ((SMALLFOOT_STATE_RESTRICT s exS) IN P = s IN P)) /\
     (SMALLFOOT_AP_PERMISSION_UNIMPORTANT P))`;






val SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___ALTERNATIVE_DEF = store_thm (
"SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___ALTERNATIVE_DEF",
``SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS vs P =

!st1 st2.
   (FDOM st1 INTER vs SUBSET FDOM st2 /\
   (!v. (v IN FDOM st1 /\ v IN vs) ==> (FST (st1 ' v) = FST (st2 ' v)))) ==>

   (!h. (st1, h) IN P ==> (st2, h) IN P) /\
   (!h. ((st2, h) IN P /\ (FDOM st2 INTER vs SUBSET (FDOM st1))) ==> (st1, h) IN P)``,


SIMP_TAC std_ss [SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS_def,
		 VAR_RES_STACK_IS_SUBSTATE_def,
		 SMALLFOOT_AP_PERMISSION_UNIMPORTANT_def,
		 ASL_IS_SUBSTATE_def,
		 NOT_IN_EMPTY,
		 VAR_RES_STACK___IS_EQUAL_UPTO_PERMISSIONS_def,
		 SMALLFOOT_STATE_RESTRICT_def,
		 PAIR_FORALL_THM, SOME___VAR_RES_STACK_COMBINE,
		 GSYM LEFT_FORALL_IMP_THM, GSYM RIGHT_EXISTS_AND_THM,
		 GSYM LEFT_EXISTS_AND_THM]  THEN
REPEAT STRIP_TAC THEN EQ_TAC THENL [
   REPEAT STRIP_TAC THENL [
      Q.ABBREV_TAC `vs' = FDOM st1 INTER vs` THEN
      Q.PAT_ASSUM `!st1 st2 h. X st1 st2 h` (MP_TAC o Q.SPECL [`DRESTRICT st2 vs'`, `h`, `DRESTRICT st2 (COMPL vs')`]) THEN
      MATCH_MP_TAC (prove (``(A /\ (st1 = st2)) ==> ((A ==> (st1,h) IN P) ==> (st2,h) IN P)``, METIS_TAC[])) THEN
      REPEAT STRIP_TAC THENL [
         SIMP_TAC (std_ss++bool_neg_pair_ss) [VAR_RES_STACK_IS_SEPARATE_def, DRESTRICT_DEF,
			  IN_INTER, IN_COMPL],

	 
         Q.PAT_ASSUM `!st1 st2 h. X st1 st2 h` (MP_TAC o Q.SPECL [`DRESTRICT st1 vs`, `DRESTRICT st2 vs'`, `h`]) THEN
	 UNABBREV_ALL_TAC THEN
         FULL_SIMP_TAC (std_ss++bool_eq_imp_ss) [DRESTRICT_DEF, IN_INTER, SUBSET_DEF,
			       EXTENSION],

	 FULL_SIMP_TAC (std_ss++bool_eq_imp_ss) [GSYM fmap_EQ_THM, FMERGE_DEF,
			       EXTENSION, DRESTRICT_DEF, IN_UNION,
			       IN_COMPL, IN_INTER, DISJ_IMP_THM]
      ],


      Q.PAT_ASSUM `!st1 st2 h:smallfoot_heap. X st1 st2 h` 
	  (MP_TAC o Q.SPECL [`DRESTRICT st1 vs`, `DRESTRICT st2 vs`, `h`]) THEN
      ASM_SIMP_TAC std_ss [] THEN
      MATCH_MP_TAC (prove (``A ==> ((A ==> B) ==> B)``, SIMP_TAC std_ss [])) THEN

      FULL_SIMP_TAC std_ss [EXTENSION, DRESTRICT_DEF, IN_INTER, SUBSET_DEF] THEN
      GEN_TAC THEN EQ_TAC THEN ASM_SIMP_TAC std_ss []
   ],


   REPEAT STRIP_TAC THENL [
      Q.PAT_ASSUM `!st1 st2. X st1 st2` (MP_TAC o Q.SPECL [`DRESTRICT x1 vs`, `x1`]) THEN
      SIMP_TAC std_ss [DRESTRICT_DEF, INTER_SUBSET, SUBSET_INTER, SUBSET_REFL,
		       IN_INTER, INTER_IDEMPOT, GSYM INTER_ASSOC] THEN
      METIS_TAC[],


      Q.PAT_ASSUM `!st1 st2. X st1 st2` (MP_TAC o Q.SPECL [`st1`, `st2`]) THEN
      ASM_SIMP_TAC std_ss [INTER_SUBSET] THEN
      METIS_TAC[],


      Q.PAT_ASSUM `!st1 st2. X st1 st2` (MP_TAC o Q.SPECL [`st1`, 
           `FMERGE VAR_RES_STACK_COMBINE___MERGE_FUNC st1 s1`]) THEN
      FULL_SIMP_TAC std_ss [SUBSET_DEF, IN_INTER, FMERGE_DEF, IN_UNION,
			    VAR_RES_STACK_IS_SEPARATE_def,
			    VAR_RES_STACK_COMBINE___MERGE_FUNC_def,
			    COND_REWRITES]
   ]
]);



val SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___ALTERNATIVE_DEF_2 =
store_thm ("SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___ALTERNATIVE_DEF_2",
``
!vs P.
SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS vs P =

(!s s2. (s2 IN P /\ (SND s2 = SND s) /\
     FDOM (FST s2) INTER vs SUBSET FDOM (FST s) /\
     (!v.  v IN FDOM (FST s2) /\ v IN vs ==>
            (FST ((FST s) ' v) = FST ((FST s2) ' v))))
==>
s IN P)``,


SIMP_TAC std_ss [SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___ALTERNATIVE_DEF,
		 PAIR_FORALL_THM] THEN
REPEAT STRIP_TAC THEN EQ_TAC THENL [
   REPEAT STRIP_TAC THEN
   METIS_TAC[],


   REPEAT STRIP_TAC THENL [
      METIS_TAC[],

      Q.PAT_ASSUM `!x1 x2. X x1 x2` MATCH_MP_TAC THEN
      Q.EXISTS_TAC `st2` THEN
      `FDOM st2 INTER vs = FDOM  st1 INTER vs` by ALL_TAC THEN1 (
         FULL_SIMP_TAC std_ss [EXTENSION, SUBSET_DEF, IN_INTER] THEN
	 METIS_TAC[]
      ) THEN
      METIS_TAC[IN_INTER]
   ]
]);




val SMALLFOOT_AP_PERMISSION_UNIMPORTANT___ALTERNATIVE_DEF =
store_thm ("SMALLFOOT_AP_PERMISSION_UNIMPORTANT___ALTERNATIVE_DEF",
``
!P.
SMALLFOOT_AP_PERMISSION_UNIMPORTANT P =
SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS UNIV P``,

SIMP_TAC std_ss [SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS_def,
		 SMALLFOOT_STATE_RESTRICT_def, DRESTRICT_UNIV]);



val SMALLFOOT_AP_PERMISSION_UNIMPORTANT___ALTERNATIVE_DEF_2=
store_thm ("SMALLFOOT_AP_PERMISSION_UNIMPORTANT___ALTERNATIVE_DEF_2",
``
!P.
SMALLFOOT_AP_PERMISSION_UNIMPORTANT P =

(!s s2. (s2 IN P /\ (SND s2 = SND s) /\
     FDOM (FST s2) SUBSET FDOM (FST s) /\
     (!v.  v IN FDOM (FST s2) ==>
            (FST ((FST s) ' v) = FST ((FST s2) ' v))))
==>
s IN P)``,


SIMP_TAC std_ss [SMALLFOOT_AP_PERMISSION_UNIMPORTANT___ALTERNATIVE_DEF,
		 SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___ALTERNATIVE_DEF_2,
		 IN_UNIV, INTER_UNIV]);


val SMALLFOOT_AP_PERMISSION_UNIMPORTANT___SUBSTATE = store_thm (
"SMALLFOOT_AP_PERMISSION_UNIMPORTANT___SUBSTATE",
``!P s s'. (SMALLFOOT_AP_PERMISSION_UNIMPORTANT P /\
      (s' IN P) /\ (SMALLFOOT_IS_SUBSTATE s' s)) ==>
      (FST s, SND s') IN P``,

REPEAT STRIP_TAC THEN
FULL_SIMP_TAC std_ss [SMALLFOOT_AP_PERMISSION_UNIMPORTANT___ALTERNATIVE_DEF_2] THEN
Q.PAT_ASSUM `!s s2. X s s2` MATCH_MP_TAC THEN
Q.EXISTS_TAC `s'` THEN
FULL_SIMP_TAC std_ss [SMALLFOOT_IS_SUBSTATE_REWRITE,
		      VAR_RES_STACK_IS_SUBSTATE_REWRITE]);



val SMALLFOOT_AP_PERMISSION_UNIMPORTANT___IMP =
store_thm ("SMALLFOOT_AP_PERMISSION_UNIMPORTANT___IMP",
``
!P vs.
SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS vs P ==>
SMALLFOOT_AP_PERMISSION_UNIMPORTANT P``,

SIMP_TAC std_ss [SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS_def]);



val SMALLFOOT_AP_PERMISSION_UNIMPORTANT___smallfoot_ap_stack_true =
store_thm ("SMALLFOOT_AP_PERMISSION_UNIMPORTANT___smallfoot_ap_stack_true",
``
SMALLFOOT_AP_PERMISSION_UNIMPORTANT smallfoot_ap_stack_true``,


SIMP_TAC std_ss [SMALLFOOT_AP_PERMISSION_UNIMPORTANT___ALTERNATIVE_DEF_2,
		 smallfoot_ap_stack_true_def,
		 PAIR_FORALL_THM, IN_ABS]);




val SMALLFOOT_AP_PERMISSION_UNIMPORTANT___asl_false =
store_thm ("SMALLFOOT_AP_PERMISSION_UNIMPORTANT___asl_false",
``
SMALLFOOT_AP_PERMISSION_UNIMPORTANT smallfoot_ap_false /\
SMALLFOOT_AP_PERMISSION_UNIMPORTANT asl_false``,


SIMP_TAC std_ss [SMALLFOOT_AP_PERMISSION_UNIMPORTANT___ALTERNATIVE_DEF_2,
		 PAIR_FORALL_THM, IN_ABS, asl_false_def, NOT_IN_EMPTY,
	         smallfoot_ap_false_def]);


val SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___asl_false =
store_thm ("SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___asl_false",
``(!vs. SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS vs smallfoot_ap_false) /\
  (!vs. SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS vs asl_false)``,


SIMP_TAC std_ss [SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___ALTERNATIVE_DEF_2,
		 PAIR_FORALL_THM, IN_ABS, asl_false_def, NOT_IN_EMPTY,
	         smallfoot_ap_false_def]);


val SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___smallfoot_ap_stack_true =
store_thm ("SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___smallfoot_ap_stack_true",
``!vs. SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS vs smallfoot_ap_stack_true``,

SIMP_TAC std_ss [SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___ALTERNATIVE_DEF_2,
		 IN_ABS, smallfoot_ap_stack_true_def, PAIR_FORALL_THM]);



val SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___smallfoot_ap_emp =
store_thm ("SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___smallfoot_ap_emp",
``!vs. ~(SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS vs smallfoot_ap_emp)``,


SIMP_TAC std_ss [SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___ALTERNATIVE_DEF_2,
		 smallfoot_ap_emp_ALTERNATIVE_DEF, IN_ABS, PAIR_EXISTS_THM,
		 FDOM_FEMPTY, NOT_IN_EMPTY, INTER_EMPTY, EMPTY_SUBSET] THEN
PROVE_TAC[NOT_EQ_FEMPTY_FUPDATE]);



val SMALLFOOT_AP_PERMISSION_UNIMPORTANT___exists =
store_thm ("SMALLFOOT_AP_PERMISSION_UNIMPORTANT___exists",
``
(!x. SMALLFOOT_AP_PERMISSION_UNIMPORTANT (P x)) ==>
SMALLFOOT_AP_PERMISSION_UNIMPORTANT (asl_exists x. P x)``,


SIMP_TAC std_ss [SMALLFOOT_AP_PERMISSION_UNIMPORTANT___ALTERNATIVE_DEF_2,
		 asl_bool_EVAL, GSYM LEFT_EXISTS_AND_THM,
		 GSYM RIGHT_EXISTS_AND_THM,
		 GSYM LEFT_FORALL_IMP_THM] THEN
METIS_TAC[]);
    

val SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___star = store_thm (
"SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___star",
``(SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS exS1 P1 /\
SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS exS2 P2) ==>
(SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS (exS1 UNION exS2) (smallfoot_ap_star P1 P2))``,

SIMP_TAC std_ss [SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS_def,
		 SMALLFOOT_AP_PERMISSION_UNIMPORTANT_def,
		 SMALLFOOT_STATE_RESTRICT_def, PAIR_FORALL_THM,
		 smallfoot_ap_star_def,
		 asl_star_def, IN_ABS, SOME___smallfoot_separation_combinator,
                 PAIR_EXISTS_THM] THEN
REPEAT STRIP_TAC THENL [
   EQ_TAC THEN REPEAT STRIP_TAC THENL [
      Q.EXISTS_TAC `FUNION (DRESTRICT x1 (COMPL (exS1 UNION exS2))) x1'` THEN
      Q.EXISTS_TAC `x2'` THEN
      Q.EXISTS_TAC `x1''` THEN
      Q.EXISTS_TAC `x2''` THEN
      ASM_SIMP_TAC std_ss [] THEN
      CONJ_TAC THENL [
         FULL_SIMP_TAC std_ss [GSYM fmap_EQ_THM, FMERGE_DEF, FUNION_DEF,
			       DRESTRICT_DEF, IN_UNION, IN_INTER, IN_COMPL,
      		               EXTENSION, VAR_RES_STACK_IS_SEPARATE_def,
			       SOME___VAR_RES_STACK_COMBINE,
			       VAR_RES_STACK_COMBINE___MERGE_FUNC_def,
			       DISJOINT_DEF, EXTENSION, NOT_IN_EMPTY, GSYM 
			       FORALL_AND_THM] THEN
         GEN_TAC THEN
         Q.PAT_ASSUM `!x:smallfoot_var. P x` (ASSUME_TAC o Q.SPEC `x`) THEN
	 Cases_on `~(x IN FDOM x1)` THEN1 (
	    FULL_SIMP_TAC std_ss []
         ) THEN
         Cases_on `x IN exS2` THEN1 (
	    FULL_SIMP_TAC std_ss []
         ) THEN
         Cases_on `x IN exS1` THEN (
	    FULL_SIMP_TAC std_ss []
         ),




         Tactical.REVERSE (`DRESTRICT (FUNION (DRESTRICT x1 (COMPL (exS1 UNION exS2))) x1') exS1 =
         DRESTRICT x1' exS1` by ALL_TAC) THEN1 (
            METIS_TAC[]
         ) THEN
         SIMP_TAC std_ss [GSYM fmap_EQ_THM, DRESTRICT_DEF, FUNION_DEF, EXTENSION,
		       IN_INTER, IN_COMPL, IN_UNION] THEN
         METIS_TAC[]
      ],



      Q.EXISTS_TAC `DRESTRICT x1' (exS1 UNION exS2)` THEN
      Q.EXISTS_TAC `x2'` THEN
      Q.EXISTS_TAC `DRESTRICT x1'' (exS1 UNION exS2)` THEN
      Q.EXISTS_TAC `x2''` THEN
      FULL_SIMP_TAC std_ss [VAR_RES_STACK_IS_SEPARATE___DRESTRICT,
			    FMERGE_DRESTRICT,
			    SOME___VAR_RES_STACK_COMBINE] THEN
      `(DRESTRICT (DRESTRICT x1' (exS1 UNION exS2)) exS1 =
       DRESTRICT x1' exS1) /\
       (DRESTRICT (DRESTRICT x1'' (exS1 UNION exS2)) exS2 =
       DRESTRICT x1'' exS2)` by METIS_TAC[DRESTRICT_DRESTRICT,INTER_UNION] THEN
      METIS_TAC[]
   ],


   HO_MATCH_MP_TAC (
   prove (``(!x2 x2'. ((?x1 x1'. P x1 x2 x1' x2') =
                      (?x1 x1'. Q x1 x2 x1' x2'))) ==>
            ((?x1 x2 x1' x2'. P x1 x2 x1' x2') =
            (?x1 x2 x1' x2'. Q x1 x2 x1' x2'))``, METIS_TAC[])) THEN
   SIMP_TAC (std_ss++bool_eq_imp_ss) [] THEN
   REPEAT STRIP_TAC THEN EQ_TAC THEN STRIP_TAC THENL [
      MP_TAC (ISPECL [``x1:smallfoot_stack``, 
                      ``x1':smallfoot_stack``, 
                      ``st1:smallfoot_stack``, 
                      ``st2:smallfoot_stack``, 
                      ``{}:smallfoot_var set``] 
                  VAR_RES_STACK___IS_EQUAL_UPTO_PERMISSIONS___COMBINE_EXISTS) THEN
      ASM_SIMP_TAC std_ss [] THEN
      REPEAT STRIP_TAC THEN
      Q.EXISTS_TAC `st1'` THEN
      Q.EXISTS_TAC `st2'` THEN
      METIS_TAC[],


      MP_TAC (ISPECL [``x1:smallfoot_stack``, 
                      ``x1':smallfoot_stack``, 
                      ``st2:smallfoot_stack``, 
                      ``st1:smallfoot_stack``, 
                      ``{}:smallfoot_var set``] 
                  VAR_RES_STACK___IS_EQUAL_UPTO_PERMISSIONS___COMBINE_EXISTS) THEN
      `COMM ((VAR_RES_STACK___IS_EQUAL_UPTO_PERMISSIONS {}):(smallfoot_stack -> smallfoot_stack -> bool))` by REWRITE_TAC
         [VAR_RES_STACK___IS_EQUAL_UPTO_PERMISSIONS_THM] THEN
      FULL_SIMP_TAC std_ss [COMM_DEF] THEN
      REPEAT STRIP_TAC THEN
      Q.EXISTS_TAC `st1'` THEN
      Q.EXISTS_TAC `st2'` THEN
      METIS_TAC[]
   ],



   `?st3. VAR_RES_STACK_COMBINE (SOME st1) (SOME st3) = SOME st2` by ALL_TAC THEN1 (
      FULL_SIMP_TAC std_ss [VAR_RES_STACK_IS_SUBSTATE_def,
       		            ASL_IS_SUBSTATE_def] THEN
      PROVE_TAC[]
   ) THEN
   `IS_SEPARATION_COMBINATOR (VAR_RES_STACK_COMBINE:smallfoot_stack bin_option_function)` by
      REWRITE_TAC[VAR_RES_STACK_COMBINE___IS_SEPARATION_COMBINATOR] THEN
   FULL_SIMP_TAC std_ss [IS_SEPARATION_COMBINATOR_EXPAND_THM] THEN
   `VAR_RES_STACK_COMBINE (SOME x1) (VAR_RES_STACK_COMBINE (SOME x1') (SOME st3)) = SOME st2` by
	METIS_TAC[ASSOC_DEF] THEN
   Cases_on `VAR_RES_STACK_COMBINE (SOME x1') (SOME st3)` THEN1 (
      METIS_TAC[optionTheory.option_CLAUSES]
   ) THEN
   Q.EXISTS_TAC `x1` THEN
   Q.EXISTS_TAC `x2` THEN
   Q.EXISTS_TAC `x` THEN
   Q.EXISTS_TAC `x2'` THEN
   ASM_SIMP_TAC std_ss [] THEN

   Tactical.REVERSE (`VAR_RES_STACK_IS_SUBSTATE x1' x` by ALL_TAC) THEN1 PROVE_TAC[] THEN
   ASM_SIMP_TAC std_ss [VAR_RES_STACK_IS_SUBSTATE_def, ASL_IS_SUBSTATE_def] THEN
   Q.EXISTS_TAC `st3` THEN
   ASM_REWRITE_TAC[]
]);











val SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___star_MP = store_thm (
"SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___star_MP",
``(SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS exS P1 /\
SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS exS P2) ==>
(SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS exS (smallfoot_ap_star P1 P2))``,

METIS_TAC[UNION_IDEMPOT, SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___star]);






val SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___bigstar = store_thm (
"SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___bigstar",
``
!sfb.(~(sfb = EMPTY_BAG) /\
!sf. BAG_IN sf sfb ==> (SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS exS sf)) ==>
(SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS exS (smallfoot_ap_bigstar sfb))``,


GEN_TAC THEN 
Tactical.REVERSE (Cases_on `FINITE_BAG sfb`) THEN1 (
    ASM_REWRITE_TAC  [smallfoot_ap_bigstar_def,
			 asl_bigstar_def,
			 SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___ALTERNATIVE_DEF,
			 asl_false_def, NOT_IN_EMPTY]
) THEN
POP_ASSUM MP_TAC THEN
Q.SPEC_TAC (`sfb`, `sfb`) THEN
HO_MATCH_MP_TAC bagTheory.FINITE_BAG_INDUCT THEN
REPEAT STRIP_TAC THENL [
   FULL_SIMP_TAC std_ss [],


   Cases_on `sfb = EMPTY_BAG` THENL [
      FULL_SIMP_TAC std_ss [bagTheory.BAG_IN_BAG_INSERT,
			    bagTheory.NOT_IN_EMPTY_BAG, smallfoot_ap_bigstar_REWRITE,
			    smallfoot_ap_star___PROPERTIES],


      FULL_SIMP_TAC std_ss [bagTheory.BAG_IN_BAG_INSERT,
			 DISJ_IMP_THM, FORALL_AND_THM,
			 smallfoot_ap_bigstar_REWRITE] THEN
      METIS_TAC[SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___star, UNION_IDEMPOT]
  ]
]);





val SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___bigstar_list = store_thm (
"SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___bigstar_list",
``
!L.((~(L = [])) /\
(!sf. MEM sf L ==> (SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS exS sf))) ==>
(SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS exS (smallfoot_ap_bigstar_list L))``,



REPEAT STRIP_TAC THEN
SIMP_TAC std_ss [smallfoot_ap_bigstar_list_def,
	         asl_bigstar_list___DEF2,
		 IS_SEPARATION_COMBINATOR___smallfoot_separation_combinator,
		 GSYM smallfoot_ap_bigstar_def] THEN
MATCH_MP_TAC SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___bigstar THEN
ASM_SIMP_TAC std_ss [IN_LIST_TO_BAG, LIST_TO_BAG_EQ_EMPTY]);



val SMALLFOOT_AP_PERMISSION_UNIMPORTANT___star = store_thm (
"SMALLFOOT_AP_PERMISSION_UNIMPORTANT___star",
``(SMALLFOOT_AP_PERMISSION_UNIMPORTANT P1 /\
SMALLFOOT_AP_PERMISSION_UNIMPORTANT P2) ==>
(SMALLFOOT_AP_PERMISSION_UNIMPORTANT (smallfoot_ap_star P1 P2))``,

SIMP_TAC std_ss [SMALLFOOT_AP_PERMISSION_UNIMPORTANT___ALTERNATIVE_DEF] THEN
METIS_TAC[UNION_UNIV, SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___star]);




val SMALLFOOT_AP_PERMISSION_UNIMPORTANT___bigstar = store_thm (
"SMALLFOOT_AP_PERMISSION_UNIMPORTANT___bigstar",
``
!sfb.((~(sfb = EMPTY_BAG)) /\
(!sf. BAG_IN sf sfb ==> (SMALLFOOT_AP_PERMISSION_UNIMPORTANT sf))) ==>
(SMALLFOOT_AP_PERMISSION_UNIMPORTANT (smallfoot_ap_bigstar sfb))``,

SIMP_TAC std_ss [SMALLFOOT_AP_PERMISSION_UNIMPORTANT___ALTERNATIVE_DEF,
		 SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___bigstar]);



val SMALLFOOT_AP_PERMISSION_UNIMPORTANT___bigstar_list = store_thm (
"SMALLFOOT_AP_PERMISSION_UNIMPORTANT___bigstar_list",
``
!L.((~(L = [])) /\
(!sf. MEM sf L ==> (SMALLFOOT_AP_PERMISSION_UNIMPORTANT sf))) ==>
(SMALLFOOT_AP_PERMISSION_UNIMPORTANT (smallfoot_ap_bigstar_list L))``,

SIMP_TAC std_ss [SMALLFOOT_AP_PERMISSION_UNIMPORTANT___ALTERNATIVE_DEF,
		 SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___bigstar_list]);




val SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___SUBSET = store_thm (
"SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___SUBSET",
``!exS1 exS2 P. ((exS1 SUBSET exS2) /\
SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS exS1 P) ==>
SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS exS2 P``,


REPEAT GEN_TAC THEN
SIMP_TAC std_ss [SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___ALTERNATIVE_DEF,
		 SUBSET_DEF, IN_INTER] THEN
STRIP_TAC THEN REPEAT GEN_TAC THEN
Q.PAT_ASSUM `!st1 st2. X st1 st2` (ASSUME_TAC o Q.SPECL [`st1`, `st2`]) THEN
METIS_TAC[]);



val SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___asl_and = store_thm (
"SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___asl_and",
``!exS P1 P2.
(SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS exS P1 /\
   SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS exS P2) ==>
SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS exS (asl_and P1 P2)``,

REPEAT GEN_TAC THEN
SIMP_TAC std_ss [SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___ALTERNATIVE_DEF, asl_and_def,
		 IN_ABS] THEN
STRIP_TAC THEN REPEAT GEN_TAC THEN
REPEAT (Q.PAT_ASSUM `!st1 st2. X st1 st2` (ASSUME_TAC o Q.SPECL [`st1`, `st2`])) THEN
METIS_TAC[]);



val SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___asl_or = store_thm (
"SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___asl_or",
``!exS P1 P2.
(SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS exS P1 /\
 SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS exS P2) ==>
SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS exS (asl_or P1 P2)``,

REPEAT GEN_TAC THEN
SIMP_TAC std_ss [SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___ALTERNATIVE_DEF, asl_or_def,
		 IN_ABS] THEN
STRIP_TAC THEN REPEAT GEN_TAC THEN
REPEAT (Q.PAT_ASSUM `!st1 st2. X st1 st2` (ASSUME_TAC o Q.SPECL [`st1`, `st2`])) THEN
METIS_TAC[]);



val SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___const = store_thm (
"SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___const",
``!exS c. SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS exS (K c)``,

SIMP_TAC std_ss [SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___ALTERNATIVE_DEF,
		 IN_DEF]);






val SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___asl_exists = store_thm (
"SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___asl_exists",
``!exS P.
(!s x. P x s ==> (?x2. P x2 s /\ 
                       SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS exS (P x2))) ==>
SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS exS (asl_exists x. P x)``,

REPEAT STRIP_TAC THEN
FULL_SIMP_TAC std_ss [SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___ALTERNATIVE_DEF,
		 asl_exists_def, IN_DEF] THEN
REPEAT STRIP_TAC THEN (
   RES_TAC THEN
   Q.EXISTS_TAC `x2` THEN
   RES_TAC
));




val SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___asl_exists_direct = store_thm (
"SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___asl_exists_direct",
``!exS P.
(!x. SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS exS (P x)) ==>
SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS exS (asl_exists x. P x)``,

REPEAT STRIP_TAC THEN
MATCH_MP_TAC SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___asl_exists THEN
REPEAT STRIP_TAC THEN
Q.EXISTS_TAC `x` THEN
ASM_REWRITE_TAC[]);






val SMALLFOOT_AE_USED_VARS_REL_def = Define `
    SMALLFOOT_AE_USED_VARS_REL (e:smallfoot_a_expression) vs =
    ((!st. e (DRESTRICT st vs) = e st) /\ FINITE vs /\
    (!st1 st2. VAR_RES_STACK___IS_EQUAL_UPTO_PERMISSIONS {} st1 st2 ==>
               (e st1 = e st2)) /\
    (!st. IS_SOME (e st) = (vs SUBSET FDOM st)))`;


val SMALLFOOT_AE_USED_VARS_REL_11 = store_thm (
"SMALLFOOT_AE_USED_VARS_REL_11",
``(SMALLFOOT_AE_USED_VARS_REL e vs1 /\
  SMALLFOOT_AE_USED_VARS_REL e vs2) ==>
  (vs1 = vs2)``,

REPEAT STRIP_TAC THEN
CCONTR_TAC THEN
FULL_SIMP_TAC std_ss [SMALLFOOT_AE_USED_VARS_REL_def, EXTENSION, SUBSET_DEF] THEN
`?st:smallfoot_stack. FDOM st = (vs1 UNION vs2) DELETE x` by ALL_TAC THEN1 (
   Q.EXISTS_TAC `FUN_FMAP ARB ((vs1 UNION vs2) DELETE x)` THEN
   ASM_SIMP_TAC std_ss [FINITE_UNION, FINITE_DELETE, FUN_FMAP_DEF]
) THEN
Q.PAT_ASSUM `!st. (!x. P x st) = (!x. Q x st)` (MP_TAC o Q.SPEC `st`) THEN
ASM_SIMP_TAC std_ss [IN_UNION, IN_DELETE]);



val SMALLFOOT_AE_USED_VARS_def = Define `
SMALLFOOT_AE_USED_VARS e =
if ?vs. SMALLFOOT_AE_USED_VARS_REL e vs then
SOME (@vs.SMALLFOOT_AE_USED_VARS_REL e vs) else
NONE`;


val SMALLFOOT_AE_USED_VARS_THM = store_thm ("SMALLFOOT_AE_USED_VARS_THM",
``
(!e vs. ((SMALLFOOT_AE_USED_VARS e = SOME vs) = (SMALLFOOT_AE_USED_VARS_REL e vs))) /\
(!e. (((SMALLFOOT_AE_USED_VARS e = NONE) = !vs. ~(SMALLFOOT_AE_USED_VARS_REL e vs))))``,

SIMP_TAC std_ss [SMALLFOOT_AE_USED_VARS_def, COND_RAND, COND_RATOR] THEN
REPEAT GEN_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THENL [
   Q.PAT_ASSUM `X = vs` (fn thm => ONCE_REWRITE_TAC[GSYM thm]) THEN
   SELECT_ELIM_TAC THEN
   PROVE_TAC[],


   PROVE_TAC[],


   SELECT_ELIM_TAC THEN
   METIS_TAC[SMALLFOOT_AE_USED_VARS_REL_11]
]);




val SMALLFOOT_AE_USED_VARS_REL___REWRITE = store_thm ("SMALLFOOT_AE_USED_VARS_REL___REWRITE",

``SMALLFOOT_AE_USED_VARS_REL e vs =
  FINITE vs /\
  (!st. IS_SOME (e st) = vs SUBSET (FDOM st)) /\
  (!st. ((e st) = NONE) = ~(vs SUBSET (FDOM st))) /\
  (!st1 st2. ((vs SUBSET FDOM st1) /\ (vs SUBSET FDOM st2) /\
             (!v. v IN vs ==> (FST (st1 ' v) = FST (st2 ' v)))) ==>
             ((e st1) = (e st2)))``,

SIMP_TAC std_ss [SMALLFOOT_AE_USED_VARS_REL_def,		 
		 VAR_RES_STACK___IS_EQUAL_UPTO_PERMISSIONS_def,
		 NOT_IN_EMPTY] THEN
EQ_TAC THEN STRIP_TAC THENL [
   ASM_SIMP_TAC std_ss [] THEN
   REPEAT STRIP_TAC THENL [
      METIS_TAC[optionTheory.option_CLAUSES],

      Tactical.REVERSE (`e (DRESTRICT st1 vs) = e (DRESTRICT st2 vs)` by ALL_TAC) THEN1 METIS_TAC[] THEN
      Q.PAT_ASSUM `!st1 st2. X st1 st2` MATCH_MP_TAC THEN
      FULL_SIMP_TAC std_ss [DRESTRICT_DEF, IN_INTER, SUBSET_DEF, EXTENSION] THEN
      METIS_TAC[]
   ],


   ASM_SIMP_TAC std_ss [] THEN
   REPEAT STRIP_TAC THENL [
      Tactical.REVERSE (Cases_on `vs SUBSET FDOM st`) THEN1 (
         `~(vs SUBSET (FDOM (DRESTRICT st vs)))` by ALL_TAC THEN1 (
    	     FULL_SIMP_TAC std_ss [DRESTRICT_DEF, SUBSET_DEF, IN_INTER] THEN
             METIS_TAC[]
         ) THEN
	 `~(IS_SOME (e st)) /\ ~(IS_SOME (e (DRESTRICT st vs)))` by PROVE_TAC[] THEN
	 FULL_SIMP_TAC std_ss []
      ) THEN
      Q.PAT_ASSUM `!st1 st2. X st1 st2` MATCH_MP_TAC THEN
      FULL_SIMP_TAC std_ss [SUBSET_DEF, DRESTRICT_DEF, IN_INTER],



      Tactical.REVERSE (Cases_on `vs SUBSET FDOM st2`) THEN1 (
	 `~(IS_SOME (e st1)) /\ ~(IS_SOME (e st2))` by PROVE_TAC[] THEN
	 FULL_SIMP_TAC std_ss []
      ) THEN
      Q.PAT_ASSUM `!st1 st2. X st1 st2` MATCH_MP_TAC THEN
      FULL_SIMP_TAC std_ss [SUBSET_DEF]
  ]
]);



val SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___binexpression = store_thm (
"SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___binexpression",

``!emp p e1 e2 vs1 vs2 vs.
  ((SMALLFOOT_AE_USED_VARS e1 = SOME vs1) /\
  (SMALLFOOT_AE_USED_VARS e2 = SOME vs2) /\
  (vs1 UNION vs2 SUBSET vs)) ==>

(SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS vs (smallfoot_ap_binexpression emp p e1 e2))``,



SIMP_TAC std_ss [SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___ALTERNATIVE_DEF, 
		 SMALLFOOT_AE_USED_VARS_THM,
		 SMALLFOOT_AE_USED_VARS_REL___REWRITE,
		 smallfoot_ap_binexpression_def, LET_THM,
		 smallfoot_a_stack_proposition_def, IN_ABS] THEN
REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
REPEAT (Q.PAT_ASSUM `!st1 st2. X st1 st2` (ASSUME_TAC o Q.SPECL [`st1`, `st2`])) THEN
FULL_SIMP_TAC std_ss [SUBSET_DEF, IN_INTER, IN_UNION] THEN
STRIP_TAC THEN GEN_TAC THEN
Q.ABBREV_TAC `unimportant = ((h = FEMPTY) \/ ~emp)` THEN
STRIP_TAC THEN
Tactical.REVERSE (`(e1 st2 = e1 st1) /\ (e2 st2 = e2 st1)` by ALL_TAC) THEN ASM_REWRITE_TAC[] THEN
FULL_SIMP_TAC std_ss []);



      



val SMALLFOOT_AE_USED_VARS___smallfoot_ae_const = store_thm (
"SMALLFOOT_AE_USED_VARS___smallfoot_ae_const",
``SMALLFOOT_AE_USED_VARS (smallfoot_ae_const c) = SOME {}``,


SIMP_TAC std_ss [smallfoot_ae_const_def,
		 SMALLFOOT_AE_USED_VARS_THM,
		 SMALLFOOT_AE_USED_VARS_REL___REWRITE,
		 EMPTY_SUBSET, FINITE_EMPTY]);




val SMALLFOOT_AE_USED_VARS___smallfoot_ae_var = store_thm (
"SMALLFOOT_AE_USED_VARS___smallfoot_ae_var",
``SMALLFOOT_AE_USED_VARS (smallfoot_ae_var v) = SOME {v}``,

SIMP_TAC std_ss [SMALLFOOT_AE_USED_VARS_THM,
		 SMALLFOOT_AE_USED_VARS_REL___REWRITE,
		 smallfoot_ae_var_def, SUBSET_DEF, IN_SING,
		 COND_REWRITES, FINITE_INSERT, FINITE_EMPTY]);


    
val SMALLFOOT_AE_USED_VARS___smallfoot_ae_binop = store_thm (
"SMALLFOOT_AE_USED_VARS___smallfoot_ae_binop",
``!e1 e2 vs1 vs2 bop.
  ((SMALLFOOT_AE_USED_VARS e1 = SOME vs1) /\
  (SMALLFOOT_AE_USED_VARS e2 = SOME vs2)) ==>

  (SMALLFOOT_AE_USED_VARS (smallfoot_ae_binop bop e1 e2) = SOME (vs1 UNION vs2))
``,

SIMP_TAC std_ss [SMALLFOOT_AE_USED_VARS_THM,
		 SMALLFOOT_AE_USED_VARS_REL___REWRITE,
		 smallfoot_ae_binop_def, LET_THM] THEN
SIMP_TAC std_ss [SUBSET_REFL, FINITE_UNION,
		     UNION_SUBSET, IN_UNION] THEN
REPEAT STRIP_TAC THENL [
   ASM_SIMP_TAC std_ss [COND_RAND, COND_RATOR],
   ASM_SIMP_TAC std_ss [COND_RAND, COND_RATOR],   
   METIS_TAC[]
]);


val SMALLFOOT_PE_USED_VARS_def = Define `
    SMALLFOOT_PE_USED_VARS p = 
    SMALLFOOT_AE_USED_VARS (SMALLFOOT_P_EXPRESSION_EVAL p)`;



val SMALLFOOT_PE_USED_VARS___IS_SOME =
store_thm ("SMALLFOOT_PE_USED_VARS___IS_SOME",
``!p. IS_SOME (SMALLFOOT_PE_USED_VARS p)``,

REWRITE_TAC [SMALLFOOT_PE_USED_VARS_def] THEN
Induct_on `p` THENL [
   SIMP_TAC std_ss [SMALLFOOT_P_EXPRESSION_EVAL_def, 
		    SMALLFOOT_AE_USED_VARS___smallfoot_ae_var],

   SIMP_TAC std_ss [SMALLFOOT_P_EXPRESSION_EVAL_def, 
		    SMALLFOOT_AE_USED_VARS___smallfoot_ae_const],


   FULL_SIMP_TAC std_ss [SMALLFOOT_P_EXPRESSION_EVAL_def,
			 IS_SOME_EXISTS] THEN
   Q.EXISTS_TAC `y UNION y'` THEN
   MATCH_MP_TAC SMALLFOOT_AE_USED_VARS___smallfoot_ae_binop THEN
   ASM_SIMP_TAC std_ss [],


   FULL_SIMP_TAC std_ss [SMALLFOOT_P_EXPRESSION_EVAL_def,
			 IS_SOME_EXISTS] THEN
   Q.EXISTS_TAC `y UNION y'` THEN
   MATCH_MP_TAC SMALLFOOT_AE_USED_VARS___smallfoot_ae_binop THEN
   ASM_SIMP_TAC std_ss []
]);



val SMALLFOOT_PE_USED_VARS___REWRITE =
store_thm ("SMALLFOOT_PE_USED_VARS___REWRITE",
``(!c. (SMALLFOOT_PE_USED_VARS (smallfoot_p_const c) = SOME {})) /\
  (!v. (SMALLFOOT_PE_USED_VARS (smallfoot_p_var v) = SOME {v})) /\
  (!e1 e2. 
       (SMALLFOOT_PE_USED_VARS (smallfoot_p_add e1 e2) = 
	SOME ((THE (SMALLFOOT_PE_USED_VARS e1)) UNION 
              (THE (SMALLFOOT_PE_USED_VARS e2))))) /\
  (!e1 e2. 
       (SMALLFOOT_PE_USED_VARS (smallfoot_p_sub e1 e2) = 
	SOME ((THE (SMALLFOOT_PE_USED_VARS e1)) UNION 
              (THE (SMALLFOOT_PE_USED_VARS e2)))))``,


SIMP_TAC std_ss [SMALLFOOT_PE_USED_VARS_def,
		 SMALLFOOT_P_EXPRESSION_EVAL_def,
		 SMALLFOOT_AE_USED_VARS___smallfoot_ae_const,
		 SMALLFOOT_AE_USED_VARS___smallfoot_ae_var] THEN
REPEAT STRIP_TAC THEN (
   MATCH_MP_TAC SMALLFOOT_AE_USED_VARS___smallfoot_ae_binop THEN
   ASM_SIMP_TAC std_ss [SOME_THE_EQ, GSYM SMALLFOOT_PE_USED_VARS_def,
		        SMALLFOOT_PE_USED_VARS___IS_SOME]
));



val SMALLFOOT_PP_USED_VARS_def = Define `
   (SMALLFOOT_PP_USED_VARS (fasl_pred_true) = EMPTY) /\
   (SMALLFOOT_PP_USED_VARS (fasl_pred_false) = EMPTY) /\
   (SMALLFOOT_PP_USED_VARS (fasl_pred_neg p) = SMALLFOOT_PP_USED_VARS p) /\
   (SMALLFOOT_PP_USED_VARS (fasl_pred_and p1 p2) = 
      SMALLFOOT_PP_USED_VARS p1 UNION SMALLFOOT_PP_USED_VARS p2) /\
   (SMALLFOOT_PP_USED_VARS (fasl_pred_or p1 p2) = 
      SMALLFOOT_PP_USED_VARS p1 UNION SMALLFOOT_PP_USED_VARS p2) /\
   (SMALLFOOT_PP_USED_VARS (fasl_pred_prim (smallfoot_pt_equal e1 e2)) = 
      THE (SMALLFOOT_PE_USED_VARS e1) UNION THE (SMALLFOOT_PE_USED_VARS e2)) /\
   (SMALLFOOT_PP_USED_VARS (fasl_pred_prim (smallfoot_pt_less e1 e2)) = 
      THE (SMALLFOOT_PE_USED_VARS e1) UNION THE (SMALLFOOT_PE_USED_VARS e2))`;



val SMALLFOOT_PP_USED_VARS_THM = store_thm("SMALLFOOT_PP_USED_VARS_THM",
``   (SMALLFOOT_PP_USED_VARS (fasl_pred_true) = EMPTY) /\
   (SMALLFOOT_PP_USED_VARS (fasl_pred_false) = EMPTY) /\
   (SMALLFOOT_PP_USED_VARS (fasl_pred_neg p) = SMALLFOOT_PP_USED_VARS p) /\
   (SMALLFOOT_PP_USED_VARS (fasl_pred_and p1 p2) = 
      SMALLFOOT_PP_USED_VARS p1 UNION SMALLFOOT_PP_USED_VARS p2) /\
   (SMALLFOOT_PP_USED_VARS (fasl_pred_or p1 p2) = 
      SMALLFOOT_PP_USED_VARS p1 UNION SMALLFOOT_PP_USED_VARS p2) /\
   (SMALLFOOT_PP_USED_VARS (fasl_pred_prim (smallfoot_pt_equal e1 e2)) = 
      THE (SMALLFOOT_PE_USED_VARS e1) UNION THE (SMALLFOOT_PE_USED_VARS e2)) /\
   (SMALLFOOT_PP_USED_VARS (fasl_pred_prim (smallfoot_pt_less e1 e2)) = 
      THE (SMALLFOOT_PE_USED_VARS e1) UNION THE (SMALLFOOT_PE_USED_VARS e2)) /\

   (SMALLFOOT_PP_USED_VARS (smallfoot_p_equal e1 e2) = 
      THE (SMALLFOOT_PE_USED_VARS e1) UNION THE (SMALLFOOT_PE_USED_VARS e2)) /\
   (SMALLFOOT_PP_USED_VARS (smallfoot_p_unequal e1 e2) = 
      THE (SMALLFOOT_PE_USED_VARS e1) UNION THE (SMALLFOOT_PE_USED_VARS e2)) /\
   (SMALLFOOT_PP_USED_VARS (smallfoot_p_less e1 e2) = 
      THE (SMALLFOOT_PE_USED_VARS e1) UNION THE (SMALLFOOT_PE_USED_VARS e2)) /\
   (SMALLFOOT_PP_USED_VARS (smallfoot_p_lesseq e1 e2) = 
      THE (SMALLFOOT_PE_USED_VARS e1) UNION THE (SMALLFOOT_PE_USED_VARS e2)) /\
   (SMALLFOOT_PP_USED_VARS (smallfoot_p_greater e1 e2) = 
      THE (SMALLFOOT_PE_USED_VARS e1) UNION THE (SMALLFOOT_PE_USED_VARS e2)) /\
   (SMALLFOOT_PP_USED_VARS (smallfoot_p_greatereq e1 e2) = 
      THE (SMALLFOOT_PE_USED_VARS e1) UNION THE (SMALLFOOT_PE_USED_VARS e2))``,

SIMP_TAC std_ss [SMALLFOOT_PP_USED_VARS_def,
	     smallfoot_p_equal_def, smallfoot_p_unequal_def,
	     smallfoot_p_lesseq_def, smallfoot_p_less_def,
	     smallfoot_p_greatereq_def, smallfoot_p_greater_def] THEN
SIMP_TAC std_ss [EXTENSION, IN_UNION] THEN
METIS_TAC[]);








val smallfoot_predicate_IS_DECIDED_IN_STATE =
store_thm ("smallfoot_predicate_IS_DECIDED_IN_STATE",
``
!p state.
SMALLFOOT_PP_USED_VARS p SUBSET FDOM (FST state) ==>
fasl_predicate_IS_DECIDED_IN_STATE smallfoot_env state p``,

Induct_on `p` THENL [
   SIMP_TAC std_ss [fasl_predicate_IS_DECIDED_IN_STATE_def,
	   	    XEVAL_fasl_predicate_def,
   		    EVAL_fasl_predicate_def,
		 smallfoot_env_def, IN_ABS,
		 ASL_INTUITIONISTIC_NEGATION_def,
		 ASL_IS_SEPARATE_def,
		 IS_SOME_EXISTS,
		 GSYM LEFT_FORALL_IMP_THM] THEN
   SIMP_TAC std_ss [SOME___smallfoot_separation_combinator,
		 GSYM LEFT_FORALL_IMP_THM, PAIR_FORALL_THM,
		 SOME___VAR_RES_STACK_COMBINE] THEN
   Cases_on `p` THEN (
      SIMP_TAC std_ss [SMALLFOOT_PT_PROPOSITION_pred_map_def,
		       smallfoot_ap_binexpression_def,
		       smallfoot_a_stack_proposition_def,
		       LET_THM, IN_ABS, SMALLFOOT_PP_USED_VARS_def] THEN
      REPEAT STRIP_TAC THEN
      `?vs1. SMALLFOOT_PE_USED_VARS s' = SOME vs1` by
          PROVE_TAC[SMALLFOOT_PE_USED_VARS___IS_SOME, IS_SOME_EXISTS] THEN
      `?vs2. SMALLFOOT_PE_USED_VARS s0 = SOME vs2` by
          PROVE_TAC[SMALLFOOT_PE_USED_VARS___IS_SOME, IS_SOME_EXISTS] THEN
      FULL_SIMP_TAC std_ss [UNION_SUBSET] THEN
      FULL_SIMP_TAC std_ss [SMALLFOOT_PE_USED_VARS_def,
			    SMALLFOOT_AE_USED_VARS_THM,
			    SMALLFOOT_AE_USED_VARS_REL___REWRITE,
			    FMERGE_DEF] THEN
      FULL_SIMP_TAC std_ss [SUBSET_DEF, IN_UNION] THEN
      MATCH_MP_TAC (prove (``(~A ==> B) ==> (A \/ B)``, PROVE_TAC[])) THEN
      REPEAT STRIP_TAC THEN
      Tactical.REVERSE (`(SMALLFOOT_P_EXPRESSION_EVAL s'
                (FMERGE VAR_RES_STACK_COMBINE___MERGE_FUNC x1 x1') =
                        SMALLFOOT_P_EXPRESSION_EVAL s' x1) /\
                (SMALLFOOT_P_EXPRESSION_EVAL s0
                (FMERGE VAR_RES_STACK_COMBINE___MERGE_FUNC x1 x1') =
                        SMALLFOOT_P_EXPRESSION_EVAL s0 x1)` by ALL_TAC) THEN1 (
         FULL_SIMP_TAC std_ss []
      ) THEN
      CONJ_TAC THENL [
         Q.PAT_ASSUM `!st1 st2. X st1 st2 ==>
	              (SMALLFOOT_P_EXPRESSION_EVAL s' st1 =
                       SMALLFOOT_P_EXPRESSION_EVAL s' st2)` MP_TAC THEN
	 ASM_SIMP_TAC std_ss [FMERGE_DEF, IN_UNION,
			      VAR_RES_STACK_COMBINE___MERGE_FUNC_def,
			      COND_REWRITES],

         Q.PAT_ASSUM `!st1 st2. X st1 st2 ==>
	              (SMALLFOOT_P_EXPRESSION_EVAL s0 st1 =
                       SMALLFOOT_P_EXPRESSION_EVAL s0 st2)` MATCH_MP_TAC THEN
	 ASM_SIMP_TAC std_ss [FMERGE_DEF, IN_UNION,
			      VAR_RES_STACK_COMBINE___MERGE_FUNC_def,
			      COND_REWRITES]
      ]
   ),


   REWRITE_TAC [fasl_predicate_IS_DECIDED_IN_STATE___pred_true],
   REWRITE_TAC [fasl_predicate_IS_DECIDED_IN_STATE___pred_false],


   REPEAT STRIP_TAC THEN
   MATCH_MP_TAC fasl_predicate_IS_DECIDED_IN_STATE_NEGATION THEN
   FULL_SIMP_TAC std_ss [SMALLFOOT_PP_USED_VARS_def,
			 FASL_IS_LOCAL_EVAL_XENV_def,
			 FASL_IS_LOCAL_EVAL_ENV___smallfoot_env],


   REPEAT STRIP_TAC THEN
   MATCH_MP_TAC fasl_predicate_IS_DECIDED_IN_STATE___pred_and THEN
   FULL_SIMP_TAC std_ss [SMALLFOOT_PP_USED_VARS_def,
			 UNION_SUBSET],


   REPEAT STRIP_TAC THEN
   MATCH_MP_TAC fasl_predicate_IS_DECIDED_IN_STATE___pred_or THEN
   FULL_SIMP_TAC std_ss [SMALLFOOT_PP_USED_VARS_def,
			 UNION_SUBSET]
]);








val SMALLFOOT_P_PROPOSITION_EVAL_def = Define `
	(SMALLFOOT_P_PROPOSITION_EVAL fasl_pred_true = 
        smallfoot_ap_stack_true) /\
	(SMALLFOOT_P_PROPOSITION_EVAL fasl_pred_false = 
        asl_false) /\

	(SMALLFOOT_P_PROPOSITION_EVAL (fasl_pred_and p1 p2) = 
        asl_and (SMALLFOOT_P_PROPOSITION_EVAL p1) 
                         (SMALLFOOT_P_PROPOSITION_EVAL p2)) /\
	(SMALLFOOT_P_PROPOSITION_EVAL (fasl_pred_or p1 p2) = 
        asl_or (SMALLFOOT_P_PROPOSITION_EVAL p1) 
                         (SMALLFOOT_P_PROPOSITION_EVAL p2)) /\

	(SMALLFOOT_P_PROPOSITION_EVAL (fasl_pred_prim (smallfoot_pt_less e1 e2)) =
           smallfoot_ap_less (SMALLFOOT_P_EXPRESSION_EVAL e1)  (SMALLFOOT_P_EXPRESSION_EVAL e2)) /\

	(SMALLFOOT_P_PROPOSITION_EVAL (fasl_pred_prim (smallfoot_pt_equal e1 e2)) =
           smallfoot_ap_equal (SMALLFOOT_P_EXPRESSION_EVAL e1)  (SMALLFOOT_P_EXPRESSION_EVAL e2)) /\


	(SMALLFOOT_P_PROPOSITION_EVAL (fasl_pred_neg fasl_pred_true) = 
         SMALLFOOT_P_PROPOSITION_EVAL fasl_pred_false) /\

	(SMALLFOOT_P_PROPOSITION_EVAL (fasl_pred_neg fasl_pred_false) = 
         SMALLFOOT_P_PROPOSITION_EVAL fasl_pred_true) /\

	(SMALLFOOT_P_PROPOSITION_EVAL (fasl_pred_neg (fasl_pred_and p1 p2)) = 
         asl_or (SMALLFOOT_P_PROPOSITION_EVAL (fasl_pred_neg p1)) 
                (SMALLFOOT_P_PROPOSITION_EVAL (fasl_pred_neg p2))) /\


	(SMALLFOOT_P_PROPOSITION_EVAL (fasl_pred_neg (fasl_pred_or p1 p2)) = 
         asl_and (SMALLFOOT_P_PROPOSITION_EVAL (fasl_pred_neg p1)) 
                 (SMALLFOOT_P_PROPOSITION_EVAL (fasl_pred_neg p2))) /\


	(SMALLFOOT_P_PROPOSITION_EVAL (fasl_pred_neg (fasl_pred_prim (smallfoot_pt_less e1 e2))) =
           smallfoot_ap_lesseq (SMALLFOOT_P_EXPRESSION_EVAL e2)  (SMALLFOOT_P_EXPRESSION_EVAL e1)) /\

	(SMALLFOOT_P_PROPOSITION_EVAL (fasl_pred_neg (fasl_pred_prim (smallfoot_pt_equal e1 e2))) =
           smallfoot_ap_unequal (SMALLFOOT_P_EXPRESSION_EVAL e2)  (SMALLFOOT_P_EXPRESSION_EVAL e1)) /\

	(SMALLFOOT_P_PROPOSITION_EVAL (fasl_pred_neg (fasl_pred_neg p)) =
         SMALLFOOT_P_PROPOSITION_EVAL p)` 




val SMALLFOOT_P_PROPOSITION___NEG_REWRITE_def = Define
`(SMALLFOOT_P_PROPOSITION___NEG_REWRITE fasl_pred_true = fasl_pred_true) /\
 (SMALLFOOT_P_PROPOSITION___NEG_REWRITE fasl_pred_false = fasl_pred_false) /\
 (SMALLFOOT_P_PROPOSITION___NEG_REWRITE (fasl_pred_and p1 p2) = 
      fasl_pred_and (SMALLFOOT_P_PROPOSITION___NEG_REWRITE p1)
                    (SMALLFOOT_P_PROPOSITION___NEG_REWRITE p2)) /\
  (SMALLFOOT_P_PROPOSITION___NEG_REWRITE (fasl_pred_or p1 p2) = 
      fasl_pred_or (SMALLFOOT_P_PROPOSITION___NEG_REWRITE p1) 
                   (SMALLFOOT_P_PROPOSITION___NEG_REWRITE p2)) /\
  (SMALLFOOT_P_PROPOSITION___NEG_REWRITE (fasl_pred_prim pt) = 
      fasl_pred_prim pt) /\

  (SMALLFOOT_P_PROPOSITION___NEG_REWRITE (fasl_pred_neg fasl_pred_true) = fasl_pred_false) /\
  (SMALLFOOT_P_PROPOSITION___NEG_REWRITE (fasl_pred_neg fasl_pred_false) = fasl_pred_true) /\
  (SMALLFOOT_P_PROPOSITION___NEG_REWRITE (fasl_pred_neg (fasl_pred_and p1 p2)) = 
      fasl_pred_or (SMALLFOOT_P_PROPOSITION___NEG_REWRITE (fasl_pred_neg p1)) 
                   (SMALLFOOT_P_PROPOSITION___NEG_REWRITE (fasl_pred_neg p2))) /\
  (SMALLFOOT_P_PROPOSITION___NEG_REWRITE (fasl_pred_neg (fasl_pred_or p1 p2)) = 
      fasl_pred_and (SMALLFOOT_P_PROPOSITION___NEG_REWRITE (fasl_pred_neg p1)) 
                   (SMALLFOOT_P_PROPOSITION___NEG_REWRITE (fasl_pred_neg p2))) /\
  (SMALLFOOT_P_PROPOSITION___NEG_REWRITE (fasl_pred_neg (fasl_pred_prim (smallfoot_pt_less e1 e2))) = 
      fasl_pred_or (fasl_pred_prim (smallfoot_pt_less e2 e1))
                   (fasl_pred_prim (smallfoot_pt_equal e1 e2))) /\
  (SMALLFOOT_P_PROPOSITION___NEG_REWRITE (fasl_pred_neg (fasl_pred_prim (smallfoot_pt_equal e1 e2))) = 
      fasl_pred_or (fasl_pred_prim (smallfoot_pt_less e2 e1))
                   (fasl_pred_prim (smallfoot_pt_less e1 e2))) /\
  (SMALLFOOT_P_PROPOSITION___NEG_REWRITE (fasl_pred_neg (fasl_pred_neg p)) = 
   SMALLFOOT_P_PROPOSITION___NEG_REWRITE p)`;






val SMALLFOOT_P_PROPOSITION___IS_NEG_FREE_def = Define
`(SMALLFOOT_P_PROPOSITION___IS_NEG_FREE fasl_pred_true = T) /\
 (SMALLFOOT_P_PROPOSITION___IS_NEG_FREE fasl_pred_false = T) /\
 (SMALLFOOT_P_PROPOSITION___IS_NEG_FREE (fasl_pred_and p1 p2) = 
      ((SMALLFOOT_P_PROPOSITION___IS_NEG_FREE p1) /\
      (SMALLFOOT_P_PROPOSITION___IS_NEG_FREE p2))) /\
  (SMALLFOOT_P_PROPOSITION___IS_NEG_FREE (fasl_pred_or p1 p2) = 
      (SMALLFOOT_P_PROPOSITION___IS_NEG_FREE p1) /\
      (SMALLFOOT_P_PROPOSITION___IS_NEG_FREE p2)) /\
  (SMALLFOOT_P_PROPOSITION___IS_NEG_FREE (fasl_pred_prim pt) = T) /\
  (SMALLFOOT_P_PROPOSITION___IS_NEG_FREE (fasl_pred_neg p) = F)`;



val SMALLFOOT_P_PROPOSITION___NEG_COUNT_def = Define 
`(SMALLFOOT_P_PROPOSITION___NEG_COUNT fasl_pred_true = 0) /\
 (SMALLFOOT_P_PROPOSITION___NEG_COUNT fasl_pred_false = 0) /\
 (SMALLFOOT_P_PROPOSITION___NEG_COUNT (fasl_pred_and p1 p2) = 
      ((SMALLFOOT_P_PROPOSITION___NEG_COUNT p1) +
      (SMALLFOOT_P_PROPOSITION___NEG_COUNT p2))) /\
  (SMALLFOOT_P_PROPOSITION___NEG_COUNT (fasl_pred_or p1 p2) = 
      (SMALLFOOT_P_PROPOSITION___NEG_COUNT p1) +
      (SMALLFOOT_P_PROPOSITION___NEG_COUNT p2)) /\
  (SMALLFOOT_P_PROPOSITION___NEG_COUNT (fasl_pred_prim pt) = 0) /\
  (SMALLFOOT_P_PROPOSITION___NEG_COUNT (fasl_pred_neg p) = 
   SUC (SMALLFOOT_P_PROPOSITION___NEG_COUNT p))`;


val SMALLFOOT_P_PROPOSITION___NEG_COUNT___IS_NEG_FREE = 
store_thm ("SMALLFOOT_P_PROPOSITION___NEG_COUNT___IS_NEG_FREE",
``(SMALLFOOT_P_PROPOSITION___NEG_COUNT p = 0) =
  (SMALLFOOT_P_PROPOSITION___IS_NEG_FREE p)``,

Induct_on `p` THEN (
   ASM_SIMP_TAC arith_ss [SMALLFOOT_P_PROPOSITION___NEG_COUNT_def,
		    SMALLFOOT_P_PROPOSITION___IS_NEG_FREE_def]
));




val SMALLFOOT_P_PROPOSITION___IS_NEG_FREE___NEG_REWRITE_ID =
store_thm ("SMALLFOOT_P_PROPOSITION___IS_NEG_FREE___NEG_REWRITE_ID",
``
!p. SMALLFOOT_P_PROPOSITION___IS_NEG_FREE p ==>
    ((SMALLFOOT_P_PROPOSITION___NEG_REWRITE p) = p)``,

Induct_on `p` THEN (
   ASM_SIMP_TAC std_ss [SMALLFOOT_P_PROPOSITION___NEG_REWRITE_def,
		    SMALLFOOT_P_PROPOSITION___IS_NEG_FREE_def]
));




val SMALLFOOT_P_PROPOSITION___NEG_REWRITE___IS_NEG_FREE___helper = 
prove (``
!p n. (SMALLFOOT_P_PROPOSITION___NEG_COUNT p <= n) ==>
(SMALLFOOT_P_PROPOSITION___IS_NEG_FREE (SMALLFOOT_P_PROPOSITION___NEG_REWRITE p))``,

Induct_on `n` THEN1 (
   SIMP_TAC arith_ss [SMALLFOOT_P_PROPOSITION___IS_NEG_FREE___NEG_REWRITE_ID,
		    SMALLFOOT_P_PROPOSITION___NEG_COUNT___IS_NEG_FREE]
) THEN
Induct_on `p` THEN (
   ASM_SIMP_TAC arith_ss [SMALLFOOT_P_PROPOSITION___NEG_REWRITE_def,
		        SMALLFOOT_P_PROPOSITION___IS_NEG_FREE_def,
		        SMALLFOOT_P_PROPOSITION___NEG_COUNT_def]
) THEN

Induct_on `p` THEN (
   ASM_SIMP_TAC arith_ss [SMALLFOOT_P_PROPOSITION___NEG_REWRITE_def,
        SMALLFOOT_P_PROPOSITION___IS_NEG_FREE_def,
        SMALLFOOT_P_PROPOSITION___NEG_COUNT_def]
) THEN
Cases_on `p` THEN (
  SIMP_TAC std_ss [SMALLFOOT_P_PROPOSITION___NEG_REWRITE_def,
      SMALLFOOT_P_PROPOSITION___IS_NEG_FREE_def]
));



val SMALLFOOT_P_PROPOSITION___NEG_REWRITE___IS_NEG_FREE = store_thm 
("SMALLFOOT_P_PROPOSITION___NEG_REWRITE___IS_NEG_FREE", 
``!p. SMALLFOOT_P_PROPOSITION___IS_NEG_FREE (SMALLFOOT_P_PROPOSITION___NEG_REWRITE p)``,

    METIS_TAC [SMALLFOOT_P_PROPOSITION___NEG_REWRITE___IS_NEG_FREE___helper,
	       LESS_EQ_REFL]);





val SMALLFOOT_P_PROPOSITION___IS_NEG_REWRITE___IDEM =
store_thm ("SMALLFOOT_P_PROPOSITION___IS_NEG_REWRITE___IDEM",
``
!p. (SMALLFOOT_P_PROPOSITION___NEG_REWRITE (SMALLFOOT_P_PROPOSITION___NEG_REWRITE p)) =
    (SMALLFOOT_P_PROPOSITION___NEG_REWRITE p)``,

METIS_TAC[SMALLFOOT_P_PROPOSITION___NEG_REWRITE___IS_NEG_FREE,
	  SMALLFOOT_P_PROPOSITION___IS_NEG_FREE___NEG_REWRITE_ID]);




val SMALLFOOT_P_PROPOSITION_EVAL___NEG_REWRITE___helper =
prove (
``
!p n. (SMALLFOOT_P_PROPOSITION___NEG_COUNT p <= n) ==>
(SMALLFOOT_P_PROPOSITION_EVAL (SMALLFOOT_P_PROPOSITION___NEG_REWRITE p) =
SMALLFOOT_P_PROPOSITION_EVAL p)``,

Induct_on `n` THEN1 (
   SIMP_TAC arith_ss [SMALLFOOT_P_PROPOSITION___NEG_COUNT___IS_NEG_FREE,
		      SMALLFOOT_P_PROPOSITION___IS_NEG_FREE___NEG_REWRITE_ID]
) THEN
Induct_on `p` THEN (
   ASM_SIMP_TAC arith_ss [SMALLFOOT_P_PROPOSITION___NEG_REWRITE_def,
  		        SMALLFOOT_P_PROPOSITION___NEG_COUNT_def,
			  SMALLFOOT_P_PROPOSITION_EVAL_def]
) THEN
Induct_on `p` THEN (
   ASM_SIMP_TAC arith_ss [SMALLFOOT_P_PROPOSITION___NEG_REWRITE_def,
  		        SMALLFOOT_P_PROPOSITION___NEG_COUNT_def,
			  SMALLFOOT_P_PROPOSITION_EVAL_def]
) THEN
Cases_on `p` THEN (
  ONCE_REWRITE_TAC [EXTENSION] THEN
  SIMP_TAC (std_ss++bool_eq_imp_ss)
                  [SMALLFOOT_P_PROPOSITION___NEG_REWRITE_def,
      SMALLFOOT_P_PROPOSITION_EVAL_def,
		   smallfoot_ap_unequal_def,
		   smallfoot_ap_less_def,
		   smallfoot_ap_lesseq_def,
		   smallfoot_ap_equal_def,
		   asl_bool_EVAL, smallfoot_ap_binexpression_def,
		   smallfoot_a_stack_proposition_def,
		   IN_ABS, PAIR_FORALL_THM, LET_THM] THEN
  REPEAT STRIP_TAC THEN
  FULL_SIMP_TAC arith_ss [IS_SOME_EXISTS]   
));



val SMALLFOOT_P_PROPOSITION_EVAL___NEG_REWRITE =
store_thm ("SMALLFOOT_P_PROPOSITION_EVAL___NEG_REWRITE",
``!p. 
(SMALLFOOT_P_PROPOSITION_EVAL (SMALLFOOT_P_PROPOSITION___NEG_REWRITE p) =
SMALLFOOT_P_PROPOSITION_EVAL p)``,

PROVE_TAC [SMALLFOOT_P_PROPOSITION_EVAL___NEG_REWRITE___helper,
	   LESS_EQ_REFL]);


val SMALLFOOT_PP_USED_VARS___SMALLFOOT_P_PROPOSITION___NEG_REWRITE___helper =
prove (
``!p n. (SMALLFOOT_P_PROPOSITION___NEG_COUNT p <= n) ==>
(SMALLFOOT_PP_USED_VARS (SMALLFOOT_P_PROPOSITION___NEG_REWRITE p) =
SMALLFOOT_PP_USED_VARS p)``,

completeInduct_on `n` THEN
Induct_on `p` THEN (
   ASM_SIMP_TAC arith_ss [SMALLFOOT_PP_USED_VARS_def,
		    SMALLFOOT_P_PROPOSITION___NEG_REWRITE_def,
		        SMALLFOOT_P_PROPOSITION___NEG_COUNT_def]
) THEN
Cases_on `n` THEN SIMP_TAC arith_ss [] THEN
REPEAT STRIP_TAC THEN
Q.PAT_ASSUM `!m. X m` (ASSUME_TAC o Q.SPEC `n'`) THEN
FULL_SIMP_TAC arith_ss [] THEN
Induct_on `p` THEN (
   ASM_SIMP_TAC arith_ss [SMALLFOOT_PP_USED_VARS_def,
		    SMALLFOOT_P_PROPOSITION___NEG_REWRITE_def,
		        SMALLFOOT_P_PROPOSITION___NEG_COUNT_def]
) THEN
Cases_on `p` THEN (
   SIMP_TAC std_ss [SMALLFOOT_P_PROPOSITION___NEG_REWRITE_def,
		    SMALLFOOT_PP_USED_VARS_def, EXTENSION, 
		    IN_UNION] THEN
   METIS_TAC[]
));


val SMALLFOOT_PP_USED_VARS___SMALLFOOT_P_PROPOSITION___NEG_REWRITE =
store_thm ("SMALLFOOT_PP_USED_VARS___SMALLFOOT_P_PROPOSITION___NEG_REWRITE",
``!p.
(SMALLFOOT_PP_USED_VARS (SMALLFOOT_P_PROPOSITION___NEG_REWRITE p) =
SMALLFOOT_PP_USED_VARS p)``,

PROVE_TAC[SMALLFOOT_PP_USED_VARS___SMALLFOOT_P_PROPOSITION___NEG_REWRITE___helper,
	  LESS_EQ_REFL]);




val SMALLFOOT_P_PROPOSITION_EVAL_PREDICATE_REWRITE =
store_thm ("SMALLFOOT_P_PROPOSITION_EVAL_PREDICATE_REWRITE",
``!P. 
  ((!p. P (SMALLFOOT_P_PROPOSITION_EVAL p) (SMALLFOOT_PP_USED_VARS p)) =
   (!p. SMALLFOOT_P_PROPOSITION___IS_NEG_FREE p ==>
	P (SMALLFOOT_P_PROPOSITION_EVAL p) (SMALLFOOT_PP_USED_VARS p)))``,

GEN_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THEN1 (
   ASM_SIMP_TAC std_ss []
) THEN
Q.PAT_ASSUM `!P. X P` (MP_TAC o Q.SPEC `SMALLFOOT_P_PROPOSITION___NEG_REWRITE p`) THEN
ASM_SIMP_TAC std_ss [SMALLFOOT_P_PROPOSITION___NEG_REWRITE___IS_NEG_FREE,
		     SMALLFOOT_P_PROPOSITION_EVAL___NEG_REWRITE,
	             SMALLFOOT_PP_USED_VARS___SMALLFOOT_P_PROPOSITION___NEG_REWRITE]);



val SMALLFOOT_P_PROPOSITION_EVAL_PREDICATE_REWRITE___IMP =
store_thm ("SMALLFOOT_P_PROPOSITION_EVAL_PREDICATE_REWRITE___IMP",
``!P.
   (!p. SMALLFOOT_P_PROPOSITION___IS_NEG_FREE p ==>
	P (SMALLFOOT_P_PROPOSITION_EVAL p) (SMALLFOOT_PP_USED_VARS p)) ==>
   (!p. P (SMALLFOOT_P_PROPOSITION_EVAL p) (SMALLFOOT_PP_USED_VARS p))``,

METIS_TAC[SMALLFOOT_P_PROPOSITION_EVAL_PREDICATE_REWRITE]);


val SMALLFOOT_P_PROPOSITION_EVAL___HEAP_EMPTY = store_thm (
"SMALLFOOT_P_PROPOSITION_EVAL___HEAP_EMPTY",
``
!p s. SMALLFOOT_P_PROPOSITION_EVAL p s ==>
    (SND s = FEMPTY)``,

HO_MATCH_MP_TAC SMALLFOOT_P_PROPOSITION_EVAL_PREDICATE_REWRITE___IMP THEN
Induct_on `p` THEN (
   ASM_SIMP_TAC std_ss [SMALLFOOT_P_PROPOSITION_EVAL_def,
		        SMALLFOOT_P_PROPOSITION___IS_NEG_FREE_def]
) THENL [
   Cases_on `p` THEN
   SIMP_TAC std_ss [SMALLFOOT_P_PROPOSITION_EVAL_def,
		    smallfoot_ap_equal_def,
		    smallfoot_ap_less_def,
		    smallfoot_ap_binexpression_def,
		    smallfoot_a_stack_proposition_def],

   SIMP_TAC std_ss [smallfoot_ap_stack_true_def],

   SIMP_TAC std_ss [asl_bool_EVAL],

   ASM_SIMP_TAC std_ss [asl_bool_EVAL, IN_DEF],

   ASM_SIMP_TAC std_ss [asl_bool_EVAL, IN_DEF,
		        DISJ_IMP_THM]
]);




val fasl_predicate_IS_DECIDED_IN_STATE___pred_neg_is_neg =
store_thm ("fasl_predicate_IS_DECIDED_IN_STATE___pred_neg_is_neg",
``!env s p.
FASL_IS_LOCAL_EVAL_ENV env ==>
(
fasl_predicate_IS_DECIDED_IN_STATE env s p ==>

(s IN XEVAL_fasl_predicate env (fasl_pred_neg p) =
 ~(s IN XEVAL_fasl_predicate env p)))``,

REPEAT GEN_TAC THEN STRIP_TAC THEN
SIMP_TAC std_ss [fasl_predicate_IS_DECIDED_IN_STATE_def,
		 DISJ_IMP_THM,
		 XEVAL_fasl_predicate_def,
		 EVAL_fasl_predicate_def,
		 ASL_INTUITIONISTIC_NEGATION_REWRITE,
		 IN_ABS] THEN
Tactical.REVERSE (`!s. ASL_IS_SUBSTATE (FST env) s s` by ALL_TAC) THEN1 (
   METIS_TAC[]
) THEN
FULL_SIMP_TAC std_ss [FASL_IS_LOCAL_EVAL_ENV_THM,
		      ASL_IS_SUBSTATE_def,
		      IS_SEPARATION_COMBINATOR_EXPAND_THM]);


val SMALLFOOT_AE_USED_VARS_REL___P_EXPRESSION_EVAL = 
store_thm ("SMALLFOOT_AE_USED_VARS_REL___P_EXPRESSION_EVAL",
``!p. SMALLFOOT_AE_USED_VARS_REL (SMALLFOOT_P_EXPRESSION_EVAL p) (THE (SMALLFOOT_PE_USED_VARS p))``,

GEN_TAC THEN
`?vs. SMALLFOOT_PE_USED_VARS p = SOME vs` by 
   PROVE_TAC[SMALLFOOT_PE_USED_VARS___IS_SOME,
             IS_SOME_EXISTS] THEN
ASM_SIMP_TAC std_ss [] THEN
FULL_SIMP_TAC std_ss [SMALLFOOT_PE_USED_VARS_def,
		      SMALLFOOT_AE_USED_VARS_THM]);


val SMALLFOOT_AE_USED_VARS___P_EXPRESSION_EVAL = 
store_thm ("SMALLFOOT_AE_USED_VARS_REL___P_EXPRESSION_EVAL",
``!p. SMALLFOOT_AE_USED_VARS (SMALLFOOT_P_EXPRESSION_EVAL p) = SOME (THE (SMALLFOOT_PE_USED_VARS p))``,

PROVE_TAC[SMALLFOOT_AE_USED_VARS_THM, SMALLFOOT_AE_USED_VARS_REL___P_EXPRESSION_EVAL]);




val SMALLFOOT_P_PROPOSITION_EVAL___fasl_pred_neg = store_thm (
"SMALLFOOT_P_PROPOSITION_EVAL___fasl_pred_neg",
``
!p st. SMALLFOOT_PP_USED_VARS p SUBSET FDOM st ==>
(SMALLFOOT_P_PROPOSITION_EVAL (fasl_pred_neg p) (st,FEMPTY) =
 ~SMALLFOOT_P_PROPOSITION_EVAL p (st,FEMPTY))``,

Induct_on `p` THEN (
   ASM_SIMP_TAC arith_ss [SMALLFOOT_P_PROPOSITION___NEG_COUNT_def,
		        SMALLFOOT_P_PROPOSITION_EVAL_def,
			 asl_bool_EVAL, smallfoot_ap_stack_true_def,
			 IN_DEF, SMALLFOOT_PP_USED_VARS_def,
			 UNION_SUBSET]
) THEN 
Cases_on `p` THEN (
   SIMP_TAC std_ss [SMALLFOOT_P_PROPOSITION_EVAL_def,
		    smallfoot_ap_unequal_def, IN_ABS,
		    smallfoot_ap_equal_def,
		    smallfoot_ap_less_def,
		    smallfoot_ap_lesseq_def,
		    smallfoot_ap_binexpression_def,
		    SMALLFOOT_PP_USED_VARS_def,
		    smallfoot_a_stack_proposition_def,
		    LET_THM, UNION_SUBSET] THEN
   ASSUME_TAC (Q.SPEC `s'` SMALLFOOT_AE_USED_VARS_REL___P_EXPRESSION_EVAL) THEN
   ASSUME_TAC (Q.SPEC `s0` SMALLFOOT_AE_USED_VARS_REL___P_EXPRESSION_EVAL) THEN
   FULL_SIMP_TAC arith_ss [SMALLFOOT_AE_USED_VARS_REL___REWRITE] THEN
   METIS_TAC[]
));



val SMALLFOOT_P_PROPOSITION_EVAL___ALTERNATIVE_DEF___helper =
prove (

``!p n s. 
(SMALLFOOT_P_PROPOSITION___NEG_COUNT p <= n) /\
(SMALLFOOT_PP_USED_VARS p) SUBSET (FDOM (FST s)) ==>

(SMALLFOOT_P_PROPOSITION_EVAL p s =
(((SND s) = FEMPTY) /\
  (s IN XEVAL_fasl_predicate smallfoot_env p)))``,

completeInduct_on `n` THEN
Induct_on `p` THEN (
   FULL_SIMP_TAC std_ss [XEVAL_fasl_predicate_def,
		    EVAL_fasl_predicate_def,
		    smallfoot_env_def,
		    SMALLFOOT_PP_USED_VARS_def,
		    SMALLFOOT_P_PROPOSITION_EVAL_def,
	            EMPTY_SUBSET, asl_bool_EVAL]
) THENL [
  Cases_on `p` THEN
  SIMP_TAC std_ss [SMALLFOOT_PT_PROPOSITION_pred_map_def,
		   smallfoot_ap_binexpression_def,
		   LET_THM, SMALLFOOT_PP_USED_VARS_def,
		   SMALLFOOT_P_PROPOSITION_EVAL_def,
		   smallfoot_ap_equal_def,
		   smallfoot_ap_less_def,
		   smallfoot_a_stack_proposition_def, 
		   IN_ABS],


  SIMP_TAC std_ss [smallfoot_ap_stack_true_def],


  ALL_TAC, (*rotate 1*)


  ASM_SIMP_TAC arith_ss [UNION_SUBSET, asl_bool_EVAL, IN_DEF,
		       SMALLFOOT_P_PROPOSITION___NEG_COUNT_def] THEN
  METIS_TAC[],


  ASM_SIMP_TAC arith_ss [UNION_SUBSET, asl_bool_EVAL, IN_DEF,
		       SMALLFOOT_P_PROPOSITION___NEG_COUNT_def] THEN
  METIS_TAC[]
] THEN

POP_ASSUM (K ALL_TAC) THEN
Cases_on `n` THEN1 (
   SIMP_TAC arith_ss [SMALLFOOT_P_PROPOSITION___NEG_COUNT_def]
) THEN
POP_ASSUM (ASSUME_TAC o Q.SPEC `n'`) THEN
FULL_SIMP_TAC std_ss [SMALLFOOT_P_PROPOSITION___NEG_COUNT_def] THEN
REPEAT STRIP_TAC THEN
` s IN
    ASL_INTUITIONISTIC_NEGATION smallfoot_separation_combinator
      (EVAL_fasl_predicate smallfoot_separation_combinator
         SMALLFOOT_PT_PROPOSITION_pred_map p) =
 ~(s IN (EVAL_fasl_predicate smallfoot_separation_combinator
         SMALLFOOT_PT_PROPOSITION_pred_map p))` by ALL_TAC THEN1 (

   MP_TAC (ISPECL [``smallfoot_env``, ``s:smallfoot_state``,
		   ``p :smallfoot_p_proposition``] fasl_predicate_IS_DECIDED_IN_STATE___pred_neg_is_neg) THEN
   IMP_RES_TAC smallfoot_predicate_IS_DECIDED_IN_STATE THEN
   ASM_REWRITE_TAC[FASL_IS_LOCAL_EVAL_ENV___smallfoot_env,
		   FASL_IS_LOCAL_EVAL_XENV_def] THEN
   SIMP_TAC std_ss [XEVAL_fasl_predicate_def,
		    smallfoot_env_def, EVAL_fasl_predicate_def]
) THEN
ASM_REWRITE_TAC[] THEN POP_ASSUM (K ALL_TAC) THEN
Tactical.REVERSE (Cases_on `SND s = FEMPTY`) THEN1 (
   PROVE_TAC[SMALLFOOT_P_PROPOSITION_EVAL___HEAP_EMPTY]
) THEN
Q.PAT_ASSUM `!p' s. X p' s` (MP_TAC o GSYM o Q.SPECL [`p`, `s`]) THEN
Cases_on `s` THEN
FULL_SIMP_TAC std_ss [SMALLFOOT_P_PROPOSITION_EVAL___fasl_pred_neg]);





val SMALLFOOT_P_PROPOSITION_EVAL___ALTERNATIVE_DEF =
store_thm ("SMALLFOOT_P_PROPOSITION_EVAL___ALTERNATIVE_DEF",

``!p s.  
(SMALLFOOT_PP_USED_VARS p) SUBSET (FDOM (FST s)) ==>

(SMALLFOOT_P_PROPOSITION_EVAL p s =
(((SND s) = FEMPTY) /\
  (s IN XEVAL_fasl_predicate smallfoot_env p)))``,


PROVE_TAC[SMALLFOOT_P_PROPOSITION_EVAL___ALTERNATIVE_DEF___helper,
	  LESS_EQ_REFL]);



val XEVAL_fasl_predicate___smallfoot_env___NO_HEAP =
store_thm ("XEVAL_fasl_predicate___smallfoot_env___NO_HEAP",
``
!p st h1 h2.
XEVAL_fasl_predicate smallfoot_env p (st,h1) =
XEVAL_fasl_predicate smallfoot_env p (st,h2)``,


Induct_on `p` THEN (
  FULL_SIMP_TAC std_ss [XEVAL_fasl_predicate_def,
		   smallfoot_env_def,
		   EVAL_fasl_predicate_def, asl_bool_EVAL,
		   IN_DEF]
) THENL [
  Cases_on `p` THEN
  SIMP_TAC std_ss [SMALLFOOT_PT_PROPOSITION_pred_map_def,
		   smallfoot_ap_binexpression_def,
		   smallfoot_a_stack_proposition_def],


  SIMP_TAC std_ss [ASL_INTUITIONISTIC_NEGATION_REWRITE,
		   GSYM SMALLFOOT_IS_SUBSTATE_def,
		   SMALLFOOT_IS_SUBSTATE_REWRITE,
		   PAIR_FORALL_THM, IN_DEF] THEN
  METIS_TAC[ASL_IS_SUBSTATE___DISJOINT_FMAP_UNION___REFL],


  PROVE_TAC[],
  PROVE_TAC[]
]);




val XEVAL_fasl_predicate___smallfoot_env___ALTERNATIVE_DEF =
store_thm ("XEVAL_fasl_predicate___smallfoot_env___ALTERNATIVE_DEF",

``!p s. 
(SMALLFOOT_PP_USED_VARS p) SUBSET (FDOM (FST s)) ==>

(XEVAL_fasl_predicate smallfoot_env p s =
(SMALLFOOT_P_PROPOSITION_EVAL p (FST s, FEMPTY)))``,

REPEAT GEN_TAC THEN
SIMP_TAC std_ss [SMALLFOOT_P_PROPOSITION_EVAL___ALTERNATIVE_DEF,
		 IN_DEF] THEN
Cases_on `s` THEN
SIMP_TAC std_ss [XEVAL_fasl_predicate___smallfoot_env___NO_HEAP]);






val SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___SMALLFOOT_P_PROPOSITION_EVAL =
store_thm ("SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___SMALLFOOT_P_PROPOSITION_EVAL",
``
!p vs.
SMALLFOOT_PP_USED_VARS p SUBSET vs ==>
SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS vs (SMALLFOOT_P_PROPOSITION_EVAL p)``,


HO_MATCH_MP_TAC SMALLFOOT_P_PROPOSITION_EVAL_PREDICATE_REWRITE___IMP THEN
Induct_on `p` THENL [
   Cases_on `p` THEN (
      SIMP_TAC std_ss [SMALLFOOT_P_PROPOSITION_EVAL_def,
		       smallfoot_ap_equal_def, smallfoot_ap_less_def,
		       SMALLFOOT_PP_USED_VARS_def, UNION_SUBSET] THEN
      REPEAT STRIP_TAC THEN
      MATCH_MP_TAC SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___binexpression THEN
      ASM_SIMP_TAC std_ss [SMALLFOOT_AE_USED_VARS___P_EXPRESSION_EVAL,
			   UNION_SUBSET]
   ),


   SIMP_TAC std_ss [SMALLFOOT_P_PROPOSITION_EVAL_def,
		    SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___ALTERNATIVE_DEF,
		    smallfoot_ap_stack_true_def, IN_ABS],


   SIMP_TAC std_ss [SMALLFOOT_P_PROPOSITION_EVAL_def,
                    SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___ALTERNATIVE_DEF,
		    asl_bool_EVAL],


   SIMP_TAC std_ss [SMALLFOOT_P_PROPOSITION___IS_NEG_FREE_def],



   SIMP_TAC std_ss [SMALLFOOT_P_PROPOSITION___IS_NEG_FREE_def,
		    SMALLFOOT_PP_USED_VARS_def, UNION_SUBSET,
		    SMALLFOOT_P_PROPOSITION_EVAL_def] THEN
   REPEAT STRIP_TAC THEN
   MATCH_MP_TAC SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___asl_and THEN
   ASM_SIMP_TAC std_ss [],



   SIMP_TAC std_ss [SMALLFOOT_P_PROPOSITION___IS_NEG_FREE_def,
		    SMALLFOOT_PP_USED_VARS_def, UNION_SUBSET,
		    SMALLFOOT_P_PROPOSITION_EVAL_def] THEN
   REPEAT STRIP_TAC THEN
   MATCH_MP_TAC SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___asl_or THEN
   ASM_SIMP_TAC std_ss []
]);









val SMALLFOOT_P_PROPOSITION_EVAL___REWRITES = 
store_thm ("SMALLFOOT_P_PROPOSITION_EVAL___REWRITES",
``
	(SMALLFOOT_P_PROPOSITION_EVAL fasl_pred_true = 
        smallfoot_ap_stack_true) /\
	(SMALLFOOT_P_PROPOSITION_EVAL fasl_pred_false = 
        asl_false) /\


	(SMALLFOOT_P_PROPOSITION_EVAL (fasl_pred_and p1 p2) = 
        asl_and (SMALLFOOT_P_PROPOSITION_EVAL p1) 
                         (SMALLFOOT_P_PROPOSITION_EVAL p2)) /\
	(SMALLFOOT_P_PROPOSITION_EVAL (fasl_pred_or p1 p2) = 
        asl_or (SMALLFOOT_P_PROPOSITION_EVAL p1) 
                         (SMALLFOOT_P_PROPOSITION_EVAL p2)) /\

	(SMALLFOOT_P_PROPOSITION_EVAL (fasl_pred_prim (smallfoot_pt_less e1 e2)) =
           smallfoot_ap_less (SMALLFOOT_P_EXPRESSION_EVAL e1)  (SMALLFOOT_P_EXPRESSION_EVAL e2)) /\

	(SMALLFOOT_P_PROPOSITION_EVAL (fasl_pred_prim (smallfoot_pt_equal e1 e2)) =
           smallfoot_ap_equal (SMALLFOOT_P_EXPRESSION_EVAL e1)  (SMALLFOOT_P_EXPRESSION_EVAL e2)) /\


	(SMALLFOOT_P_PROPOSITION_EVAL (fasl_pred_neg (fasl_pred_neg p)) =
         SMALLFOOT_P_PROPOSITION_EVAL p) /\

	(SMALLFOOT_P_PROPOSITION_EVAL (smallfoot_p_less e1 e2) =
           smallfoot_ap_less (SMALLFOOT_P_EXPRESSION_EVAL e1)  (SMALLFOOT_P_EXPRESSION_EVAL e2)) /\


	(SMALLFOOT_P_PROPOSITION_EVAL (smallfoot_p_lesseq e1 e2) =
           smallfoot_ap_lesseq (SMALLFOOT_P_EXPRESSION_EVAL e1)  (SMALLFOOT_P_EXPRESSION_EVAL e2)) /\

	(SMALLFOOT_P_PROPOSITION_EVAL (smallfoot_p_greater e1 e2) =
           smallfoot_ap_greater (SMALLFOOT_P_EXPRESSION_EVAL e1)  (SMALLFOOT_P_EXPRESSION_EVAL e2)) /\

	(SMALLFOOT_P_PROPOSITION_EVAL (smallfoot_p_greatereq e1 e2) =
           smallfoot_ap_greatereq (SMALLFOOT_P_EXPRESSION_EVAL e1)  (SMALLFOOT_P_EXPRESSION_EVAL e2)) /\

	(SMALLFOOT_P_PROPOSITION_EVAL (smallfoot_p_equal e1 e2) =
           smallfoot_ap_equal (SMALLFOOT_P_EXPRESSION_EVAL e1)  (SMALLFOOT_P_EXPRESSION_EVAL e2)) /\

	(SMALLFOOT_P_PROPOSITION_EVAL (smallfoot_p_unequal e1 e2) =
           smallfoot_ap_unequal (SMALLFOOT_P_EXPRESSION_EVAL e1)  (SMALLFOOT_P_EXPRESSION_EVAL e2)) /\


	(SMALLFOOT_P_PROPOSITION_EVAL (fasl_pred_neg fasl_pred_true) = 
        asl_false) /\
	(SMALLFOOT_P_PROPOSITION_EVAL (fasl_pred_neg fasl_pred_false) = 
        smallfoot_ap_stack_true) /\


	(SMALLFOOT_P_PROPOSITION_EVAL (fasl_pred_neg (fasl_pred_and p1 p2)) = 
        asl_or (SMALLFOOT_P_PROPOSITION_EVAL (fasl_pred_neg p1)) 
                         (SMALLFOOT_P_PROPOSITION_EVAL (fasl_pred_neg p2))) /\

	(SMALLFOOT_P_PROPOSITION_EVAL (fasl_pred_neg (fasl_pred_or p1 p2)) = 
        asl_and (SMALLFOOT_P_PROPOSITION_EVAL (fasl_pred_neg p1)) 
                         (SMALLFOOT_P_PROPOSITION_EVAL (fasl_pred_neg p2))) /\

	(SMALLFOOT_P_PROPOSITION_EVAL (fasl_pred_neg (fasl_pred_prim (smallfoot_pt_less e1 e2))) =
           smallfoot_ap_lesseq (SMALLFOOT_P_EXPRESSION_EVAL e2)  (SMALLFOOT_P_EXPRESSION_EVAL e1)) /\

	(SMALLFOOT_P_PROPOSITION_EVAL (fasl_pred_neg (fasl_pred_prim (smallfoot_pt_equal e1 e2))) =
           smallfoot_ap_unequal (SMALLFOOT_P_EXPRESSION_EVAL e1)  (SMALLFOOT_P_EXPRESSION_EVAL e2)) /\


	(SMALLFOOT_P_PROPOSITION_EVAL (fasl_pred_neg (smallfoot_p_less e1 e2)) =
           smallfoot_ap_greatereq (SMALLFOOT_P_EXPRESSION_EVAL e1)  (SMALLFOOT_P_EXPRESSION_EVAL e2)) /\


	(SMALLFOOT_P_PROPOSITION_EVAL (fasl_pred_neg (smallfoot_p_lesseq e1 e2)) =
           smallfoot_ap_greater (SMALLFOOT_P_EXPRESSION_EVAL e1)  (SMALLFOOT_P_EXPRESSION_EVAL e2)) /\

	(SMALLFOOT_P_PROPOSITION_EVAL (fasl_pred_neg (smallfoot_p_greater e1 e2)) =
           smallfoot_ap_lesseq (SMALLFOOT_P_EXPRESSION_EVAL e1)  (SMALLFOOT_P_EXPRESSION_EVAL e2)) /\

	(SMALLFOOT_P_PROPOSITION_EVAL (fasl_pred_neg (smallfoot_p_greatereq e1 e2)) =
           smallfoot_ap_less (SMALLFOOT_P_EXPRESSION_EVAL e1)  (SMALLFOOT_P_EXPRESSION_EVAL e2)) /\

	(SMALLFOOT_P_PROPOSITION_EVAL (fasl_pred_neg (smallfoot_p_equal e1 e2)) =
           smallfoot_ap_unequal (SMALLFOOT_P_EXPRESSION_EVAL e1)  (SMALLFOOT_P_EXPRESSION_EVAL e2)) /\

	(SMALLFOOT_P_PROPOSITION_EVAL (fasl_pred_neg (smallfoot_p_unequal e1 e2)) =
           smallfoot_ap_equal (SMALLFOOT_P_EXPRESSION_EVAL e1)  (SMALLFOOT_P_EXPRESSION_EVAL e2)) /\


        (smallfoot_p_true = fasl_pred_true) /\
        (smallfoot_p_false = fasl_pred_false) /\
        (smallfoot_p_and = fasl_pred_and) /\
        (smallfoot_p_or = fasl_pred_or) /\
        (smallfoot_p_neg = fasl_pred_neg)
``, 


SIMP_TAC std_ss [SMALLFOOT_P_PROPOSITION_EVAL_def,
		 smallfoot_p_true_def, smallfoot_p_false_def,
		 smallfoot_p_and_def, smallfoot_p_or_def,
		 smallfoot_p_neg_def,

		 smallfoot_p_less_def,
		 smallfoot_p_lesseq_def,
		 smallfoot_p_greater_def,
		 smallfoot_p_greatereq_def,
		 smallfoot_p_equal_def,
		 smallfoot_p_unequal_def,
                 
		 smallfoot_ap_less_def,
		 smallfoot_ap_lesseq_def,
		 smallfoot_ap_greater_def,
		 smallfoot_ap_greatereq_def,
		 smallfoot_ap_equal_def,
		 smallfoot_ap_unequal_def] THEN
REWRITE_TAC[EXTENSION] THEN
SIMP_TAC std_ss 
                [asl_bool_EVAL, IN_DEF,
		 smallfoot_ap_binexpression_def,
		 smallfoot_a_stack_proposition_def,
		 LET_THM, GSYM FORALL_AND_THM] THEN
GEN_TAC THEN
Cases_on `SND x = FEMPTY` THEN ASM_REWRITE_TAC[] THEN
Cases_on `IS_SOME (SMALLFOOT_P_EXPRESSION_EVAL e1 (FST x))` THEN ASM_REWRITE_TAC[] THEN
Cases_on `IS_SOME (SMALLFOOT_P_EXPRESSION_EVAL e2 (FST x))` THEN ASM_REWRITE_TAC[] THEN
Q.ABBREV_TAC `n1 = THE (SMALLFOOT_P_EXPRESSION_EVAL e1 (FST x))` THEN
Q.ABBREV_TAC `n2 = THE (SMALLFOOT_P_EXPRESSION_EVAL e2 (FST x))` THEN
DECIDE_TAC);








val smallfoot_prop_internal___COND_def = Define `
	smallfoot_prop_internal___COND (wpb, rpb) d sfb =


        (BAG_ALL_DISTINCT wpb) /\ (BAG_ALL_DISTINCT rpb) /\
        (!v. BAG_IN v rpb ==> ~(BAG_IN v wpb)) /\
        d /\ FINITE_BAG sfb /\
	(!sf. BAG_IN sf sfb ==> 
	      SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS (SET_OF_BAG (BAG_UNION wpb rpb)) sf
        )`;


val smallfoot_prop_internal___PROP_def = Define `
	smallfoot_prop_internal___PROP (wpb, rpb) (wp, rp) pL sfb P =

        \s:smallfoot_state.
	(!v. BAG_IN v wpb ==> var_res_sl___has_write_permission v (FST s)) /\
	(!v. BAG_IN v rpb ==> var_res_sl___has_read_permission v (FST s)) /\
        (EVERY (\p. s IN XEVAL_fasl_predicate smallfoot_env p) pL) /\

	(!v. v IN wp ==> var_res_sl___has_write_permission v (FST s)) /\
	(!v. v IN rp ==> var_res_sl___has_read_permission v (FST s)) /\
	(s IN smallfoot_ap_bigstar (BAG_INSERT smallfoot_ap_stack_true (BAG_INSERT P sfb)))`;


val smallfoot_prop_internal_def = Define `
	smallfoot_prop_internal (wpb, rpb) (wp, rp) d pL sfb P =


	(smallfoot_prop_internal___COND (wpb, rpb) d sfb,

         if smallfoot_prop_internal___COND (wpb, rpb) d sfb then
            smallfoot_prop_internal___PROP (wpb, rpb) (wp, rp) pL sfb P 
         else 
	    asl_false
        )`;



val smallfoot_prop_input_ap_def = Define `smallfoot_prop_input_ap (wp,rp) P =
				          smallfoot_prop_internal___PROP (EMPTY_BAG, EMPTY_BAG) (wp,rp) [] EMPTY_BAG P`;


val smallfoot_prop_input_ap_distinct_def = Define `
    smallfoot_prop_input_ap_distinct (wp, rp) d P =
    asl_and (K (ALL_DISTINCT (d:smallfoot_var list))) (smallfoot_prop_input_ap (wp,rp) P)`;


val smallfoot_prop_internal_ap_def = Define `
    smallfoot_prop_internal_ap (wp, rp) (d:smallfoot_var list) pL P =
    asl_and (K (ALL_DISTINCT d)) (smallfoot_prop_internal___PROP (EMPTY_BAG, EMPTY_BAG) (wp,rp) pL EMPTY_BAG P)`


val smallfoot_prop_input_ap_distinct___internal_REWRITE = store_thm (
"smallfoot_prop_input_ap_distinct___internal_REWRITE",
``smallfoot_prop_input_ap_distinct (wp, rp) d P =
smallfoot_prop_internal_ap (wp,rp) d [] P``,

SIMP_TAC std_ss [smallfoot_prop_internal_ap_def,
		 smallfoot_prop_input_ap_distinct_def,
		 smallfoot_prop_input_ap_def,
		 ALL_DISTINCT]);







val smallfoot_prop_def = Define `
	smallfoot_prop (wpb, rpb) sfb =
	smallfoot_prop_internal (wpb, rpb) (EMPTY, EMPTY) T [] sfb smallfoot_ap_emp`;



val smallfoot_prop___PROP_def = Define `
	smallfoot_prop___PROP (wpb, rpb) sfb =
	smallfoot_prop_internal___PROP (wpb, rpb) (EMPTY, EMPTY) [] sfb smallfoot_ap_emp`;

val smallfoot_prop___PROP___REWRITE = save_thm ("smallfoot_prop___PROP___REWRITE",
SIMP_RULE list_ss [smallfoot_prop_internal___PROP_def, NOT_IN_EMPTY,
		   smallfoot_ap_bigstar_REWRITE, smallfoot_ap_star___PROPERTIES] smallfoot_prop___PROP_def);



val smallfoot_prop___COND_def = Define `
	smallfoot_prop___COND (wpb, rpb) sfb =
	smallfoot_prop_internal___COND (wpb, rpb) T sfb`;

val smallfoot_prop___COND___REWRITE = save_thm ("smallfoot_prop___COND___REWRITE",
SIMP_RULE list_ss [smallfoot_prop_internal___COND_def] smallfoot_prop___COND_def);



val smallfoot_prop___REWRITE = save_thm ("smallfoot_prop___REWRITE",
SIMP_RULE list_ss [smallfoot_prop_internal_def,
		   GSYM smallfoot_prop___COND_def,
   		   GSYM smallfoot_prop___PROP_def] 
smallfoot_prop_def);



val smallfoot_prop_input_ap___REWRITE = save_thm ("smallfoot_prop_input_ap___REWRITE",
SIMP_RULE list_ss [smallfoot_prop_internal_def,
		   smallfoot_prop_internal___PROP_def,
		   bagTheory.NOT_IN_EMPTY_BAG,
		   smallfoot_ap_bigstar_REWRITE,
		   smallfoot_ap_star___PROPERTIES]
smallfoot_prop_input_ap_def);




val smallfoot_prop___WEAK_COND_def = Define `
    smallfoot_prop___WEAK_COND wpb rpb =

    (BAG_ALL_DISTINCT wpb /\ BAG_ALL_DISTINCT rpb /\
     (!v. BAG_IN v rpb ==> ~BAG_IN v wpb))`;



val smallfoot_prop___WEAK_COND_IMP = 
store_thm ("smallfoot_prop___WEAK_COND_IMP",
``
!wpb rpb sfb.
smallfoot_prop___COND (wpb,rpb) sfb ==>
smallfoot_prop___WEAK_COND wpb rpb``,

SIMP_TAC std_ss [smallfoot_prop___COND___REWRITE,
		 smallfoot_prop___WEAK_COND_def]);




val smallfoot_prop_internal___COND___EXPAND = store_thm (
"smallfoot_prop_internal___COND___EXPAND",

``!wpb rpb sfb d.
         smallfoot_prop_internal___COND (wpb,rpb) d sfb =
             (BAG_ALL_DISTINCT wpb /\ BAG_ALL_DISTINCT rpb /\
             d /\ FINITE_BAG sfb /\
             (!v. BAG_IN v rpb ==> ~BAG_IN v wpb) /\
             (!sf.
                BAG_IN sf sfb ==>
                  SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS (SET_OF_BAG (BAG_UNION wpb rpb)) sf) /\
            (~(sfb = EMPTY_BAG) ==> 
	       (SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS 
                (SET_OF_BAG (BAG_UNION wpb rpb)) (smallfoot_ap_bigstar sfb))) /\
            (SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS (SET_OF_BAG (BAG_UNION wpb rpb))
                (smallfoot_ap_star smallfoot_ap_stack_true
              (smallfoot_ap_bigstar sfb))))``,

SIMP_TAC std_ss [smallfoot_prop_internal___COND_def] THEN
REPEAT GEN_TAC THEN EQ_TAC THEN SIMP_TAC std_ss [] THEN STRIP_TAC THEN
REPEAT STRIP_TAC THENL [
   MATCH_MP_TAC SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___bigstar THEN
   ASM_SIMP_TAC std_ss [],
   

   SIMP_TAC std_ss [GSYM smallfoot_ap_bigstar_REWRITE] THEN
   MATCH_MP_TAC SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___bigstar THEN
   ASM_SIMP_TAC std_ss [bagTheory.BAG_IN_BAG_INSERT, DISJ_IMP_THM,
		    FORALL_AND_THM, bagTheory.BAG_INSERT_NOT_EMPTY] THEN
   SIMP_TAC std_ss [SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___ALTERNATIVE_DEF, 
                    smallfoot_ap_stack_true_def,
		    IN_ABS]
]);


val smallfoot_prop___COND___EXPAND = save_thm ("smallfoot_prop___COND___EXPAND",
SIMP_RULE list_ss [smallfoot_prop_internal___COND___EXPAND] smallfoot_prop___COND_def);


val smallfoot_prop_internal___EQ = store_thm ("smallfoot_prop_internal___EQ",
``(smallfoot_prop_internal (wpb, rpb) (wp,rp) d pL sfb P =
   smallfoot_prop_internal (wpb', rpb') (wp',rp') d' pL' sfb' P') =

  ((smallfoot_prop_internal___COND (wpb, rpb) d sfb =
    smallfoot_prop_internal___COND (wpb', rpb') d' sfb') /\
   ((smallfoot_prop_internal___COND (wpb, rpb) d sfb) ==>
    (smallfoot_prop_internal___PROP (wpb, rpb) (wp,rp) pL sfb P =
     smallfoot_prop_internal___PROP (wpb', rpb') (wp',rp') pL' sfb' P')))``,

SIMP_TAC std_ss [smallfoot_prop_internal_def] THEN
METIS_TAC[]);



val smallfoot_prop___EQ = store_thm ("smallfoot_prop___EQ",
``(smallfoot_prop (wpb, rpb) sfb =
   smallfoot_prop (wpb', rpb') sfb') =

  ((smallfoot_prop___COND (wpb, rpb) sfb =
    smallfoot_prop___COND (wpb', rpb') sfb') /\
   ((smallfoot_prop___COND (wpb, rpb) sfb) ==>
    (smallfoot_prop___PROP (wpb, rpb) sfb =
     smallfoot_prop___PROP (wpb', rpb') sfb')))``,


SIMP_TAC std_ss [smallfoot_prop_def,
		 smallfoot_prop_internal___EQ,
		 smallfoot_prop___COND_def,
                 smallfoot_prop___PROP_def]);



val smallfoot_prop_internal___PROP___INSERT_PROP = 
store_thm ("smallfoot_prop_internal___PROP___INSERT_PROP",
``
(smallfoot_prop_internal___PROP (wpb,rpb) (wp,rb) (c::pL) sfb P =
 asl_and (smallfoot_prop_internal___PROP (wpb,rpb) (wp,rb) pL sfb P)
         (XEVAL_fasl_predicate smallfoot_env c))``,

ONCE_REWRITE_TAC[FUN_EQ_THM] THEN
SIMP_TAC list_ss [smallfoot_prop_internal___PROP_def, asl_bool_EVAL,
		  IN_ABS] THEN
SIMP_TAC (std_ss++bool_eq_imp_ss) []);




val smallfoot_prop_internal___VARS_TO_BAGS = store_thm ("smallfoot_prop_internal___VARS_TO_BAGS",
``
((d ==>
(~(BAG_IN v wpb) /\ ~(BAG_IN v rpb))) ==>
(smallfoot_prop_internal (wpb, rpb) (v INSERT wp,rp) d pL EMPTY_BAG P =
smallfoot_prop_internal (BAG_INSERT v wpb, rpb) (wp,rp) d pL EMPTY_BAG P)) /\


((d ==>
 (~(BAG_IN v wpb) /\ ~(BAG_IN v rpb))) ==>
(smallfoot_prop_internal (wpb, rpb) (wp,v INSERT rp) d pL EMPTY_BAG P =
smallfoot_prop_internal (wpb, BAG_INSERT v rpb) (wp,rp) d pL EMPTY_BAG P))``,

SIMP_TAC std_ss [smallfoot_prop_internal___EQ, 
		 smallfoot_prop_internal___COND_def,
		 smallfoot_prop_internal___PROP_def,
		 FUN_EQ_THM,
		 IN_INSERT, bagTheory.BAG_IN_BAG_INSERT, DISJ_IMP_THM,
		 FORALL_AND_THM, BAG_ALL_DISTINCT_THM, IMP_CONJ_THM,
		 bagTheory.NOT_IN_EMPTY_BAG] THEN
SIMP_TAC (std_ss++bool_eq_imp_ss) []);




val smallfoot_prop_internal___VARS_TO_BAGS___END = store_thm ("smallfoot_prop_internal___VARS_TO_BAGS___END",
``
(smallfoot_prop___WEAK_COND wpb rpb ==> d) ==>
(smallfoot_prop_internal (wpb, rpb) (EMPTY, EMPTY) d pL EMPTY_BAG P =
smallfoot_prop_internal (wpb, rpb) (EMPTY, EMPTY) T pL EMPTY_BAG P)``,

SIMP_TAC std_ss [smallfoot_prop_internal___COND_def,
		 smallfoot_prop_internal___PROP_def,
		 smallfoot_prop_internal___EQ,
		 ALL_DISTINCT, bagTheory.NOT_IN_EMPTY_BAG,
		 smallfoot_prop___WEAK_COND_def] THEN
SIMP_TAC (std_ss++bool_eq_imp_ss) []);



val smallfoot_prop___WEAK_COND___REWRITE =
store_thm ("smallfoot_prop___WEAK_COND___REWRITE",

``(smallfoot_prop___WEAK_COND EMPTY_BAG rpb = BAG_ALL_DISTINCT rpb) /\
  (smallfoot_prop___WEAK_COND (BAG_INSERT v wpb) rpb =
   ~(BAG_IN v wpb) /\ ~(BAG_IN v rpb) /\
   smallfoot_prop___WEAK_COND wpb rpb)``,

SIMP_TAC std_ss [smallfoot_prop___WEAK_COND_def,
		 bagTheory.BAG_IN_BAG_INSERT,
		 bagTheory.NOT_IN_EMPTY_BAG,
		 BAG_ALL_DISTINCT_THM,
		 IMP_CONJ_THM, FORALL_AND_THM] THEN
SIMP_TAC (std_ss++bool_eq_imp_ss) []);





val smallfoot_prop_internal___PROP_TO_BAG = store_thm ("smallfoot_prop_internal___PROP_TO_BAG",
``
(SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS (SET_OF_BAG (BAG_UNION wpb rpb)) P2 ==>
(smallfoot_prop_internal (wpb, rpb) ({},{}) T pL sfb (smallfoot_ap_star P1 P2) =
smallfoot_prop_internal (wpb, rpb) ({},{}) T pL (BAG_INSERT P2 sfb) P1))``,


SIMP_TAC std_ss [smallfoot_prop_internal___EQ,
	         smallfoot_prop_internal___PROP_def,
	         smallfoot_prop_internal___COND_def, FUN_EQ_THM, NOT_IN_EMPTY,
 smallfoot_ap_star___PROPERTIES, ALL_DISTINCT,
		bagTheory.FINITE_BAG_THM] THEN
SIMP_TAC (std_ss++bool_eq_imp_ss) [bagTheory.BAG_IN_BAG_INSERT, DISJ_IMP_THM, NOT_IN_EMPTY,
                                   smallfoot_ap_bigstar_REWRITE] THEN
REPEAT STRIP_TAC THEN
METIS_TAC[smallfoot_ap_star___PROPERTIES, COMM_DEF, ASSOC_DEF]);




val smallfoot_prop_internal___PROP_TO_BAG___END = store_thm ("smallfoot_prop_internal___PROP_TO_BAG___END",
``
(SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS (SET_OF_BAG (BAG_UNION wpb rpb)) P1 ==>
(smallfoot_prop_internal (wpb, rpb) ({},{}) T pL sfb P1 =
 smallfoot_prop_internal (wpb, rpb) ({},{}) T pL (BAG_INSERT P1 sfb) smallfoot_ap_emp))``,

METIS_TAC[smallfoot_ap_star___PROPERTIES, smallfoot_prop_internal___PROP_TO_BAG]);





val smallfoot_prop_internal___PROG_PROP_TO_BAG = store_thm ("smallfoot_prop_internal___PROG_PROP_TO_BAG",
``!p pL wpb rpb sfb.
  (SMALLFOOT_PP_USED_VARS p SUBSET (SET_OF_BAG (BAG_UNION wpb rpb)))
 ==>
(smallfoot_prop_internal (wpb, rpb) ({},{}) T (p::pL) sfb smallfoot_ap_emp  =
 smallfoot_prop_internal (wpb, rpb) ({},{}) T pL 
    (BAG_INSERT (SMALLFOOT_P_PROPOSITION_EVAL p) sfb) smallfoot_ap_emp)``,



SIMP_TAC std_ss [smallfoot_prop_internal___EQ, FUN_EQ_THM, NOT_IN_EMPTY,
		 ALL_DISTINCT, EVERY_DEF,
		 smallfoot_prop_internal___PROP_def] THEN
REPEAT STRIP_TAC THEN (
   ASM_SIMP_TAC (std_ss++bool_eq_imp_ss) [bagTheory.BAG_IN_BAG_INSERT, DISJ_IMP_THM, NOT_IN_EMPTY,
                                      smallfoot_ap_bigstar_REWRITE,
				      smallfoot_prop_internal___COND_def,
	             		      FORALL_AND_THM, bagTheory.FINITE_BAG_THM,
				      SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___SMALLFOOT_P_PROPOSITION_EVAL]
) THEN
Q.ABBREV_TAC `vs =  (SET_OF_BAG (BAG_UNION wpb rpb))` THEN
FULL_SIMP_TAC (std_ss++bool_eq_imp_ss)
                     [smallfoot_ap_star___PROPERTIES,
		      smallfoot_ap_bigstar_REWRITE,
		      smallfoot_prop_internal___COND___EXPAND,
		      ALL_DISTINCT] THEN
STRIP_TAC THEN
ONCE_REWRITE_TAC [smallfoot_ap_star___swap] THEN
Q.ABBREV_TAC `P = smallfoot_ap_star smallfoot_ap_stack_true (smallfoot_ap_bigstar sfb)` THEN

`SMALLFOOT_PP_USED_VARS p SUBSET FDOM (FST x)` by ALL_TAC THEN1 (
   UNABBREV_ALL_TAC THEN
   FULL_SIMP_TAC std_ss [var_res_sl___has_read_permission_def,
			 var_res_sl___has_write_permission_def,
			 SUBSET_DEF, bagTheory.IN_SET_OF_BAG,
			 bagTheory.BAG_IN_BAG_UNION] THEN
   METIS_TAC[]
) THEN

ASM_SIMP_TAC std_ss [smallfoot_ap_star_def,
		 asl_star_def, IN_ABS,
		 IN_DEF,
		 XEVAL_fasl_predicate___smallfoot_env___ALTERNATIVE_DEF] THEN
EQ_TAC THEN STRIP_TAC THENL [
   Cases_on `x` THEN
   Q.EXISTS_TAC `(VAR_RES_STACK_SPLIT1 {} q, FEMPTY)` THEN
   Q.EXISTS_TAC `(VAR_RES_STACK_SPLIT2 {} q, r)` THEN
   REPEAT STRIP_TAC THENL [
      SIMP_TAC std_ss [SOME___smallfoot_separation_combinator,
		       FDOM_FEMPTY, DISJOINT_EMPTY,
		       VAR_RES_STACK_COMBINE___VAR_RES_STACK_SPLIT12,
		       FUNION_FEMPTY_1],


      `SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS vs
             (SMALLFOOT_P_PROPOSITION_EVAL p)` by 
         PROVE_TAC[SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___SMALLFOOT_P_PROPOSITION_EVAL] THEN
      FULL_SIMP_TAC std_ss [SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS_def,
			       SMALLFOOT_AP_PERMISSION_UNIMPORTANT_def, IN_DEF] THEN
      PROVE_TAC[VAR_RES_STACK___IS_EQUAL_UPTO_PERMISSIONS___VAR_RES_STACK_SPLIT],


      FULL_SIMP_TAC std_ss [SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS_def, 
			    SMALLFOOT_AP_PERMISSION_UNIMPORTANT_def, IN_DEF] THEN
      PROVE_TAC[VAR_RES_STACK___IS_EQUAL_UPTO_PERMISSIONS___VAR_RES_STACK_SPLIT]
   ],



   Cases_on `x` THEN
   Cases_on `p'` THEN
   Cases_on `q` THEN
   FULL_SIMP_TAC std_ss [] THEN
   `r' = FEMPTY` by ALL_TAC THEN1 (
       IMP_RES_TAC SMALLFOOT_P_PROPOSITION_EVAL___HEAP_EMPTY THEN
       FULL_SIMP_TAC std_ss []
   ) THEN
   FULL_SIMP_TAC std_ss [SOME___smallfoot_separation_combinator,
			 FUNION_FEMPTY_1, DISJOINT_EMPTY, FDOM_FEMPTY] THEN
   CONJ_TAC THENL [
      `SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS vs
             (SMALLFOOT_P_PROPOSITION_EVAL p)` by 
         PROVE_TAC[SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___SMALLFOOT_P_PROPOSITION_EVAL] THEN
      FULL_SIMP_TAC std_ss [SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS_def, 
			    SMALLFOOT_AP_PERMISSION_UNIMPORTANT_def, IN_DEF] THEN
      `VAR_RES_STACK_IS_SUBSTATE q'' q'` by METIS_TAC[VAR_RES_STACK_IS_SUBSTATE_INTRO] THEN
      PROVE_TAC[],


      FULL_SIMP_TAC std_ss [SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS_def, 
			    SMALLFOOT_AP_PERMISSION_UNIMPORTANT_def, IN_DEF] THEN
      `VAR_RES_STACK_IS_SUBSTATE q''' q'` by METIS_TAC[VAR_RES_STACK_IS_SUBSTATE_INTRO] THEN
      PROVE_TAC[]
   ]
]);



val COND_PROP___STRONG_EXISTS_def = Define 
`COND_PROP___STRONG_EXISTS P =
 ((!x. FST (P x)), asl_exists x. (SND (P x)))`;



val smallfoot_prop_internal___EXISTS = store_thm ("smallfoot_prop_internal___EXISTS",
``
(smallfoot_prop_internal (EMPTY_BAG, EMPTY_BAG) (wb, rp) d pL EMPTY_BAG 
(asl_exists x. P x)) =
COND_PROP___STRONG_EXISTS (\x. 
smallfoot_prop_internal (EMPTY_BAG, EMPTY_BAG) (wb, rp) d pL EMPTY_BAG (P x))

``,


SIMP_TAC std_ss [smallfoot_prop_internal___COND_def,
		 smallfoot_prop_internal___PROP_def,
		 smallfoot_prop_internal_def,
		 bagTheory.NOT_IN_EMPTY_BAG,
                 BAG_ALL_DISTINCT_THM,
		 bagTheory.FINITE_BAG_THM,
		 smallfoot_ap_bigstar_REWRITE,
		 GSYM asl_exists___smallfoot_ap_star_THM,
		 asl_bool_EVAL,
		 COND_PROP___STRONG_EXISTS_def] THEN
ONCE_REWRITE_TAC[EXTENSION] THEN
Tactical.REVERSE (Cases_on `d`) THEN (
   SIMP_TAC std_ss [asl_bool_EVAL, asl_exists_def, IN_ABS,
		    RIGHT_EXISTS_AND_THM]
));


val COND_PROP___STRONG_EXISTS___SWAP = store_thm (
"COND_PROP___STRONG_EXISTS___SWAP",
``!X.
COND_PROP___STRONG_EXISTS (\x1. COND_PROP___STRONG_EXISTS (\x2. X x1 x2)) =
COND_PROP___STRONG_EXISTS (\x2. COND_PROP___STRONG_EXISTS (\x1. X x1 x2))``,

SIMP_TAC std_ss [COND_PROP___STRONG_EXISTS_def,
		 asl_exists_def, IN_ABS] THEN
METIS_TAC[]);


val SMALLFOOT_COND_HOARE_TRIPLE___STRONG_COND_EXISTS___PRE_IMPL =
store_thm ("SMALLFOOT_COND_HOARE_TRIPLE___STRONG_COND_EXISTS___PRE_IMPL",
``
!P prog Q.

(!x. SMALLFOOT_COND_HOARE_TRIPLE (P x) prog Q) ==>
(SMALLFOOT_COND_HOARE_TRIPLE (COND_PROP___STRONG_EXISTS P) prog Q)
``,

SIMP_TAC std_ss [COND_PROP___STRONG_EXISTS_def,
		 SMALLFOOT_COND_HOARE_TRIPLE_REWRITE,
		 GSYM LEFT_EXISTS_AND_THM,
		 GSYM LEFT_FORALL_IMP_THM,
		 SMALLFOOT_HOARE_TRIPLE_def,
		 FASL_PROGRAM_HOARE_TRIPLE_def,
		 HOARE_TRIPLE_def, IN_ABS, asl_exists_def] THEN
METIS_TAC[]);



val SMALLFOOT_COND_HOARE_TRIPLE___STRONG_COND_EXISTS___POST_IMPL =
store_thm ("SMALLFOOT_COND_HOARE_TRIPLE___STRONG_COND_EXISTS___POST_IMPL",
``
!P prog Q.

(?x. SMALLFOOT_COND_HOARE_TRIPLE P prog (Q x)) ==>
(SMALLFOOT_COND_HOARE_TRIPLE P prog (COND_PROP___STRONG_EXISTS Q))
``,

SIMP_TAC std_ss [COND_PROP___STRONG_EXISTS_def,
		 SMALLFOOT_COND_HOARE_TRIPLE_REWRITE,
		 GSYM LEFT_EXISTS_AND_THM,
		 GSYM LEFT_FORALL_IMP_THM,
		 SMALLFOOT_HOARE_TRIPLE_def,
		 FASL_PROGRAM_HOARE_TRIPLE_def,
		 HOARE_TRIPLE_def, IN_ABS, asl_exists_def] THEN
SIMP_TAC std_ss [fasl_order_THM] THEN
REPEAT STRIP_TAC THEN
FULL_SIMP_TAC std_ss [] THEN
Q.PAT_ASSUM `!x'. x' IN SND P ==> X x'` (MP_TAC o Q.SPEC `x'`) THEN
ASM_SIMP_TAC std_ss [GSYM LEFT_FORALL_IMP_THM, SUBSET_DEF, IN_ABS] THEN
METIS_TAC[]);









val smallfoot_ae_is_defined___IMPL = store_thm ("smallfoot_ae_is_defined___IMPL",
``!e wpb rpb sfb vs.
((SMALLFOOT_AE_USED_VARS e = SOME vs) /\ (vs SUBSET (SET_OF_BAG (BAG_UNION wpb rpb)))) ==>
(smallfoot_ae_is_defined (smallfoot_prop___PROP (wpb, rpb) sfb) e)``,

REPEAT GEN_TAC THEN
SIMP_TAC std_ss [SMALLFOOT_AE_USED_VARS_THM, SMALLFOOT_AE_USED_VARS_REL___REWRITE,
		 smallfoot_ae_is_defined_def] THEN
REPEAT STRIP_TAC THEN
FULL_SIMP_TAC std_ss [SUBSET_DEF, bagTheory.IN_SET_OF_BAG, bagTheory.BAG_IN_BAG_INSERT,
		      bagTheory.BAG_IN_BAG_UNION, smallfoot_prop___PROP___REWRITE,
		      var_res_sl___has_read_permission_def,
		      var_res_sl___has_write_permission_def] THEN
REPEAT STRIP_TAC THEN
RES_TAC THEN RES_TAC THEN ASM_REWRITE_TAC[]);





val smallfoot_prop___COND_VAR_INSERT = store_thm ("smallfoot_prop___COND_VAR_INSERT",

``!wpb rpb sfb.
  (smallfoot_prop___COND (wpb, rpb) sfb /\
   (~(v IN (SET_OF_BAG (BAG_UNION wpb rpb))))) ==>

  (smallfoot_prop___COND (BAG_INSERT v wpb, rpb) sfb)``,

SIMP_TAC std_ss [smallfoot_prop___COND___REWRITE, BAG_ALL_DISTINCT_THM,
		 bagTheory.BAG_IN_BAG_UNION, bagTheory.IN_SET_OF_BAG,
		 bagTheory.BAG_IN_BAG_INSERT] THEN
REPEAT STRIP_TAC THEN
RES_TAC THEN
MATCH_MP_TAC SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___SUBSET THEN
Q.EXISTS_TAC `SET_OF_BAG (BAG_UNION wpb rpb)` THEN
ASM_SIMP_TAC std_ss [SUBSET_DEF, bagTheory.BAG_IN_BAG_INSERT,
		     bagTheory.IN_SET_OF_BAG, bagTheory.BAG_IN_BAG_UNION,
		     DISJ_IMP_THM]);




val smallfoot_prop___COND_INSERT = store_thm ("smallfoot_prop___COND_INSERT",

``!wpb rpb sfb.
  (smallfoot_prop___COND (wpb, rpb) (BAG_INSERT sf sfb) =
  ((smallfoot_prop___COND (wpb, rpb) sfb) /\
   SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS
              (SET_OF_BAG (BAG_UNION wpb rpb)) sf))``,

SIMP_TAC std_ss [smallfoot_prop___COND___REWRITE,
		 bagTheory.BAG_IN_BAG_INSERT, DISJ_IMP_THM,
		 FORALL_AND_THM, bagTheory.FINITE_BAG_THM] THEN
SIMP_TAC (std_ss++bool_eq_imp_ss) []);



val smallfoot_prop___COND_UNION = store_thm ("smallfoot_prop___COND_UNION",

``!wpb rpb sfb1 sbf2.
  (smallfoot_prop___COND (wpb, rpb) (BAG_UNION sfb1 sfb2) =
  (smallfoot_prop___COND (wpb, rpb) sfb1 /\
   smallfoot_prop___COND (wpb, rpb) sfb2))``,

SIMP_TAC std_ss [smallfoot_prop___COND___REWRITE,
		 FORALL_AND_THM, bagTheory.FINITE_BAG_UNION,
		 bagTheory.BAG_IN_BAG_UNION,
		 DISJ_IMP_THM] THEN
SIMP_TAC (std_ss++bool_eq_imp_ss) []);




val smallfoot_slp_init_var___small_prop_THM = store_thm ("smallfoot_slp_init_var___small_prop_THM",
``!wpb rpb sfb vs v e.
  (SMALLFOOT_AE_USED_VARS e = SOME vs) /\ (vs SUBSET (SET_OF_BAG (BAG_UNION wpb rpb))) /\
   (smallfoot_prop___COND (wpb,rpb) sfb) /\ (~(v IN (SET_OF_BAG (BAG_UNION wpb rpb)))) ==>

   ((smallfoot_prop___COND (BAG_INSERT v wpb, rpb) 
                    (BAG_INSERT (smallfoot_ap_equal (smallfoot_ae_var v) e) sfb)) /\

  ((smallfoot_slp_init_var v e (smallfoot_prop___PROP (wpb, rpb) sfb)) =
   (smallfoot_prop___PROP (BAG_INSERT v wpb, rpb) 
                      (BAG_INSERT (smallfoot_ap_equal (smallfoot_ae_var v) e) sfb))))``,


REPEAT GEN_TAC THEN 
STRIP_TAC THEN
CONJ_TAC THEN1 (
   IMP_RES_TAC smallfoot_prop___COND_VAR_INSERT THEN
   FULL_SIMP_TAC std_ss [smallfoot_prop___COND___REWRITE, bagTheory.BAG_IN_BAG_INSERT,
			 DISJ_IMP_THM, FORALL_AND_THM, smallfoot_ap_equal_def,
			 bagTheory.FINITE_BAG_THM] THEN
   MATCH_MP_TAC SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___binexpression THEN
   FULL_SIMP_TAC std_ss [SMALLFOOT_AE_USED_VARS___smallfoot_ae_var,
                        SUBSET_DEF, IN_SING, bagTheory.BAG_IN_BAG_INSERT,
                        bagTheory.BAG_IN_BAG_UNION, bagTheory.IN_SET_OF_BAG,
			IN_SING, IN_UNION, DISJ_IMP_THM] THEN
   PROVE_TAC[]
) THEN

FULL_SIMP_TAC std_ss [bagTheory.BAG_IN_BAG_UNION, bagTheory.IN_SET_OF_BAG, SUBSET_DEF] THEN
`!v'. BAG_IN v' wpb ==> ~(v' = v)` by PROVE_TAC[] THEN
`!v'. BAG_IN v' rpb ==> ~(v' = v)` by PROVE_TAC[] THEN
ASM_SIMP_TAC std_ss [smallfoot_slp_init_var_def, FUN_EQ_THM, PAIR_FORALL_THM, LET_THM,
		     smallfoot_prop___PROP___REWRITE, smallfoot_prop___COND___REWRITE,
		     var_res_sl___has_write_permission_def,
		     var_res_sl___has_read_permission_def,
		     var_res_sl___read_def, FDOM_DOMSUB, IN_DELETE,
		     bagTheory.BAG_IN_BAG_INSERT, DISJ_IMP_THM, FORALL_AND_THM,
		     COND_NONE_SOME_REWRITES, PAIR_EQ_REWRITES,
		     DOMSUB_FAPPLY_THM, smallfoot_ap_bigstar_REWRITE] THEN
CONV_TAC (DEPTH_CONV BOOL_EQ_IMP_CONV) THEN
REPEAT STRIP_TAC THEN
ONCE_REWRITE_TAC [smallfoot_ap_star___swap] THEN
Q.ABBREV_TAC `oldP = smallfoot_ap_star smallfoot_ap_stack_true (smallfoot_ap_bigstar sfb)` THEN
SIMP_TAC (std_ss++boolSimps.CONJ_ss) [smallfoot_ap_star_def, asl_star_def, IN_ABS,
		 smallfoot_ap_equal_def, smallfoot_ap_binexpression_def,
		 smallfoot_a_stack_proposition_def, LET_THM,
		 smallfoot_ae_var_def, COND_NONE_SOME_REWRITES,
		 SOME___smallfoot_separation_combinator,
		 PAIR_EXISTS_THM, FDOM_FEMPTY, FUNION_FEMPTY_1,
		 DISJOINT_EMPTY, IS_SOME_EXISTS,
		 GSYM LEFT_EXISTS_AND_THM, GSYM RIGHT_EXISTS_AND_THM] THEN
`SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS (SET_OF_BAG (BAG_UNION wpb rpb)) oldP` by
   PROVE_TAC[smallfoot_prop___COND___EXPAND] THEN
FULL_SIMP_TAC std_ss [SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___ALTERNATIVE_DEF,
		      SUBSET_DEF, IN_INTER, bagTheory.BAG_IN_BAG_INSERT,
		      bagTheory.IN_SET_OF_BAG, bagTheory.BAG_IN_BAG_UNION] THEN
FULL_SIMP_TAC std_ss [SMALLFOOT_AE_USED_VARS_THM,
           	      SMALLFOOT_AE_USED_VARS_REL___REWRITE] THEN

EQ_TAC THEN STRIP_TAC THENL [
   Q.EXISTS_TAC `VAR_RES_STACK_SPLIT1 {v} x1` THEN
   Q.EXISTS_TAC `VAR_RES_STACK_SPLIT2 {v} x1` THEN
   SIMP_TAC std_ss [VAR_RES_STACK_COMBINE___VAR_RES_STACK_SPLIT12,
		    VAR_RES_STACK_SPLIT12___REWRITES] THEN
   REPEAT STRIP_TAC THENL [
       ASM_SIMP_TAC std_ss [],

       Tactical.REVERSE (`e (x1 \\ v) = e (VAR_RES_STACK_SPLIT1 {v} x1)` by ALL_TAC) THEN1 (
          FULL_SIMP_TAC std_ss [VAR_RES_STACK_SPLIT12___REWRITES]
       ) THEN
       Q.PAT_ASSUM `!st1 st2. X st1 st2 ==> (e st1 = e st2)` MATCH_MP_TAC THEN

       `vs SUBSET FDOM (x1 \\ v)` by METIS_TAC[IS_SOME_EXISTS] THEN
       POP_ASSUM MP_TAC THEN
       SIMP_TAC std_ss [VAR_RES_STACK_SPLIT12___REWRITES, FDOM_DOMSUB,
		        SUBSET_DEF, IN_DELETE, DOMSUB_FAPPLY_THM],




       Q.PAT_ASSUM `!st1 st2. X st1 st2` 
           (MP_TAC o Q.SPECL [`x1 \\ v`, `VAR_RES_STACK_SPLIT2 {v} x1`]) THEN
       SIMP_TAC std_ss [FDOM_DOMSUB, VAR_RES_STACK_SPLIT12___REWRITES, IN_DELETE,
		        DOMSUB_FAPPLY_THM, IN_DIFF, IN_SING] THEN
       METIS_TAC[]
   ],


   `((FDOM x1' UNION FDOM x1'') SUBSET FDOM x1) /\
    (!v. v IN FDOM x1' ==> ((FST (x1' ' v)) = (FST (x1 ' v)))) /\
    (!v. v IN FDOM x1'' ==> ((FST (x1'' ' v)) = (FST (x1 ' v))))` by ALL_TAC THEN1 (

      FULL_SIMP_TAC std_ss [SOME___VAR_RES_STACK_COMBINE,
			    FMERGE_DEF, SUBSET_REFL, COND_REWRITES,
			    VAR_RES_STACK_COMBINE___MERGE_FUNC_def,
			    VAR_RES_STACK_IS_SEPARATE_def]
   ) THEN
   CONJ_TAC THENL [
       Q.PAT_ASSUM `!st1 st2. X st1 st2` 
           (MP_TAC o Q.SPECL [`x1''`, `x1 \\ v`]) THEN
       MATCH_MP_TAC (prove (``((B ==> C) /\ A) ==> ((A ==> B) ==> C)``, METIS_TAC[])) THEN
       CONJ_TAC THEN1 METIS_TAC[] THEN
       FULL_SIMP_TAC std_ss [FDOM_DOMSUB, IN_DELETE, DOMSUB_FAPPLY_THM,
			    SUBSET_DEF, IN_UNION] THEN
       METIS_TAC[],



       Tactical.REVERSE (`e (x1 \\ v) = e x1'` by ALL_TAC) THEN1 (
          ASM_SIMP_TAC std_ss []
       ) THEN
       Q.PAT_ASSUM `!st1 st2. X st1 st2 ==> (e st1 = e st2)` MATCH_MP_TAC THEN

       `vs SUBSET FDOM x1'` by METIS_TAC[IS_SOME_EXISTS] THEN
       POP_ASSUM MP_TAC THEN
       FULL_SIMP_TAC std_ss [SUBSET_DEF, FDOM_DOMSUB, IN_DELETE, DOMSUB_FAPPLY_THM,
			     IN_UNION] THEN
       METIS_TAC[]
   ]
]);






val smallfoot_slp_new_var___small_prop_THM = store_thm ("smallfoot_slp_new_var___small_prop_THM",
``!wpb rpb v sfb.

((smallfoot_prop___COND (wpb,rpb) sfb) /\ (~(v IN (SET_OF_BAG (BAG_UNION wpb rpb))))) ==>

   ((smallfoot_prop___COND (BAG_INSERT v wpb, rpb) sfb) /\
  ((smallfoot_slp_new_var v (smallfoot_prop___PROP (wpb, rpb) sfb)) =
   (smallfoot_prop___PROP (BAG_INSERT v wpb, rpb) sfb)))``,



SIMP_TAC std_ss [smallfoot_slp_new_var_ALTERNATIVE_DEF, asl_exists_def, EXTENSION, IN_ABS] THEN
REPEAT STRIP_TAC THEN1 METIS_TAC[smallfoot_prop___COND_VAR_INSERT] THEN
MP_TAC (Q.SPECL [`wpb`, `rpb`, `sfb`, `EMPTY:smallfoot_var set`, `v`] smallfoot_slp_init_var___small_prop_THM) THEN
ASM_SIMP_TAC std_ss [EMPTY_SUBSET, SMALLFOOT_AE_USED_VARS___smallfoot_ae_const] THEN
STRIP_TAC THEN POP_ASSUM (K ALL_TAC) THEN

SIMP_TAC std_ss [smallfoot_prop___PROP___REWRITE, IN_ABS, 
		 bagTheory.BAG_IN_BAG_INSERT, DISJ_IMP_THM,
		 FORALL_AND_THM, var_res_sl___has_read_permission_def,
		 var_res_sl___has_write_permission_def,
		 LEFT_EXISTS_AND_THM, RIGHT_EXISTS_AND_THM] THEN
`?st h. x = (st, h)` by (Cases_on `x` THEN SIMP_TAC std_ss []) THEN
ASM_SIMP_TAC std_ss [smallfoot_ap_bigstar_REWRITE] THEN
CONV_TAC (DEPTH_CONV (BOOL_EQ_IMP_CONV)) THEN
REPEAT STRIP_TAC THEN
ONCE_REWRITE_TAC [smallfoot_ap_star___swap] THEN
Q.ABBREV_TAC `oldP = smallfoot_ap_star smallfoot_ap_stack_true (smallfoot_ap_bigstar sfb)` THEN
SIMP_TAC std_ss [smallfoot_ap_star_def, asl_star_def, IN_ABS,
		 smallfoot_ap_equal_def, smallfoot_ap_binexpression_def,
		 smallfoot_a_stack_proposition_def, LET_THM,
		 smallfoot_ae_var_def, COND_NONE_SOME_REWRITES,
		 SOME___smallfoot_separation_combinator,
		 PAIR_EXISTS_THM, FDOM_FEMPTY, FUNION_FEMPTY_1,
		 DISJOINT_EMPTY, IS_SOME_EXISTS,
		 GSYM LEFT_EXISTS_AND_THM, GSYM RIGHT_EXISTS_AND_THM,
		 smallfoot_ae_const_def] THEN
`SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS (SET_OF_BAG (BAG_UNION wpb rpb)) oldP` by
   PROVE_TAC[smallfoot_prop___COND___EXPAND] THEN
FULL_SIMP_TAC std_ss [SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___ALTERNATIVE_DEF,
		      SUBSET_DEF, IN_INTER, bagTheory.BAG_IN_BAG_INSERT,
		      bagTheory.IN_SET_OF_BAG, bagTheory.BAG_IN_BAG_UNION] THEN
EQ_TAC THEN STRIP_TAC THENL [
   Q.PAT_ASSUM `!st1 st2. X st1 st2` 
         (MP_TAC o Q.SPECL [`x1'`, `st`]) THEN
   MATCH_MP_TAC (prove (``((B ==> C) /\ A) ==> ((A ==> B) ==> C)``, METIS_TAC[])) THEN
   CONJ_TAC THEN1 METIS_TAC[] THEN
   FULL_SIMP_TAC std_ss [SOME___VAR_RES_STACK_COMBINE,
			 FMERGE_DEF, IN_UNION, VAR_RES_STACK_IS_SEPARATE_def,
			 VAR_RES_STACK_COMBINE___MERGE_FUNC_def] THEN
   ASM_SIMP_TAC std_ss [PAIR_EQ_REWRITES, COND_REWRITES],


   Q.EXISTS_TAC `VAR_RES_STACK_SPLIT1 {} st` THEN
   Q.EXISTS_TAC `VAR_RES_STACK_SPLIT2 {} st` THEN
   ASM_SIMP_TAC std_ss [VAR_RES_STACK_COMBINE___VAR_RES_STACK_SPLIT12,
		    VAR_RES_STACK_SPLIT12___REWRITES] THEN

   Q.PAT_ASSUM `!st1 st2. X st1 st2` 
        (MP_TAC o Q.SPECL [`st`, `VAR_RES_STACK_SPLIT2 {} st`]) THEN
   SIMP_TAC std_ss [FDOM_DOMSUB, VAR_RES_STACK_SPLIT12___REWRITES, IN_DIFF,
		    NOT_IN_EMPTY] THEN
   METIS_TAC[]
]);






 



val smallfoot_slp_new_var___PROP_COND_def =
Define `smallfoot_slp_new_var___PROP_COND v wpb rpb P =
        (FST P /\ smallfoot_prop___WEAK_COND (BAG_INSERT v wpb) rpb, 
         smallfoot_slp_new_var v (SND P))`;





val smallfoot_slp_new_var___PROP_COND___COND_PROP_STRONG_EXISTS_THM =
store_thm ("smallfoot_slp_new_var___PROP_COND___COND_PROP_STRONG_EXISTS_THM",
``
smallfoot_slp_new_var___PROP_COND v wpb rpb (COND_PROP___STRONG_EXISTS P) =
(COND_PROP___STRONG_EXISTS (\x. (smallfoot_slp_new_var___PROP_COND v wpb rpb (P x))))
``,


SIMP_TAC std_ss [smallfoot_slp_new_var___PROP_COND_def,
		 COND_PROP___STRONG_EXISTS_def,
		 FORALL_AND_THM] THEN
ONCE_REWRITE_TAC[EXTENSION] THEN
SIMP_TAC std_ss [asl_exists_def, IN_ABS,
   smallfoot_slp_new_var_def,
   smallfoot_slp_init_var_def, LET_THM, 
   GSYM RIGHT_EXISTS_AND_THM,
   GSYM LEFT_EXISTS_AND_THM] THEN
METIS_TAC[IN_DEF]);








val SMALLFOOT_COND_INFERENCE___prog_val_arg = store_thm (
   "SMALLFOOT_COND_INFERENCE___prog_val_arg",
``!wpb rpb sfb body Q.

((!v.
SMALLFOOT_COND_HOARE_TRIPLE (smallfoot_prop (BAG_INSERT v wpb,rpb) 
(BAG_INSERT (smallfoot_ap_equal (smallfoot_ae_var v) (smallfoot_ae_const c)) sfb))
(body v) (smallfoot_slp_new_var___PROP_COND v wpb rpb Q))
) ==>
(SMALLFOOT_COND_HOARE_TRIPLE (smallfoot_prop (wpb,rpb) sfb) 
(smallfoot_prog_val_arg (\x. (body x)) c) Q)``,


REPEAT GEN_TAC THEN
Cases_on `Q` THEN
SIMP_TAC std_ss [SMALLFOOT_COND_HOARE_TRIPLE_def, smallfoot_prop___REWRITE,
		 smallfoot_slp_new_var___PROP_COND_def] THEN
REPEAT STRIP_TAC THEN
MATCH_MP_TAC SMALLFOOT_INFERENCE___prog_val_arg___GENERAL THEN
GEN_TAC THEN
Cases_on `v IN SET_OF_BAG (BAG_UNION wpb rpb)` THEN1 (
    SIMP_TAC std_ss [SMALLFOOT_HOARE_TRIPLE_def,
		     FASL_PROGRAM_HOARE_TRIPLE_REWRITE] THEN
    REPEAT GEN_TAC THEN
    MATCH_MP_TAC (prove (``~A ==> ((A /\ B) ==> C)``, METIS_TAC[])) THEN
    SIMP_TAC std_ss [smallfoot_slp_init_var_def, LET_THM, IN_ABS,
		     smallfoot_prop___PROP___REWRITE, var_res_sl___has_write_permission_def,
		     var_res_sl___has_read_permission_def, FDOM_DOMSUB, IN_DELETE] THEN
    FULL_SIMP_TAC std_ss [bagTheory.IN_SET_OF_BAG, bagTheory.BAG_IN_BAG_UNION] THEN
    METIS_TAC[]
) THEN


Q.PAT_ASSUM `!v. X v` (MP_TAC o Q.SPEC `v`) THEN
MATCH_MP_TAC (prove (``(A /\ ((A /\ B) ==> C)) ==> ((A ==> B) ==> C)``, METIS_TAC[])) THEN
CONJ_TAC THEN1 (
   ASM_REWRITE_TAC[] THEN
   MATCH_MP_TAC (prove (``((A==>B) /\ A) ==> (A /\ B)``, METIS_TAC[])) THEN
   CONJ_TAC THEN1 PROVE_TAC[smallfoot_prop___WEAK_COND_IMP] THEN

   ASM_SIMP_TAC std_ss [smallfoot_prop___COND_VAR_INSERT,
		      smallfoot_prop___COND_INSERT] THEN
   SIMP_TAC std_ss [SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___ALTERNATIVE_DEF_2,
		    smallfoot_ap_equal_def, smallfoot_ap_binexpression_def,
		    smallfoot_a_stack_proposition_def, IN_ABS,
		    LET_THM, smallfoot_ae_const_def, smallfoot_ae_var_def,
		    SUBSET_DEF, IN_INTER, 
                        bagTheory.IN_SET_OF_BAG,
		        bagTheory.BAG_IN_BAG_UNION, 
		        bagTheory.BAG_IN_BAG_INSERT] THEN
  SIMP_TAC std_ss [COND_RATOR, COND_RAND] THEN
  REPEAT STRIP_TAC THEN
  METIS_TAC[]
) THEN   

REPEAT STRIP_TAC THEN
MP_TAC (Q.SPECL [`wpb`, `rpb`, `sfb`, `{}`, `v`, `smallfoot_ae_const c`]
    smallfoot_slp_init_var___small_prop_THM) THEN
ASM_SIMP_TAC std_ss [SMALLFOOT_AE_USED_VARS___smallfoot_ae_const,
		     EMPTY_SUBSET]);









val SMALLFOOT_COND_INFERENCE___prog_local_var = store_thm (
   "SMALLFOOT_COND_INFERENCE___prog_local_var",
``!wpb rpb sfb body Q.

((!v.
SMALLFOOT_COND_HOARE_TRIPLE (smallfoot_prop (BAG_INSERT v wpb,rpb) sfb)
(body v) (smallfoot_slp_new_var___PROP_COND v wpb rpb Q))) ==>
(SMALLFOOT_COND_HOARE_TRIPLE (smallfoot_prop (wpb,rpb) sfb) 
(smallfoot_prog_local_var (\x. (body x))) Q)``,


REPEAT GEN_TAC THEN
Cases_on `Q` THEN
SIMP_TAC std_ss [SMALLFOOT_COND_HOARE_TRIPLE_def, smallfoot_prop___REWRITE,
		 smallfoot_slp_new_var___PROP_COND_def] THEN
REPEAT STRIP_TAC THEN
MATCH_MP_TAC SMALLFOOT_INFERENCE___prog_local_var___GENERAL THEN
GEN_TAC THEN
Cases_on `v IN SET_OF_BAG (BAG_UNION wpb rpb)` THEN1 (
    SIMP_TAC std_ss [SMALLFOOT_HOARE_TRIPLE_def,
		     FASL_PROGRAM_HOARE_TRIPLE_REWRITE] THEN
    REPEAT GEN_TAC THEN
    MATCH_MP_TAC (prove (``~A ==> ((A /\ B) ==> C)``, METIS_TAC[])) THEN
    SIMP_TAC std_ss [smallfoot_slp_new_var_def, asl_exists_def,
		     smallfoot_slp_init_var_def, LET_THM, IN_ABS,
		     smallfoot_prop___PROP___REWRITE, var_res_sl___has_write_permission_def,
		     var_res_sl___has_read_permission_def, FDOM_DOMSUB, IN_DELETE] THEN
    FULL_SIMP_TAC std_ss [bagTheory.IN_SET_OF_BAG, bagTheory.BAG_IN_BAG_UNION] THEN
    METIS_TAC[]
) THEN

Q.PAT_ASSUM `!v. X v` (MP_TAC o Q.SPEC `v`) THEN
MATCH_MP_TAC (prove (``(A /\ ((A /\ B) ==> C)) ==> ((A ==> B) ==> C)``, METIS_TAC[])) THEN
CONJ_TAC THEN1 (
   ASM_REWRITE_TAC[] THEN
   MATCH_MP_TAC (prove (``((A==>B) /\ A) ==> (A /\ B)``, METIS_TAC[])) THEN
   CONJ_TAC THEN1 PROVE_TAC[smallfoot_prop___WEAK_COND_IMP] THEN
   PROVE_TAC[smallfoot_prop___COND_VAR_INSERT]
) THEN   

REPEAT STRIP_TAC THEN
MP_TAC (Q.SPECL [`wpb`, `rpb`, `v`, `sfb`]  smallfoot_slp_new_var___small_prop_THM) THEN
ASM_SIMP_TAC std_ss []);








val smallfoot_prog_block_def = Define `smallfoot_prog_block (L:smallfoot_prog list) =
							   fasl_prog_block L`
val smallfoot_prog_cond_def = Define `smallfoot_prog_cond c (pT:smallfoot_prog) pF = fasl_prog_cond c pT pF`;
val smallfoot_prog_while_def = Define `smallfoot_prog_while c (prog:smallfoot_prog) = fasl_prog_while c prog`;
val smallfoot_prog_while_with_invariant_def = Define `smallfoot_prog_while_with_invariant 
   (i:(smallfoot_data_type # string) list # (smallfoot_data list -> smallfoot_a_proposition)) c prog = smallfoot_prog_while c prog`;
val smallfoot_prog_parallel_def = Define `smallfoot_prog_parallel (p1:smallfoot_prog) p2 = fasl_prog_parallel p1 p2`;




val smallfoot_input_preserve_names_wrapper_def = Define `
	smallfoot_input_preserve_names_wrapper (ref_args:string list) 
	   (val_args:string list) (free_params:(smallfoot_data_type # string) list) c =
						   
	\(arg_refL:smallfoot_var list, arg_valL:num list) fvL. 
	 if (LENGTH arg_valL = LENGTH val_args) /\
            (LENGTH arg_refL = LENGTH ref_args) /\
            (LENGTH fvL = LENGTH free_params) /\
            (EVERY smallfoot_data_IS_WELL_TYPED (ZIP (MAP FST free_params, fvL)))
         then c (arg_refL, arg_valL) fvL else asl_false`;



val SMALLFOOT_SING_PROCEDURE_SPEC_def = Define `
    SMALLFOOT_SING_PROCEDURE_SPEC res_env penv pre name post arg1 arg2 arg3 =

    SMALLFOOT_HOARE_TRIPLE_INST res_env penv 
			   (smallfoot_input_preserve_names_wrapper arg1 arg2 arg3 pre)
			   (fasl_prog_procedure_call name)
			   post`;


val LIST_UNROLL_GIVEN_ELEMENT_NAMES___TYPES_def = Define
`LIST_UNROLL_GIVEN_ELEMENT_NAMES___TYPES vL (tL:(smallfoot_data_type # string) list) =
 (LENGTH tL = LENGTH vL) /\
 (EVERY smallfoot_data_IS_WELL_TYPED (ZIP (MAP FST tL, vL)))`;


val LIST_UNROLL_GIVEN_ELEMENT_NAMES___TYPES_REWRITE = store_thm (
"LIST_UNROLL_GIVEN_ELEMENT_NAMES___TYPES_REWRITE",

``(LIST_UNROLL_GIVEN_ELEMENT_NAMES___TYPES [] [] = T) /\
(LIST_UNROLL_GIVEN_ELEMENT_NAMES___TYPES (v::vL) (t::tL) = 
 smallfoot_data_IS_WELL_TYPED (FST t, v) /\
 LIST_UNROLL_GIVEN_ELEMENT_NAMES___TYPES vL tL)``,

SIMP_TAC list_ss [LIST_UNROLL_GIVEN_ELEMENT_NAMES___TYPES_def] THEN
METIS_TAC[]);



val LIST_UNROLL_GIVEN_ELEMENT_NAMES___TYPES___UNROLL = store_thm (
"LIST_UNROLL_GIVEN_ELEMENT_NAMES___TYPES___UNROLL",

``(LIST_UNROLL_GIVEN_ELEMENT_NAMES___TYPES x [] = (x = [])) /\
(LIST_UNROLL_GIVEN_ELEMENT_NAMES___TYPES x (t::tL) = 
 ?L' v. (x = (v::L')) /\ smallfoot_data_IS_WELL_TYPED (FST t, v) /\
 LIST_UNROLL_GIVEN_ELEMENT_NAMES___TYPES L' tL)``,

Cases_on `x` THEN (
   SIMP_TAC list_ss [LIST_UNROLL_GIVEN_ELEMENT_NAMES___TYPES_def]
) THEN
METIS_TAC[]);



val SMALLFOOT_INFERENCE_smallfoot_input_preserve_names_wrapper = store_thm (
"SMALLFOOT_INFERENCE_smallfoot_input_preserve_names_wrapper",
``
(SMALLFOOT_HOARE_TRIPLE res_env penv 
((smallfoot_input_preserve_names_wrapper ref_args val_args free_params c) 
(arg_refL,arg_valL) fvL) body post)

=

((LIST_UNROLL_GIVEN_ELEMENT_NAMES arg_refL ref_args /\
  LIST_UNROLL_GIVEN_ELEMENT_NAMES arg_valL val_args /\
  LIST_UNROLL_GIVEN_ELEMENT_NAMES___TYPES fvL free_params) ==>

(SMALLFOOT_HOARE_TRIPLE res_env penv (c (arg_refL,arg_valL) fvL) body post))

``,


SIMP_TAC std_ss [LIST_UNROLL_GIVEN_ELEMENT_NAMES_def,
                 LIST_UNROLL_GIVEN_ELEMENT_NAMES___TYPES_def,
		 smallfoot_input_preserve_names_wrapper_def,
		 COND_RAND, COND_RATOR] THEN
SIMP_TAC std_ss [SMALLFOOT_HOARE_TRIPLE_def,
		 FASL_PROGRAM_HOARE_TRIPLE_REWRITE, asl_false_def,
		 NOT_IN_EMPTY, IN_ABS, SUBSET_DEF] THEN
METIS_TAC[]);







val FASL_PROGRAM_IS_ABSTRACTION___smallfoot_prog_val_arg = store_thm (
"FASL_PROGRAM_IS_ABSTRACTION___smallfoot_prog_val_arg",
``!xenv penv c body body'.
(!arg. FASL_PROGRAM_IS_ABSTRACTION xenv penv (body arg) (body' arg)) ==>
FASL_PROGRAM_IS_ABSTRACTION xenv penv (smallfoot_prog_val_arg body c) 
                                      (smallfoot_prog_val_arg body' c)``,

REPEAT STRIP_TAC THEN
REWRITE_TAC[smallfoot_prog_val_arg_def] THEN 
MATCH_MP_TAC FASL_PROGRAM_IS_ABSTRACTION___select THEN
SIMP_TAC std_ss [] THEN GEN_TAC THEN
MATCH_MP_TAC FASL_PROGRAM_IS_ABSTRACTION___seq THEN
ASM_REWRITE_TAC[FASL_PROGRAM_IS_ABSTRACTION___REFL] THEN
MATCH_MP_TAC FASL_PROGRAM_IS_ABSTRACTION___seq THEN
ASM_REWRITE_TAC[FASL_PROGRAM_IS_ABSTRACTION___REFL]);



val FASL_PROGRAM_IS_ABSTRACTION___smallfoot_prog_local_var = store_thm (
"FASL_PROGRAM_IS_ABSTRACTION___smallfoot_prog_local_var",
``!xenv penv body body'.
(!arg. FASL_PROGRAM_IS_ABSTRACTION xenv penv (body arg) (body' arg)) ==>
FASL_PROGRAM_IS_ABSTRACTION xenv penv (smallfoot_prog_local_var body) 
                                      (smallfoot_prog_local_var body')``,

REPEAT STRIP_TAC THEN
REWRITE_TAC[smallfoot_prog_local_var_def, GSYM fasl_prog_ndet_def] THEN
MATCH_MP_TAC FASL_PROGRAM_IS_ABSTRACTION___ndet THEN
SIMP_TAC std_ss [IN_ABS, GSYM LEFT_EXISTS_AND_THM,
		 GSYM LEFT_FORALL_IMP_THM] THEN
GEN_TAC THEN
Q.EXISTS_TAC `e` THEN
MATCH_MP_TAC FASL_PROGRAM_IS_ABSTRACTION___smallfoot_prog_val_arg THEN
ASM_REWRITE_TAC[]);








val SMALLFOOT_P_EXPRESSION___READ_PERMISSION_def = Define `
    SMALLFOOT_P_EXPRESSION___READ_PERMISSION l = \s:smallfoot_state.

     (((SND s) = FEMPTY) /\
     (EVERY (\e. (!x. x IN (THE (SMALLFOOT_PE_USED_VARS e)) ==> 
                      var_res_sl___has_read_permission x (FST s))) l))`;




val SMALLFOOT_P_EXPRESSION___READ_PERMISSION___REWRITES = store_thm ("SMALLFOOT_P_EXPRESSION___READ_PERMISSION___REWRITES",
``(SMALLFOOT_P_EXPRESSION___READ_PERMISSION [] = smallfoot_ap_stack_true) /\

  (SMALLFOOT_P_EXPRESSION___READ_PERMISSION ((smallfoot_p_const c)::l) =
   SMALLFOOT_P_EXPRESSION___READ_PERMISSION l) /\

  (SMALLFOOT_P_EXPRESSION___READ_PERMISSION ((smallfoot_p_var v)::l) =
   \s. var_res_sl___has_read_permission v (FST s) /\
   (SMALLFOOT_P_EXPRESSION___READ_PERMISSION l) s) /\


  (SMALLFOOT_P_EXPRESSION___READ_PERMISSION ((smallfoot_p_add e1 e2)::l) =
   SMALLFOOT_P_EXPRESSION___READ_PERMISSION (e1::e2::l)) /\

  (SMALLFOOT_P_EXPRESSION___READ_PERMISSION ((smallfoot_p_sub e1 e2)::l) =
   SMALLFOOT_P_EXPRESSION___READ_PERMISSION (e1::e2::l))
``,


REWRITE_TAC[FUN_EQ_THM] THEN
SIMP_TAC list_ss [SMALLFOOT_P_EXPRESSION___READ_PERMISSION_def,
		  SMALLFOOT_PE_USED_VARS___REWRITE,
		  smallfoot_ap_stack_true_def, NOT_IN_EMPTY,
		  IN_INSERT, IN_UNION] THEN
METIS_TAC[]);






val smallfoot_p_equal_const___IS_DECIDED =
store_thm ("smallfoot_p_equal_const___IS_DECIDED",
``
!P e c.
(!s. s IN P ==> IS_SOME (SMALLFOOT_P_EXPRESSION_EVAL e (FST s))) ==>

(fasl_predicate_IS_DECIDED smallfoot_env P
   (smallfoot_p_equal e (smallfoot_p_const c)))``,


SIMP_TAC std_ss [fasl_predicate_IS_DECIDED_def,
		 GSYM fasl_predicate_IS_DECIDED_IN_STATE_def] THEN
REPEAT STRIP_TAC THEN
MATCH_MP_TAC smallfoot_predicate_IS_DECIDED_IN_STATE THEN
SIMP_TAC std_ss [SMALLFOOT_PP_USED_VARS_def,
		 smallfoot_p_equal_def,
		 SMALLFOOT_PE_USED_VARS___REWRITE,
		 UNION_EMPTY] THEN
`?vs. SMALLFOOT_PE_USED_VARS e = SOME vs` by
   PROVE_TAC[SMALLFOOT_PE_USED_VARS___IS_SOME, IS_SOME_EXISTS] THEN
ASM_SIMP_TAC std_ss [] THEN
FULL_SIMP_TAC std_ss [SMALLFOOT_PE_USED_VARS_def,
		      SMALLFOOT_AE_USED_VARS_THM,
		      SMALLFOOT_AE_USED_VARS_REL___REWRITE]);





val SMALLFOOT_INFERENCE_prog_parallel = store_thm (
"SMALLFOOT_INFERENCE_prog_parallel",
``!res_env penv P1 P2 Q1 Q2.
         SMALLFOOT_HOARE_TRIPLE res_env penv P1 p1 Q1 /\
         SMALLFOOT_HOARE_TRIPLE res_env penv P2 p2 Q2 ==>
         SMALLFOOT_HOARE_TRIPLE res_env penv
           (smallfoot_ap_star P1 P2)
           (fasl_prog_parallel p1 p2)
           (smallfoot_ap_star Q1 Q2)``,

SIMP_TAC std_ss [SMALLFOOT_HOARE_TRIPLE_def] THEN
REPEAT STRIP_TAC THEN
SIMP_TAC std_ss [FASL_PROGRAM_HOARE_TRIPLE_REWRITE, IN_ABS,
		 smallfoot_ap_star_def, asl_star_def, IN_ABS] THEN
REPEAT STRIP_TAC THEN
Q.PAT_ASSUM `!x. X x` (MP_TAC o Q.SPEC `q`) THEN
Q.PAT_ASSUM `!x. X x` (MP_TAC o Q.SPEC `p`) THEN

Q.ABBREV_TAC `P1' = (\s. s IN P1 /\ (s = p))` THEN
Q.ABBREV_TAC `P2' = (\s. s IN P2 /\ (s = q))` THEN
Q.ABBREV_TAC `Q1' = (\s. s IN Q1 /\
         VAR_RES_STACK___IS_EQUAL_UPTO_VALUES (FST p) (FST s))` THEN
Q.ABBREV_TAC `Q2' = (\s. s IN Q2 /\
         VAR_RES_STACK___IS_EQUAL_UPTO_VALUES (FST q) (FST s))` THEN

REPEAT STRIP_TAC THEN
MP_TAC (let
   val thm = ISPEC ``(smallfoot_env,res_env:string -> smallfoot_a_proposition)`` FASL_INFERENCE_prog_parallel;
   val thm2 = INST_TYPE [Type `:'g` |-> stringLib.string_ty,
			 Type `:'h` |-> Type `:smallfoot_var list # num list`] thm   
   val thm3 = Q.SPECL [`penv`, `P1'`, `P2'`, `Q1'`, `Q2'`] thm2
in
   thm3
end) THEN
ASM_SIMP_TAC std_ss [FASL_IS_LOCAL_EVAL_ENV___smallfoot_env,
		     FASL_IS_LOCAL_EVAL_XENV_def,
		     FASL_GET_XENV_COMBINATOR_def,
		     SMALLFOOT_SEPARATION_COMBINATOR___EXTRACT] THEN
UNABBREV_ALL_TAC THEN
ASM_SIMP_TAC std_ss [FASL_PROGRAM_HOARE_TRIPLE_REWRITE, asl_star_def,
		     IN_ABS, GSYM LEFT_EXISTS_IMP_THM] THEN
Q.EXISTS_TAC `x` THEN
Q.EXISTS_TAC `t` THEN
ASM_SIMP_TAC std_ss [GSYM LEFT_FORALL_IMP_THM, SUBSET_DEF, IN_ABS] THEN
GEN_TAC THEN STRIP_TAC THEN
GEN_TAC THEN STRIP_TAC THEN
RES_TAC THEN
CONJ_TAC THEN1 (
  Q.EXISTS_TAC `p'` THEN
  Q.EXISTS_TAC `q'` THEN
  ASM_REWRITE_TAC[]
) THEN

FULL_SIMP_TAC std_ss [VAR_RES_STACK___IS_EQUAL_UPTO_VALUES_def,
		      SOME___smallfoot_separation_combinator,
		      SOME___VAR_RES_STACK_COMBINE,
		      FMERGE_DEF, IN_UNION, GSYM FORALL_AND_THM] THEN
GEN_TAC THEN
REPEAT (Q.PAT_ASSUM `VAR_RES_STACK_IS_SEPARATE X Y` (MP_TAC o Q.SPEC `x''` o REWRITE_RULE [VAR_RES_STACK_IS_SEPARATE_def])) THEN
Cases_on `x'' IN FDOM (FST p')` THEN ASM_SIMP_TAC std_ss [] THEN
Cases_on `x'' IN FDOM (FST q')` THEN ASM_SIMP_TAC std_ss [] THEN
Cases_on `x'' IN FDOM (FST p)` THEN ASM_SIMP_TAC std_ss [] THEN
Cases_on `x'' IN FDOM (FST q)` THEN ASM_SIMP_TAC std_ss [] THEN
ASM_SIMP_TAC std_ss [VAR_RES_STACK_COMBINE___MERGE_FUNC_def,
		     var_res_permission_THM2]);







val smallfoot_ap_equal___P_EXPRESSION_LIST_def = Define 
`smallfoot_ap_equal___P_EXPRESSION_LIST expL constL = 
  \s:smallfoot_state. (LENGTH expL = LENGTH constL) /\ 
              EVERY (\p. SMALLFOOT_P_EXPRESSION_EVAL (FST p) (FST s) = 
               SOME (SND p)) (ZIP (expL,constL))`;



val SMALLFOOT_INFERENCE___choose_constants =
store_thm ("SMALLFOOT_INFERENCE___choose_constants",
``!res_env penv P prog expL Q.

((!e. MEM e expL ==> smallfoot_ae_is_defined P (SMALLFOOT_P_EXPRESSION_EVAL e)) /\

(!constL. 
SMALLFOOT_HOARE_TRIPLE res_env penv (asl_and (smallfoot_ap_equal___P_EXPRESSION_LIST expL constL) P)
                            (prog constL) Q)) ==>

SMALLFOOT_HOARE_TRIPLE res_env penv P (
     smallfoot_prog_choose_constants prog expL) Q``,


REPEAT STRIP_TAC THEN
FULL_SIMP_TAC std_ss [SMALLFOOT_HOARE_TRIPLE_def,
		      smallfoot_prog_choose_constants_def,
                      fasl_prog_ndet___HOARE_TRIPLE,
		      IN_IMAGE, GSYM LEFT_FORALL_IMP_THM,
		      IN_ABS, FASL_IS_LOCAL_EVAL_ENV___smallfoot_env,
		      FASL_IS_LOCAL_EVAL_XENV_def] THEN
REPEAT STRIP_TAC THEN
Q.PAT_ASSUM `!constL. X constL` (ASSUME_TAC o Q.SPEC `constL`) THEN
Q.ABBREV_TAC `c = (fasl_pred_bigand (MAP
                     (\x.
                        smallfoot_p_equal (FST x) (smallfoot_p_const (SND x)))
                     (ZIP (expL,constL))))` THEN
Q.ABBREV_TAC `P2 =
 asl_and (smallfoot_ap_equal___P_EXPRESSION_LIST
         expL constL) P` THEN
MATCH_MP_TAC FASL_INFERENCE_prog_seq THEN
Q.EXISTS_TAC `asl_and (\s. s IN P /\ (s = x)) (XEVAL_fasl_predicate (FST (smallfoot_env,res_env)) c)` THEN
CONJ_TAC THEN1 (
   MATCH_MP_TAC FASL_INFERENCE_assume THEN
   UNABBREV_ALL_TAC THEN
   MATCH_MP_TAC fasl_predicate_IS_DECIDED___fasl_pred_bigand THEN
   ASM_SIMP_TAC list_ss [EVERY_MEM, MEM_MAP, GSYM LEFT_FORALL_IMP_THM,
		     PAIR_FORALL_THM, MEM_ZIP] THEN
   REPEAT STRIP_TAC THEN
   MATCH_MP_TAC smallfoot_p_equal_const___IS_DECIDED THEN
   SIMP_TAC std_ss [IN_ABS] THEN
   REPEAT STRIP_TAC THEN
   `MEM (EL n expL) expL` by PROVE_TAC[MEM_EL] THEN
   RES_TAC THEN
   Cases_on `x` THEN
   FULL_SIMP_TAC std_ss [smallfoot_ae_is_defined_def] THEN
   PROVE_TAC[IN_DEF]
) THEN

Tactical.REVERSE (`(XEVAL_fasl_predicate smallfoot_env c) =
                  (smallfoot_ap_equal___P_EXPRESSION_LIST expL constL)` by ALL_TAC) THEN1 (

  UNABBREV_ALL_TAC THEN
  FULL_SIMP_TAC std_ss [ASL_BOOL___PRED_SET_REWRITES, IN_INTER,
		        INTER_ABS, IN_ABS, GSYM CONJ_ASSOC] THEN
  Q.PAT_ASSUM `!x. X x` (MP_TAC o Q.SPEC `x`) THEN 
  MATCH_MP_TAC (prove (``(PP = PP') ==>
                        (FASL_PROGRAM_HOARE_TRIPLE smallfoot_xenv penv PP (prog constL) QQ ==>
                         FASL_PROGRAM_HOARE_TRIPLE smallfoot_xenv penv PP' (prog constL) QQ)``,
                      SIMP_TAC std_ss [])) THEN
  SIMP_TAC (std_ss++bool_eq_imp_ss) [EXTENSION, IN_ABS]
) THEN

UNABBREV_ALL_TAC THEN
ONCE_REWRITE_TAC [FUN_EQ_THM] THEN
ASM_SIMP_TAC std_ss [ XEVAL_fasl_predicate_def,
		    EVAL_fasl_predicate___fasl_pred_bigand,
		    asl_bigand_list_THM, IN_ABS,
		    smallfoot_ap_equal___P_EXPRESSION_LIST_def,
		    EVERY_MEM, MEM_MAP,
		    GSYM RIGHT_EXISTS_AND_THM, GSYM LEFT_FORALL_IMP_THM,
		    smallfoot_env_def, smallfoot_p_equal_def,
		    MEM_ZIP, EVAL_fasl_predicate_def,
	            SMALLFOOT_PT_PROPOSITION_pred_map_def,
		    smallfoot_ap_binexpression_def,
		    smallfoot_a_stack_proposition_def,
		    LET_THM,
		    SMALLFOOT_P_EXPRESSION_EVAL_def,
		    smallfoot_ae_const_def] THEN
SIMP_TAC (std_ss++boolSimps.CONJ_ss) [IS_SOME_EXISTS,
				      GSYM LEFT_EXISTS_AND_THM]);




val smallfoot_ap_equal___P_EXPRESSION_LIST_11 =
store_thm ("smallfoot_ap_equal___P_EXPRESSION_LIST_11",

``!s expL consL1 consL2.
  (s IN smallfoot_ap_equal___P_EXPRESSION_LIST expL constL1 /\
   s IN smallfoot_ap_equal___P_EXPRESSION_LIST expL constL2) ==>
  (constL2 = constL1)``,

SIMP_TAC (std_ss++boolSimps.CONJ_ss) 
                [smallfoot_ap_equal___P_EXPRESSION_LIST_def,
		 IN_ABS, LIST_EQ_REWRITE, EVERY_MEM,
		 MEM_ZIP, GSYM LEFT_FORALL_IMP_THM]);




val ZIP_APPEND = store_thm ("ZIP_APPEND",

``!l1 l2 l3 l4. (LENGTH l1 = LENGTH l3) ==>
(ZIP (l1++l2,l3++l4) = ZIP (l1,l3)++ZIP(l2,l4))``,

Induct_on `l3` THENL [
   SIMP_TAC list_ss [LENGTH_NIL],

   Cases_on `l1` THEN
   ASM_SIMP_TAC list_ss []
]);



val smallfoot_ap_equal___P_EXPRESSION_LIST___APPEND =
store_thm ("smallfoot_ap_equal___P_EXPRESSION_LIST___APPEND",

``(LENGTH expL1 = LENGTH constL1) ==>

  (smallfoot_ap_equal___P_EXPRESSION_LIST (expL1++expL2) (constL1++constL2) =
   asl_and (smallfoot_ap_equal___P_EXPRESSION_LIST expL1 constL1)
           (smallfoot_ap_equal___P_EXPRESSION_LIST expL2 constL2))``,

ONCE_REWRITE_TAC[EXTENSION] THEN
SIMP_TAC list_ss [smallfoot_ap_equal___P_EXPRESSION_LIST_def,
		 asl_and_def, IN_ABS,
	         ZIP_APPEND] THEN
METIS_TAC[]);






val smallfoot_prog_best_local_action_def = Define `
        smallfoot_prog_best_local_action P Q =
        fasl_prog_quant_best_local_action (\x s. s IN P /\ (s = x)) 
(\x s. s IN Q /\ (VAR_RES_STACK___IS_EQUAL_UPTO_VALUES (FST x) (FST s)))`;



val FASL_PROGRAM_IS_ABSTRACTION___smallfoot_proc_call = store_thm (
"FASL_PROGRAM_IS_ABSTRACTION___smallfoot_proc_call",
``!res_env penv pre name post a1 a2 a3 ref_argL val_argL val_arg_constL cons.
 (SMALLFOOT_SING_PROCEDURE_SPEC res_env penv pre name post a1 a2 a3 /\
 (LENGTH ref_argL = LENGTH a1) /\
 (LENGTH val_argL = LENGTH a2) /\
 (LENGTH val_arg_constL = LENGTH a2) /\
 LIST_UNROLL_GIVEN_ELEMENT_NAMES___TYPES cons a3) ==>

(FASL_PROGRAM_IS_ABSTRACTION (smallfoot_env,res_env) penv 
   (smallfoot_prog_procedure_call name (ref_argL, val_argL))
   (smallfoot_prog_best_local_action 
      (asl_and (smallfoot_ap_equal___P_EXPRESSION_LIST
                             val_argL val_arg_constL)
                         (pre (ref_argL, val_arg_constL) cons))
      (post (ref_argL, val_arg_constL) cons)))``,


REPEAT STRIP_TAC THEN
FULL_SIMP_TAC std_ss [FASL_PROGRAM_IS_ABSTRACTION___quant_best_local_action,
		      FASL_IS_LOCAL_EVAL_ENV___smallfoot_env,
		      FASL_IS_LOCAL_EVAL_XENV_def,
		      smallfoot_prog_procedure_call_def,
		      smallfoot_prog_best_local_action_def,
		      GSYM SMALLFOOT_HOARE_TRIPLE_def] THEN
MATCH_MP_TAC SMALLFOOT_INFERENCE___choose_constants THEN
CONJ_TAC THEN1 (
   SIMP_TAC (std_ss++boolSimps.CONJ_ss)
	           [smallfoot_ae_is_defined_def,
		    asl_bool_EVAL,
		    smallfoot_ap_equal___P_EXPRESSION_LIST_def,
		    IN_ABS, EVERY_MEM, MEM_ZIP, MEM_EL,
		    GSYM LEFT_FORALL_IMP_THM, EL_ZIP,
		    LENGTH_ZIP] THEN
   METIS_TAC[IS_SOME_EXISTS]
) THEN
FULL_SIMP_TAC std_ss [SMALLFOOT_HOARE_TRIPLE_def,
		 FASL_PROGRAM_HOARE_TRIPLE_REWRITE,
		 asl_bool_EVAL,
		 SMALLFOOT_SING_PROCEDURE_SPEC_def,
		 SMALLFOOT_HOARE_TRIPLE_INST_def, IN_ABS, SUBSET_DEF,
		 smallfoot_input_preserve_names_wrapper_def,
		 LIST_UNROLL_GIVEN_ELEMENT_NAMES___TYPES_def] THEN
REPEAT STRIP_TAC THEN
Q.PAT_ASSUM `!cond_arg. X cond_arg` MATCH_MP_TAC THEN
ASM_SIMP_TAC std_ss [] THEN
`val_arg_constL = constL` by PROVE_TAC[smallfoot_ap_equal___P_EXPRESSION_LIST_11] THEN
ASM_REWRITE_TAC[]);





val SMALLFOOT_HOARE_TRIPLE___asl_and = store_thm (
"SMALLFOOT_HOARE_TRIPLE___asl_and",

``!res_env penv P prog Q X.
  SMALLFOOT_HOARE_TRIPLE res_env penv P prog Q ==>
  SMALLFOOT_HOARE_TRIPLE res_env penv (asl_and X P) prog Q``,

SIMP_TAC std_ss [FASL_PROGRAM_HOARE_TRIPLE_REWRITE, IN_ABS,
		 asl_bool_EVAL, SMALLFOOT_HOARE_TRIPLE_def]);




val FASL_PROGRAM_IS_ABSTRACTION___smallfoot_parallel_proc_call = store_thm (
"FASL_PROGRAM_IS_ABSTRACTION___smallfoot_parallel_proc_call",
``!res_env penv pre1 name1 post1 a11 a21 a31 ref_argL1 val_argL1 val_arg_constL1 cons1
                pre2 name2 post2 a12 a22 a32 ref_argL2 val_argL2 val_arg_constL2 cons2.

 ((SMALLFOOT_SING_PROCEDURE_SPEC res_env penv pre1 name1 post1 a11 a21 a31) /\
 (LENGTH ref_argL1 = LENGTH a11) /\
 (LENGTH val_argL1 = LENGTH a21) /\
 (LENGTH val_arg_constL1 = LENGTH a21) /\
 LIST_UNROLL_GIVEN_ELEMENT_NAMES___TYPES cons1 a31 /\

 (SMALLFOOT_SING_PROCEDURE_SPEC res_env penv pre2 name2 post2 a12 a22 a32) /\
 (LENGTH ref_argL2 = LENGTH a12) /\
 (LENGTH val_argL2 = LENGTH a22) /\
 (LENGTH val_arg_constL2 = LENGTH a22) /\
 LIST_UNROLL_GIVEN_ELEMENT_NAMES___TYPES cons2 a32) ==>


(FASL_PROGRAM_IS_ABSTRACTION (smallfoot_env,res_env) penv 
   (smallfoot_prog_parallel_procedure_call name1 (ref_argL1, val_argL1)
                                           name2 (ref_argL2, val_argL2))
   (smallfoot_prog_best_local_action 
      (asl_and (smallfoot_ap_equal___P_EXPRESSION_LIST
                  (val_argL1++val_argL2) 
                  (val_arg_constL1++val_arg_constL2))
               (smallfoot_ap_star
                   (pre1 (ref_argL1, val_arg_constL1) cons1)
                   (pre2 (ref_argL2, val_arg_constL2) cons2)))
      (smallfoot_ap_star 
         (post1 (ref_argL1, val_arg_constL1) cons1)
         (post2 (ref_argL2, val_arg_constL2) cons2))))``,


REPEAT STRIP_TAC THEN
FULL_SIMP_TAC std_ss [FASL_PROGRAM_IS_ABSTRACTION___quant_best_local_action,
		      FASL_IS_LOCAL_EVAL_ENV___smallfoot_env,
		      FASL_IS_LOCAL_EVAL_XENV_def,
		      smallfoot_prog_parallel_procedure_call_def,
		      GSYM SMALLFOOT_HOARE_TRIPLE_def,
		      smallfoot_ap_equal___P_EXPRESSION_LIST___APPEND,
		      smallfoot_prog_best_local_action_def] THEN
MATCH_MP_TAC SMALLFOOT_INFERENCE___choose_constants THEN
CONJ_TAC THEN1 (
   SIMP_TAC (list_ss++boolSimps.CONJ_ss)
	           [smallfoot_ae_is_defined_def,
		    asl_bool_EVAL,
		    smallfoot_ap_equal___P_EXPRESSION_LIST_def,
		    IN_ABS, EVERY_MEM, MEM_ZIP, MEM_EL,
		    GSYM LEFT_FORALL_IMP_THM, EL_ZIP,
		    LENGTH_ZIP] THEN
   METIS_TAC[IS_SOME_EXISTS]
) THEN
SIMP_TAC std_ss [] THEN GEN_TAC THEN
MATCH_MP_TAC SMALLFOOT_INFERENCE___choose_constants THEN
CONJ_TAC THEN1 (
   SIMP_TAC (list_ss++boolSimps.CONJ_ss)
	           [smallfoot_ae_is_defined_def,
		    asl_bool_EVAL,
		    smallfoot_ap_equal___P_EXPRESSION_LIST_def,
		    IN_ABS, EVERY_MEM, MEM_ZIP, MEM_EL,
		    GSYM LEFT_FORALL_IMP_THM, EL_ZIP,
		    LENGTH_ZIP] THEN
   METIS_TAC[IS_SOME_EXISTS]
) THEN
SIMP_TAC std_ss [SMALLFOOT_HOARE_TRIPLE_def] THEN
GEN_TAC THEN
Tactical.REVERSE (
    Cases_on `(constL  = val_arg_constL1) /\
              (constL' = val_arg_constL2)`) THEN1 (

   SIMP_TAC std_ss [FASL_PROGRAM_HOARE_TRIPLE_REWRITE,
		    asl_bool_EVAL, IN_ABS] THEN
   METIS_TAC[smallfoot_ap_equal___P_EXPRESSION_LIST_11]
) THEN
SIMP_TAC std_ss [GSYM SMALLFOOT_HOARE_TRIPLE_def] THEN
NTAC 3 (MATCH_MP_TAC SMALLFOOT_HOARE_TRIPLE___asl_and) THEN
MATCH_MP_TAC SMALLFOOT_INFERENCE_prog_parallel THEN
FULL_SIMP_TAC std_ss [SMALLFOOT_SING_PROCEDURE_SPEC_def,
		      smallfoot_input_preserve_names_wrapper_def,
		      SMALLFOOT_HOARE_TRIPLE_INST_def,
		      LIST_UNROLL_GIVEN_ELEMENT_NAMES___TYPES_def] THEN
METIS_TAC[]);






val smallfoot_choose_const_best_local_action_def = Define `
smallfoot_choose_const_best_local_action pre post condL expL =
   (fasl_prog_quant_best_local_action 
      (\(args:num list # smallfoot_data list,state).
      (asl_and (K (LIST_UNROLL_GIVEN_ELEMENT_NAMES___TYPES (SND args) condL))
      (asl_and (smallfoot_ap_equal___P_EXPRESSION_LIST
                  expL (FST args))
               (asl_and (pre args) (\s. s = state)))))
      (\(args,state). asl_and (post args) (\s. VAR_RES_STACK___IS_EQUAL_UPTO_VALUES (FST state) (FST s)))):smallfoot_prog`;





val smallfoot_proc_call_abstraction_def = Define `
smallfoot_proc_call_abstraction pre post (ref_argL:smallfoot_var list, val_argL) condL =
smallfoot_choose_const_best_local_action 
(\args. pre (ref_argL, FST args) (SND args))
(\args. post (ref_argL, FST args) (SND args)) condL val_argL`;


val FASL_PROGRAM_IS_ABSTRACTION___smallfoot_proc_call___quant = store_thm (
"FASL_PROGRAM_IS_ABSTRACTION___smallfoot_proc_call___quant",
``!res_env penv pre name post a1 a2 a3 ref_argL val_argL.
 (SMALLFOOT_SING_PROCEDURE_SPEC res_env penv pre name post a1 a2 a3 /\
 (LENGTH ref_argL = LENGTH a1) /\
 (LENGTH val_argL = LENGTH a2)) ==>

(FASL_PROGRAM_IS_ABSTRACTION (smallfoot_env,res_env) penv 
   (smallfoot_prog_procedure_call name (ref_argL, val_argL))
   (smallfoot_proc_call_abstraction pre post (ref_argL, val_argL) a3))``,


REPEAT STRIP_TAC THEN
SIMP_TAC std_ss [smallfoot_proc_call_abstraction_def,
                 FASL_PROGRAM_IS_ABSTRACTION___quant_best_local_action2,
                 FASL_IS_LOCAL_EVAL_ENV___smallfoot_env,
                 FASL_IS_LOCAL_EVAL_XENV_def,
		 LIST_UNROLL_GIVEN_ELEMENT_NAMES_def, PAIR_FORALL_THM,
		 smallfoot_choose_const_best_local_action_def] THEN
REPEAT GEN_TAC THEN
Cases_on `~(LENGTH x1 = LENGTH a2) \/ ~(LIST_UNROLL_GIVEN_ELEMENT_NAMES___TYPES x2 a3)` THEN1 (
   FULL_SIMP_TAC std_ss [asl_bool_REWRITES,
			smallfoot_ap_equal___P_EXPRESSION_LIST_def,
		        fasl_prog_best_local_action___false_pre,
		        FASL_PROGRAM_IS_ABSTRACTION___shallow_fail]
) THEN
FULL_SIMP_TAC std_ss [asl_bool_REWRITES] THEN

MP_TAC (Q.SPECL [`res_env`, `penv`, `pre`, `name`, `post`, `a1`, `a2`, `a3`, `ref_argL`,
                 `val_argL`, `x1`, `x2`]
    FASL_PROGRAM_IS_ABSTRACTION___smallfoot_proc_call) THEN

ASM_SIMP_TAC std_ss [smallfoot_prog_best_local_action_def,
		     asl_and_def, IN_ABS,
		     FASL_IS_LOCAL_EVAL_ENV___smallfoot_env,
		     FASL_IS_LOCAL_EVAL_XENV_def,
                     FASL_PROGRAM_IS_ABSTRACTION___quant_best_local_action2,
		     PAIR_FORALL_THM, GSYM CONJ_ASSOC]);

		

val smallfoot_parallel_proc_call_abstraction_def = Define `
smallfoot_parallel_proc_call_abstraction pre1 post1 (ref_argL1:smallfoot_var list, val_argL1) free_params1
                                         pre2 post2 (ref_argL2:smallfoot_var list, val_argL2) free_params2 =
smallfoot_choose_const_best_local_action
(\args. smallfoot_ap_star (pre1 (ref_argL1, 
                                   (FIRSTN (LENGTH val_argL1) (FST args))) 
                                (FIRSTN (LENGTH free_params1) (SND args)))
                          (pre2 (ref_argL2, 
                                   (BUTFIRSTN (LENGTH val_argL1) (FST args))) 
                                (BUTFIRSTN (LENGTH free_params1) (SND args))))
(\args. smallfoot_ap_star (post1 (ref_argL1, 
                                   (FIRSTN (LENGTH val_argL1) (FST args))) 
                                (FIRSTN (LENGTH free_params1) (SND args)))
                          (post2 (ref_argL2, 
                                   (BUTFIRSTN (LENGTH val_argL1) (FST args))) 
                                (BUTFIRSTN (LENGTH free_params1) (SND args))))
(free_params1++free_params2) (val_argL1++val_argL2)`;





val FASL_PROGRAM_IS_ABSTRACTION___smallfoot_parallel_proc_call___quant = store_thm (
"FASL_PROGRAM_IS_ABSTRACTION___smallfoot_parallel_proc_call___quant",
``!penv res_env pre1 name1 post1 a11 a21 a31 ref_argL1 val_argL1
                pre2 name2 post2 a12 a22 a32 ref_argL2 val_argL2.

 ((SMALLFOOT_SING_PROCEDURE_SPEC res_env penv pre1 name1 post1 a11 a21 a31) /\
 (LENGTH ref_argL1 = LENGTH a11) /\
 (LENGTH val_argL1 = LENGTH a21) /\
 (SMALLFOOT_SING_PROCEDURE_SPEC res_env penv pre2 name2 post2 a12 a22 a32) /\
 (LENGTH ref_argL2 = LENGTH a12) /\
 (LENGTH val_argL2 = LENGTH a22)) ==>

(FASL_PROGRAM_IS_ABSTRACTION (smallfoot_env,res_env) penv 
   (smallfoot_prog_parallel_procedure_call name1 (ref_argL1, val_argL1)
                                           name2 (ref_argL2, val_argL2))
   (smallfoot_parallel_proc_call_abstraction pre1 post1 (ref_argL1, val_argL1) a31
                                             pre2 post2 (ref_argL2, val_argL2) a32))``,


REPEAT STRIP_TAC THEN
SIMP_TAC std_ss [smallfoot_parallel_proc_call_abstraction_def,
                 FASL_PROGRAM_IS_ABSTRACTION___quant_best_local_action2,
                 FASL_IS_LOCAL_EVAL_ENV___smallfoot_env,
		 FASL_IS_LOCAL_EVAL_XENV_def,
		 LIST_UNROLL_GIVEN_ELEMENT_NAMES_def, PAIR_FORALL_THM,
		 smallfoot_choose_const_best_local_action_def] THEN
REPEAT GEN_TAC THEN
Cases_on `~(LENGTH x1 = LENGTH (a21++a22))` THEN1 (
   FULL_SIMP_TAC list_ss [asl_bool_REWRITES,
		        fasl_prog_best_local_action___false_pre,
			smallfoot_ap_equal___P_EXPRESSION_LIST_def,
		        FASL_PROGRAM_IS_ABSTRACTION___shallow_fail]
) THEN
Cases_on `~LIST_UNROLL_GIVEN_ELEMENT_NAMES___TYPES x2 (a31 ++ a32)` THEN1 (
   ASM_SIMP_TAC std_ss [asl_bool_REWRITES,
		        fasl_prog_best_local_action___false_pre,
		        FASL_PROGRAM_IS_ABSTRACTION___shallow_fail]
) THEN
`LENGTH x2 = LENGTH (a31++a32)` by ALL_TAC THEN1 (
   FULL_SIMP_TAC list_ss [LIST_UNROLL_GIVEN_ELEMENT_NAMES___TYPES_def]
) THEN
FULL_SIMP_TAC std_ss [asl_bool_REWRITES] THEN

Q.ABBREV_TAC `constL11 = FIRSTN (LENGTH a21) x1` THEN
Q.ABBREV_TAC `constL12 = FIRSTN (LENGTH a31) x2` THEN
Q.ABBREV_TAC `constL21 = BUTFIRSTN (LENGTH a21) x1` THEN
Q.ABBREV_TAC `constL22 = BUTFIRSTN (LENGTH a31) x2` THEN

`(x1 = constL11 ++ constL21) /\
 (x2 = constL12 ++ constL22)` by ALL_TAC THEN1 (
   UNABBREV_ALL_TAC THEN ASM_SIMP_TAC list_ss []
) THEN
ASM_REWRITE_TAC[] THEN


MP_TAC (Q.SPECL [`res_env`, `penv`, `pre1`, `name1`, `post1`, `a11`, `a21`, `a31`,
		 `ref_argL1`, `val_argL1`, `constL11`, `constL12`,
                 `pre2`, `name2`, `post2`, `a12`, `a22`, `a32`,
		 `ref_argL2`, `val_argL2`, `constL21`, `constL22`]
FASL_PROGRAM_IS_ABSTRACTION___smallfoot_parallel_proc_call) THEN

`(LENGTH constL11 = LENGTH a21) /\
 (LENGTH constL12 = LENGTH a31) /\ 
 (LENGTH constL21 = LENGTH a22) /\ 
 (LENGTH constL22 = LENGTH a32)` by ALL_TAC THEN1 (
   UNABBREV_ALL_TAC THEN
   ASM_SIMP_TAC list_ss []
) THEN

Q.PAT_ASSUM `LIST_UNROLL_GIVEN_ELEMENT_NAMES___TYPES x2 X` MP_TAC THEN
ASM_SIMP_TAC list_ss [smallfoot_prog_best_local_action_def,
   LIST_UNROLL_GIVEN_ELEMENT_NAMES___TYPES_def,
   asl_and_def, IN_ABS, CONJ_ASSOC,
   FASL_IS_LOCAL_EVAL_ENV___smallfoot_env, 
   FASL_IS_LOCAL_EVAL_XENV_def, PAIR_FORALL_THM,
   FASL_PROGRAM_IS_ABSTRACTION___quant_best_local_action2,
   ZIP_APPEND]);











val smallfoot_choose_const_best_local_action___no_quant_REWRITE =
store_thm ("smallfoot_choose_const_best_local_action___no_quant_REWRITE",
``
smallfoot_prog_best_local_action pre post =
smallfoot_choose_const_best_local_action (K pre) (K post) [] []
``,

SIMP_TAC list_ss [smallfoot_choose_const_best_local_action_def,
	          LIST_UNROLL_GIVEN_ELEMENT_NAMES_def,
	          LIST_UNROLL_GIVEN_ELEMENT_NAMES___TYPES_def,
	          IS_SEPARATION_COMBINATOR___smallfoot_separation_combinator,
		  asl_bool_REWRITES, asl_and_def, IN_ABS,
		  fasl_prog_best_local_action_def,
		  smallfoot_prog_best_local_action_def,
		  fasl_prog_quant_best_local_action_def,
		  combinTheory.K_DEF, LENGTH_NIL] THEN
SIMP_TAC (list_ss++boolSimps.CONJ_ss) [smallfoot_ap_equal___P_EXPRESSION_LIST_def,
				       IN_ABS] THEN

AP_TERM_TAC THEN AP_TERM_TAC THEN
REWRITE_TAC [FUN_EQ_THM] THEN
SIMP_TAC std_ss [quant_best_local_action_def,
		 INF_fasl_action_order_def,
		 INF_fasl_order_def,
		 IN_IMAGE, IN_ABS,
		 GSYM RIGHT_EXISTS_AND_THM,
		 GSYM LEFT_FORALL_IMP_THM,
		 PAIR_FORALL_THM] THEN
SIMP_TAC (list_ss++boolSimps.CONJ_ss) [GSYM_LENGTH_NIL] THEN
SIMP_TAC std_ss [NONE___best_local_action, IN_ABS] THEN
SIMP_TAC std_ss [COND_NONE_SOME_REWRITES_EQ] THEN
REPEAT STRIP_TAC THEN

ONCE_REWRITE_TAC[EXTENSION] THEN
FULL_SIMP_TAC std_ss [IN_BIGINTER, IN_IMAGE, IN_INTER, GSYM RIGHT_EXISTS_AND_THM,
		   IN_ABS, GSYM LEFT_FORALL_IMP_THM, IS_SOME_EXISTS] THEN
SIMP_TAC std_ss [SOME___best_local_action, IN_ABS, PAIR_FORALL_THM] THEN
METIS_TAC[]);





val smallfoot_cond_best_local_action_def =
Define `smallfoot_cond_best_local_action pre post =
        if ~(FST pre) \/ ~(FST post) then
           (fasl_prog_diverge:smallfoot_prog)
        else
	   smallfoot_prog_best_local_action (SND pre) (SND post)`





val smallfoot_cond_choose_const_best_local_action_def =
Define `smallfoot_cond_choose_const_best_local_action c pre post condL expL =
        if ~c then fasl_prog_shallow_fail else
        if ~(!arg. (FST (pre arg)) /\ (FST (post arg))) then
           (fasl_prog_diverge:smallfoot_prog)
        else
	   smallfoot_choose_const_best_local_action
	       (\arg. SND (pre arg)) (\arg. SND (post arg)) condL expL`


val smallfoot_cond_choose_const_best_local_action___INTRO =
store_thm ("smallfoot_cond_choose_const_best_local_action___INTRO",
``
!c pre post condL expL.
((~c ==> !x. (pre x = asl_false)) /\
(c ==> !x. (FST (pre' x)) /\
           (FST (post' x)) /\
           ((SND (pre' x)) = pre x)/\
           ((SND (post' x)) = post x))) ==>

(smallfoot_choose_const_best_local_action pre post condL expL =
smallfoot_cond_choose_const_best_local_action c pre' post' condL expL)``,


SIMP_TAC std_ss [smallfoot_cond_choose_const_best_local_action_def] THEN
SIMP_TAC std_ss [COND_RAND, COND_RATOR, ETA_THM] THEN
SIMP_TAC std_ss [smallfoot_choose_const_best_local_action_def,
		 asl_bool_REWRITES, fasl_prog_quant_best_local_action___false_pre,
	         prove (``(\(args,state). asl_false) = \x. asl_false``, 
                        SIMP_TAC std_ss [FUN_EQ_THM, PAIR_FORALL_THM])]);








val smallfoot_prog_best_local_action___COND_CHOOSE_REWRITE =
store_thm ("smallfoot_prog_best_local_action___COND_CHOOSE_REWRITE",
``
smallfoot_prog_best_local_action 
   (smallfoot_prop_internal_ap (wp1,rp1) d pL1 P1)
   (smallfoot_prop_internal_ap (wp2,rp2) d pL2 P2) =

(smallfoot_cond_choose_const_best_local_action
   (ALL_DISTINCT d)
   (K (smallfoot_prop_internal (EMPTY_BAG, EMPTY_BAG) (wp1, rp1) (ALL_DISTINCT d) pL1 EMPTY_BAG P1))
   (K (smallfoot_prop_internal (EMPTY_BAG, EMPTY_BAG) (wp2, rp2) (ALL_DISTINCT d) pL2 EMPTY_BAG P2))
   [] [])
``,


ONCE_REWRITE_TAC[smallfoot_choose_const_best_local_action___no_quant_REWRITE] THEN
MATCH_MP_TAC smallfoot_cond_choose_const_best_local_action___INTRO THEN
SIMP_TAC std_ss [smallfoot_prop_internal_def,
	         smallfoot_prop_internal___COND_def,
	         smallfoot_prop_internal___PROP_def,
	         BAG_ALL_DISTINCT_THM, bagTheory.NOT_IN_EMPTY_BAG,
	         asl_bool_REWRITES, ALL_DISTINCT, bagTheory.FINITE_BAG_THM,
	         smallfoot_prop_internal_ap_def]);




val smallfoot_choose_const_best_local_action___COND_CHOOSE_REWRITE =
store_thm ("smallfoot_choose_const_best_local_action___COND_CHOOSE_REWRITE",
``
smallfoot_choose_const_best_local_action
   (\args.
       (smallfoot_prop_internal_ap (wp1 args, rp1 args) 
                                   d
                                   (pL1 args)
                                   (P1 args))) 
   (\args.
       (smallfoot_prop_internal_ap (wp2 args, rp2 args) 
                                   d
                                   (pL2 args)
                                   (P2 args)))
   condL val_argL =

(smallfoot_cond_choose_const_best_local_action
   (ALL_DISTINCT d)
   (\args. smallfoot_prop_internal (EMPTY_BAG, EMPTY_BAG) (wp1 args, rp1 args) (ALL_DISTINCT d) (pL1 args) EMPTY_BAG (P1 args))
   (\args. smallfoot_prop_internal (EMPTY_BAG, EMPTY_BAG) (wp2 args, rp2 args) (ALL_DISTINCT d) (pL2 args) EMPTY_BAG (P2 args))
   condL val_argL
)
``,


MATCH_MP_TAC smallfoot_cond_choose_const_best_local_action___INTRO THEN
SIMP_TAC std_ss [smallfoot_prop_internal_def, 
                 smallfoot_prop_internal___PROP_def, 
                 smallfoot_prop_internal___COND_def, 
		 smallfoot_prop_internal_ap_def,
                 BAG_ALL_DISTINCT_THM,
		 ALL_DISTINCT, bagTheory.NOT_IN_EMPTY_BAG,
		 asl_bool_REWRITES, bagTheory.FINITE_BAG_THM]);





val smallfoot_cond_star_def = Define 
`smallfoot_cond_star P1 P2 =
 (FST P1 /\ FST P2, smallfoot_ap_star (SND P1) (SND P2))`;



val smallfoot_choose_const_best_local_action___COND_CHOOSE_REWRITE___cond_star =
store_thm ("smallfoot_choose_const_best_local_action___COND_CHOOSE_REWRITE___cond_star",
``
smallfoot_choose_const_best_local_action
   (\args.
       smallfoot_ap_star
       (smallfoot_prop_internal_ap (wp1 args, rp1 args) 
                                   d
                                   (pL1 args)
                                   (P1 args))  
       (smallfoot_prop_internal_ap (wp1' args, rp1' args) 
                                   d'
                                   (pL1' args)
                                   (P1' args))) 

   (\args.
       smallfoot_ap_star
       (smallfoot_prop_internal_ap (wp2 args, rp2 args) 
                                   d
                                   (pL2 args)
                                   (P2 args))
       (smallfoot_prop_internal_ap (wp2' args, rp2' args) 
                                   d'
                                   (pL2' args)
                                   (P2' args)))

   condL val_argL =
(smallfoot_cond_choose_const_best_local_action
   (ALL_DISTINCT d /\ ALL_DISTINCT d')
   (\args. smallfoot_cond_star 
              (smallfoot_prop_internal (EMPTY_BAG, EMPTY_BAG) (wp1 args, rp1 args) (ALL_DISTINCT d) (pL1 args) EMPTY_BAG (P1 args))
              (smallfoot_prop_internal (EMPTY_BAG, EMPTY_BAG) (wp1' args, rp1' args) (ALL_DISTINCT d') (pL1' args) EMPTY_BAG (P1' args)))

   (\args. smallfoot_cond_star 
              (smallfoot_prop_internal (EMPTY_BAG, EMPTY_BAG) (wp2 args, rp2 args) (ALL_DISTINCT d) (pL2 args) EMPTY_BAG (P2 args))
              (smallfoot_prop_internal (EMPTY_BAG, EMPTY_BAG) (wp2' args, rp2' args) (ALL_DISTINCT d') (pL2' args) EMPTY_BAG (P2' args)))

   condL val_argL
)
``,


MATCH_MP_TAC smallfoot_cond_choose_const_best_local_action___INTRO THEN
SIMP_TAC std_ss [smallfoot_prop_internal_def, 
                 smallfoot_prop_internal___COND_def,
		 smallfoot_prop_internal___PROP_def,
		 smallfoot_prop_internal_ap_def,
                 BAG_ALL_DISTINCT_THM,
		 ALL_DISTINCT, bagTheory.NOT_IN_EMPTY_BAG,
		 asl_bool_REWRITES, DISJ_IMP_THM,
	         smallfoot_cond_star_def,
                 asl_false___asl_star_THM,
		 smallfoot_ap_star_def,
	         bagTheory.FINITE_BAG_THM]);







val smallfoot_prog_while_with_invariant_REWRITE =
store_thm ("smallfoot_prog_while_with_invariant_REWRITE",
``smallfoot_prog_while_with_invariant i c prog =
  fasl_prog_while_with_invariant i c prog``,

SIMP_TAC std_ss [smallfoot_prog_while_with_invariant_def,
		 smallfoot_prog_while_def,
		 fasl_prog_while_with_invariant_def]);


val SMALLFOOT_REL_HOARE_TRIPLE___WEAKEN_PRECOND = store_thm (
"SMALLFOOT_REL_HOARE_TRIPLE___WEAKEN_PRECOND",
``!res_env penv P prog.
  SMALLFOOT_REL_HOARE_TRIPLE res_env penv asl_true prog ==>
  SMALLFOOT_REL_HOARE_TRIPLE res_env penv P prog``,

SIMP_TAC std_ss [SMALLFOOT_REL_HOARE_TRIPLE_def,
		 asl_bool_EVAL]);



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
ASM_SIMP_TAC (std_ss++boolSimps.CONJ_ss) []);




val VAR_RES_STACK___IS_EQUAL_UPTO_VALUES___REFL =
store_thm ("VAR_RES_STACK___IS_EQUAL_UPTO_VALUES___REFL",
``!st. VAR_RES_STACK___IS_EQUAL_UPTO_VALUES st st``,

SIMP_TAC (std_ss++boolSimps.CONJ_ss) [VAR_RES_STACK___IS_EQUAL_UPTO_VALUES_def]);





val VAR_RES_STACK___IS_EQUAL_UPTO_VALUES___SYM =
store_thm ("VAR_RES_STACK___IS_EQUAL_UPTO_VALUES___SYM",
``!st1 st2. VAR_RES_STACK___IS_EQUAL_UPTO_VALUES st1 st2 =
            VAR_RES_STACK___IS_EQUAL_UPTO_VALUES st2 st1``,

SIMP_TAC std_ss [VAR_RES_STACK___IS_EQUAL_UPTO_VALUES_def] THEN
METIS_TAC[]);








val SMALLFOOT_REL_HOARE_TRIPLE___prog_seq = store_thm (
"SMALLFOOT_REL_HOARE_TRIPLE___prog_seq",
``!res_env penv P prog1 prog2.
 (SMALLFOOT_REL_HOARE_TRIPLE res_env penv P prog1 /\
  SMALLFOOT_REL_HOARE_TRIPLE res_env penv asl_true prog2) ==>
  SMALLFOOT_REL_HOARE_TRIPLE res_env penv P (fasl_prog_seq prog1 prog2)``,

SIMP_TAC std_ss [SMALLFOOT_REL_HOARE_TRIPLE_def, asl_bool_EVAL,
		 SMALLFOOT_PROGRAM_SEM_def,
		 FASL_PROGRAM_SEM___prog_seq,
		 SOME___fasla_seq, GSYM RIGHT_EXISTS_AND_THM,
		 GSYM LEFT_FORALL_IMP_THM,
		 IN_BIGUNION, IN_IMAGE] THEN
REPEAT STRIP_TAC THEN
`VAR_RES_STACK___IS_EQUAL_UPTO_VALUES (FST s) (FST x')` by RES_TAC THEN

`?s1'. FASL_PROGRAM_SEM (smallfoot_env,res_env) penv prog2 x' = SOME s1'` by
   METIS_TAC[IS_SOME_EXISTS] THEN
FULL_SIMP_TAC std_ss [] THEN
`VAR_RES_STACK___IS_EQUAL_UPTO_VALUES (FST x') (FST s2)` by RES_TAC THEN
PROVE_TAC [VAR_RES_STACK___IS_EQUAL_UPTO_VALUES___TRANS]);




val SMALLFOOT_INFERENCE_prog_seq = store_thm ("SMALLFOOT_INFERENCE_prog_seq",
``!res_env penv P Q R.
         SMALLFOOT_HOARE_TRIPLE res_env penv P p1 Q /\
         SMALLFOOT_HOARE_TRIPLE res_env penv Q p2 R ==>
         SMALLFOOT_HOARE_TRIPLE res_env penv P (fasl_prog_seq p1 p2) R``,

SIMP_TAC std_ss [SMALLFOOT_HOARE_TRIPLE_REWRITE] THEN
REPEAT STRIP_TAC THENL [
   MATCH_MP_TAC FASL_INFERENCE_prog_seq THEN
   Q.EXISTS_TAC `Q` THEN
   ASM_REWRITE_TAC[],



   FULL_SIMP_TAC std_ss [SMALLFOOT_REL_HOARE_TRIPLE_def,
			 SMALLFOOT_PROGRAM_SEM_def,
			 FASL_PROGRAM_SEM___prog_seq,
			 SOME___fasla_seq,
			 GSYM RIGHT_EXISTS_AND_THM,
			 GSYM LEFT_FORALL_IMP_THM,
			 IN_BIGUNION, IN_IMAGE] THEN
   REPEAT STRIP_TAC THEN
   `VAR_RES_STACK___IS_EQUAL_UPTO_VALUES (FST s) (FST x')` by METIS_TAC[] THEN
   `x' IN Q` by ALL_TAC THEN1 (
      FULL_SIMP_TAC std_ss [FASL_PROGRAM_HOARE_TRIPLE_def, HOARE_TRIPLE_def,
			    fasl_order_THM, SUBSET_DEF] THEN
      METIS_TAC[SOME_11]
   ) THEN
   `?s1'. FASL_PROGRAM_SEM (smallfoot_env,res_env) penv p2 x' = SOME s1'` by METIS_TAC[IS_SOME_EXISTS] THEN
   FULL_SIMP_TAC std_ss [] THEN
   `VAR_RES_STACK___IS_EQUAL_UPTO_VALUES (FST x') (FST s2)` by METIS_TAC[] THEN
   PROVE_TAC [VAR_RES_STACK___IS_EQUAL_UPTO_VALUES___TRANS]
]);





val SMALLFOOT_REL_HOARE_TRIPLE___assume = store_thm (
"SMALLFOOT_REL_HOARE_TRIPLE___assume",
``!res_env penv P c.
  SMALLFOOT_REL_HOARE_TRIPLE res_env penv P (fasl_prog_prim_command (fasl_pc_assume c))``,

SIMP_TAC std_ss [SMALLFOOT_REL_HOARE_TRIPLE_def,
		 SMALLFOOT_PROGRAM_SEM_def,
		 FASL_PROGRAM_SEM___prim_command,
		 FASL_ATOMIC_ACTION_SEM_def,
		 EVAL_fasl_prim_command_THM,
		 fasla_assume_def] THEN
GEN_TAC THEN GEN_TAC THEN
Cases_on `s IN EVAL_fasl_predicate (FST smallfoot_env)
               (FST (SND smallfoot_env)) c` THENL [
   SIMP_TAC std_ss [IN_SING, VAR_RES_STACK___IS_EQUAL_UPTO_VALUES___REFL],
   SIMP_TAC std_ss [COND_NONE_SOME_REWRITES, NOT_IN_EMPTY]
]);






val SMALLFOOT_REL_HOARE_TRIPLE___kleene_star = store_thm (
"SMALLFOOT_REL_HOARE_TRIPLE___kleene_star",
``!res_env penv P prog.
  (FASL_PROGRAM_HOARE_TRIPLE (smallfoot_env,res_env) penv P prog P  /\
   SMALLFOOT_REL_HOARE_TRIPLE res_env penv P prog) ==>
  SMALLFOOT_REL_HOARE_TRIPLE res_env penv P (fasl_prog_kleene_star prog)``,


SIMP_TAC std_ss [SMALLFOOT_REL_HOARE_TRIPLE_def,
		 SMALLFOOT_PROGRAM_SEM_def,
		 FASL_PROGRAM_SEM___prog_kleene_star,
		 SUP_fasl_order_def,
		 SUP_fasl_action_order_def,
		 COND_NONE_SOME_REWRITES, IN_IMAGE,
		 GSYM RIGHT_EXISTS_AND_THM, IN_UNIV, IN_ABS,
		 IN_BIGUNION, GSYM LEFT_FORALL_IMP_THM] THEN
REPEAT GEN_TAC THEN STRIP_TAC THEN
HO_MATCH_MP_TAC (prove (``(!s n. (s IN P /\ X s n) ==> (!s2. Y s2 n s)) ==>
                       (!s. (s IN P /\ (!n. X s n)) ==> (!s2 n. Y s2 n s))``,
		       METIS_TAC[])) THEN
SIMP_TAC std_ss [NOT_NONE_IS_SOME, IS_SOME_EXISTS,
		 GSYM RIGHT_EXISTS_AND_THM,
		 GSYM LEFT_FORALL_IMP_THM] THEN
Induct_on `n` THEN1 (
   SIMP_TAC std_ss [fasl_prog_repeat_num_def,
		    FASL_PROGRAM_SEM___skip,
		    fasla_skip_def, IN_SING,
		    VAR_RES_STACK___IS_EQUAL_UPTO_VALUES___REFL]
) THEN

FULL_SIMP_TAC std_ss [fasl_prog_repeat_num_def,
		    FASL_PROGRAM_SEM_def,
		    FASL_PROGRAM_TRACES_def,
		    FASL_TRACE_SET_SEM_def,
		    SUP_fasl_action_order_def,
		    SUP_fasl_order_def,
		    COND_NONE_SOME_REWRITES,
		    FASL_PROGRAM_HOARE_TRIPLE_REWRITE,
		    IN_BIGUNION, IN_IMAGE, IN_ABS,
		    GSYM RIGHT_EXISTS_AND_THM,
		    FASL_PROTO_TRACES_EVAL_IN_THM,
		    GSYM RIGHT_FORALL_OR_THM,
    		    GSYM LEFT_FORALL_OR_THM,
		    GSYM RIGHT_EXISTS_AND_THM,
		    GSYM LEFT_EXISTS_AND_THM,
		    FASL_TRACE_SEM_APPEND,
		    NOT_NONE_IS_SOME,
		    GSYM LEFT_FORALL_IMP_THM] THEN
REPEAT STRIP_TAC THEN
`?s3. (fasla_seq (FASL_TRACE_SEM (smallfoot_env,res_env) t1)
                 (FASL_TRACE_SEM (smallfoot_env,res_env) t2) s) = SOME s3` by ALL_TAC THEN1 (
      Q.PAT_ASSUM `!pt1 pt2. X pt1 pt2` (MP_TAC o Q.SPECL [`pt1`, `pt2`, `t1`, `t2`]) THEN
      ASM_SIMP_TAC std_ss [IS_SOME_EXISTS]
) THEN
FULL_SIMP_TAC std_ss [] THEN
FULL_SIMP_TAC std_ss [SOME___fasla_seq] THEN
FULL_SIMP_TAC std_ss [IN_BIGUNION, IN_IMAGE, GSYM RIGHT_EXISTS_AND_THM] THEN
`?s'. FASL_TRACE_SEM (smallfoot_env,res_env) t2 x' = SOME s'` by ALL_TAC THEN1 (
   `IS_SOME (FASL_TRACE_SEM (smallfoot_env,res_env) t2 x')` by RES_TAC THEN
   FULL_SIMP_TAC std_ss [IS_SOME_EXISTS]
) THEN
`VAR_RES_STACK___IS_EQUAL_UPTO_VALUES (FST s) (FST x')` by ALL_TAC THEN1 (
   Q.PAT_ASSUM `!s. s IN P /\ (X s) ==> Y s` (K ALL_TAC) THEN
   Q.PAT_ASSUM `!s. s IN P /\ (X s) ==> Y s` (MP_TAC o Q.SPEC `s`) THEN
   ASM_SIMP_TAC std_ss [] THEN
   MATCH_MP_TAC (prove (``(A /\ (B ==> C)) ==> ((A ==> B) ==> C)``,
			SIMP_TAC std_ss [])) THEN
   CONJ_TAC THEN1 (
      SIMP_TAC std_ss [IS_SOME_EXISTS] THEN
      METIS_TAC[]
   ) THEN
   STRIP_TAC THEN POP_ASSUM MATCH_MP_TAC THEN
   Q.EXISTS_TAC `t1` THEN
   Q.EXISTS_TAC `pt1` THEN
   ASM_SIMP_TAC std_ss []
) THEN
`VAR_RES_STACK___IS_EQUAL_UPTO_VALUES (FST x') (FST s2)` by ALL_TAC THEN1 (
   Q.PAT_ASSUM `!s. s IN P /\ (X s) ==> Y s` (MP_TAC o Q.SPEC `x'`) THEN
   `x' IN P` by METIS_TAC[SUBSET_DEF, SOME_11] THEN
   ASM_SIMP_TAC std_ss [] THEN
   MATCH_MP_TAC (prove (``(A /\ (B ==> C)) ==> ((A ==> B) ==> C)``,
			SIMP_TAC std_ss [])) THEN
   CONJ_TAC THEN1 (
      REPEAT GEN_TAC THEN
      Q.PAT_ASSUM `!pt1 pt2 t1 t2. X pt1 pt2 t1 t2` (MP_TAC o Q.SPECL [`pt1`, `x'''`, `t1`, `x''`]) THEN
      ASM_SIMP_TAC std_ss [IS_SOME___fasla_seq, DISJ_IMP_THM]
   ) THEN
   STRIP_TAC THEN POP_ASSUM MATCH_MP_TAC THEN
   Q.EXISTS_TAC `t2` THEN
   Q.EXISTS_TAC `pt2` THEN
   ASM_SIMP_TAC std_ss []
) THEN
PROVE_TAC [VAR_RES_STACK___IS_EQUAL_UPTO_VALUES___TRANS]);








val FASL_PROGRAM_IS_ABSTRACTION___smallfoot_prog_while_with_invariant = store_thm (
"FASL_PROGRAM_IS_ABSTRACTION___smallfoot_prog_while_with_invariant",
``!res_env penv free_params qP c prog.
 (!fvL. smallfoot_ap_implies_readperms (qP fvL) (SMALLFOOT_PP_USED_VARS c)) ==>

 ((!fvL. LIST_UNROLL_GIVEN_ELEMENT_NAMES___TYPES fvL free_params ==>
 SMALLFOOT_HOARE_TRIPLE res_env penv (asl_and (qP fvL) (XEVAL_fasl_predicate smallfoot_env c)) prog (qP fvL))
 ==>

 FASL_PROGRAM_IS_ABSTRACTION (smallfoot_env,res_env) penv (smallfoot_prog_while_with_invariant (free_params, qP) c prog) 
     (smallfoot_choose_const_best_local_action (\x. qP (SND x)) 
         (\x. (asl_and (qP (SND x)) (XEVAL_fasl_predicate smallfoot_env (fasl_pred_neg c))))
         free_params []))
         ``,


REPEAT STRIP_TAC THEN
Q.ABBREV_TAC `vs = SMALLFOOT_PP_USED_VARS c` THEN
FULL_SIMP_TAC std_ss [smallfoot_prog_while_with_invariant_REWRITE,
                      smallfoot_choose_const_best_local_action_def,
                      smallfoot_prog_best_local_action_def,
                      FASL_PROGRAM_IS_ABSTRACTION___quant_best_local_action,
                      FASL_IS_LOCAL_EVAL_ENV___smallfoot_env,
		      FASL_IS_LOCAL_EVAL_XENV_def, IN_ABS,
		      pairTheory.ELIM_UNCURRY,
		      fasl_prog_while_with_invariant_def] THEN
GEN_TAC THEN
Cases_on `x` THEN
Cases_on `q` THEN
SIMP_TAC (list_ss++boolSimps.CONJ_ss) [smallfoot_ap_equal___P_EXPRESSION_LIST_def,
		  GSYM_LENGTH_NIL] THEN
Cases_on `~(LIST_UNROLL_GIVEN_ELEMENT_NAMES___TYPES r' free_params) \/
          ~(q' = [])` THEN1 (
   FULL_SIMP_TAC list_ss [asl_bool_REWRITES,
			  FASL_PROGRAM_HOARE_TRIPLE_REWRITE,
			  asl_bool_EVAL]
) THEN
FULL_SIMP_TAC std_ss [asl_bool_REWRITES] THEN
POP_ASSUM (K ALL_TAC) THEN
Q.ABBREV_TAC `P = qP r'` THEN
Q.ABBREV_TAC `Q = asl_and P (XEVAL_fasl_predicate smallfoot_env (fasl_pred_neg c))` THEN

Q.SPEC_TAC (`r`, `r`) THEN
SIMP_TAC std_ss [GSYM SMALLFOOT_HOARE_TRIPLE_def, asl_and_def, IN_ABS] THEN
FULL_SIMP_TAC std_ss [SMALLFOOT_HOARE_TRIPLE_REWRITE] THEN
Q.UNABBREV_TAC `P` THEN
Q.UNABBREV_TAC `Q` THEN
REPEAT (Q.PAT_ASSUM `!fvL. X fvL` (MP_TAC o Q.SPEC `r'`)) THEN
ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
`fasl_predicate_IS_DECIDED smallfoot_env (qP r') c` by ALL_TAC THEN1 (
   FULL_SIMP_TAC std_ss [fasl_predicate_IS_DECIDED_def,
		 GSYM fasl_predicate_IS_DECIDED_IN_STATE_def,
		 smallfoot_ap_implies_readperms_def, PAIR_FORALL_THM,
		 FASL_IS_LOCAL_EVAL_ENV___smallfoot_env,
		 IN_DEF] THEN
   REPEAT STRIP_TAC THEN
   MATCH_MP_TAC smallfoot_predicate_IS_DECIDED_IN_STATE THEN
   RES_TAC THEN
   ASM_SIMP_TAC std_ss []
) THEN
CONJ_TAC THENL [
   Q.ABBREV_TAC `xenv = (smallfoot_env,res_env)` THEN
   `smallfoot_env = FST xenv` by ALL_TAC THEN1 (
      Q.UNABBREV_TAC `xenv` THEN SIMP_TAC std_ss []
   ) THEN
   ASM_REWRITE_TAC[] THEN
   MATCH_MP_TAC FASL_INFERENCE_prog_while THEN
   Q.UNABBREV_TAC `xenv` THEN
   ASM_SIMP_TAC std_ss [FASL_IS_LOCAL_EVAL_ENV___smallfoot_env,
		        FASL_IS_LOCAL_EVAL_XENV_def],


   SIMP_TAC std_ss [fasl_prog_while_def] THEN
   MATCH_MP_TAC SMALLFOOT_REL_HOARE_TRIPLE___prog_seq THEN
   SIMP_TAC std_ss [SMALLFOOT_REL_HOARE_TRIPLE___assume] THEN
   MATCH_MP_TAC SMALLFOOT_REL_HOARE_TRIPLE___kleene_star THEN
   CONJ_TAC THENL [
      MATCH_MP_TAC FASL_INFERENCE_prog_seq THEN
      Q.EXISTS_TAC `asl_and (qP r') (XEVAL_fasl_predicate smallfoot_env c)` THEN
      ASM_REWRITE_TAC[] THEN
      Q.ABBREV_TAC `xenv = (smallfoot_env,res_env)` THEN
      `smallfoot_env = FST xenv` by ALL_TAC THEN1 (
         Q.UNABBREV_TAC `xenv` THEN SIMP_TAC std_ss []
      ) THEN
      FULL_SIMP_TAC std_ss [] THEN
      MATCH_MP_TAC FASL_INFERENCE_assume THEN
      Q.UNABBREV_TAC `xenv` THEN
      ASM_SIMP_TAC std_ss [],


      FULL_SIMP_TAC std_ss [SMALLFOOT_REL_HOARE_TRIPLE_def,
			    SMALLFOOT_PROGRAM_SEM_def, asl_bool_EVAL,
			    FASL_PROGRAM_SEM___prog_seq,
			    SOME___fasla_seq, GSYM LEFT_EXISTS_AND_THM,
			    GSYM RIGHT_EXISTS_AND_THM,
			    GSYM LEFT_FORALL_IMP_THM] THEN
      SIMP_TAC std_ss [FASL_PROGRAM_SEM___prim_command,
		       FASL_ATOMIC_ACTION_SEM_def,
		       EVAL_fasl_prim_command_THM] THEN
      SIMP_TAC std_ss [fasla_assume_def] THEN
      GEN_TAC THEN
      Tactical.REVERSE (Cases_on `s IN XEVAL_fasl_predicate smallfoot_env c`) THEN1 (
         FULL_SIMP_TAC std_ss [XEVAL_fasl_predicate_def, 
			       COND_NONE_SOME_REWRITES, NOT_IN_EMPTY,
			       IMAGE_EMPTY, BIGUNION_EMPTY]
      ) THEN
      FULL_SIMP_TAC std_ss [XEVAL_fasl_predicate_def, 
			    IN_SING, IN_BIGUNION, IN_IMAGE, IS_SOME_EXISTS,
			    GSYM RIGHT_EXISTS_AND_THM, GSYM LEFT_FORALL_IMP_THM]
   ]
]);






val smallfoot_prop_internal_ap___asl_and_XEVAL = prove (
``!c wp rp d pL P.
(asl_and (smallfoot_prop_internal_ap (wp,rp) d pL P)
        (XEVAL_fasl_predicate smallfoot_env c) =
(smallfoot_prop_internal_ap (wp,rp) d (c::pL) P))``,


SIMP_TAC list_ss [EXTENSION, asl_bool_EVAL,
		  smallfoot_prop_internal_ap_def,
		  smallfoot_prop_internal_def,
		  smallfoot_prop_internal___PROP_def,
		  bagTheory.NOT_IN_EMPTY_BAG,
		  IN_ABS] THEN
SIMP_TAC (std_ss++bool_eq_imp_ss) []);









val FASL_PROGRAM_IS_ABSTRACTION___smallfoot_prog_while_with_invariant2 = store_thm (
"FASL_PROGRAM_IS_ABSTRACTION___smallfoot_prog_while_with_invariant2",
``!res_env penv wp rp d c pL free_params P prog.
 ((SMALLFOOT_PP_USED_VARS c) SUBSET wp UNION rp) ==>
 (!fvL. LIST_UNROLL_GIVEN_ELEMENT_NAMES___TYPES fvL free_params ==>
 (SMALLFOOT_HOARE_TRIPLE res_env penv 
     (smallfoot_prop_internal_ap (wp,rp) (d fvL) (c::(pL fvL)) (P fvL)) prog 
     (smallfoot_prop_internal_ap (wp,rp) (d fvL) (pL fvL) (P fvL)))) ==>
 FASL_PROGRAM_IS_ABSTRACTION (smallfoot_env,res_env) penv 
     (smallfoot_prog_while_with_invariant 
         (free_params, 
          \fvL. smallfoot_prop_internal_ap (wp,rp) (d fvL) (pL fvL) (P fvL)) 
         c prog) 
     (smallfoot_choose_const_best_local_action 
         (\x. smallfoot_prop_internal_ap (wp,rp) (d (SND x)) (pL (SND x)) (P (SND x)))
         (\x. smallfoot_prop_internal_ap (wp,rp) (d (SND x)) ((fasl_pred_neg c)::(pL (SND x))) (P (SND x)))
     free_params [])``,



REPEAT STRIP_TAC THEN
ASM_SIMP_TAC std_ss [GSYM smallfoot_prop_internal_ap___asl_and_XEVAL] THEN
HO_MATCH_MP_TAC (REWRITE_RULE [AND_IMP_INTRO] FASL_PROGRAM_IS_ABSTRACTION___smallfoot_prog_while_with_invariant) THEN
ASM_SIMP_TAC std_ss [smallfoot_prop_internal_ap___asl_and_XEVAL] THEN


FULL_SIMP_TAC std_ss [smallfoot_ap_implies_readperms_def,
		 smallfoot_prop_internal_ap_def,
		 smallfoot_prop_internal___PROP_def,
		 asl_bool_EVAL, IN_ABS,
		 smallfoot_prop_internal_def,
		 bagTheory.NOT_IN_EMPTY_BAG, SUBSET_DEF,
		 IN_UNION, var_res_sl___has_write_permission_def,
		 var_res_sl___has_read_permission_def] THEN
METIS_TAC[]);




val FASL_PROGRAM_IS_ABSTRACTION___SEM_IMP = store_thm (
"FASL_PROGRAM_IS_ABSTRACTION___SEM_IMP",
``!res_env penv prog1 prog2.
 (FASL_PROGRAM_SEM (smallfoot_env,res_env) penv prog1 =
  FASL_PROGRAM_SEM (smallfoot_env,res_env) penv prog2) ==>

 FASL_PROGRAM_IS_ABSTRACTION (smallfoot_env,res_env) penv prog1 prog2``,

SIMP_TAC std_ss [FASL_PROGRAM_IS_ABSTRACTION_def,
		 fasl_action_order_POINTWISE_DEF] THEN
REPEAT STRIP_TAC THEN
Cases_on `FASL_PROGRAM_SEM (smallfoot_env,res_env) penv prog2 s` THEN
SIMP_TAC std_ss [fasl_order_THM, SUBSET_REFL]);





val NONE___SUP_fasl_order = store_thm ("NONE___SUP_fasl_order",
``(SUP_fasl_order M = NONE) = (NONE IN M)``,

SIMP_TAC std_ss [SUP_fasl_order_def, COND_RATOR, 
		 COND_RAND]);


val FASL_PROGRAM_SEM___fasl_prog_critical_section =
store_thm ("FASL_PROGRAM_SEM___fasl_prog_critical_section",
``!env lock_env penv l prog.
  (FASL_IS_LOCAL_EVAL_ENV env /\
  (?e t. (t IN FASL_PROTO_TRACES_EVAL penv e) /\ (e IN prog))) ==>

(
FASL_PROGRAM_SEM (env,lock_env) penv 
(fasl_prog_critical_section l prog) =
FASL_PROGRAM_SEM (env,lock_env) penv 
(fasl_prog_block [
fasl_prog_prim_command (fasl_pc_shallow_command (\f. fasla_materialisation f (lock_env l)));
prog; 
fasl_prog_prim_command (fasl_pc_shallow_command (\f. fasla_annihilation f (lock_env l)))]))``,


SIMP_TAC std_ss [fasl_prog_block_def,
		 FASL_PROGRAM_SEM___prog_seq] THEN
SIMP_TAC std_ss [fasl_prog_critical_section_def,
		 FASL_PROGRAM_SEM_def,
		 FASL_TRACE_SET_SEM_def] THEN
SIMP_TAC std_ss [IMAGE_ABS, FASL_PROGRAM_TRACES_def,
		 IN_BIGUNION, GSYM RIGHT_EXISTS_AND_THM,
		 GSYM LEFT_EXISTS_AND_THM,
		 FASL_PROTO_TRACES_EVAL_IN_THM,
		 IN_INSERT, IN_ABS,
		 FASL_TRACE_SEM_APPEND] THEN
SIMP_TAC std_ss [SUP_fasl_action_order_def,
		 SUP_fasl_order_def, IN_ABS,
		 IN_IMAGE, GSYM RIGHT_EXISTS_AND_THM,
		 NONE___fasla_seq] THEN
REPEAT STRIP_TAC THEN
ONCE_REWRITE_TAC[FUN_EQ_THM] THEN
GEN_TAC THEN SIMP_TAC std_ss [] THEN
FULL_SIMP_TAC std_ss [FASL_TRACE_SEM_REWRITE,
          	 fasla_seq_skip, FASL_ATOMIC_ACTION_SEM_def,
		 fasl_prog_prim_command_def, IN_SING,
		 FASL_PROTO_TRACES_EVAL_IN_THM,
		 EVAL_fasl_prim_command_THM,
		 fasla_materialisation_def,
		 fasla_annihilation_def,
		 best_local_action_IS_LOCAL,
		 FASL_IS_LOCAL_EVAL_ENV_THM] THEN
REWRITE_TAC [prove (``(NONE = X) = (X = NONE)``, PROVE_TAC[])] THEN
MATCH_MP_TAC (prove (``((c ==> (A1 = B)) /\
		        (~c ==> (A2 = B))) ==>
                       ((if c then A1 else A2) = B)``, METIS_TAC[])) THEN
CONJ_TAC THENL [
   SIMP_TAC std_ss [NONE___fasla_seq, IN_ABS,
		    COND_RATOR, COND_RAND,
		    IN_BIGUNION, IN_IMAGE,
		    GSYM RIGHT_EXISTS_AND_THM,
		    SOME___fasla_seq,
		    GSYM LEFT_FORALL_IMP_THM] THEN
   Cases_on `best_local_action (FST env) (asl_emp (FST env)) (lock_env l) x` THEN (
     ASM_SIMP_TAC std_ss []
   ) THEN
   REPEAT STRIP_TAC THEN
   Tactical.REVERSE (Cases_on `!e. e IN x' ==> IS_SOME (FASL_TRACE_SEM (env,lock_env) t' e)`) THEN1 (
      FULL_SIMP_TAC std_ss [] THEN
      Q.EXISTS_TAC `e''` THEN
      ASM_SIMP_TAC std_ss [GSYM LEFT_EXISTS_IMP_THM] THEN
      Q.EXISTS_TAC `t'` THEN
      Q.EXISTS_TAC `e'` THEN
      ASM_SIMP_TAC std_ss []
   ) THEN
   FULL_SIMP_TAC std_ss [] THEN
   Q.EXISTS_TAC `x''` THEN
   ASM_REWRITE_TAC[] THEN
   METIS_TAC[],



   SIMP_TAC std_ss [NONE___fasla_seq, IN_ABS,
		    COND_RATOR, COND_RAND,
		    IN_BIGUNION, IN_IMAGE,
		    GSYM RIGHT_EXISTS_AND_THM,
		    SOME___fasla_seq,
		    GSYM LEFT_FORALL_IMP_THM,
		    IS_SOME___fasla_seq] THEN
   Cases_on `best_local_action (FST env) (asl_emp (FST env)) (lock_env l) x` THEN1 (
     ASM_SIMP_TAC std_ss [] THEN
     METIS_TAC[]
   ) THEN
   ASM_SIMP_TAC std_ss [] THEN
   REPEAT STRIP_TAC THENL [
      REWRITE_TAC[NOT_NONE_IS_SOME] THEN
      METIS_TAC[],

      FULL_SIMP_TAC std_ss [IN_BIGUNION, IN_IMAGE,
			    GSYM RIGHT_EXISTS_AND_THM] THEN
      METIS_TAC[],

      ALL_TAC
   ] THEN
   ONCE_REWRITE_TAC[EXTENSION] THEN
   FULL_SIMP_TAC std_ss [IN_BIGUNION, IN_IMAGE,
			 GSYM RIGHT_EXISTS_AND_THM,
			 IN_ABS, fasla_seq_def,
			 NONE___SUP_fasl_order,
			 FORALL_AND_THM] THEN
   `?P1. !t'. (?x. (NONE = FASL_TRACE_SEM (env,lock_env) t' x) /\ x IN x') =
              P1 t'` by ALL_TAC THEN1 (
      Q.EXISTS_TAC `\t'. ?x. (NONE = FASL_TRACE_SEM (env,lock_env) t' x) /\ x IN x'` THEN
      SIMP_TAC std_ss []
   ) THEN
   `?P2. !e' t'. (t' IN FASL_PROTO_TRACES_EVAL penv e' /\ e' IN prog) =
              P2 e' t'` by ALL_TAC THEN1 (
      Q.EXISTS_TAC `\e' t'. (t' IN FASL_PROTO_TRACES_EVAL penv e' /\ e' IN prog)` THEN
      SIMP_TAC std_ss []
   ) THEN
   `!e' t'. P2 e' t' ==>  ~(P1 t')` by ALL_TAC THEN1 (
      Q.PAT_ASSUM `!e' t'. Y e' t' = P2 e' t'` (ASSUME_TAC o GSYM) THEN
      Q.PAT_ASSUM `!t'. Y t' = P1 t'` (ASSUME_TAC o GSYM) THEN
      ASM_SIMP_TAC std_ss [NOT_NONE_IS_SOME] THEN
      METIS_TAC[]
   ) THEN
   ASM_SIMP_TAC (std_ss++bool_eq_imp_ss) [COND_NONE_SOME_REWRITES] THEN


   `?P3. !x'''. (?e e'.
               (FASL_TRACE_SEM (env,lock_env) e x''' = NONE) /\
               P2 e' e) =
              P3 x'''` by ALL_TAC THEN1 (
      Q.EXISTS_TAC `\x'''. (?e e'.
               (FASL_TRACE_SEM (env,lock_env) e x''' = NONE) /\
               P2 e' e)` THEN
      SIMP_TAC std_ss []
   ) THEN
   `!x'''. (x''' IN x') ==> ~(P3 x''')` by ALL_TAC THEN1 (
      Q.PAT_ASSUM `!e e'. Y e e' = P2 e e'` (ASSUME_TAC o GSYM) THEN
      Q.PAT_ASSUM `!x'''. Y x''' = P3 x'''` (ASSUME_TAC o GSYM) THEN
      ASM_SIMP_TAC std_ss [NOT_NONE_IS_SOME] THEN
      METIS_TAC[]
   ) THEN
   ASM_SIMP_TAC (std_ss++boolSimps.CONJ_ss) [COND_NONE_SOME_REWRITES] THEN
   ASM_SIMP_TAC (std_ss++bool_eq_imp_ss) [IN_THE_COND_REWRITE] THEN


   ASM_SIMP_TAC std_ss [SUP_fasl_order_def, IN_IMAGE, IN_ABS,
		        COND_NONE_SOME_REWRITES,
		        IN_BIGUNION, IN_IMAGE, GSYM RIGHT_EXISTS_AND_THM] THEN


   `?P4. !t' x'' x'''. 
         ((NONE =  best_local_action (FST env) (lock_env l)
                     (asl_emp (FST env)) x'') /\
          x'' IN THE (FASL_TRACE_SEM (env,lock_env) t' x''') /\
          x''' IN x') =
          P4 t' x'' x'''` by ALL_TAC THEN1 (
      Q.EXISTS_TAC `\t' x'' x'''. 
         ((NONE =  best_local_action (FST env) (lock_env l)
                     (asl_emp (FST env)) x'') /\
          x'' IN THE (FASL_TRACE_SEM (env,lock_env) t' x''') /\
          x''' IN x')` THEN
      SIMP_TAC std_ss []
   ) THEN
   `!e' t' x'' x'''. P2 e' t' ==>  ~(P4 t' x'' x''')` by ALL_TAC THEN1 (
      Q.PAT_ASSUM `!e' t'. Y e' t' = P2 e' t'` (ASSUME_TAC o GSYM) THEN
      Q.PAT_ASSUM `!t' x'' x'''. Y t' x'' x''' = P4 t' x'' x'''` (ASSUME_TAC o GSYM) THEN
      METIS_TAC[]
   ) THEN
   ASM_SIMP_TAC (std_ss++bool_eq_imp_ss) [COND_NONE_SOME_REWRITES] THEN

   `?P5. !x'''. (?x' e e'.
               (best_local_action (FST env) (lock_env l) (asl_emp (FST env))
                  x' =
                NONE) /\ x' IN THE (FASL_TRACE_SEM (env,lock_env) e x''') /\
               P2 e' e) =
              P5 x'''` by ALL_TAC THEN1 (
      Q.EXISTS_TAC `\x'''. (?x' e e'.
               (best_local_action (FST env) (lock_env l) (asl_emp (FST env))
                  x' =
                NONE) /\ x' IN THE (FASL_TRACE_SEM (env,lock_env) e x''') /\
               P2 e' e)` THEN
      SIMP_TAC std_ss []
   ) THEN
   `!x'''. (x''' IN x') ==> ~(P5 x''')` by ALL_TAC THEN1 (
      Q.PAT_ASSUM `!e e'. Y e e' = P2 e e'` (ASSUME_TAC o GSYM) THEN
      Q.PAT_ASSUM `!x'''. Y x''' = P5 x'''` (ASSUME_TAC o GSYM) THEN
      METIS_TAC[]
   ) THEN
   ASM_SIMP_TAC (std_ss++boolSimps.CONJ_ss) [COND_NONE_SOME_REWRITES] THEN
   ASM_SIMP_TAC (std_ss++bool_eq_imp_ss) [IN_THE_COND_REWRITE] THEN


   ASM_SIMP_TAC std_ss [IN_ABS, IN_THE_COND_REWRITE, GSYM LEFT_EXISTS_AND_THM,
		        IN_BIGUNION, IN_IMAGE, GSYM RIGHT_EXISTS_AND_THM] THEN
   GEN_TAC THEN EQ_TAC THEN STRIP_TAC THENL [
      `~(P1 t')` by METIS_TAC[] THEN
      `!x'' x'''. ~P4 t' x'' x'''` by METIS_TAC[] THEN
      FULL_SIMP_TAC std_ss [] THEN
      Q.EXISTS_TAC `x''''` THEN
      Q.EXISTS_TAC `x'''` THEN
      Q.EXISTS_TAC `t'` THEN
      Q.EXISTS_TAC `e'` THEN
      ASM_SIMP_TAC std_ss [] THEN
      METIS_TAC[],


      Q.EXISTS_TAC `e''` THEN
      Q.EXISTS_TAC `e'` THEN
      `~(P1 e')` by METIS_TAC[] THEN
      `!x'' x'''. ~P4 e' x'' x'''` by METIS_TAC[] THEN
      ASM_SIMP_TAC std_ss [] THEN
      Q.EXISTS_TAC `x''''` THEN
      Q.EXISTS_TAC `x'''` THEN
      ASM_SIMP_TAC std_ss [] THEN
      METIS_TAC[]
  ]
]);

      







val smallfoot_prog_aquire_resource_input_def =
Define `smallfoot_prog_aquire_resource_input c wp P =
        fasl_prog_seq (
        (fasl_prog_best_local_action
	    smallfoot_ap_emp
	    (smallfoot_ap_resource_invariant wp P)):smallfoot_prog)
        (fasl_prog_prim_command (fasl_pc_assume c))`;




val smallfoot_prog_release_resource_input_def =
Define `smallfoot_prog_release_resource_input wp P =
        (fasl_prog_best_local_action
	     (smallfoot_ap_resource_invariant wp P)
	     smallfoot_ap_emp):smallfoot_prog`;



val FASL_PROGRAM_IS_ABSTRACTION___smallfoot_prog_with_resource = store_thm (
"FASL_PROGRAM_IS_ABSTRACTION___smallfoot_prog_with_resource",
``!res_env penv r c prog P.
 (res_env r = smallfoot_ap_resource_invariant wp P) ==>

 FASL_PROGRAM_IS_ABSTRACTION (smallfoot_env,res_env) penv 
      (smallfoot_prog_with_resource r c prog) 
      (smallfoot_prog_block
         [smallfoot_prog_aquire_resource_input c wp P;
          prog;
          smallfoot_prog_release_resource_input wp P])``,

REPEAT STRIP_TAC THEN
MATCH_MP_TAC FASL_PROGRAM_IS_ABSTRACTION___SEM_IMP THEN
SIMP_TAC std_ss [smallfoot_prog_with_resource_def] THEN
(fn (asm,t) =>
   MP_TAC (PART_MATCH (lhs o snd o dest_imp) (SPEC_ALL FASL_PROGRAM_SEM___fasl_prog_critical_section)
			  (lhs t)) (asm,t)) THEN
MATCH_MP_TAC (prove (``(A /\ (C = D)) ==> ((A ==> (B = C)) ==> (B = D))``,
		       SIMP_TAC std_ss [])) THEN
CONJ_TAC THEN1 (
   SIMP_TAC std_ss [FASL_IS_LOCAL_EVAL_ENV___smallfoot_env,
		    fasl_prog_seq_def, IN_INSERT, IN_ABS,
		    GSYM RIGHT_EXISTS_AND_THM,
		    GSYM LEFT_EXISTS_AND_THM,
		    FASL_PROTO_TRACES_EVAL_IN_THM] THEN
   Q.EXISTS_TAC `fasl_pt_diverge` THEN
   Q.EXISTS_TAC `fasl_pt_diverge` THEN 
   SIMP_TAC std_ss [FASL_PROTO_TRACES_EVAL_IN_THM,
		    fasl_pt_diverge_def]
) THEN


SIMP_TAC std_ss [smallfoot_prog_aquire_resource_input_def,
                 smallfoot_prog_release_resource_input_def,
		 FASL_PROGRAM_SEM___prog_seq,
		 FASL_PROGRAM_SEM___prog_block,
		 smallfoot_prog_block_def,
		 fasla_seq_skip,
		 REWRITE_RULE [ASSOC_DEF] fasla_seq___ASSOC] THEN
DEPTH_CONSEQ_CONV_TAC (K (PART_MATCH (snd o dest_imp)
(prove (``((A = A') /\ (B = B')) ==> (fasla_seq A B = fasla_seq A' B')``,
	 PROVE_TAC[])))) THEN

SIMP_TAC std_ss [smallfoot_prog_best_local_action_def,
		 fasl_prog_best_local_action_def,
		 FASL_PROGRAM_SEM___prim_command,
		 FASL_ATOMIC_ACTION_SEM_def,
		 EVAL_fasl_prim_command_THM] THEN
`IS_SEPARATION_COMBINATOR (FST (smallfoot_env))` by ALL_TAC THEN1 (
   ASSUME_TAC FASL_IS_LOCAL_EVAL_ENV___smallfoot_env THEN
   FULL_SIMP_TAC std_ss [FASL_IS_LOCAL_EVAL_ENV_THM]
) THEN
FULL_SIMP_TAC std_ss [fasla_materialisation_def,
            	     fasla_annihilation_def,
  		 best_local_action_IS_LOCAL,
		     GSYM smallfoot_ap_emp_def,
		     smallfoot_env_def]);



val SMALLFOOT_res_decls_renv_MEM_REWRITES = store_thm (
"SMALLFOOT_res_decls_renv_MEM_REWRITES",

``!res_decls r wpL P.
(ALL_DISTINCT (MAP FST res_decls) /\
(MEM (r,wpL,P) res_decls)) ==>

((SMALLFOOT_res_decls_renv res_decls) r = 
 smallfoot_ap_resource_invariant (LIST_TO_SET wpL) P)``,


Induct_on `res_decls` THEN1 (
   SIMP_TAC list_ss []
) THEN
SIMP_TAC list_ss [LEFT_AND_OVER_OR, DISJ_IMP_THM, FORALL_AND_THM] THEN
CONJ_TAC THEN1 (
   REPEAT GEN_TAC THEN STRIP_TAC THEN
   SIMP_TAC list_ss [SMALLFOOT_res_decls_renv_def,
		LET_THM,
		LISTS_TO_FMAP_def, FAPPLY_FUPDATE_THM,
		NOT_IN_EMPTY, EVERY_MEM]
) THEN
REPEAT GEN_TAC THEN STRIP_TAC THEN
`~(FST h = r)` by ALL_TAC THEN1 (
	CCONTR_TAC THEN
	FULL_SIMP_TAC std_ss [MEM_MAP] THEN
	METIS_TAC [pairTheory.FST]
) THEN
RES_TAC THEN NTAC 2 (POP_ASSUM MP_TAC) THEN
SIMP_TAC list_ss [SMALLFOOT_res_decls_renv_def, LISTS_TO_FMAP_def, FAPPLY_FUPDATE_THM, SMALLFOOT_proc_specs_spec_def, LET_THM]);








val FASL_PROGRAM_IS_ABSTRACTION___smallfoot_prog_with_resource___res_decls_renv = store_thm (
"FASL_PROGRAM_IS_ABSTRACTION___smallfoot_prog_with_resource___res_decls_renv",
``!res_decls penv r c prog wpL P.
 (ALL_DISTINCT (MAP FST res_decls) /\ MEM (r,wpL,P) res_decls) ==>

 FASL_PROGRAM_IS_ABSTRACTION (smallfoot_env,SMALLFOOT_res_decls_renv res_decls) penv 
      (smallfoot_prog_with_resource r c prog) 
      (fasl_prog_block
         [smallfoot_prog_aquire_resource_input c (LIST_TO_SET wpL) P;
          prog;
          smallfoot_prog_release_resource_input (LIST_TO_SET wpL) P])``,


REPEAT STRIP_TAC THEN
REWRITE_TAC [GSYM smallfoot_prog_block_def] THEN
MATCH_MP_TAC FASL_PROGRAM_IS_ABSTRACTION___smallfoot_prog_with_resource THEN
MATCH_MP_TAC SMALLFOOT_res_decls_renv_MEM_REWRITES THEN
ASM_REWRITE_TAC[]);



val SMALLFOOT_AE_USED_VARS_SUBSET_def = Define
`SMALLFOOT_AE_USED_VARS_SUBSET vs e =
 (IS_SOME (SMALLFOOT_AE_USED_VARS e) /\
 (THE (SMALLFOOT_AE_USED_VARS e) SUBSET vs))`;



val SMALLFOOT_AE_USED_VARS_SUBSET___REWRITE = store_thm (
"SMALLFOOT_AE_USED_VARS_SUBSET___REWRITE",
``SMALLFOOT_AE_USED_VARS_SUBSET vs e =
 ?vs'. vs' SUBSET vs /\
       SMALLFOOT_AE_USED_VARS_REL e vs'``,

SIMP_TAC (std_ss++boolSimps.CONJ_ss)
                [SMALLFOOT_AE_USED_VARS_SUBSET_def,
		 IS_SOME_EXISTS,
		 GSYM LEFT_EXISTS_AND_THM] THEN
SIMP_TAC std_ss [SMALLFOOT_AE_USED_VARS_THM] THEN
PROVE_TAC[]);



val SMALLFOOT_AE_USED_VARS_SUBSET___EVAL = store_thm ("SMALLFOOT_AE_USED_VARS_SUBSET___EVAL",
``(SMALLFOOT_AE_USED_VARS_SUBSET vs (smallfoot_ae_const c)) /\
  (SMALLFOOT_AE_USED_VARS_SUBSET vs smallfoot_ae_null) /\
  (SMALLFOOT_AE_USED_VARS_SUBSET vs (smallfoot_ae_var v) =
   v IN vs)``,

SIMP_TAC std_ss [SMALLFOOT_AE_USED_VARS_SUBSET_def,
		 SMALLFOOT_AE_USED_VARS___smallfoot_ae_const,
		 SMALLFOOT_AE_USED_VARS___smallfoot_ae_var,
		 smallfoot_ae_null_def,
		 SUBSET_DEF, IN_INSERT, NOT_IN_EMPTY]);


val IS_SOME___SMALLFOOT_AE_USED_VARS_def = Define `
IS_SOME___SMALLFOOT_AE_USED_VARS e =
IS_SOME (SMALLFOOT_AE_USED_VARS e)`



val SMALLFOOT_AE_USED_VARS_SUBSET___UNIV_REWRITE =
store_thm ("SMALLFOOT_AE_USED_VARS_SUBSET___UNIV_REWRITE",
``!e.
SMALLFOOT_AE_USED_VARS_SUBSET UNIV e =
IS_SOME___SMALLFOOT_AE_USED_VARS e``,

SIMP_TAC std_ss [IS_SOME___SMALLFOOT_AE_USED_VARS_def,
		 SMALLFOOT_AE_USED_VARS_SUBSET_def,
		 SUBSET_UNIV]);



val IS_SOME___SMALLFOOT_AE_USED_VARS___EVAL = store_thm ("IS_SOME___SMALLFOOT_AE_USED_VARS___EVAL",
``(IS_SOME___SMALLFOOT_AE_USED_VARS (smallfoot_ae_const c)) /\
  (IS_SOME___SMALLFOOT_AE_USED_VARS smallfoot_ae_null) /\
  (IS_SOME___SMALLFOOT_AE_USED_VARS (smallfoot_ae_var v))``,

SIMP_TAC std_ss [IS_SOME___SMALLFOOT_AE_USED_VARS_def,
		 SMALLFOOT_AE_USED_VARS___smallfoot_ae_const,
		 SMALLFOOT_AE_USED_VARS___smallfoot_ae_var,
		 smallfoot_ae_null_def]);


val IS_SOME___SMALLFOOT_AE_USED_VARS___REWRITE = 
store_thm("IS_SOME___SMALLFOOT_AE_USED_VARS___REWRITE",
``
IS_SOME___SMALLFOOT_AE_USED_VARS e =
?vs. SMALLFOOT_AE_USED_VARS_REL e vs``,

SIMP_TAC std_ss [IS_SOME___SMALLFOOT_AE_USED_VARS_def,
		 IS_SOME_EXISTS, SMALLFOOT_AE_USED_VARS_THM]);





val SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___points_to =
store_thm ("SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___points_to",
``!vs e1 L.
(SMALLFOOT_AE_USED_VARS_SUBSET vs e1 /\
FEVERY (\x. SMALLFOOT_AE_USED_VARS_SUBSET vs (SND x)) L) ==>

SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS vs (smallfoot_ap_points_to e1 L)``,

SIMP_TAC std_ss [SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___ALTERNATIVE_DEF,
		 IN_ABS, LET_THM,
		 smallfoot_ap_points_to_def] THEN
REPEAT GEN_TAC THEN STRIP_TAC THEN
Q.PAT_ASSUM `SMALLFOOT_AE_USED_VARS_SUBSET vs e1` (ASSUME_TAC o REWRITE_RULE [SMALLFOOT_AE_USED_VARS_SUBSET___REWRITE]) THEN
REPEAT GEN_TAC THEN STRIP_TAC THEN

FULL_SIMP_TAC std_ss [SMALLFOOT_AE_USED_VARS_REL___REWRITE] THEN
Cases_on `~(vs' SUBSET FDOM st2)` THEN1 (
   `~(vs' SUBSET FDOM st1)` by ALL_TAC THEN1 (
     FULL_SIMP_TAC std_ss [SUBSET_DEF, IN_INTER] THEN
     METIS_TAC[]
   ) THEN
   ASM_SIMP_TAC std_ss []
) THEN
Cases_on `~(vs' SUBSET FDOM st1)` THEN1 (
   FULL_SIMP_TAC std_ss [SUBSET_DEF, IN_INTER] THEN
   METIS_TAC[]
) THEN
FULL_SIMP_TAC std_ss [] THEN
`e1 st2 = e1 st1` by ALL_TAC THEN1 (
   Q.PAT_ASSUM `!st1 st2. X st1 st2` MATCH_MP_TAC THEN
   FULL_SIMP_TAC std_ss [VAR_RES_STACK___IS_EQUAL_UPTO_PERMISSIONS_def,
			 SUBSET_DEF]
) THEN
ASM_SIMP_TAC std_ss [] THEN
`?n. (e1 st1 = SOME n)` by ALL_TAC THEN1 (
   `IS_SOME (e1 st1)` by PROVE_TAC[] THEN
   FULL_SIMP_TAC std_ss [IS_SOME_EXISTS]
) THEN
Cases_on `n = 0` THEN ASM_SIMP_TAC std_ss [] THEN
SIMP_TAC std_ss [GSYM FORALL_AND_THM] THEN
GEN_TAC THEN
Cases_on `FDOM h = {n}` THEN ASM_REWRITE_TAC[] THEN
Q.PAT_ASSUM `FEVERY X L` MP_TAC THEN
Q.SPEC_TAC (`L`, `L`) THEN

HO_MATCH_MP_TAC fmap_INDUCT THEN
SIMP_TAC std_ss [FEVERY_FEMPTY, FEVERY_FUPDATE,
  		 NOT_FDOM_DRESTRICT] THEN
GEN_TAC THEN STRIP_TAC THEN
POP_ASSUM (K ALL_TAC) THEN
REPEAT GEN_TAC THEN STRIP_TAC THEN
STRIP_TAC THEN
FULL_SIMP_TAC std_ss [SMALLFOOT_AE_USED_VARS_SUBSET___REWRITE,
		      SMALLFOOT_AE_USED_VARS_REL___REWRITE] THEN
Cases_on `~(vs'' SUBSET FDOM st2)` THEN1 (
   `~(vs'' SUBSET FDOM st1)` by ALL_TAC THEN1 (
     FULL_SIMP_TAC std_ss [SUBSET_DEF, IN_INTER] THEN
     METIS_TAC[]
   ) THEN
   ASM_SIMP_TAC std_ss []
) THEN
Cases_on `~(vs'' SUBSET FDOM st1)` THEN1 (
   FULL_SIMP_TAC std_ss [SUBSET_DEF, IN_INTER] THEN
   METIS_TAC[]
) THEN
FULL_SIMP_TAC std_ss [] THEN
`y st2 = y st1` by ALL_TAC THEN1 (
   Q.PAT_ASSUM `!st1 st2. X st1 st2` MATCH_MP_TAC THEN
   FULL_SIMP_TAC std_ss [VAR_RES_STACK___IS_EQUAL_UPTO_PERMISSIONS_def,
			 SUBSET_DEF]
) THEN
ASM_SIMP_TAC std_ss []);




val SMALLFOOT_AP_PERMISSION_UNIMPORTANT___points_to =
store_thm ("SMALLFOOT_AP_PERMISSION_UNIMPORTANT___points_to",
``!e L.
(IS_SOME___SMALLFOOT_AE_USED_VARS e /\
FEVERY (\x. IS_SOME___SMALLFOOT_AE_USED_VARS (SND x)) L) ==>

SMALLFOOT_AP_PERMISSION_UNIMPORTANT (smallfoot_ap_points_to e L)``,

REWRITE_TAC [SMALLFOOT_AP_PERMISSION_UNIMPORTANT___ALTERNATIVE_DEF,
	     GSYM SMALLFOOT_AE_USED_VARS_SUBSET___UNIV_REWRITE,
             SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___points_to]);




val SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___compare1 = prove (
``!vs e1 e2.
(SMALLFOOT_AE_USED_VARS_SUBSET vs e1 /\
 SMALLFOOT_AE_USED_VARS_SUBSET vs e2) ==>

(
SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS vs (smallfoot_ap_equal e1 e2) /\ 
SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS vs (smallfoot_ap_unequal e1 e2) /\
SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS vs (smallfoot_ap_less e1 e2) /\
SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS vs (smallfoot_ap_lesseq e1 e2) /\
SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS vs (smallfoot_ap_weak_unequal e1 e2) /\
SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS vs (smallfoot_ap_weak_equal e1 e2) /\
SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS vs (smallfoot_ap_greater e1 e2) /\
SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS vs (smallfoot_ap_greatereq e1 e2))``,

SIMP_TAC std_ss [smallfoot_ap_greatereq_def,
		 smallfoot_ap_greater_def,
		 smallfoot_ap_equal_def,
		 smallfoot_ap_unequal_def,
		 smallfoot_ap_less_def,
		 smallfoot_ap_lesseq_def,
		 SMALLFOOT_AE_USED_VARS_SUBSET___REWRITE,
		 smallfoot_ap_weak_equal_def,
		 smallfoot_ap_weak_unequal_def,
		 GSYM SMALLFOOT_AE_USED_VARS_THM] THEN
CONSEQ_REWRITE_TAC ([],[SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___binexpression],[]) THEN
SIMP_TAC (std_ss++boolSimps.CONJ_ss) [GSYM LEFT_FORALL_IMP_THM,
				      GSYM LEFT_EXISTS_AND_THM, GSYM RIGHT_EXISTS_AND_THM] THEN
METIS_TAC[UNION_SUBSET]);



val SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___compare = save_thm (
"SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___compare",
SIMP_RULE std_ss [IMP_CONJ_THM, FORALL_AND_THM] SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___compare1);



val SMALLFOOT_AP_PERMISSION_UNIMPORTANT___compare = save_thm (
"SMALLFOOT_AP_PERMISSION_UNIMPORTANT___compare",
SIMP_RULE std_ss [IMP_CONJ_THM, FORALL_AND_THM,
		  GSYM SMALLFOOT_AP_PERMISSION_UNIMPORTANT___ALTERNATIVE_DEF,
		  SMALLFOOT_AE_USED_VARS_SUBSET___UNIV_REWRITE]
    (SPEC ``UNIV:smallfoot_var set`` SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___compare1))





val SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___or =
store_thm ("SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___or",
``!vs P1 P2.
(SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS vs P1 /\
SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS vs P2) ==>
SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS vs (asl_or P1 P2)``,

SIMP_TAC std_ss [SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___ALTERNATIVE_DEF_2,
		 asl_bool_EVAL] THEN
METIS_TAC[]);



val SMALLFOOT_AP_PERMISSION_UNIMPORTANT___or =
save_thm ("SMALLFOOT_AP_PERMISSION_UNIMPORTANT___or",

SIMP_RULE std_ss [SMALLFOOT_AE_USED_VARS_SUBSET___UNIV_REWRITE,
		  GSYM SMALLFOOT_AP_PERMISSION_UNIMPORTANT___ALTERNATIVE_DEF]
 (SPEC ``UNIV:smallfoot_var set`` SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___or)

);




val smallfoot_ap_tree_seg_num_GSYM_REWRITE = save_thm (
"smallfoot_ap_tree_seg_num_GSYM_REWRITE",
CONV_RULE GSYM_FUN_EQ_CONV (GSYM smallfoot_ap_tree_seg_num_def));









val SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___smallfoot_ap_tree_seg_num = 
store_thm ("SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___smallfoot_ap_tree_seg_num",
``
!n bal tagL startExp endExp vs.
(SMALLFOOT_AE_USED_VARS_SUBSET vs startExp /\
 SMALLFOOT_AE_USED_VARS_SUBSET vs endExp) ==>

SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS vs (
smallfoot_ap_tree_seg_num n bal tagL startExp endExp)``,
	   

Induct_on `n` THEN1 (
   SIMP_TAC std_ss [smallfoot_ap_tree_seg_num_def,
		    asl_rec_pred_num_def,
		    SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___compare]
) THEN
SIMP_TAC std_ss [smallfoot_ap_tree_seg_num_def,
		 asl_rec_pred_num_def] THEN
REPEAT STRIP_TAC THEN
MATCH_MP_TAC SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___asl_or THEN
CONJ_TAC THEN1 (
  MATCH_MP_TAC SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___asl_and THEN 
  ASM_SIMP_TAC std_ss [SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___const,
	       	       SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___compare]
) THEN
MATCH_MP_TAC SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___asl_and THEN
CONJ_TAC THEN1 (
  REWRITE_TAC [smallfoot_ap_weak_unequal_def] THEN
  MATCH_MP_TAC SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___binexpression THEN
  FULL_SIMP_TAC std_ss [SMALLFOOT_AE_USED_VARS_SUBSET___REWRITE,
		        UNION_SUBSET, GSYM SMALLFOOT_AE_USED_VARS_THM]
) THEN


SIMP_TAC (list_ss++boolSimps.CONJ_ss) [asl_choose_pred_args_def,
	             asl_exists_def, IN_ABS, asl_and_def,
		     EVERY_MEM, MEM_ZIP, GSYM LEFT_FORALL_IMP_THM,
		     EL_MAP, asl_bool_EVAL] THEN
SIMP_TAC std_ss [asl_exists___GSYM_REWRITE,
		 smallfoot_ap_tree_seg_num_GSYM_REWRITE] THEN
HO_MATCH_MP_TAC SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___asl_exists_direct THEN
GEN_TAC THEN
Tactical.REVERSE (Cases_on `((LENGTH x = LENGTH tagL) /\
            !n. n < LENGTH tagL ==> smallfoot_ae_is_const (EL n x))`) THEN1 (
   ASM_SIMP_TAC std_ss [SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___ALTERNATIVE_DEF,
			 IN_ABS]
) THEN
FULL_SIMP_TAC std_ss [IN_ABS3, GSYM smallfoot_ap_bigstar_list_def] THEN
MATCH_MP_TAC SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___bigstar_list THEN
SIMP_TAC list_ss [MEM_MAP, DISJ_IMP_THM, FORALL_AND_THM,
                  GSYM LEFT_FORALL_IMP_THM] THEN
`!n. n < LENGTH tagL ==>
     SMALLFOOT_AE_USED_VARS_SUBSET vs (EL n x)` by ALL_TAC THEN1 (
   REPEAT STRIP_TAC THEN 
   RES_TAC THEN
   FULL_SIMP_TAC std_ss [smallfoot_ae_is_const_def,
			 SMALLFOOT_AE_USED_VARS_SUBSET___EVAL]
) THEN
REPEAT STRIP_TAC THENL [
     MATCH_MP_TAC SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___points_to THEN
     ASM_SIMP_TAC std_ss [] THEN
     MATCH_MP_TAC FEVERY_LISTS_TO_FMAP THEN
     ASM_SIMP_TAC list_ss [MEM_ZIP,
			   GSYM LEFT_FORALL_IMP_THM, EL_MAP,
			   SMALLFOOT_AE_USED_VARS_SUBSET___EVAL],


     Q.PAT_ASSUM `!bal tagL. X bal tagL` MATCH_MP_TAC THEN
     FULL_SIMP_TAC std_ss [SMALLFOOT_AE_USED_VARS_SUBSET___EVAL, 
			  MEM_EL] THEN
     METIS_TAC[]
]);






val SMALLFOOT_AP_PERMISSION_UNIMPORTANT___smallfoot_ap_tree_seg_num = 
store_thm ("SMALLFOOT_AP_PERMISSION_UNIMPORTANT___smallfoot_ap_tree_seg_num",
``
!n bal tagL startExp endExp.
(IS_SOME___SMALLFOOT_AE_USED_VARS startExp /\
 IS_SOME___SMALLFOOT_AE_USED_VARS endExp) ==>

SMALLFOOT_AP_PERMISSION_UNIMPORTANT (smallfoot_ap_tree_seg_num n bal tagL startExp endExp)``,


REWRITE_TAC [SMALLFOOT_AP_PERMISSION_UNIMPORTANT___ALTERNATIVE_DEF] THEN
REPEAT STRIP_TAC THEN
MATCH_MP_TAC SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___smallfoot_ap_tree_seg_num THEN
FULL_SIMP_TAC std_ss [IS_SOME___SMALLFOOT_AE_USED_VARS_def,
	              SMALLFOOT_AE_USED_VARS_SUBSET_def, SUBSET_UNIV]);





val SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___smallfoot_ap_tree_seg = 
store_thm ("SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___smallfoot_ap_tree_seg",
``
!bal tagL startExp endExp vs.
(SMALLFOOT_AE_USED_VARS_SUBSET vs startExp /\
 SMALLFOOT_AE_USED_VARS_SUBSET vs endExp) ==>

SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS vs (
smallfoot_ap_tree_seg bal tagL startExp endExp)``,


SIMP_TAC std_ss [smallfoot_ap_tree_seg_def] THEN
REPEAT STRIP_TAC THEN
HO_MATCH_MP_TAC SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___asl_exists_direct THEN
ASM_SIMP_TAC std_ss [SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___smallfoot_ap_tree_seg_num]);






val SMALLFOOT_AP_PERMISSION_UNIMPORTANT___smallfoot_ap_tree_seg = 
store_thm ("SMALLFOOT_AP_PERMISSION_UNIMPORTANT___smallfoot_ap_tree_seg",
``
!bal tagL startExp endExp vs.
(IS_SOME___SMALLFOOT_AE_USED_VARS startExp /\
 IS_SOME___SMALLFOOT_AE_USED_VARS endExp) ==>

SMALLFOOT_AP_PERMISSION_UNIMPORTANT (smallfoot_ap_tree_seg bal tagL startExp endExp)``,


REWRITE_TAC [SMALLFOOT_AP_PERMISSION_UNIMPORTANT___ALTERNATIVE_DEF] THEN
REPEAT STRIP_TAC THEN
MATCH_MP_TAC SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___smallfoot_ap_tree_seg THEN
FULL_SIMP_TAC std_ss [IS_SOME___SMALLFOOT_AE_USED_VARS_def,
	              SMALLFOOT_AE_USED_VARS_SUBSET_def, SUBSET_UNIV]);





    


val SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___data_list_seg_num =
store_thm ("SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___data_list_seg_num",

``!vs n tl startExp data endExp.
  (SMALLFOOT_AE_USED_VARS_SUBSET vs startExp /\
  SMALLFOOT_AE_USED_VARS_SUBSET vs endExp) ==>
  SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS vs (smallfoot_ap_data_list_seg_num n tl startExp data endExp)``,


Induct_on `n` THENL [
   SIMP_TAC std_ss [smallfoot_ap_data_list_seg_num_def] THEN
   CONSEQ_HO_REWRITE_TAC ([],[SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___asl_and,
		       SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___compare],[]) THEN
   ASM_SIMP_TAC std_ss [SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___ALTERNATIVE_DEF_2,
		    IN_ABS],

   SIMP_TAC std_ss [smallfoot_ap_data_list_seg_num_def] THEN
   CONSEQ_HO_REWRITE_TAC ([],[SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___compare,
                       SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___asl_and,
		       SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___asl_exists_direct,
		       SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___star_MP,
		       SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___points_to,
		       FEVERY_STRENGTHEN_THM],[]) THEN
   ASM_SIMP_TAC std_ss [SMALLFOOT_AE_USED_VARS_SUBSET___EVAL,
                        FEVERY_DEF, FMAP_MAP_THM] THEN
   SIMP_TAC std_ss [SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___ALTERNATIVE_DEF_2,
		    IN_ABS]
]);


val SMALLFOOT_AP_PERMISSION_UNIMPORTANT___data_list_seg_num =
save_thm ("SMALLFOOT_AP_PERMISSION_UNIMPORTANT___data_list_seg_num",

SIMP_RULE std_ss [SMALLFOOT_AE_USED_VARS_SUBSET___UNIV_REWRITE,
		  GSYM SMALLFOOT_AP_PERMISSION_UNIMPORTANT___ALTERNATIVE_DEF]
 (SPEC ``UNIV:smallfoot_var set`` SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___data_list_seg_num)
);




val SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___data_list_seg =
store_thm ("SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___data_list_seg",

``!vs tl startExp data endExp.
  (SMALLFOOT_AE_USED_VARS_SUBSET vs startExp /\
  SMALLFOOT_AE_USED_VARS_SUBSET vs endExp) ==>
  SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS vs (smallfoot_ap_data_list_seg tl startExp data endExp)``,


SIMP_TAC std_ss [smallfoot_ap_data_list_seg_def] THEN
REPEAT STRIP_TAC THEN
HO_MATCH_MP_TAC SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___asl_exists_direct THEN
ASM_SIMP_TAC std_ss [SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___data_list_seg_num]);



val SMALLFOOT_AP_PERMISSION_UNIMPORTANT___data_list_seg =
save_thm ("SMALLFOOT_AP_PERMISSION_UNIMPORTANT___data_list_seg",

SIMP_RULE std_ss [SMALLFOOT_AE_USED_VARS_SUBSET___UNIV_REWRITE,
		  GSYM SMALLFOOT_AP_PERMISSION_UNIMPORTANT___ALTERNATIVE_DEF]
 (SPEC ``UNIV:smallfoot_var set`` SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___data_list_seg)

);


val SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___data_list =
store_thm ("SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___data_list",

``!vs tl startExp data.
  (SMALLFOOT_AE_USED_VARS_SUBSET vs startExp) ==>
  SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS vs (smallfoot_ap_data_list tl startExp data)``,

SIMP_TAC std_ss [smallfoot_ap_data_list_def,
		 SMALLFOOT_AE_USED_VARS_SUBSET___EVAL,
		 SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___data_list_seg]);




val SMALLFOOT_AP_PERMISSION_UNIMPORTANT___data_list =
save_thm ("SMALLFOOT_AP_PERMISSION_UNIMPORTANT___data_list",

SIMP_RULE std_ss [SMALLFOOT_AE_USED_VARS_SUBSET___UNIV_REWRITE,
		  GSYM SMALLFOOT_AP_PERMISSION_UNIMPORTANT___ALTERNATIVE_DEF]
 (SPEC ``UNIV:smallfoot_var set`` SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___data_list)

);





val SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___bintree =
store_thm ("SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___bintree",

``!vs lt rt startExp.
  (SMALLFOOT_AE_USED_VARS_SUBSET vs startExp) ==>
  SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS vs (smallfoot_ap_bintree (lt,rt) startExp)``,

SIMP_TAC std_ss [smallfoot_ap_bintree_def] THEN
REPEAT STRIP_TAC THEN
HO_MATCH_MP_TAC SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___asl_exists_direct THEN
ASM_SIMP_TAC std_ss [smallfoot_ap_bintree_num_def,
		 SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___smallfoot_ap_tree_seg_num,
	         SMALLFOOT_AE_USED_VARS_SUBSET___EVAL]);

    

val SMALLFOOT_AP_PERMISSION_UNIMPORTANT___bintree =
save_thm ("SMALLFOOT_AP_PERMISSION_UNIMPORTANT___bintree",

SIMP_RULE std_ss [SMALLFOOT_AE_USED_VARS_SUBSET___UNIV_REWRITE,
		  GSYM SMALLFOOT_AP_PERMISSION_UNIMPORTANT___ALTERNATIVE_DEF]
 (SPEC ``UNIV:smallfoot_var set`` SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___bintree)

);





val smallfoot_ap_star___PERMISSION_UNIMPORTANT =
store_thm ("smallfoot_ap_star___PERMISSION_UNIMPORTANT",

``!P1 P2.
(SMALLFOOT_AP_PERMISSION_UNIMPORTANT P1 /\
 SMALLFOOT_AP_PERMISSION_UNIMPORTANT P2) ==>

(smallfoot_ap_star P1 P2 =
\s. ?h1 h2. DISJOINT (FDOM h1) (FDOM h2) /\
            (SND s = FUNION h1 h2) /\
            (FST s, h1) IN P1 /\
            (FST s, h2) IN P2)``,


REPEAT STRIP_TAC THEN
REWRITE_TAC [EXTENSION] THEN
Cases_on `x` THEN
SIMP_TAC std_ss [smallfoot_ap_star_def,
		 asl_star_def, IN_ABS,
		 PAIR_EXISTS_THM,
		 SOME___smallfoot_separation_combinator] THEN
EQ_TAC THEN STRIP_TAC THENL [
   Q.EXISTS_TAC `x2` THEN
   Q.EXISTS_TAC `x2'` THEN
   ASM_SIMP_TAC std_ss [] THEN
   CONJ_TAC THENL [
      Q.PAT_ASSUM `SMALLFOOT_AP_PERMISSION_UNIMPORTANT P1` 
        (MATCH_MP_TAC o SIMP_RULE std_ss [SMALLFOOT_AP_PERMISSION_UNIMPORTANT___ALTERNATIVE_DEF_2]) THEN
      Q.EXISTS_TAC `(x1,x2)` THEN
      `VAR_RES_STACK_IS_SUBSTATE x1 q` by PROVE_TAC[VAR_RES_STACK_IS_SUBSTATE_INTRO] THEN
      FULL_SIMP_TAC std_ss [VAR_RES_STACK_IS_SUBSTATE_REWRITE],


      Q.PAT_ASSUM `SMALLFOOT_AP_PERMISSION_UNIMPORTANT P2` 
        (MATCH_MP_TAC o SIMP_RULE std_ss [SMALLFOOT_AP_PERMISSION_UNIMPORTANT___ALTERNATIVE_DEF_2]) THEN
      Q.EXISTS_TAC `(x1',x2')` THEN
      `VAR_RES_STACK_IS_SUBSTATE x1' q` by PROVE_TAC[VAR_RES_STACK_IS_SUBSTATE_INTRO] THEN
      FULL_SIMP_TAC std_ss [VAR_RES_STACK_IS_SUBSTATE_REWRITE]
   ],



   Q.EXISTS_TAC `VAR_RES_STACK_SPLIT1 EMPTY q` THEN
   Q.EXISTS_TAC `h1` THEN
   Q.EXISTS_TAC `VAR_RES_STACK_SPLIT2 EMPTY q` THEN
   Q.EXISTS_TAC `h2` THEN
   ASM_SIMP_TAC std_ss [VAR_RES_STACK_COMBINE___VAR_RES_STACK_SPLIT12] THEN
   CONJ_TAC THENL [
      Q.PAT_ASSUM `SMALLFOOT_AP_PERMISSION_UNIMPORTANT P1` 
        (MATCH_MP_TAC o SIMP_RULE std_ss [SMALLFOOT_AP_PERMISSION_UNIMPORTANT___ALTERNATIVE_DEF_2]) THEN
      Q.EXISTS_TAC `(q,h1)` THEN
      ASM_SIMP_TAC std_ss [VAR_RES_STACK_SPLIT12___REWRITES,
			   SUBSET_REFL],


      Q.PAT_ASSUM `SMALLFOOT_AP_PERMISSION_UNIMPORTANT P2` 
        (MATCH_MP_TAC o SIMP_RULE std_ss [SMALLFOOT_AP_PERMISSION_UNIMPORTANT___ALTERNATIVE_DEF_2]) THEN
      Q.EXISTS_TAC `(q,h2)` THEN
      ASM_SIMP_TAC std_ss [VAR_RES_STACK_SPLIT12___REWRITES,
			   SUBSET_REFL, DIFF_EMPTY, NOT_IN_EMPTY]
   ]
]);









val smallfoot_ap_star___ap_stack_true =
store_thm ("smallfoot_ap_star___ap_stack_true",
``!P.
smallfoot_ap_star smallfoot_ap_stack_true P =
\s. (?st. VAR_RES_STACK_IS_SUBSTATE st (FST s) /\
         (st, SND s) IN P)``,

ONCE_REWRITE_TAC [EXTENSION] THEN
SIMP_TAC std_ss [smallfoot_ap_star_def, IN_ABS,
		 asl_star_def,
		 smallfoot_ap_stack_true_def,
		 PAIR_FORALL_THM,
		 PAIR_EXISTS_THM,
		 SOME___smallfoot_separation_combinator,
		 FUNION_FEMPTY_1, DISJOINT_EMPTY,
		 FDOM_FEMPTY, VAR_RES_STACK_IS_SUBSTATE_def,
		 ASL_IS_SUBSTATE_def, GSYM LEFT_EXISTS_AND_THM] THEN
METIS_TAC[VAR_RES_STACK_COMBINE___IS_SEPARATION_COMBINATOR,
	  IS_SEPARATION_COMBINATOR_def, COMM_DEF]);



val smallfoot_ap_star___ap_stack_true___PERMISSION_UNIMPORTANT =
store_thm ("smallfoot_ap_star___ap_stack_true___PERMISSION_UNIMPORTANT",
``!P. SMALLFOOT_AP_PERMISSION_UNIMPORTANT P ==>
(smallfoot_ap_star smallfoot_ap_stack_true P = P)``,

ONCE_REWRITE_TAC [EXTENSION] THEN
SIMP_TAC std_ss [smallfoot_ap_star___PERMISSION_UNIMPORTANT,
		 SMALLFOOT_AP_PERMISSION_UNIMPORTANT___smallfoot_ap_stack_true] THEN
SIMP_TAC std_ss [IN_ABS, smallfoot_ap_stack_true_def, FDOM_FEMPTY,
		 DISJOINT_EMPTY, FUNION_FEMPTY_1]);



val smallfoot_ap_star___ap_stack_true___IDEM =
store_thm ("smallfoot_ap_star___ap_stack_true___IDEM",
``
smallfoot_ap_star smallfoot_ap_stack_true smallfoot_ap_stack_true =
smallfoot_ap_stack_true``,

SIMP_TAC std_ss [smallfoot_ap_star___ap_stack_true___PERMISSION_UNIMPORTANT,
		 SMALLFOOT_AP_PERMISSION_UNIMPORTANT___smallfoot_ap_stack_true]);



val smallfoot_ap_star___ap_stack_true___IDEM2 =
store_thm ("smallfoot_ap_star___ap_stack_true___IDEM2",
``!P.
smallfoot_ap_star smallfoot_ap_stack_true 
(smallfoot_ap_star smallfoot_ap_stack_true P) =
smallfoot_ap_star smallfoot_ap_stack_true P``,

METIS_TAC[smallfoot_ap_star___PROPERTIES,
	  ASSOC_DEF, smallfoot_ap_star___ap_stack_true___IDEM]);













val SMALLFOOT_PROG_IS_RESOURCE_AND_PROCCALL_FREE_def = Define `
SMALLFOOT_PROG_IS_RESOURCE_AND_PROCCALL_FREE prog =

!res_env penv res_env' penv'.
SMALLFOOT_PROGRAM_SEM res_env  penv  prog =
SMALLFOOT_PROGRAM_SEM res_env' penv' prog`




val SMALLFOOT_PROG_IS_RESOURCE_AND_PROCCALL_FREE___SIMPLE_REWRITES =
store_thm ("SMALLFOOT_PROG_IS_RESOURCE_AND_PROCCALL_FREE___SIMPLE_REWRITES",
``SMALLFOOT_PROG_IS_RESOURCE_AND_PROCCALL_FREE 
    (smallfoot_prog_assign v e) /\

  SMALLFOOT_PROG_IS_RESOURCE_AND_PROCCALL_FREE 
    (fasl_prog_prim_command (smallfoot_pc_assume c)) /\

  SMALLFOOT_PROG_IS_RESOURCE_AND_PROCCALL_FREE 
    (fasl_prog_best_local_action P Q) /\

  SMALLFOOT_PROG_IS_RESOURCE_AND_PROCCALL_FREE 
    (fasl_prog_quant_best_local_action qP qQ) /\

  SMALLFOOT_PROG_IS_RESOURCE_AND_PROCCALL_FREE 
    (smallfoot_prog_best_local_action P Q) /\

  SMALLFOOT_PROG_IS_RESOURCE_AND_PROCCALL_FREE 
    (smallfoot_prog_field_assign e1 t e2) /\

  SMALLFOOT_PROG_IS_RESOURCE_AND_PROCCALL_FREE 
    (smallfoot_prog_field_lookup v e t) /\

  SMALLFOOT_PROG_IS_RESOURCE_AND_PROCCALL_FREE 
    (smallfoot_prog_new_var_init v e) /\

  SMALLFOOT_PROG_IS_RESOURCE_AND_PROCCALL_FREE 
    (smallfoot_prog_new_var v) /\

  SMALLFOOT_PROG_IS_RESOURCE_AND_PROCCALL_FREE 
    (smallfoot_prog_new v) /\

  SMALLFOOT_PROG_IS_RESOURCE_AND_PROCCALL_FREE 
    (smallfoot_prog_dispose e) /\

  SMALLFOOT_PROG_IS_RESOURCE_AND_PROCCALL_FREE 
    (fasl_prog_quant_best_local_action qP qQ) /\

  SMALLFOOT_PROG_IS_RESOURCE_AND_PROCCALL_FREE
    (smallfoot_prog_release_resource_input wp P) /\

  SMALLFOOT_PROG_IS_RESOURCE_AND_PROCCALL_FREE 
    fasl_prog_skip
``,


SIMP_TAC std_ss [SMALLFOOT_PROG_IS_RESOURCE_AND_PROCCALL_FREE_def,
		 SMALLFOOT_PROGRAM_SEM_def,
		 IMAGE_ABS, IN_ABS, fasl_prog_skip_def,
		 GSYM RIGHT_EXISTS_AND_THM,
		

		 smallfoot_prog_field_assign_def,
		 fasl_prog_best_local_action_def,
		 smallfoot_prog_field_lookup_def,
		 smallfoot_prog_new_var_def,
		 smallfoot_prog_new_var_init_def,
		 smallfoot_prog_dispose_def,
		 smallfoot_prog_new_def,
		 smallfoot_prog_assign_def,
		 smallfoot_prog_best_local_action_def,
                 smallfoot_prog_release_resource_input_def,
		 fasl_prog_quant_best_local_action_def,
		 FASL_PROGRAM_SEM___prim_command,
		 FASL_ATOMIC_ACTION_SEM_def,
		 FASL_PROGRAM_SEM___prog_ndet]);



val SMALLFOOT_PROG_IS_RESOURCE_AND_PROCCALL_FREE___prog_seq =
store_thm ("SMALLFOOT_PROG_IS_RESOURCE_AND_PROCCALL_FREE___prog_seq",
``SMALLFOOT_PROG_IS_RESOURCE_AND_PROCCALL_FREE prog1 /\
  SMALLFOOT_PROG_IS_RESOURCE_AND_PROCCALL_FREE prog2 ==>
  SMALLFOOT_PROG_IS_RESOURCE_AND_PROCCALL_FREE
    (fasl_prog_seq prog1 prog2)``,


SIMP_TAC std_ss [SMALLFOOT_PROG_IS_RESOURCE_AND_PROCCALL_FREE_def,
		 SMALLFOOT_PROGRAM_SEM_def,
		 FASL_PROGRAM_SEM___prog_seq] THEN
METIS_TAC[]);



val SMALLFOOT_PROG_IS_RESOURCE_AND_PROCCALL_FREE___prog_block =
store_thm ("SMALLFOOT_PROG_IS_RESOURCE_AND_PROCCALL_FREE___prog_block",
``EVERY SMALLFOOT_PROG_IS_RESOURCE_AND_PROCCALL_FREE L ==>
  SMALLFOOT_PROG_IS_RESOURCE_AND_PROCCALL_FREE
    (smallfoot_prog_block L)``,


SIMP_TAC std_ss [SMALLFOOT_PROG_IS_RESOURCE_AND_PROCCALL_FREE_def,
		 SMALLFOOT_PROGRAM_SEM_def,
		 smallfoot_prog_block_def] THEN
Induct_on `L` THEN1 (
   SIMP_TAC list_ss [fasl_prog_block_def,
		     FASL_PROGRAM_SEM___skip]
) THEN
Cases_on `L` THENL [
   SIMP_TAC list_ss [fasl_prog_block_def,
		     SMALLFOOT_PROG_IS_RESOURCE_AND_PROCCALL_FREE_def,
		     SMALLFOOT_PROGRAM_SEM_def],

   SIMP_TAC list_ss [fasl_prog_block_def,
		     SMALLFOOT_PROG_IS_RESOURCE_AND_PROCCALL_FREE_def,
		     SMALLFOOT_PROGRAM_SEM_def] THEN
   REPEAT STRIP_TAC THEN
   FULL_SIMP_TAC list_ss [SMALLFOOT_PROG_IS_RESOURCE_AND_PROCCALL_FREE_def,
			  SMALLFOOT_PROGRAM_SEM_def,
			  FASL_PROGRAM_SEM___prog_seq] THEN
   METIS_TAC[]
]);



val SMALLFOOT_PROG_IS_RESOURCE_AND_PROCCALL_FREE___prog_cond =
store_thm("SMALLFOOT_PROG_IS_RESOURCE_AND_PROCCALL_FREE___prog_cond",
``SMALLFOOT_PROG_IS_RESOURCE_AND_PROCCALL_FREE p1 /\
  SMALLFOOT_PROG_IS_RESOURCE_AND_PROCCALL_FREE p2 ==>
  SMALLFOOT_PROG_IS_RESOURCE_AND_PROCCALL_FREE
    (smallfoot_prog_cond c p1 p2)``,

SIMP_TAC std_ss [SMALLFOOT_PROG_IS_RESOURCE_AND_PROCCALL_FREE_def,
		 SMALLFOOT_PROGRAM_SEM_def,
		 smallfoot_prog_cond_def,
		 fasl_prog_cond_def,
		 FASL_PROGRAM_SEM___prog_choice,
		 FASL_PROGRAM_SEM___prog_seq,
		 FASL_PROGRAM_SEM___prim_command,
		 FASL_ATOMIC_ACTION_SEM_def] THEN
METIS_TAC[]);



val SMALLFOOT_PROG_IS_RESOURCE_AND_PROCCALL_FREE___prog_aquire_resource_input =
store_thm("SMALLFOOT_PROG_IS_RESOURCE_AND_PROCCALL_FREE___prog_aquire_resource_input",
``SMALLFOOT_PROG_IS_RESOURCE_AND_PROCCALL_FREE
    (smallfoot_prog_aquire_resource_input c wp P)``,


SIMP_TAC std_ss [smallfoot_prog_aquire_resource_input_def] THEN
MATCH_MP_TAC SMALLFOOT_PROG_IS_RESOURCE_AND_PROCCALL_FREE___prog_seq THEN
SIMP_TAC std_ss [SMALLFOOT_PROG_IS_RESOURCE_AND_PROCCALL_FREE___SIMPLE_REWRITES]);








val SMALLFOOT_PROG_IS_RESOURCE_AND_PROCCALL_FREE___prog_val_arg =
store_thm("SMALLFOOT_PROG_IS_RESOURCE_AND_PROCCALL_FREE___prog_val_arg",
``(!v. SMALLFOOT_PROG_IS_RESOURCE_AND_PROCCALL_FREE (prog v)) ==>
  SMALLFOOT_PROG_IS_RESOURCE_AND_PROCCALL_FREE
    (smallfoot_prog_val_arg prog e)``,

SIMP_TAC std_ss [SMALLFOOT_PROG_IS_RESOURCE_AND_PROCCALL_FREE_def,
		 SMALLFOOT_PROGRAM_SEM_def,
		 smallfoot_prog_val_arg_def,
		 fasl_prog_select_def,
		 fasl_prog_forall_def,
		 GSYM fasl_prog_ndet_def,
		 FASL_PROGRAM_SEM___prog_ndet,
		 IMAGE_ABS, IN_ABS,
		 GSYM RIGHT_EXISTS_AND_THM,
		 FASL_PROGRAM_SEM___prog_seq,
		 FASL_PROGRAM_SEM___prim_command,
		 smallfoot_prog_dispose_var_def,
		 smallfoot_prog_new_var_init_def,
		 FASL_ATOMIC_ACTION_SEM_def] THEN
REPEAT STRIP_TAC THEN
`!x'. (FASL_PROGRAM_SEM (smallfoot_env,res_env') penv' (prog x')) =
 (FASL_PROGRAM_SEM (smallfoot_env,res_env)  penv  (prog x'))` by METIS_TAC[] THEN
ASM_SIMP_TAC std_ss []);




val SMALLFOOT_PROG_IS_RESOURCE_AND_PROCCALL_FREE___prog_local_var =
store_thm("SMALLFOOT_PROG_IS_RESOURCE_AND_PROCCALL_FREE___prog_local_var",
``(!v. SMALLFOOT_PROG_IS_RESOURCE_AND_PROCCALL_FREE (prog v)) ==>
  SMALLFOOT_PROG_IS_RESOURCE_AND_PROCCALL_FREE
    (smallfoot_prog_local_var prog)``,

REPEAT STRIP_TAC THEN
IMP_RES_TAC SMALLFOOT_PROG_IS_RESOURCE_AND_PROCCALL_FREE___prog_val_arg THEN
FULL_SIMP_TAC std_ss [SMALLFOOT_PROG_IS_RESOURCE_AND_PROCCALL_FREE_def,
		 SMALLFOOT_PROGRAM_SEM_def,
		 smallfoot_prog_local_var_def,
		 GSYM fasl_prog_ndet_def,
		 FASL_PROGRAM_SEM___prog_ndet,
		 IMAGE_ABS, IN_ABS,
		 GSYM RIGHT_EXISTS_AND_THM] THEN
REPEAT STRIP_TAC THEN
`!e. FASL_PROGRAM_SEM (smallfoot_env,res_env) penv
              (smallfoot_prog_val_arg prog e) =
     FASL_PROGRAM_SEM (smallfoot_env,res_env') penv'
              (smallfoot_prog_val_arg prog e)` by METIS_TAC[] THEN
ASM_SIMP_TAC std_ss []);


val SMALLFOOT_PROG_IS_RESOURCE_AND_PROCCALL_FREE___smallfoot_cond_choose_const =
store_thm("SMALLFOOT_PROG_IS_RESOURCE_AND_PROCCALL_FREE___smallfoot_cond_choose_const",
``SMALLFOOT_PROG_IS_RESOURCE_AND_PROCCALL_FREE
    (smallfoot_cond_choose_const_best_local_action 
     c pre post condL expL)``,

SIMP_TAC std_ss [SMALLFOOT_PROG_IS_RESOURCE_AND_PROCCALL_FREE_def,
		smallfoot_cond_choose_const_best_local_action_def] THEN
REPEAT STRIP_TAC THEN
Tactical.REVERSE (Cases_on `c`) THEN1 (
   SIMP_TAC std_ss [SMALLFOOT_PROGRAM_SEM_def,
		    fasl_prog_shallow_fail_def,
		    FASL_PROGRAM_SEM___prim_command,
		    FASL_ATOMIC_ACTION_SEM_def]
) THEN
Cases_on `?arg. ~FST (pre arg) \/ ~FST (post arg)` THEN1 (
   ASM_SIMP_TAC std_ss [SMALLFOOT_PROGRAM_SEM_def,
		    fasl_prog_diverge_def,
		    FASL_PROGRAM_SEM___prim_command,
		    FASL_ATOMIC_ACTION_SEM_def]
) THEN
ASM_SIMP_TAC std_ss [smallfoot_choose_const_best_local_action_def,
		     fasl_prog_quant_best_local_action_def,
		     SMALLFOOT_PROGRAM_SEM_def,
		     FASL_PROGRAM_SEM___prim_command,
		     FASL_ATOMIC_ACTION_SEM_def]);



val SMALLFOOT_PROG_IS_RESOURCE_AND_PROCCALL_FREE___smallfoot_proc_call =
store_thm("SMALLFOOT_PROG_IS_RESOURCE_AND_PROCCALL_FREE___smallfoot_proc_call",
``
SMALLFOOT_PROG_IS_RESOURCE_AND_PROCCALL_FREE
  (smallfoot_proc_call_abstraction pre post (ref_argL,val_argL) condL) /\

SMALLFOOT_PROG_IS_RESOURCE_AND_PROCCALL_FREE
  (smallfoot_parallel_proc_call_abstraction pre1 post1 
           (ref_argL1,val_argL1) condL1 pre2 post2 
           (ref_argL2,val_argL2) condL2) ``,


SIMP_TAC std_ss [smallfoot_proc_call_abstraction_def,
		 smallfoot_parallel_proc_call_abstraction_def,
		 SMALLFOOT_PROG_IS_RESOURCE_AND_PROCCALL_FREE___SIMPLE_REWRITES,
		 smallfoot_choose_const_best_local_action_def]);



val SMALLFOOT_PROG_IS_RESOURCE_AND_PROCCALL_FREE_THM =
save_thm ("SMALLFOOT_PROG_IS_RESOURCE_AND_PROCCALL_FREE_THM",

LIST_CONJ [SMALLFOOT_PROG_IS_RESOURCE_AND_PROCCALL_FREE___SIMPLE_REWRITES,
	   SMALLFOOT_PROG_IS_RESOURCE_AND_PROCCALL_FREE___prog_cond,
	   SMALLFOOT_PROG_IS_RESOURCE_AND_PROCCALL_FREE___prog_block,
	   SMALLFOOT_PROG_IS_RESOURCE_AND_PROCCALL_FREE___prog_seq,
           SMALLFOOT_PROG_IS_RESOURCE_AND_PROCCALL_FREE___prog_val_arg,
           SMALLFOOT_PROG_IS_RESOURCE_AND_PROCCALL_FREE___prog_local_var,
           SMALLFOOT_PROG_IS_RESOURCE_AND_PROCCALL_FREE___smallfoot_proc_call,
	   SMALLFOOT_PROG_IS_RESOURCE_AND_PROCCALL_FREE___smallfoot_cond_choose_const]);






val SMALLFOOT_COND_HOARE_TRIPLE_INTRO = store_thm ("SMALLFOOT_COND_HOARE_TRIPLE_INTRO",
``SMALLFOOT_PROG_IS_RESOURCE_AND_PROCCALL_FREE prog ==>

  (SMALLFOOT_HOARE_TRIPLE res_env penv (smallfoot_prop_internal_ap (wp1, rp1) d pL1 P1) prog (smallfoot_prop_internal_ap (wp2, rp2) d pL2 P2) =
   SMALLFOOT_COND_HOARE_TRIPLE (smallfoot_prop_internal (EMPTY_BAG, EMPTY_BAG) (wp1, rp1) (ALL_DISTINCT d) pL1 EMPTY_BAG P1) prog 
                              (smallfoot_prop_internal (EMPTY_BAG, EMPTY_BAG) (wp2, rp2) (ALL_DISTINCT d) pL2 EMPTY_BAG P2))``,

SIMP_TAC std_ss [SMALLFOOT_COND_HOARE_TRIPLE_def,
		 smallfoot_prop_internal_ap_def,
		 smallfoot_prop_internal_def,
		 smallfoot_prop_internal___COND_def,
		 smallfoot_prop_internal___PROP_def,
		 BAG_ALL_DISTINCT_THM,
		 bagTheory.NOT_IN_EMPTY_BAG,
		 asl_bool_EVAL, IN_ABS,
		 SMALLFOOT_HOARE_TRIPLE_def,
		 FASL_PROGRAM_HOARE_TRIPLE_def,
		 SUBSET_DEF,
		 bagTheory.FINITE_EMPTY_BAG,
		 HOARE_TRIPLE_def, 
		 SMALLFOOT_PROG_IS_RESOURCE_AND_PROCCALL_FREE_def,
		 SMALLFOOT_PROGRAM_SEM_def] THEN
Cases_on `ALL_DISTINCT d` THEN ASM_REWRITE_TAC[] THEN
METIS_TAC[]);



val SMALLFOOT_COND_HOARE_TRIPLE_ABSTRACTION___INTRO = store_thm (
"SMALLFOOT_COND_HOARE_TRIPLE_ABSTRACTION___INTRO",
``
!P prog1 Q prog2.
FASL_PROGRAM_IS_ABSTRACTION (smallfoot_env, K smallfoot_ap_true) FEMPTY prog1 prog2 ==>
SMALLFOOT_COND_HOARE_TRIPLE P prog2 Q ==>
SMALLFOOT_COND_HOARE_TRIPLE P prog1 Q``,

Cases_on `P` THEN Cases_on `Q` THEN
SIMP_TAC std_ss [FASL_PROGRAM_IS_ABSTRACTION___ALTERNATIVE_DEF,
		 SMALLFOOT_COND_HOARE_TRIPLE_def,
		 SMALLFOOT_HOARE_TRIPLE_def]);













val SMALLFOOT_COND_PROP___IMP_def = Define `
SMALLFOOT_COND_PROP___IMP P1 P2 =
(!x. (FST P1 /\ x IN SND P1) ==> 
  (FST P2 /\ x IN SND P2))`;



val SMALLFOOT_COND_PROP___STRONG_IMP_def = Define `
SMALLFOOT_COND_PROP___STRONG_IMP P1 P2 =
((FST P1 ==> FST P2) /\
 (FST P1 /\ FST P2 ==> (SND P1 = SND P2)))`;





val SMALLFOOT_COND_PROP___STRONG_IMP_IMP = store_thm ("SMALLFOOT_COND_PROP___STRONG_IMP_IMP",
``!P1 P2.
SMALLFOOT_COND_PROP___STRONG_IMP P1 P2 ==>
SMALLFOOT_COND_PROP___IMP P1 P2``,

SIMP_TAC std_ss [SMALLFOOT_COND_PROP___IMP_def,
		 SMALLFOOT_COND_PROP___STRONG_IMP_def] THEN
METIS_TAC[]);





val SMALLFOOT_COND_PROP___EQUIV_def = Define `
SMALLFOOT_COND_PROP___EQUIV P1 P2 =

(SMALLFOOT_COND_PROP___IMP P1 P2 /\
SMALLFOOT_COND_PROP___IMP P2 P1)`;


val SMALLFOOT_COND_PROP___STRONG_EQUIV_def = Define `
SMALLFOOT_COND_PROP___STRONG_EQUIV P1 P2 =

(SMALLFOOT_COND_PROP___STRONG_IMP P1 P2 /\
SMALLFOOT_COND_PROP___STRONG_IMP P2 P1)`;


val SMALLFOOT_COND_PROP___STRONG_EQUIV___SYM = store_thm
("SMALLFOOT_COND_PROP___STRONG_EQUIV___SYM",

``SMALLFOOT_COND_PROP___STRONG_EQUIV P1 P2 =
  SMALLFOOT_COND_PROP___STRONG_EQUIV P2 P1``,

  SIMP_TAC std_ss [SMALLFOOT_COND_PROP___STRONG_EQUIV_def] THEN
  METIS_TAC[]
);



val SMALLFOOT_COND_PROP___EQUIV_REWRITE = 
store_thm("SMALLFOOT_COND_PROP___EQUIV_REWRITE",

``SMALLFOOT_COND_PROP___EQUIV P1 P2 =
(!x. (FST P1 /\ x IN SND P1) = (FST P2 /\ x IN SND P2))``,

SIMP_TAC std_ss [SMALLFOOT_COND_PROP___EQUIV_def,
		 SMALLFOOT_COND_PROP___IMP_def] THEN
METIS_TAC[]);




val SMALLFOOT_COND_PROP___STRONG_EQUIV_REWRITE = 
store_thm("SMALLFOOT_COND_PROP___STRONG_EQUIV_REWRITE",

``SMALLFOOT_COND_PROP___STRONG_EQUIV P1 P2 =
((FST P1 = FST P2) /\ ((FST P1 /\ FST P2) ==> (SND P1 = SND P2)))``,

SIMP_TAC std_ss [SMALLFOOT_COND_PROP___STRONG_EQUIV_def,
		 SMALLFOOT_COND_PROP___STRONG_IMP_def] THEN
METIS_TAC[]);





val SMALLFOOT_COND_PROP___STRONG_EQUIV_IMP = store_thm ("SMALLFOOT_COND_PROP___STRONG_EQUIV_IMP",
``!P1 P2.
SMALLFOOT_COND_PROP___STRONG_EQUIV P1 P2 ==>
SMALLFOOT_COND_PROP___EQUIV P1 P2
``,

SIMP_TAC std_ss [SMALLFOOT_COND_PROP___STRONG_EQUIV_REWRITE,
		 SMALLFOOT_COND_PROP___EQUIV_REWRITE] THEN
METIS_TAC[]);



val SMALLFOOT_COND_HOARE_TRIPLE___COND_PROP_IMP =
store_thm ("SMALLFOOT_COND_HOARE_TRIPLE___COND_PROP_IMP",
``
!P1 P2 prog Q.

SMALLFOOT_COND_PROP___IMP P1 P2 ==>

(SMALLFOOT_COND_HOARE_TRIPLE P2 prog Q ==>
 SMALLFOOT_COND_HOARE_TRIPLE P1 prog Q)``,


Cases_on `P1` THEN
Cases_on `P2` THEN
Cases_on `Q` THEN
SIMP_TAC std_ss [SMALLFOOT_COND_HOARE_TRIPLE_def,
		 SMALLFOOT_COND_PROP___IMP_def,
		 SMALLFOOT_HOARE_TRIPLE_def, IN_ABS,
		 FASL_PROGRAM_HOARE_TRIPLE_def,
		 HOARE_TRIPLE_def] THEN
REPEAT STRIP_TAC THEN
METIS_TAC[]);


val SMALLFOOT_COND_HOARE_TRIPLE___COND_PROP_STRONG_IMP___POST =
store_thm ("SMALLFOOT_COND_HOARE_TRIPLE___COND_PROP_STRONG_IMP___POST",
``
!P prog Q1 Q2.

SMALLFOOT_COND_PROP___STRONG_IMP Q1 Q2 ==>

(SMALLFOOT_COND_HOARE_TRIPLE P prog Q2 ==>
 SMALLFOOT_COND_HOARE_TRIPLE P prog Q1)``,


Cases_on `Q1` THEN
Cases_on `Q2` THEN
Cases_on `P` THEN
SIMP_TAC std_ss [SMALLFOOT_COND_HOARE_TRIPLE_def,
		 SMALLFOOT_COND_PROP___STRONG_IMP_def]);


val COND_PROP___STRONG_EXISTS___SMALLFOOT_COND_PROP___STRONG_IMP =
store_thm ("COND_PROP___STRONG_EXISTS___SMALLFOOT_COND_PROP___STRONG_IMP",
``
(!x. SMALLFOOT_COND_PROP___STRONG_IMP (P x) (P' x)) ==>

SMALLFOOT_COND_PROP___STRONG_IMP
(COND_PROP___STRONG_EXISTS P) 
(COND_PROP___STRONG_EXISTS P')

``,

SIMP_TAC std_ss [COND_PROP___STRONG_EXISTS_def,
		 SMALLFOOT_COND_PROP___STRONG_IMP_def]);


val smallfoot_slp_new_var___PROP_COND___COND_PROP_STRONG_EXISTS___IMP =
store_thm ("smallfoot_slp_new_var___PROP_COND___COND_PROP_STRONG_EXISTS___IMP",
``!v wpb rpb P P'.
(!x. SMALLFOOT_COND_PROP___STRONG_IMP
     (smallfoot_slp_new_var___PROP_COND v wpb rpb (P x)) (P' x)) ==>

SMALLFOOT_COND_PROP___STRONG_IMP
(smallfoot_slp_new_var___PROP_COND v wpb rpb (COND_PROP___STRONG_EXISTS P))
(COND_PROP___STRONG_EXISTS P')
``,

REWRITE_TAC[smallfoot_slp_new_var___PROP_COND___COND_PROP_STRONG_EXISTS_THM] THEN
REPEAT STRIP_TAC THEN
MATCH_MP_TAC COND_PROP___STRONG_EXISTS___SMALLFOOT_COND_PROP___STRONG_IMP THEN
ASM_SIMP_TAC std_ss []);


val SMALLFOOT_COND_HOARE_TRIPLE___COND_PROP_EQUIV =
store_thm ("SMALLFOOT_COND_HOARE_TRIPLE___COND_PROP_EQUIV",
``
!P1 P2 prog Q.

SMALLFOOT_COND_PROP___EQUIV P1 P2 ==>

(SMALLFOOT_COND_HOARE_TRIPLE P1 prog Q =
 SMALLFOOT_COND_HOARE_TRIPLE P2 prog Q)``,


METIS_TAC[SMALLFOOT_COND_HOARE_TRIPLE___COND_PROP_IMP,
	  SMALLFOOT_COND_PROP___EQUIV_def]);




val SMALLFOOT_COND_PROP___IMP___REFL = store_thm ("SMALLFOOT_COND_PROP___IMP___REFL",
``!p. SMALLFOOT_COND_PROP___IMP p p``,
SIMP_TAC std_ss [SMALLFOOT_COND_PROP___IMP_def]);


val SMALLFOOT_COND_PROP___IMP___REFL___COMPUTE = store_thm ("SMALLFOOT_COND_PROP___IMP___REFL___COMPUTE",
``!p1 p2. (p1 = p2) ==>
SMALLFOOT_COND_PROP___IMP p1 p2``,
SIMP_TAC std_ss [SMALLFOOT_COND_PROP___IMP_def]);


val SMALLFOOT_COND_PROP___IMP___TRANS = store_thm ("SMALLFOOT_COND_PROP___IMP___TRANS",
``!p1 p2 p3. SMALLFOOT_COND_PROP___IMP p1 p2 ==>
             (SMALLFOOT_COND_PROP___IMP p2 p3 ==>
             SMALLFOOT_COND_PROP___IMP p1 p3)``,
SIMP_TAC std_ss [SMALLFOOT_COND_PROP___IMP_def] THEN
METIS_TAC[]);



val SMALLFOOT_COND_PROP___EQUIV___REFL = store_thm ("SMALLFOOT_COND_PROP___EQUIV___REFL",
``!p. SMALLFOOT_COND_PROP___EQUIV p p``,
SIMP_TAC std_ss [SMALLFOOT_COND_PROP___EQUIV_def,
		 SMALLFOOT_COND_PROP___IMP___REFL]);


val SMALLFOOT_COND_PROP___EQUIV___REFL___COMPUTE = store_thm ("SMALLFOOT_COND_PROP___EQUIV___REFL___COMPUTE",
``!p1 p2. (p1 = p2) ==>
SMALLFOOT_COND_PROP___EQUIV p1 p2``,
SIMP_TAC std_ss [SMALLFOOT_COND_PROP___EQUIV___REFL]);



val SMALLFOOT_COND_PROP___EQUIV___TRANS = store_thm ("SMALLFOOT_COND_PROP___EQUIV___TRANS",
``!p1 p2 p3. SMALLFOOT_COND_PROP___EQUIV p1 p2 ==>
             (SMALLFOOT_COND_PROP___EQUIV p2 p3 ==>
             SMALLFOOT_COND_PROP___EQUIV p1 p3)``,
SIMP_TAC std_ss [SMALLFOOT_COND_PROP___EQUIV_def] THEN
METIS_TAC[SMALLFOOT_COND_PROP___IMP___TRANS]);


val SMALLFOOT_COND_PROP___EQUIV_IMP___COMPUTE = store_thm (
"SMALLFOOT_COND_PROP___EQUIV_IMP___COMPUTE",
``!p1 p2. SMALLFOOT_COND_PROP___EQUIV p1 p2 ==>
          SMALLFOOT_COND_PROP___IMP p1 p2``,
SIMP_TAC std_ss [SMALLFOOT_COND_PROP___EQUIV_def]);











val SMALLFOOT_COND_PROP___STRONG_IMP___REFL = store_thm ("SMALLFOOT_COND_PROP___STRONG_IMP___REFL",
``!p. SMALLFOOT_COND_PROP___STRONG_IMP p p``,
SIMP_TAC std_ss [SMALLFOOT_COND_PROP___STRONG_IMP_def]);


val SMALLFOOT_COND_PROP___STRONG_IMP___REFL___COMPUTE = store_thm ("SMALLFOOT_COND_PROP___STRONG_IMP___REFL___COMPUTE",
``!p1 p2. (p1 = p2) ==>
SMALLFOOT_COND_PROP___STRONG_IMP p1 p2``,
SIMP_TAC std_ss [SMALLFOOT_COND_PROP___STRONG_IMP_def]);


val SMALLFOOT_COND_PROP___STRONG_IMP___TRANS = store_thm ("SMALLFOOT_COND_PROP___STRONG_IMP___TRANS",
``!p1 p2 p3. SMALLFOOT_COND_PROP___STRONG_IMP p1 p2 ==>
             (SMALLFOOT_COND_PROP___STRONG_IMP p2 p3 ==>
             SMALLFOOT_COND_PROP___STRONG_IMP p1 p3)``,
SIMP_TAC std_ss [SMALLFOOT_COND_PROP___STRONG_IMP_def] THEN
METIS_TAC[]);




val SMALLFOOT_COND_PROP___STRONG_EQUIV___REFL = store_thm ("SMALLFOOT_COND_PROP___STRONG_EQUIV___REFL",
``!p. SMALLFOOT_COND_PROP___STRONG_EQUIV p p``,
SIMP_TAC std_ss [SMALLFOOT_COND_PROP___STRONG_EQUIV_def,
		 SMALLFOOT_COND_PROP___STRONG_IMP___REFL]);


val SMALLFOOT_COND_PROP___STRONG_EQUIV___REFL___COMPUTE = store_thm ("SMALLFOOT_COND_PROP___STRONG_EQUIV___REFL___COMPUTE",
``!p1 p2. (p1 = p2) ==>
SMALLFOOT_COND_PROP___STRONG_EQUIV p1 p2``,
SIMP_TAC std_ss [SMALLFOOT_COND_PROP___STRONG_EQUIV___REFL]);



val SMALLFOOT_COND_PROP___STRONG_EQUIV___TRANS = store_thm ("SMALLFOOT_COND_PROP___STRONG_EQUIV___TRANS",
``!p1 p2 p3. SMALLFOOT_COND_PROP___STRONG_EQUIV p1 p2 ==>
             (SMALLFOOT_COND_PROP___STRONG_EQUIV p2 p3 ==>
             SMALLFOOT_COND_PROP___STRONG_EQUIV p1 p3)``,
SIMP_TAC std_ss [SMALLFOOT_COND_PROP___STRONG_EQUIV_def] THEN
METIS_TAC[SMALLFOOT_COND_PROP___STRONG_IMP___TRANS]);


val SMALLFOOT_COND_PROP___STRONG_EQUIV_IMP___COMPUTE = store_thm (
"SMALLFOOT_COND_PROP___STRONG_EQUIV_IMP___COMPUTE",
``!p1 p2. SMALLFOOT_COND_PROP___STRONG_EQUIV p1 p2 ==>
          SMALLFOOT_COND_PROP___STRONG_IMP p1 p2``,
SIMP_TAC std_ss [SMALLFOOT_COND_PROP___STRONG_EQUIV_def]);









val cond_prop_false_def = Define `
cond_prop_false = (F, asl_false)`

val COND_PROP___EXISTS_def = Define 
`$COND_PROP___EXISTS P = (T, \s:smallfoot_state. ?x. (FST (P x)) /\
                                    s IN (SND (P x)))`

val _ = add_binder("COND_PROP___EXISTS", std_binder_precedence);




val COND_PROP___EXISTS___ELIM = store_thm ("COND_PROP___EXISTS___ELIM",
``!P. SMALLFOOT_COND_PROP___EQUIV
       (COND_PROP___EXISTS x. P) P``,

SIMP_TAC std_ss [COND_PROP___EXISTS_def,
		 SMALLFOOT_COND_PROP___EQUIV_def,
		 SMALLFOOT_COND_PROP___IMP_def, IN_ABS]);





val COND_PROP___EXISTS___COND_PROP_FALSE = store_thm ("COND_PROP___EXISTS___COND_PROP_FALSE",
``!P. SMALLFOOT_COND_PROP___EQUIV
       (COND_PROP___EXISTS x. cond_prop_false) cond_prop_false``,

SIMP_TAC std_ss [COND_PROP___EXISTS___ELIM]);






val SMALLFOOT_COND_HOARE_TRIPLE___COND_EXISTS =
store_thm ("SMALLFOOT_COND_HOARE_TRIPLE___COND_EXISTS",
``
!P prog Q.

((SMALLFOOT_COND_HOARE_TRIPLE (COND_PROP___EXISTS x. P x) prog Q) =
(!x. SMALLFOOT_COND_HOARE_TRIPLE (P x) prog Q))
``,

SIMP_TAC std_ss [COND_PROP___EXISTS_def,
		 SMALLFOOT_COND_HOARE_TRIPLE_REWRITE,
		 GSYM LEFT_EXISTS_AND_THM,
		 GSYM LEFT_FORALL_IMP_THM,
		 SMALLFOOT_HOARE_TRIPLE_def,
		 FASL_PROGRAM_HOARE_TRIPLE_def,
		 HOARE_TRIPLE_def, IN_ABS] THEN
METIS_TAC[]);








val COND_PROP___ADD_COND_def = Define 
`COND_PROP___ADD_COND c P = (c /\ FST P, (SND P):smallfoot_a_proposition)`;



val SMALLFOOT_COND_HOARE_TRIPLE___ADD_COND =
store_thm ("SMALLFOOT_COND_HOARE_TRIPLE___ADD_COND",
``
!c P prog Q.

(SMALLFOOT_COND_HOARE_TRIPLE (COND_PROP___ADD_COND c P) prog Q) =
(c ==> (SMALLFOOT_COND_HOARE_TRIPLE P prog Q))
``,

SIMP_TAC std_ss [COND_PROP___ADD_COND_def,
		 SMALLFOOT_COND_HOARE_TRIPLE_REWRITE] THEN
METIS_TAC[]);







val SMALLFOOT_COND_HOARE_TRIPLE___cond_prop_false =
store_thm ("SMALLFOOT_COND_HOARE_TRIPLE___cond_prop_false",
``
!prog Q.
SMALLFOOT_COND_HOARE_TRIPLE (cond_prop_false) prog Q
``,

SIMP_TAC std_ss [SMALLFOOT_COND_HOARE_TRIPLE_REWRITE,
		 cond_prop_false_def]);



val COND_PROP_OR_def = Define `COND_PROP_OR p1 p2 =
(FST p1 /\ FST p2, asl_or (SND p1) (SND p2))`;


val COND_PROP_OR___cond_prop_false = store_thm (
"COND_PROP_OR___cond_prop_false",
``SMALLFOOT_COND_PROP___IMP Q cond_prop_false ==>

  ((SMALLFOOT_COND_PROP___IMP (COND_PROP_OR P Q) P) /\
   (SMALLFOOT_COND_PROP___IMP (COND_PROP_OR Q P) P))``,

SIMP_TAC std_ss [COND_PROP_OR_def, cond_prop_false_def,
		 asl_bool_REWRITES,
		 SMALLFOOT_COND_PROP___IMP_def,
		 asl_bool_EVAL] THEN
METIS_TAC[]);




val SMALLFOOT_COND_HOARE_TRIPLE___COND_PROP_OR =
store_thm ("SMALLFOOT_COND_HOARE_TRIPLE___COND_PROP_OR",
``
!P1 P2 prog Q.

(SMALLFOOT_COND_HOARE_TRIPLE P1 prog Q /\
SMALLFOOT_COND_HOARE_TRIPLE P2 prog Q) ==>

SMALLFOOT_COND_HOARE_TRIPLE (COND_PROP_OR P1 P2) prog Q
``,

SIMP_TAC std_ss [SMALLFOOT_COND_HOARE_TRIPLE_REWRITE,
		 SMALLFOOT_HOARE_TRIPLE_def,
		 COND_PROP_OR_def,
		 FASL_PROGRAM_HOARE_TRIPLE_def,
		 HOARE_TRIPLE_def, IN_ABS,
		 asl_bool_EVAL] THEN
METIS_TAC[]);








val SMALLFOOT_COND_PROP___IMP___ADD_COND = store_thm ("SMALLFOOT_COND_PROP___IMP___ADD_COND",
``!p1 p2 c. SMALLFOOT_COND_PROP___IMP p1 p2 ==>
          SMALLFOOT_COND_PROP___IMP (COND_PROP___ADD_COND c p1) (COND_PROP___ADD_COND c p2)``,

SIMP_TAC std_ss [SMALLFOOT_COND_PROP___IMP_def,
		 COND_PROP___ADD_COND_def] THEN
METIS_TAC[]);


val SMALLFOOT_COND_PROP___EQUIV___ADD_COND = store_thm ("SMALLFOOT_COND_PROP___EQUIV___ADD_COND",
``!p1 p2 c. SMALLFOOT_COND_PROP___EQUIV p1 p2 ==>
          SMALLFOOT_COND_PROP___EQUIV (COND_PROP___ADD_COND c p1) (COND_PROP___ADD_COND c p2)``,

SIMP_TAC std_ss [SMALLFOOT_COND_PROP___EQUIV_def,
		 SMALLFOOT_COND_PROP___IMP___ADD_COND]);



val SMALLFOOT_COND_PROP___IMP___EXISTS = store_thm ("SMALLFOOT_COND_PROP___IMP___EXISTS",
``!p1 p2. (!x. SMALLFOOT_COND_PROP___IMP (p1 x) (p2 x)) ==>
           (SMALLFOOT_COND_PROP___IMP (COND_PROP___EXISTS x. p1 x) 
                                     (COND_PROP___EXISTS x. p2 x))``,

SIMP_TAC std_ss [COND_PROP___EXISTS_def,
		      SMALLFOOT_COND_PROP___IMP_def,
		      IN_ABS] THEN
METIS_TAC[]);



val SMALLFOOT_COND_PROP___EQUIV___EXISTS = store_thm ("SMALLFOOT_COND_PROP___EQUIV___EXISTS",
``!p1 p2. (!x. SMALLFOOT_COND_PROP___EQUIV (p1 x) (p2 x)) ==>
           (SMALLFOOT_COND_PROP___EQUIV (COND_PROP___EXISTS x. p1 x) 
                                     (COND_PROP___EXISTS x. p2 x))``,

SIMP_TAC std_ss [SMALLFOOT_COND_PROP___EQUIV_def,
		 SMALLFOOT_COND_PROP___IMP___EXISTS]);




val smallfoot_slp_new_var___PROP_COND___small_prop_THM =
store_thm ("smallfoot_slp_new_var___PROP_COND___small_prop_THM",
``SMALLFOOT_COND_PROP___STRONG_IMP


  (smallfoot_slp_new_var___PROP_COND v wpb rpb 
   (smallfoot_prop (wpb,rpb) sfb)) 
(smallfoot_prop (BAG_INSERT v wpb,rpb) sfb)``,


SIMP_TAC std_ss [smallfoot_prop___REWRITE,
		 smallfoot_slp_new_var___PROP_COND_def,
		 SMALLFOOT_COND_PROP___STRONG_IMP_def] THEN
REPEAT STRIP_TAC THENL [
   MATCH_MP_TAC smallfoot_prop___COND_VAR_INSERT THEN
   ASM_REWRITE_TAC[] THEN
   FULL_SIMP_TAC std_ss [smallfoot_prop___WEAK_COND_def,
			 bagTheory.BAG_IN_BAG_UNION,
			 bagTheory.IN_SET_OF_BAG,
			 bagTheory.BAG_IN_BAG_INSERT,
			 BAG_ALL_DISTINCT_THM,
			 IMP_CONJ_THM, FORALL_AND_THM],

   Tactical.REVERSE (`~(v IN SET_OF_BAG (BAG_UNION wpb rpb))` by ALL_TAC) THEN1 (
      PROVE_TAC[smallfoot_slp_new_var___small_prop_THM]
   ) THEN
   FULL_SIMP_TAC std_ss [bagTheory.BAG_IN_BAG_UNION,
			 bagTheory.IN_SET_OF_BAG,
			 bagTheory.BAG_IN_BAG_INSERT,
			 BAG_ALL_DISTINCT_THM,
			 smallfoot_prop___COND___REWRITE,
			 IMP_CONJ_THM, FORALL_AND_THM]
]);



    


val FASL_PROGRAM_IS_ABSTRACTION___smallfoot_cond_choose_const_best_local_action___GENERAL =
store_thm ("FASL_PROGRAM_IS_ABSTRACTION___smallfoot_cond_choose_const_best_local_action___GENERAL",
``
!res_env penv c1 c2 P1 P2 Q1 Q2 condL expL.
((c2 ==> c1) /\
 (!arg. FST (P1 arg) ==> FST (P2 arg)) /\
 (!arg. FST (Q1 arg) ==> FST (Q2 arg)) /\
 (!arg s. (FST (P1 arg) /\ FST (P2 arg) /\
          s IN SND (P2 arg)) ==> s IN SND (P1 arg)) /\
 (!arg s. (FST (Q1 arg) /\ FST (Q2 arg) /\
          s IN SND (Q1 arg)) ==> s IN SND (Q2 arg))
) ==>

FASL_PROGRAM_IS_ABSTRACTION (smallfoot_env,res_env) penv
(smallfoot_cond_choose_const_best_local_action c1 P1 Q1 condL expL)
(smallfoot_cond_choose_const_best_local_action c2 P2 Q2 condL expL)``,


SIMP_TAC std_ss [SMALLFOOT_COND_PROP___IMP_def,
		 smallfoot_cond_choose_const_best_local_action_def] THEN
REPEAT STRIP_TAC THEN
Cases_on `c2` THEN (
   FULL_SIMP_TAC std_ss [FASL_PROGRAM_IS_ABSTRACTION___shallow_fail]
) THEN
Q.ABBREV_TAC `c3 = ?arg. ~FST (P1 arg) \/ ~FST (Q1 arg)` THEN
Q.ABBREV_TAC `c4 = ?arg. ~FST (P2 arg) \/ ~FST (Q2 arg)` THEN

`c4 ==> c3` by ALL_TAC THEN1 (
   UNABBREV_ALL_TAC THEN 
   METIS_TAC[]
) THEN
Cases_on `c3` THEN1 (
   ASM_SIMP_TAC std_ss [FASL_PROGRAM_IS_ABSTRACTION_def,
		        fasl_action_order_POINTWISE_DEF,
		        FASL_PROGRAM_SEM___diverge,
		        fasla_diverge_def,
		        fasl_order_THM, EMPTY_SUBSET,
		        GSYM IS_SOME_EXISTS] THEN
   REWRITE_TAC [NONE_IS_NOT_SOME] THEN
   METIS_TAC[]
) THEN
FULL_SIMP_TAC std_ss [smallfoot_choose_const_best_local_action_def,
		      markerTheory.Abbrev_def] THEN
ASM_SIMP_TAC std_ss [FASL_PROGRAM_IS_ABSTRACTION___quant_best_local_action,
		     FASL_IS_LOCAL_EVAL_ENV___smallfoot_env,
		     FASL_IS_LOCAL_EVAL_XENV_def] THEN


Q.ABBREV_TAC `PRE1 = (\(arg,state).
		asl_and (K (LIST_UNROLL_GIVEN_ELEMENT_NAMES___TYPES (SND arg) condL))		  
                 (asl_and
                    (smallfoot_ap_equal___P_EXPRESSION_LIST expL (FST arg))
                    (asl_and (SND (P1 arg)) (\s. s = state))))` THEN

Q.ABBREV_TAC `PRE2 = (\(arg,state).
              asl_and (K (LIST_UNROLL_GIVEN_ELEMENT_NAMES___TYPES (SND arg) condL))
                 (asl_and
                    (smallfoot_ap_equal___P_EXPRESSION_LIST expL (FST arg))
                    (asl_and (SND (P2 arg)) (\s. s = state))))` THEN



Q.ABBREV_TAC `POST1 = ((\(arg,state:smallfoot_state).
            asl_and (SND (Q1 arg))
              (\s.
                 VAR_RES_STACK___IS_EQUAL_UPTO_VALUES (FST state) (FST s))))` THEN
Q.ABBREV_TAC `POST2 = ((\(arg,state:smallfoot_state).
            asl_and (SND (Q2 arg))
              (\s.
                 VAR_RES_STACK___IS_EQUAL_UPTO_VALUES (FST state) (FST s))))` THEN


Tactical.REVERSE (`(!arg. (PRE2 arg) SUBSET (PRE1 arg)) /\
		   (!arg. (POST1 arg) SUBSET (POST2 arg))` by ALL_TAC) THEN1 (

   GEN_TAC THEN
   Tactical.REVERSE (`
      FASL_PROGRAM_HOARE_TRIPLE (smallfoot_env,res_env) penv (PRE1 arg)
         (fasl_prog_quant_best_local_action PRE1 POST1) (POST1 arg)` by ALL_TAC) THEN1 (
         METIS_TAC[FASL_INFERENCE_STRENGTHEN]
   ) THEN
   `FASL_IS_LOCAL_EVAL_XENV (smallfoot_env,res_env)` by ALL_TAC THEN1 (
      SIMP_TAC std_ss [FASL_IS_LOCAL_EVAL_XENV_def,
		       FASL_IS_LOCAL_EVAL_ENV___smallfoot_env]
   ) THEN
   METIS_TAC[FASL_INFERENCE_prog_quant_best_local_action]
) THEN

UNABBREV_ALL_TAC THEN
FULL_SIMP_TAC std_ss [PAIR_FORALL_THM, SUBSET_DEF,
		 asl_bool_EVAL, IN_ABS]);







val FASL_PROGRAM_IS_ABSTRACTION___smallfoot_cond_choose_const_best_local_action =
store_thm ("FASL_PROGRAM_IS_ABSTRACTION___smallfoot_cond_choose_const_best_local_action",
``
!res_env penv c1 c2 P1 P2 Q1 Q2 condL expL.
((c2 ==> c1) /\
 (!arg. SMALLFOOT_COND_PROP___STRONG_IMP (P1 arg) (P2 arg)) /\
 (!arg. SMALLFOOT_COND_PROP___STRONG_IMP (Q1 arg) (Q2 arg))) ==>

FASL_PROGRAM_IS_ABSTRACTION (smallfoot_env,res_env) penv
(smallfoot_cond_choose_const_best_local_action c1 P1 Q1 condL expL)
(smallfoot_cond_choose_const_best_local_action c2 P2 Q2 condL expL)``,


REPEAT STRIP_TAC THEN
MATCH_MP_TAC FASL_PROGRAM_IS_ABSTRACTION___smallfoot_cond_choose_const_best_local_action___GENERAL THEN
FULL_SIMP_TAC std_ss [SMALLFOOT_COND_PROP___STRONG_IMP_def] THEN
METIS_TAC[]);


    






val asl_bigstar___BAG_UNION = store_thm ("asl_bigstar___BAG_UNION", 
``!f. IS_SEPARATION_COMBINATOR f ==>
!b1 b2.
asl_bigstar f (BAG_UNION b1 b2) =
asl_star f (asl_bigstar f b1) (asl_bigstar f b2)``,

GEN_TAC THEN STRIP_TAC THEN
GEN_TAC THEN
Tactical.REVERSE (Cases_on `FINITE_BAG b1`) THEN1 (
   ASM_SIMP_TAC std_ss [asl_bigstar_def, 
		        asl_false___asl_star_THM,
		        bagTheory.FINITE_BAG_UNION]
) THEN
POP_ASSUM MP_TAC THEN
Q.SPEC_TAC (`b1`, `b1`) THEN
HO_MATCH_MP_TAC bagTheory.FINITE_BAG_INDUCT THEN

ASM_SIMP_TAC std_ss [bagTheory.BAG_UNION_EMPTY,
		 asl_bigstar_REWRITE,
		 REWRITE_RULE [ASSOC_DEF] asl_star___PROPERTIES,
		 bagTheory.BAG_UNION_INSERT]);




val smallfoot_ap_bigstar___BAG_UNION = store_thm ("smallfoot_ap_bigstar___BAG_UNION", 
``!b1 b2.
smallfoot_ap_bigstar (BAG_UNION b1 b2) =
smallfoot_ap_star (smallfoot_ap_bigstar b1) (smallfoot_ap_bigstar b2)``,

REWRITE_TAC [smallfoot_ap_bigstar_def, smallfoot_ap_star_def] THEN
MATCH_MP_TAC asl_bigstar___BAG_UNION THEN
REWRITE_TAC [IS_SEPARATION_COMBINATOR___smallfoot_separation_combinator]);





val SMALLFOOT_COND_PROP___STRONG_IMP____smallfoot_cond_star___smallfoot_prop =
store_thm ("SMALLFOOT_COND_PROP___STRONG_IMP____smallfoot_cond_star___smallfoot_prop",
``
!wpb1 wpb2 rpb1 rpb2 sfb1 sfb2.
(BAG_DISJOINT wpb1 wpb2 /\
BAG_DISJOINT wpb1 rpb2 /\
BAG_DISJOINT wpb2 rpb1) ==>


SMALLFOOT_COND_PROP___STRONG_IMP 
(smallfoot_cond_star
   (smallfoot_prop (wpb1, rpb1) sfb1)
   (smallfoot_prop (wpb2, rpb2) sfb2))

(smallfoot_prop (BAG_UNION wpb1 wpb2,
	        BAG_MERGE rpb1 rpb2)
	       (BAG_UNION sfb1 sfb2))``,



SIMP_TAC std_ss [smallfoot_cond_star_def,
		 smallfoot_prop___REWRITE,
		 SMALLFOOT_COND_PROP___STRONG_IMP_def] THEN
REPEAT STRIP_TAC THENL [
   FULL_SIMP_TAC std_ss [smallfoot_prop___COND___REWRITE,
			 BAG_ALL_DISTINCT___BAG_UNION,
			 BAG_ALL_DISTINCT___BAG_MERGE,
			 BAG_IN_BAG_MERGE, bagTheory.BAG_IN_BAG_UNION,
			 BAG_DISJOINT___BAG_IN, DISJ_IMP_THM,
			 IMP_CONJ_THM, FORALL_AND_THM,
			 bagTheory.FINITE_BAG_UNION] THEN
   REPEAT STRIP_TAC THENL [
      PROVE_TAC[],
      PROVE_TAC[],

      MATCH_MP_TAC SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___SUBSET THEN
      Q.EXISTS_TAC `SET_OF_BAG (BAG_UNION wpb1 rpb1)` THEN
      ASM_SIMP_TAC std_ss [SUBSET_DEF, bagTheory.IN_SET_OF_BAG,
			   bagTheory.BAG_IN_BAG_UNION,
			   DISJ_IMP_THM,
			   BAG_IN_BAG_MERGE],

      MATCH_MP_TAC SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___SUBSET THEN
      Q.EXISTS_TAC `SET_OF_BAG (BAG_UNION wpb2 rpb2)` THEN
      ASM_SIMP_TAC std_ss [SUBSET_DEF, bagTheory.IN_SET_OF_BAG,
			   bagTheory.BAG_IN_BAG_UNION,
			   DISJ_IMP_THM,
			   BAG_IN_BAG_MERGE]
   ],



   ONCE_REWRITE_TAC [EXTENSION] THEN
   SIMP_TAC std_ss [smallfoot_prop___PROP___REWRITE,
		    IN_ABS] THEN
   Q.ABBREV_TAC `P1 = smallfoot_ap_star smallfoot_ap_stack_true
                         (smallfoot_ap_bigstar sfb1)` THEN
   Q.ABBREV_TAC `P2 = smallfoot_ap_star smallfoot_ap_stack_true
                         (smallfoot_ap_bigstar sfb2)` THEN
   `smallfoot_ap_star smallfoot_ap_stack_true
        (smallfoot_ap_bigstar (BAG_UNION sfb1 sfb2)) = 
    smallfoot_ap_star P1 P2` by ALL_TAC THEN1 (
      UNABBREV_ALL_TAC THEN
      SIMP_TAC std_ss [smallfoot_ap_bigstar___BAG_UNION] THEN
      REPEAT (POP_ASSUM (K ALL_TAC)) THEN
      METIS_TAC[smallfoot_ap_star___PROPERTIES, COMM_DEF, ASSOC_DEF,
	        GSYM smallfoot_ap_star___ap_stack_true___IDEM]
   ) THEN
   ASM_REWRITE_TAC[] THEN

   SIMP_TAC std_ss [smallfoot_ap_star_def, asl_star_def,
		    IN_ABS] THEN
   REPEAT STRIP_TAC THEN EQ_TAC THEN STRIP_TAC THENL [
      `SMALLFOOT_IS_SUBSTATE p x /\
       SMALLFOOT_IS_SUBSTATE q x` by PROVE_TAC[SMALLFOOT_IS_SUBSTATE_INTRO] THEN
      FULL_SIMP_TAC std_ss [BAG_IN_BAG_MERGE, bagTheory.BAG_IN_BAG_UNION,
			    SMALLFOOT_IS_SUBSTATE_def] THEN
      REPEAT STRIP_TAC THENL [
         RES_TAC THEN
         IMP_RES_TAC SMALLFOOT_STACK_WRITE_PERM___SUBSTATE,

         RES_TAC THEN
         IMP_RES_TAC SMALLFOOT_STACK_WRITE_PERM___SUBSTATE,

         RES_TAC THEN
         IMP_RES_TAC SMALLFOOT_STACK_READ_PERM___SUBSTATE,

         RES_TAC THEN
         IMP_RES_TAC SMALLFOOT_STACK_READ_PERM___SUBSTATE,


	 Q.EXISTS_TAC `p` THEN
	 Q.EXISTS_TAC `q` THEN
	 ASM_REWRITE_TAC[]
      ],


      `?p_h p_st q_h q_st x_h x_st. (p = (p_st,p_h)) /\
                                    (q = (q_st,q_h)) /\
                                    (x = (x_st,x_h))` by ALL_TAC THEN1 (
         Cases_on `p` THEN
         Cases_on `q` THEN
         Cases_on `x` THEN
         SIMP_TAC std_ss []
      ) THEN
      Q.EXISTS_TAC (`(VAR_RES_STACK_SPLIT (SET_OF_BAG wpb1) (SET_OF_BAG wpb2) x_st, p_h)`) THEN
      Q.EXISTS_TAC (`(VAR_RES_STACK_SPLIT (SET_OF_BAG wpb2) (SET_OF_BAG wpb1) x_st, q_h)`) THEN
      FULL_SIMP_TAC std_ss [SOME___smallfoot_separation_combinator,
			    VAR_RES_STACK_SPLIT___read_writes,
			    bagTheory.IN_SET_OF_BAG, BAG_IN_BAG_MERGE,
			    bagTheory.BAG_IN_BAG_UNION,
			    DISJ_IMP_THM, FORALL_AND_THM,
                            VAR_RES_STACK_COMBINE___VAR_RES_STACK_SPLIT,
			    BAG_DISJOINT___BAG_IN] THEN
      REPEAT STRIP_TAC THENL [
         Tactical.REVERSE (`(SET_OF_BAG wpb1 INTER SET_OF_BAG wpb2) = EMPTY` by ALL_TAC) THEN1 (
	   ASM_REWRITE_TAC[COMPL_EMPTY, DRESTRICT_UNIV]
	 ) THEN
	 ONCE_REWRITE_TAC[EXTENSION] THEN
	 ASM_SIMP_TAC std_ss [NOT_IN_EMPTY, IN_INTER, bagTheory.IN_SET_OF_BAG],


	 PROVE_TAC[],
	 PROVE_TAC[],
	 

	 `SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS (SET_OF_BAG (BAG_UNION wpb1 rpb1)) P1` by
            FULL_SIMP_TAC std_ss [smallfoot_prop___COND___EXPAND] THEN
	 POP_ASSUM (MATCH_MP_TAC o REWRITE_RULE [SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___ALTERNATIVE_DEF_2]) THEN
	 Q.EXISTS_TAC `(p_st,p_h)` THEN
         FULL_SIMP_TAC std_ss [PAIR_EXISTS_THM, VAR_RES_STACK_SPLIT___REWRITES,
			       bagTheory.IN_SET_OF_BAG, bagTheory.BAG_IN_BAG_UNION,
			       SOME___VAR_RES_STACK_COMBINE,
			       FMERGE_DEF, SUBSET_DEF, IN_INTER, IN_UNION,
			       IN_DIFF] THEN
	 CONJ_TAC THEN1 METIS_TAC[] THEN
         GEN_TAC THEN
	 Q.ABBREV_TAC `c = (BAG_IN v wpb1 \/ BAG_IN v rpb1)` THEN
	 REPEAT STRIP_TAC THEN
         `v IN FDOM (FMERGE VAR_RES_STACK_COMBINE___MERGE_FUNC p_st q_st)` by ASM_SIMP_TAC std_ss [IN_UNION, FMERGE_DEF] THEN
         `~(v IN SET_OF_BAG wpb2)` by METIS_TAC[bagTheory.IN_SET_OF_BAG] THEN
	 ASM_SIMP_TAC std_ss [VAR_RES_STACK_SPLIT___REWRITES,
			      FMERGE_DEF,
                              VAR_RES_STACK_COMBINE___MERGE_FUNC_def,
			      COND_REWRITES],


         PROVE_TAC[],
         PROVE_TAC[],



	 `SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS (SET_OF_BAG (BAG_UNION wpb2 rpb2)) P2` by
            FULL_SIMP_TAC std_ss [smallfoot_prop___COND___EXPAND] THEN
	 POP_ASSUM (MATCH_MP_TAC o REWRITE_RULE [SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___ALTERNATIVE_DEF_2]) THEN
	 Q.EXISTS_TAC `(q_st,q_h)` THEN
         FULL_SIMP_TAC std_ss [PAIR_EXISTS_THM, VAR_RES_STACK_SPLIT___REWRITES,
			       bagTheory.IN_SET_OF_BAG, bagTheory.BAG_IN_BAG_UNION,
			       SOME___VAR_RES_STACK_COMBINE,
			       FMERGE_DEF, SUBSET_DEF, IN_INTER, IN_UNION,
			       IN_DIFF] THEN
	 CONJ_TAC THEN1 METIS_TAC[] THEN
         GEN_TAC THEN
	 Q.ABBREV_TAC `c = (BAG_IN v wpb2 \/ BAG_IN v rpb2)` THEN
	 REPEAT STRIP_TAC THEN
         `v IN FDOM (FMERGE VAR_RES_STACK_COMBINE___MERGE_FUNC p_st q_st)` by ASM_SIMP_TAC std_ss [IN_UNION, FMERGE_DEF] THEN
         `~(v IN SET_OF_BAG wpb1)` by METIS_TAC[bagTheory.IN_SET_OF_BAG] THEN
	 ASM_SIMP_TAC std_ss [VAR_RES_STACK_SPLIT___REWRITES,
			      FMERGE_DEF,
                              VAR_RES_STACK_COMBINE___MERGE_FUNC_def,
			      COND_REWRITES] THEN
 	 STRIP_TAC THEN
	 FULL_SIMP_TAC std_ss [VAR_RES_STACK_IS_SEPARATE_def]
      ]
   ]
]);







(*

val FASL_PROGRAM_IS_ABSTRACTION___smallfoot_cond_choose_const_best_local_action___smallfoot_cond_star =
store_thm ("FASL_PROGRAM_IS_ABSTRACTION___smallfoot_cond_choose_const_best_local_action___smallfoot_cond_star",
``
!res_env penv wpb1 wpb2 rpb1 rpb2 sfb_pre1 sfb_pre2 sfb_post1 sfb_post2
 condL expL d.

(
FASL_PROGRAM_IS_ABSTRACTION (smallfoot_env,res_env) penv
(smallfoot_cond_choose_const_best_local_action 
  d
  (\args. smallfoot_cond_star
             (smallfoot_prop (wpb1,rpb1) (sfb_pre1 args))
             (smallfoot_prop (wpb2,rpb2) (sfb_pre2 args)))
  (\args. smallfoot_cond_star
             (smallfoot_prop (wpb1,rpb1) (sfb_post1 args))
             (smallfoot_prop (wpb2,rpb2) (sfb_post2 args)))
  condL expL
)

(smallfoot_cond_choose_const_best_local_action 
(d /\ BAG_DISJOINT wpb1 wpb2 /\
   BAG_DISJOINT wpb1 rpb2 /\
   BAG_DISJOINT wpb2 rpb1)
  (\args. (smallfoot_prop (BAG_UNION wpb1 wpb2, BAG_MERGE rpb1 rpb2)
	       (BAG_UNION (sfb_pre1 args) (sfb_pre2 args))))
  (\args. (smallfoot_prop (BAG_UNION wpb1 wpb2, BAG_MERGE rpb1 rpb2)
	       (BAG_UNION (sfb_post1 args) (sfb_post2 args))))
  condL expL
))``,


REPEAT STRIP_TAC THEN
Cases_on `~d \/ ~BAG_DISJOINT wpb1 wpb2 \/ ~BAG_DISJOINT wpb1 rpb2 \/
         ~BAG_DISJOINT wpb2 rpb1` THEN1 (
   FULL_SIMP_TAC std_ss [smallfoot_cond_choose_const_best_local_action_def,
			 FASL_PROGRAM_IS_ABSTRACTION___shallow_fail]
) THEN
MATCH_MP_TAC FASL_PROGRAM_IS_ABSTRACTION___smallfoot_cond_choose_const_best_local_action THEN
REPEAT STRIP_TAC THEN (
   FULL_SIMP_TAC std_ss [] THEN
   MATCH_MP_TAC SMALLFOOT_COND_PROP___STRONG_IMP____smallfoot_cond_star___smallfoot_prop THEN
   ASM_REWRITE_TAC[]
));


*)


val SMALLFOOT_COND_PROP___STRONG_EQUIV___cond_star = store_thm (
"SMALLFOOT_COND_PROP___STRONG_EQUIV___cond_star",
``!p1 p1' p2 p2'.
  (SMALLFOOT_COND_PROP___STRONG_EQUIV p1 p1' /\
  SMALLFOOT_COND_PROP___STRONG_EQUIV p2 p2') ==>

  SMALLFOOT_COND_PROP___STRONG_EQUIV 
     (smallfoot_cond_star p1 p2) (smallfoot_cond_star p1' p2')``,


SIMP_TAC std_ss [SMALLFOOT_COND_PROP___STRONG_EQUIV_REWRITE,
		 smallfoot_cond_star_def]);





val FASL_PROGRAM_IS_ABSTRACTION___smallfoot_cond_choose_const_best_local_action___smallfoot_cond_star =
store_thm ("FASL_PROGRAM_IS_ABSTRACTION___smallfoot_cond_choose_const_best_local_action___smallfoot_cond_star",
``
!res_env penv pre1 pre2 post1 post2 wpb1 wpb2 rpb1 rpb2 sfb_pre1 sfb_pre2 sfb_post1 sfb_post2
 condL expL d.

(!args. SMALLFOOT_COND_PROP___STRONG_EQUIV (pre1  args) (smallfoot_prop (wpb1,rpb1) (sfb_pre1 args))) ==>
(!args. SMALLFOOT_COND_PROP___STRONG_EQUIV (pre2  args) (smallfoot_prop (wpb2,rpb2) (sfb_pre2 args))) ==>
(!args. SMALLFOOT_COND_PROP___STRONG_EQUIV (post1 args) (smallfoot_prop (wpb1,rpb1) (sfb_post1 args))) ==>
(!args. SMALLFOOT_COND_PROP___STRONG_EQUIV (post2 args) (smallfoot_prop (wpb2,rpb2) (sfb_post2 args))) ==>

(
FASL_PROGRAM_IS_ABSTRACTION (smallfoot_env,res_env) penv
(smallfoot_cond_choose_const_best_local_action 
  d
  (\args. smallfoot_cond_star (pre1 args) (pre2 args))
  (\args. smallfoot_cond_star (post1 args) (post2 args))
  condL expL
)

(smallfoot_cond_choose_const_best_local_action 
(d /\ BAG_DISJOINT wpb1 wpb2 /\
   BAG_DISJOINT wpb1 rpb2 /\
   BAG_DISJOINT wpb2 rpb1)
  (\args. (smallfoot_prop (BAG_UNION wpb1 wpb2, BAG_MERGE rpb1 rpb2)
	       (BAG_UNION (sfb_pre1 args) (sfb_pre2 args))))
  (\args. (smallfoot_prop (BAG_UNION wpb1 wpb2, BAG_MERGE rpb1 rpb2)
	       (BAG_UNION (sfb_post1 args) (sfb_post2 args))))
  condL expL
))``,


REPEAT STRIP_TAC THEN
Cases_on `~d \/ ~BAG_DISJOINT wpb1 wpb2 \/ ~BAG_DISJOINT wpb1 rpb2 \/
         ~BAG_DISJOINT wpb2 rpb1` THEN1 (
   FULL_SIMP_TAC std_ss [smallfoot_cond_choose_const_best_local_action_def,
			 FASL_PROGRAM_IS_ABSTRACTION___shallow_fail]
) THEN
MATCH_MP_TAC FASL_PROGRAM_IS_ABSTRACTION___smallfoot_cond_choose_const_best_local_action THEN
FULL_SIMP_TAC std_ss [] THEN
REPEAT STRIP_TAC THENL [

   MATCH_MP_TAC (SIMP_RULE std_ss [AND_IMP_INTRO] SMALLFOOT_COND_PROP___STRONG_IMP___TRANS) THEN
   Q.EXISTS_TAC `smallfoot_cond_star (smallfoot_prop (wpb1,rpb1) (sfb_pre1 arg))
				     (smallfoot_prop (wpb2,rpb2) (sfb_pre2 arg))` THEN
   Tactical.REVERSE CONJ_TAC THEN1 (
      MATCH_MP_TAC SMALLFOOT_COND_PROP___STRONG_IMP____smallfoot_cond_star___smallfoot_prop THEN
      ASM_REWRITE_TAC[]
   ) THEN
   MATCH_MP_TAC SMALLFOOT_COND_PROP___STRONG_EQUIV_IMP___COMPUTE THEN
   MATCH_MP_TAC SMALLFOOT_COND_PROP___STRONG_EQUIV___cond_star THEN
   ASM_REWRITE_TAC[],



   MATCH_MP_TAC (SIMP_RULE std_ss [AND_IMP_INTRO] SMALLFOOT_COND_PROP___STRONG_IMP___TRANS) THEN
   Q.EXISTS_TAC `smallfoot_cond_star (smallfoot_prop (wpb1,rpb1) (sfb_post1 arg))
				     (smallfoot_prop (wpb2,rpb2) (sfb_post2 arg))` THEN
   Tactical.REVERSE CONJ_TAC THEN1 (
      MATCH_MP_TAC SMALLFOOT_COND_PROP___STRONG_IMP____smallfoot_cond_star___smallfoot_prop THEN
      ASM_REWRITE_TAC[]
   ) THEN
   MATCH_MP_TAC SMALLFOOT_COND_PROP___STRONG_EQUIV_IMP___COMPUTE THEN
   MATCH_MP_TAC SMALLFOOT_COND_PROP___STRONG_EQUIV___cond_star THEN
   ASM_REWRITE_TAC[]
]);







val smallfoot_prop___PROP_EMPTY = store_thm ("smallfoot_prop___PROP_EMPTY",

``!wpb rpb.

  (smallfoot_prop___PROP (wpb, rpb) EMPTY_BAG =
  (\s. (!v. BAG_IN v wpb ==> var_res_sl___has_write_permission v (FST s)) /\
       (!v. BAG_IN v rpb ==> var_res_sl___has_read_permission v (FST s)) /\
       (SND s = FEMPTY)))``,


REPEAT STRIP_TAC THEN
ONCE_REWRITE_TAC [EXTENSION] THEN
SIMP_TAC std_ss [smallfoot_prop___PROP___REWRITE,
		 IN_ABS, smallfoot_ap_bigstar_REWRITE,
		 smallfoot_ap_star___PROPERTIES] THEN
SIMP_TAC std_ss [smallfoot_ap_stack_true_def, IN_ABS]);






val smallfoot_prop___PROP_INSERT = store_thm ("smallfoot_prop___PROP_INSERT",

``!wpb rpb sf sfb.
  (smallfoot_prop___COND (wpb, rpb) (BAG_INSERT sf sfb)) ==>

  (smallfoot_prop___PROP (wpb, rpb) (BAG_INSERT sf sfb) =
  (\s. ?h1 h2. ?h1 h2.
               DISJOINT (FDOM h1) (FDOM h2) /\ (SND s = FUNION h1 h2) /\
               (FST s,h1) IN sf /\ 
               (FST s,h2) IN smallfoot_prop___PROP (wpb, rpb) sfb))``,


REPEAT STRIP_TAC THEN
ONCE_REWRITE_TAC [EXTENSION] THEN
SIMP_TAC std_ss [smallfoot_prop___PROP___REWRITE,
		 IN_ABS, smallfoot_ap_bigstar_REWRITE,
		 smallfoot_ap_star___swap_ap_stack_true] THEN
SIMP_TAC (std_ss++bool_eq_imp_ss) [] THEN
REPEAT STRIP_TAC THEN
FULL_SIMP_TAC std_ss [smallfoot_prop___COND_INSERT] THEN
FULL_SIMP_TAC std_ss [smallfoot_prop___COND___EXPAND,
		      SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS_def,
		      smallfoot_ap_star___PERMISSION_UNIMPORTANT,
		      IN_ABS]);






val smallfoot_prop___CONST_INTRO = store_thm (
"smallfoot_prop___CONST_INTRO",
``
!v wpb rpb sfb.

(v IN SET_OF_BAG (BAG_UNION wpb rpb)) ==>

(SMALLFOOT_COND_PROP___EQUIV
 (smallfoot_prop (wpb,rpb) sfb)
 (COND_PROP___EXISTS c. (smallfoot_prop (wpb,rpb) 
	       	        (BAG_INSERT (smallfoot_ap_equal (smallfoot_ae_var v)
                                                        (smallfoot_ae_const c)) 
                                    sfb))))``,

REPEAT STRIP_TAC THEN
SIMP_TAC std_ss [smallfoot_prop___REWRITE,
		 COND_PROP___EXISTS_def,
		 SMALLFOOT_COND_PROP___EQUIV_REWRITE] THEN
`!c.  (smallfoot_prop___COND (wpb,rpb)
         (BAG_INSERT
            (smallfoot_ap_equal (smallfoot_ae_var v) (smallfoot_ae_const c))
            sfb) =
      smallfoot_prop___COND (wpb,rpb) sfb)` by ALL_TAC THEN1 (
   SIMP_TAC std_ss [smallfoot_prop___COND_INSERT] THEN
   REPEAT STRIP_TAC THEN EQ_TAC THEN SIMP_TAC std_ss [] THEN REPEAT STRIP_TAC THEN
   MATCH_MP_TAC (el 1
     (CONJUNCTS SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___compare)) THEN
   ASM_SIMP_TAC std_ss [SMALLFOOT_AE_USED_VARS_SUBSET___EVAL]
) THEN
ASM_SIMP_TAC std_ss [IN_ABS] THEN
Tactical.REVERSE (Cases_on `smallfoot_prop___COND (wpb,rpb) sfb`) THEN (
   ASM_REWRITE_TAC[]
) THEN
ASM_SIMP_TAC std_ss [smallfoot_prop___PROP___REWRITE, IN_ABS,
		     smallfoot_ap_bigstar_REWRITE,
		     RIGHT_EXISTS_AND_THM] THEN
SIMP_TAC (std_ss++bool_eq_imp_ss) [] THEN
REPEAT STRIP_TAC THEN
ONCE_REWRITE_TAC[smallfoot_ap_star___swap] THEN
Q.ABBREV_TAC `P = smallfoot_ap_star smallfoot_ap_stack_true (smallfoot_ap_bigstar sfb)` THEN
`SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS
            (SET_OF_BAG (BAG_UNION wpb rpb)) P` by
   FULL_SIMP_TAC std_ss [smallfoot_prop___COND___EXPAND] THEN
`!c. SMALLFOOT_AP_PERMISSION_UNIMPORTANT 
    (smallfoot_ap_equal (smallfoot_ae_var v) 
                        (smallfoot_ae_const c))` by ALL_TAC THEN1 (
   REWRITE_TAC [SMALLFOOT_AP_PERMISSION_UNIMPORTANT___ALTERNATIVE_DEF] THEN
   GEN_TAC THEN
   MATCH_MP_TAC (el 1 (CONJUNCTS SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___compare)) THEN
   ASM_REWRITE_TAC [SMALLFOOT_AE_USED_VARS_SUBSET___EVAL, IN_UNIV]
) THEN

FULL_SIMP_TAC std_ss [SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS_def,
		      smallfoot_ap_star___PERMISSION_UNIMPORTANT] THEN

SIMP_TAC std_ss [IN_ABS, smallfoot_ap_equal_def,
		 smallfoot_ap_binexpression_def,
		 smallfoot_a_stack_proposition_def,
		 FUNION_FEMPTY_1, DISJOINT_EMPTY,
		 FDOM_FEMPTY, smallfoot_ae_var_def,
		 smallfoot_ae_const_def,
		 LET_THM,
		 COND_NONE_SOME_REWRITES] THEN
Tactical.REVERSE (`v IN FDOM (FST x)` by ALL_TAC) THEN1 ASM_REWRITE_TAC[] THEN
FULL_SIMP_TAC std_ss [var_res_sl___has_write_permission_def,
		      var_res_sl___has_read_permission_def,
		      bagTheory.BAG_IN_BAG_UNION,
		      bagTheory.IN_SET_OF_BAG]);














val SMALLFOOT_COND_INFERENCE___EQ_CASE_SPLIT = store_thm (
"SMALLFOOT_COND_INFERENCE___EQ_CASE_SPLIT",
``
!e1 e2 wpb rpb sfb prog post.

(SMALLFOOT_AE_USED_VARS_SUBSET (SET_OF_BAG (BAG_UNION wpb rpb)) e1 /\
SMALLFOOT_AE_USED_VARS_SUBSET (SET_OF_BAG (BAG_UNION wpb rpb)) e2)

 ==>

(SMALLFOOT_COND_HOARE_TRIPLE (smallfoot_prop (wpb,rpb) sfb) prog post =
 ((SMALLFOOT_COND_HOARE_TRIPLE  
        (smallfoot_prop (wpb,rpb) 
	       	        (BAG_INSERT (smallfoot_ap_equal e1 e2)
                                    sfb))
        prog post) /\
 (SMALLFOOT_COND_HOARE_TRIPLE  
        (smallfoot_prop (wpb,rpb) 
	       	        (BAG_INSERT (smallfoot_ap_unequal e1 e2)
                                    sfb))
        prog post)))``,



REPEAT STRIP_TAC THEN
ASM_SIMP_TAC std_ss [SMALLFOOT_COND_HOARE_TRIPLE_REWRITE,
		 smallfoot_prop___REWRITE,
		 smallfoot_prop___COND_INSERT,
		     SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___compare] THEN
SIMP_TAC (std_ss++bool_eq_imp_ss) [] THEN
ASM_SIMP_TAC std_ss [SMALLFOOT_HOARE_TRIPLE_def,
		 FASL_PROGRAM_HOARE_TRIPLE_def,
		 HOARE_TRIPLE_def, IN_ABS,

		 smallfoot_prop___PROP_INSERT,
                 SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___compare,
		 smallfoot_prop___COND_INSERT] THEN
SIMP_TAC std_ss [smallfoot_ap_unequal_def, IN_ABS,
		 smallfoot_ap_equal_def, LET_THM,
		 smallfoot_ap_binexpression_def,
		 smallfoot_a_stack_proposition_def,
		 FUNION_FEMPTY_1, DISJOINT_EMPTY, FDOM_FEMPTY] THEN
REPEAT STRIP_TAC THEN
Tactical.REVERSE (`!x. x IN smallfoot_prop___PROP (wpb,rpb) sfb ==>
                       (IS_SOME (e1 (FST x)) /\ IS_SOME (e2 (FST x)))` by
		       ALL_TAC) THEN1 (
   METIS_TAC[]
) THEN

FULL_SIMP_TAC std_ss [SMALLFOOT_AE_USED_VARS_SUBSET___REWRITE,
		      SMALLFOOT_AE_USED_VARS_REL___REWRITE,
		      smallfoot_prop___PROP___REWRITE, IN_ABS,
		      SUBSET_DEF, var_res_sl___has_read_permission_def,
		      var_res_sl___has_write_permission_def,
		      bagTheory.IN_SET_OF_BAG,
		      bagTheory.BAG_IN_BAG_UNION] THEN
METIS_TAC[]);








val SMALLFOOT_COND_INFERENCE___CONST_INTRO = store_thm (
"SMALLFOOT_COND_INFERENCE___CONST_INTRO",
``
!v wpb rpb sfb prog post.

(v IN SET_OF_BAG (BAG_UNION wpb rpb)) ==>

(SMALLFOOT_COND_HOARE_TRIPLE (smallfoot_prop (wpb,rpb) sfb) prog post =
 !c. SMALLFOOT_COND_HOARE_TRIPLE  
        (smallfoot_prop (wpb,rpb) 
	       	        (BAG_INSERT (smallfoot_ap_equal (smallfoot_ae_var v)
                                                        (smallfoot_ae_const c)) 
                                    sfb))
        prog
        post)``,



REPEAT STRIP_TAC THEN
MP_TAC (Q.SPECL [`v`, `wpb`,`rpb`,`sfb`] smallfoot_prop___CONST_INTRO) THEN
ASM_SIMP_TAC std_ss [GSYM SMALLFOOT_COND_HOARE_TRIPLE___COND_EXISTS,
		     SMALLFOOT_COND_HOARE_TRIPLE___COND_PROP_EQUIV]);






val smallfoot_prop___UNEQUAL_INTRO = store_thm (
"smallfoot_prop___UNEQUAL_INTRO",
``
!c1 c2 wpb rpb sfb.

(~(c1 = c2)) ==>

 (smallfoot_prop (wpb,rpb) sfb =
  smallfoot_prop (wpb,rpb) (BAG_INSERT (smallfoot_ap_unequal (smallfoot_ae_const c1)
                                                             (smallfoot_ae_const c2)) 
                                        sfb))``,


SIMP_TAC std_ss [smallfoot_prop___REWRITE,
		 smallfoot_prop___COND_INSERT,
		 smallfoot_prop___PROP_INSERT,
		 SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___compare,
		 SMALLFOOT_AE_USED_VARS_SUBSET___EVAL] THEN
SIMP_TAC std_ss [COND_RATOR, COND_RAND] THEN
SIMP_TAC std_ss [smallfoot_ap_unequal_def,
		 smallfoot_ap_binexpression_def,
		 smallfoot_a_stack_proposition_def,
		 IN_ABS, LET_THM, FUNION_FEMPTY_1,
		 DISJOINT_EMPTY, FDOM_FEMPTY,
		 smallfoot_ae_const_def, IN_ABS3]);





val smallfoot_prop___EQUAL_POINTS_TO = store_thm (
"smallfoot_prop___EQUAL_POINTS_TO",
``
!e1 e2 L wpb rpb sfb.
 (SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS
            (SET_OF_BAG (BAG_UNION wpb rpb)) (smallfoot_ap_points_to e1 L) /\
  SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS
            (SET_OF_BAG (BAG_UNION wpb rpb)) (smallfoot_ap_points_to e2 L)) ==>


 (smallfoot_prop (wpb,rpb) (BAG_INSERT (smallfoot_ap_points_to e2 L) 
		           (BAG_INSERT (smallfoot_ap_equal e1 e2) sfb)) =
  smallfoot_prop (wpb,rpb) (BAG_INSERT (smallfoot_ap_points_to e1 L) 
		           (BAG_INSERT (smallfoot_ap_equal e1 e2) sfb)))``,



SIMP_TAC std_ss [smallfoot_prop___REWRITE,
		 smallfoot_prop___COND_INSERT,
		 smallfoot_prop___PROP_INSERT,
		 SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___compare,
		 SMALLFOOT_AE_USED_VARS_SUBSET___EVAL,
		 IN_ABS] THEN
REPEAT STRIP_TAC THEN
SIMP_TAC std_ss [COND_RAND, COND_RATOR, COND_EXPAND_IMP] THEN
SIMP_TAC std_ss [smallfoot_ap_equal_def, DISJ_IMP_THM,
		 smallfoot_ap_binexpression_def,
		 smallfoot_a_stack_proposition_def,
		 IN_ABS, LET_THM, FUNION_FEMPTY_1,
		 DISJOINT_EMPTY, FDOM_FEMPTY,
		 smallfoot_ae_const_def, IN_ABS3,
		 smallfoot_ap_points_to_def] THEN
METIS_TAC[]);



val smallfoot_ap_empty_heap_cond_def =
Define `smallfoot_ap_empty_heap_cond c =
        \s:smallfoot_state. (((SND s) = FEMPTY) /\ c)`


val smallfoot_ap_exp_is_defined_def =
Define `smallfoot_ap_exp_is_defined (e:smallfoot_a_expression) =
        \s:smallfoot_state. (((SND s) = FEMPTY) /\
			     IS_SOME (e (FST s)))`;


val smallfoot_ap_cond_equal_def = Define
`smallfoot_ap_cond_equal e1 e2 e3 =
                asl_or (smallfoot_ap_unequal e1 e2)
                  (smallfoot_ap_equal e2 e3)`




val SMALLFOOT_AP_PERMISSION_UNIMPORTANT___smallfoot_ap_exp_is_defined =
store_thm ("SMALLFOOT_AP_PERMISSION_UNIMPORTANT___smallfoot_ap_exp_is_defined",
``!e. IS_SOME___SMALLFOOT_AE_USED_VARS e ==>
SMALLFOOT_AP_PERMISSION_UNIMPORTANT (smallfoot_ap_exp_is_defined e)``,


SIMP_TAC std_ss [SMALLFOOT_AP_PERMISSION_UNIMPORTANT___ALTERNATIVE_DEF_2,
		 smallfoot_ap_exp_is_defined_def,
		 IS_SOME___SMALLFOOT_AE_USED_VARS_def,
		 SMALLFOOT_AE_USED_VARS_THM,
		 IS_SOME_EXISTS,
		 GSYM LEFT_FORALL_IMP_THM,
		 SMALLFOOT_AE_USED_VARS_REL___REWRITE,
		 PAIR_FORALL_THM, IN_ABS] THEN
METIS_TAC[SUBSET_TRANS]);



val smallfoot_ap_var_update_def = Define `
    smallfoot_ap_var_update v c P =
    \s:smallfoot_state. ((SMALLFOOT_STATE_UPDATE_VAR v c var_res_write_permission s) IN P)`;



val smallfoot_ae_var_update_def = Define `
    smallfoot_ae_var_update v c (e:smallfoot_a_expression) =
    \st:smallfoot_stack. 
           (e (SMALLFOOT_STACK_UPDATE_VAR v c var_res_write_permission st))`;




val smallfoot_ae_var_update_EVAL = store_thm ("smallfoot_ae_var_update_EVAL",
``
(smallfoot_ae_var_update v c (smallfoot_ae_const c2) = smallfoot_ae_const c2) /\
(smallfoot_ae_var_update v c smallfoot_ae_null = smallfoot_ae_null) /\
(smallfoot_ae_var_update v c (smallfoot_ae_var v) = smallfoot_ae_const c) /\
(~(v2 = v) ==> (smallfoot_ae_var_update v c (smallfoot_ae_var v2) = smallfoot_ae_var v2)) /\
(smallfoot_ae_var_update v c (smallfoot_ae_binop bop e1 e2) =
 smallfoot_ae_binop bop (smallfoot_ae_var_update v c e1) (smallfoot_ae_var_update v c e2))
``,

ONCE_REWRITE_TAC [FUN_EQ_THM] THEN 
SIMP_TAC std_ss [smallfoot_ae_var_update_def,
		 SMALLFOOT_STACK_UPDATE_VAR_def,
		 smallfoot_ae_const_def,
		 smallfoot_ae_null_def,
		 smallfoot_ae_var_def,
		 smallfoot_ae_binop_def,
		 FDOM_FUPDATE, IN_INSERT,
		 FAPPLY_FUPDATE_THM]);




val smallfoot_ap_var_update___smallfoot_ap_star =
store_thm ("smallfoot_ap_var_update___smallfoot_ap_star",
``
!v c p1 p2.

(SMALLFOOT_AP_PERMISSION_UNIMPORTANT p1 /\
 SMALLFOOT_AP_PERMISSION_UNIMPORTANT p2) ==>

(smallfoot_ap_var_update v c (smallfoot_ap_star p1 p2) =
 smallfoot_ap_star (smallfoot_ap_var_update v c p1) (smallfoot_ap_var_update v c p2))``,



SIMP_TAC std_ss [smallfoot_ap_var_update_def, smallfoot_ap_star_def,
		 EXTENSION, IN_ABS, asl_star_def] THEN
REPEAT STRIP_TAC THEN EQ_TAC THEN STRIP_TAC THENL [
   Q.EXISTS_TAC `(DRESTRICT (FST p) (COMPL {v}), SND p)` THEN
   Q.EXISTS_TAC `(FUNION (DRESTRICT (FST q) (COMPL {v}))
                         (DRESTRICT (FST x) {v}), SND q)` THEN
   REPEAT STRIP_TAC THENL [
      FULL_SIMP_TAC std_ss [SOME___smallfoot_separation_combinator,
			    SMALLFOOT_STATE_UPDATE_VAR_def,
			    SOME___VAR_RES_STACK_COMBINE,
			    SMALLFOOT_STACK_UPDATE_VAR_def,
			    GSYM fmap_EQ_THM,
			    FMERGE_DEF, VAR_RES_STACK_IS_SEPARATE_def,
			    FDOM_FUPDATE, DRESTRICT_DEF,
			    FUNION_DEF, EXTENSION, IN_INTER,
			    IN_UNION, IN_COMPL, IN_SING,
			    IN_INSERT, FAPPLY_FUPDATE_THM, GSYM FORALL_AND_THM] THEN
      GEN_TAC THEN 
      Cases_on `x' = v` THEN (
         ASM_SIMP_TAC std_ss []
      ) THEN      
      METIS_TAC[],


      
      Q.PAT_ASSUM `SMALLFOOT_AP_PERMISSION_UNIMPORTANT p1` 
          (MATCH_MP_TAC o SIMP_RULE  std_ss [SMALLFOOT_AP_PERMISSION_UNIMPORTANT___ALTERNATIVE_DEF_2]) THEN
      Q.EXISTS_TAC `p` THEN
      FULL_SIMP_TAC std_ss [SMALLFOOT_STATE_UPDATE_VAR_def,
			    SMALLFOOT_STACK_UPDATE_VAR_def,
			    FDOM_FUPDATE, DRESTRICT_DEF,
			    SUBSET_DEF, IN_INTER, IN_INSERT,
			    IN_COMPL, IN_SING, FAPPLY_FUPDATE_THM,
			    COND_RATOR, COND_RAND] THEN
      `SMALLFOOT_IS_SUBSTATE p (FST x |+ (v,c,var_res_write_permission),SND x)` by
         METIS_TAC[SMALLFOOT_IS_SUBSTATE_INTRO] THEN
      FULL_SIMP_TAC std_ss [SMALLFOOT_IS_SUBSTATE_REWRITE,
			    VAR_RES_STACK_IS_SUBSTATE_REWRITE,
			    FAPPLY_FUPDATE_THM],



      Q.PAT_ASSUM `SMALLFOOT_AP_PERMISSION_UNIMPORTANT p2` 
          (MATCH_MP_TAC o SIMP_RULE  std_ss [SMALLFOOT_AP_PERMISSION_UNIMPORTANT___ALTERNATIVE_DEF_2]) THEN
      Q.EXISTS_TAC `q` THEN
      FULL_SIMP_TAC std_ss [SMALLFOOT_STATE_UPDATE_VAR_def,
			    SMALLFOOT_STACK_UPDATE_VAR_def,
			    FDOM_FUPDATE, DRESTRICT_DEF,
			    SUBSET_DEF, IN_INTER, IN_INSERT,
			    IN_COMPL, IN_SING, FAPPLY_FUPDATE_THM,
			    FUNION_DEF, IN_UNION,
			    COND_RAND, COND_RATOR] THEN
      `SMALLFOOT_IS_SUBSTATE q (FST x |+ (v,c,var_res_write_permission),SND x)` by
         METIS_TAC[SMALLFOOT_IS_SUBSTATE_INTRO] THEN
      FULL_SIMP_TAC std_ss [SMALLFOOT_IS_SUBSTATE_REWRITE,
			    VAR_RES_STACK_IS_SUBSTATE_REWRITE,
			    FAPPLY_FUPDATE_THM]
   ],



   Q.EXISTS_TAC `SMALLFOOT_STATE_UPDATE_VAR v c (var_res_permission_split var_res_write_permission) p` THEN
   Q.EXISTS_TAC `SMALLFOOT_STATE_UPDATE_VAR v c (var_res_permission_split var_res_write_permission) q` THEN
   REPEAT STRIP_TAC THENL [
      FULL_SIMP_TAC std_ss [SOME___smallfoot_separation_combinator,
			    SMALLFOOT_STATE_UPDATE_VAR_def,
			    SOME___VAR_RES_STACK_COMBINE,
			    SMALLFOOT_STACK_UPDATE_VAR_def,
			    GSYM fmap_EQ_THM,
			    FMERGE_DEF, VAR_RES_STACK_IS_SEPARATE_def,
			    FDOM_FUPDATE,
			    FUNION_DEF, EXTENSION, IN_INTER,
			    IN_UNION, IN_COMPL, IN_SING,
			    IN_INSERT, FAPPLY_FUPDATE_THM,
			    VAR_RES_STACK_COMBINE___MERGE_FUNC_def,
			    GSYM FORALL_AND_THM] THEN
      GEN_TAC THEN
      Cases_on `x' = v` THENL [
         ASM_SIMP_TAC std_ss [var_res_permission_THM2],
	 ASM_SIMP_TAC std_ss []
      ],

      
      Q.PAT_ASSUM `SMALLFOOT_AP_PERMISSION_UNIMPORTANT p1` 
          (MATCH_MP_TAC o SIMP_RULE  std_ss [SMALLFOOT_AP_PERMISSION_UNIMPORTANT___ALTERNATIVE_DEF_2]) THEN
      Q.EXISTS_TAC `SMALLFOOT_STATE_UPDATE_VAR v c var_res_write_permission p` THEN
      ASM_SIMP_TAC std_ss [SMALLFOOT_STATE_UPDATE_VAR_def,
			   SMALLFOOT_STACK_UPDATE_VAR_def,
			   FDOM_FUPDATE, INTER_SUBSET, FAPPLY_FUPDATE_THM,
			   COND_RATOR, COND_RAND, SUBSET_REFL],



      Q.PAT_ASSUM `SMALLFOOT_AP_PERMISSION_UNIMPORTANT p2` 
          (MATCH_MP_TAC o SIMP_RULE  std_ss [SMALLFOOT_AP_PERMISSION_UNIMPORTANT___ALTERNATIVE_DEF_2]) THEN
      Q.EXISTS_TAC `SMALLFOOT_STATE_UPDATE_VAR v c var_res_write_permission q` THEN
      ASM_SIMP_TAC std_ss [SMALLFOOT_STATE_UPDATE_VAR_def,
			   SMALLFOOT_STACK_UPDATE_VAR_def,
			   FDOM_FUPDATE, INTER_SUBSET, FAPPLY_FUPDATE_THM,
			   COND_RATOR, COND_RAND, SUBSET_REFL]
   ]
]);






val smallfoot_ap_var_update___smallfoot_ap_binexpression =
store_thm ("smallfoot_ap_var_update___smallfoot_ap_binexpression",

``
smallfoot_ap_var_update v c (smallfoot_ap_binexpression emp p e1 e2) =
smallfoot_ap_binexpression emp p (smallfoot_ae_var_update v c e1) (smallfoot_ae_var_update v c e2)``,


ONCE_REWRITE_TAC [EXTENSION] THEN
SIMP_TAC std_ss [smallfoot_ap_var_update_def,
		 smallfoot_ap_binexpression_def,
		 smallfoot_a_stack_proposition_def,
		 SMALLFOOT_STATE_UPDATE_VAR_def,
		 IN_ABS, smallfoot_ae_var_update_def]);





val smallfoot_ap_var_update___smallfoot_ap_bigstar_list =
store_thm ("smallfoot_ap_var_update___smallfoot_ap_bigstar_list",
``
!v c pL.

((~(pL = [])) /\
(!p. MEM p pL ==> SMALLFOOT_AP_PERMISSION_UNIMPORTANT p))  ==>

(smallfoot_ap_var_update v c (smallfoot_ap_bigstar_list pL) =
 smallfoot_ap_bigstar_list (MAP (smallfoot_ap_var_update v c) pL))``,

Induct_on `pL` THEN1 REWRITE_TAC[] THEN
Cases_on `pL` THENL [
   FULL_SIMP_TAC list_ss [smallfoot_ap_bigstar_list_def,
   		          asl_bigstar_list_REWRITE] THEN
   SIMP_TAC std_ss [GSYM smallfoot_ap_star_def,
		    GSYM smallfoot_ap_emp_def,
		    smallfoot_ap_star___PROPERTIES],


   REPEAT STRIP_TAC THEN
   FULL_SIMP_TAC list_ss [DISJ_IMP_THM, FORALL_AND_THM] THEN
   FULL_SIMP_TAC list_ss [smallfoot_ap_bigstar_list_def,
		     asl_bigstar_list_REWRITE] THEN
   FULL_SIMP_TAC std_ss [GSYM smallfoot_ap_star_def] THEN
   `SMALLFOOT_AP_PERMISSION_UNIMPORTANT 
      (smallfoot_ap_star h (asl_bigstar_list smallfoot_separation_combinator t))` by ALL_TAC THEN1 (
   
      SIMP_TAC std_ss [GSYM asl_bigstar_list_REWRITE, smallfoot_ap_star_def] THEN
      SIMP_TAC std_ss [GSYM smallfoot_ap_bigstar_list_def] THEN
      MATCH_MP_TAC SMALLFOOT_AP_PERMISSION_UNIMPORTANT___bigstar_list THEN
      ASM_SIMP_TAC list_ss [DISJ_IMP_THM, FORALL_AND_THM]
   ) THEN
   ASM_SIMP_TAC std_ss [smallfoot_ap_var_update___smallfoot_ap_star]
]);

   





val smallfoot_ap_var_update___compare = store_thm ("smallfoot_ap_var_update___compare",
``
(smallfoot_ap_var_update v c (smallfoot_ap_equal e1 e2) =
smallfoot_ap_equal (smallfoot_ae_var_update v c e1) (smallfoot_ae_var_update v c e2)) /\

(smallfoot_ap_var_update v c (smallfoot_ap_unequal e1 e2) =
smallfoot_ap_unequal (smallfoot_ae_var_update v c e1) (smallfoot_ae_var_update v c e2)) /\

(smallfoot_ap_var_update v c (smallfoot_ap_less e1 e2) =
smallfoot_ap_less (smallfoot_ae_var_update v c e1) (smallfoot_ae_var_update v c e2)) /\

(smallfoot_ap_var_update v c (smallfoot_ap_lesseq e1 e2) =
smallfoot_ap_lesseq (smallfoot_ae_var_update v c e1) (smallfoot_ae_var_update v c e2)) /\

(smallfoot_ap_var_update v c (smallfoot_ap_greater e1 e2) =
smallfoot_ap_greater (smallfoot_ae_var_update v c e1) (smallfoot_ae_var_update v c e2)) /\

(smallfoot_ap_var_update v c (smallfoot_ap_greatereq e1 e2) =
smallfoot_ap_greatereq (smallfoot_ae_var_update v c e1) (smallfoot_ae_var_update v c e2)) /\

(smallfoot_ap_var_update v c (smallfoot_ap_weak_unequal e1 e2) =
smallfoot_ap_weak_unequal (smallfoot_ae_var_update v c e1) (smallfoot_ae_var_update v c e2)) /\

(smallfoot_ap_var_update v c (smallfoot_ap_weak_equal e1 e2) =
smallfoot_ap_weak_equal (smallfoot_ae_var_update v c e1) (smallfoot_ae_var_update v c e2))


``,

SIMP_TAC std_ss [smallfoot_ap_equal_def,
                 smallfoot_ap_unequal_def,
                 smallfoot_ap_less_def,
                 smallfoot_ap_lesseq_def,
                 smallfoot_ap_greater_def,
                 smallfoot_ap_greatereq_def,
                 smallfoot_ap_weak_equal_def,
                 smallfoot_ap_weak_unequal_def,
		 smallfoot_ap_var_update___smallfoot_ap_binexpression]);




val smallfoot_ap_var_update___smallfoot_ap_points_to =
store_thm ("smallfoot_ap_var_update___smallfoot_ap_points_to",
``!v c e L.
smallfoot_ap_var_update v c (smallfoot_ap_points_to e L) =
smallfoot_ap_points_to (smallfoot_ae_var_update v c e)
                       (FMAP_MAP (smallfoot_ae_var_update v c) L)``,

ONCE_REWRITE_TAC[EXTENSION] THEN
Cases_on `x` THEN
SIMP_TAC std_ss [smallfoot_ap_points_to_def,
		 smallfoot_ap_var_update_def,
		 IN_ABS, LET_THM,
		 SMALLFOOT_STATE_UPDATE_VAR_def,
		 smallfoot_ae_var_update_def,
		 FEVERY_FMAP_MAP] THEN
REPEAT GEN_TAC THEN
Q.ABBREV_TAC `q' = SMALLFOOT_STACK_UPDATE_VAR v c var_res_write_permission q` THEN
SIMP_TAC std_ss [FEVERY_DEF]);



val smallfoot_ap_var_update___smallfoot_ap_exp_is_defined =
store_thm ("smallfoot_ap_var_update___smallfoot_ap_exp_is_defined",
``!v c e.
smallfoot_ap_var_update v c (smallfoot_ap_exp_is_defined e) =
smallfoot_ap_exp_is_defined (smallfoot_ae_var_update v c e)``,

SIMP_TAC std_ss [smallfoot_ap_var_update_def, smallfoot_ap_exp_is_defined_def,
		 SMALLFOOT_STATE_UPDATE_VAR_def, IN_ABS,
		 smallfoot_ae_var_update_def]);







val smallfoot_ap_var_update___BOOL = store_thm ("smallfoot_ap_var_update___BOOL",

``(smallfoot_ap_var_update v c (asl_and p1 p2) =
  asl_and (smallfoot_ap_var_update v c p1) (smallfoot_ap_var_update v c p2)) /\

  (smallfoot_ap_var_update v c (asl_or p1 p2) =
  asl_or (smallfoot_ap_var_update v c p1) (smallfoot_ap_var_update v c p2)) /\

  (smallfoot_ap_var_update v c (K cp) = (K cp)) /\

  (smallfoot_ap_var_update v c smallfoot_ap_false = smallfoot_ap_false) /\
  (smallfoot_ap_var_update v c smallfoot_ap_stack_true = smallfoot_ap_stack_true) /\
  (smallfoot_ap_var_update v c (smallfoot_ap_empty_heap_cond cp) = (smallfoot_ap_empty_heap_cond cp)) /\

  (smallfoot_ap_var_update v c (asl_exists x. p x) =
   asl_exists x. (smallfoot_ap_var_update v c (p x)))``,

ONCE_REWRITE_TAC [EXTENSION] THEN
SIMP_TAC std_ss [asl_bool_EVAL,
		 smallfoot_ap_var_update_def,
		 IN_ABS, asl_exists_def,
		 smallfoot_ap_false_def,
		 smallfoot_ap_stack_true_def,
		 smallfoot_ap_empty_heap_cond_def,
		 SMALLFOOT_STATE_UPDATE_VAR_def]);




val smallfoot_ap_var_update___smallfoot_ap_cond_equal =
store_thm ("smallfoot_ap_var_update___smallfoot_ap_cond_equal",
``!v c e1 e2 e3.
smallfoot_ap_var_update v c (smallfoot_ap_cond_equal e1 e2 e3) =
smallfoot_ap_cond_equal (smallfoot_ae_var_update v c e1)
			    (smallfoot_ae_var_update v c e2)
                            (smallfoot_ae_var_update v c e3)``,

			    
SIMP_TAC std_ss [smallfoot_ap_cond_equal_def,
		 smallfoot_ap_var_update___BOOL,
		 smallfoot_ap_var_update___compare]);






val SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___cond_equal =
store_thm ("SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___cond_equal",
``!vs P1 P2 P3.
(SMALLFOOT_AE_USED_VARS_SUBSET vs P1 /\
 SMALLFOOT_AE_USED_VARS_SUBSET vs P2 /\
 SMALLFOOT_AE_USED_VARS_SUBSET vs P3) ==>
SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS vs (smallfoot_ap_cond_equal P1 P2 P3)``,


SIMP_TAC std_ss [SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___or,
		 SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___compare,
		 smallfoot_ap_cond_equal_def]);




val SMALLFOOT_AP_PERMISSION_UNIMPORTANT___cond_equal =
save_thm ("SMALLFOOT_AP_PERMISSION_UNIMPORTANT___cond_equal",

SIMP_RULE std_ss [SMALLFOOT_AE_USED_VARS_SUBSET___UNIV_REWRITE,
		  GSYM SMALLFOOT_AP_PERMISSION_UNIMPORTANT___ALTERNATIVE_DEF]
 (SPEC ``UNIV:smallfoot_var set`` SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___cond_equal)

);



val smallfoot_ap_var_update___smallfoot_ap_tree_seg_num =
store_thm ("smallfoot_ap_var_update___smallfoot_ap_tree_seg_num",
``!v c n bal tagL startExp endExp.
(IS_SOME___SMALLFOOT_AE_USED_VARS startExp /\
 IS_SOME___SMALLFOOT_AE_USED_VARS endExp) ==>

(smallfoot_ap_var_update v c (smallfoot_ap_tree_seg_num n bal tagL startExp endExp) =
smallfoot_ap_tree_seg_num n bal tagL (smallfoot_ae_var_update v c startExp)
                                     (smallfoot_ae_var_update v c endExp))``,


Induct_on `n` THEN1 (
   SIMP_TAC std_ss [smallfoot_ap_tree_seg_num_def,
		    asl_rec_pred_num_def,
		    smallfoot_ap_var_update___compare]
) THEN
ASM_SIMP_TAC std_ss [smallfoot_ap_tree_seg_num_def,
		     asl_rec_pred_num_def,
		    smallfoot_ap_var_update___compare,
		    smallfoot_ap_var_update___BOOL] THEN
ONCE_REWRITE_TAC[EXTENSION] THEN
SIMP_TAC (std_ss++bool_eq_imp_ss) [asl_bool_EVAL] THEN
REPEAT GEN_TAC THEN STRIP_TAC THEN GEN_TAC THEN
MATCH_MP_TAC (prove(``A ==> (B ==> A)``, SIMP_TAC std_ss [])) THEN
STRIP_TAC THEN
ASM_SIMP_TAC list_ss [asl_choose_pred_args_def,
                      smallfoot_ap_var_update___BOOL, asl_bool_EVAL,
		      IN_ABS, MAP_MAP_o,
		      combinTheory.o_DEF] THEN
HO_MATCH_MP_TAC (
   prove (``(!eL. (P eL = Q eL)) ==> ((?eL. P eL) = (?eL. Q eL))``, METIS_TAC[])) THEN
GEN_TAC THEN
Tactical.REVERSE (Cases_on `LENGTH eL = LENGTH tagL`) THEN1 (
   ASM_SIMP_TAC std_ss [smallfoot_ap_var_update_def,
		        IN_ABS]
) THEN  
ASM_REWRITE_TAC[] THEN
MATCH_MP_TAC (prove (``((A = A') /\ (A' ==> (B = B'))) ==> ((A /\ B) = (A' /\ B'))``, PROVE_TAC[])) THEN
CONJ_TAC THEN1 (
   ASM_SIMP_TAC list_ss [smallfoot_ap_var_update_def,
		    IN_ABS, EVERY_MEM,
		    MEM_ZIP, GSYM LEFT_FORALL_IMP_THM,
			 EL_MAP]
) THEN
REPEAT STRIP_TAC THEN
`?cl. eL = MAP smallfoot_ae_const cl` by ALL_TAC THEN1 (
   Q.PAT_ASSUM `LENGTH eL = LENGTH tagL` MP_TAC THEN
   Q.PAT_ASSUM `EVERY P X` MP_TAC THEN
   REPEAT (POP_ASSUM (K ALL_TAC)) THEN
   Q.SPEC_TAC (`tagL`, `tagL`) THEN
   Induct_on `eL` THENL [
      REPEAT STRIP_TAC THEN
      Q.EXISTS_TAC `[]` THEN
      SIMP_TAC list_ss [],


      Cases_on `tagL` THEN
      SIMP_TAC list_ss [DISJ_IMP_THM, FORALL_AND_THM] THEN
      REPEAT STRIP_TAC THEN
      `?cl. eL = MAP smallfoot_ae_const cl` by METIS_TAC[] THEN
      FULL_SIMP_TAC std_ss [smallfoot_ae_is_const_def] THEN
      Q.EXISTS_TAC `n::cl` THEN
      ASM_SIMP_TAC list_ss []
   ]
) THEN
Q.PAT_ASSUM `EVERY P X` (K ALL_TAC) THEN
ASM_SIMP_TAC std_ss [smallfoot_ap_tree_seg_num_GSYM_REWRITE] THEN

Q.ABBREV_TAC `pL =  (smallfoot_ap_points_to startExp
            (LISTS_TO_FMAP (tagL,MAP smallfoot_ae_const cl))::
              MAP
                (\startExp.
                   smallfoot_ap_tree_seg_num n bal tagL startExp endExp)
                (MAP smallfoot_ae_const cl))` THEN
`~(pL = []) /\
 (!p. MEM p pL ==> SMALLFOOT_AP_PERMISSION_UNIMPORTANT p)` by ALL_TAC THEN1 (

   UNABBREV_ALL_TAC THEN
   SIMP_TAC list_ss [MEM_MAP,
		     GSYM LEFT_EXISTS_AND_THM,
		     GSYM RIGHT_EXISTS_AND_THM,
		     DISJ_IMP_THM, FORALL_AND_THM,
		     GSYM LEFT_FORALL_IMP_THM] THEN
   CONJ_TAC THENL [
       MATCH_MP_TAC SMALLFOOT_AP_PERMISSION_UNIMPORTANT___points_to THEN
       ASM_REWRITE_TAC[] THEN
       MATCH_MP_TAC FEVERY_LISTS_TO_FMAP THEN
       FULL_SIMP_TAC list_ss [MEM_ZIP, GSYM LEFT_FORALL_IMP_THM,
			      EL_MAP,
			      IS_SOME___SMALLFOOT_AE_USED_VARS___EVAL],


       REPEAT STRIP_TAC THEN
       REWRITE_TAC [SMALLFOOT_AP_PERMISSION_UNIMPORTANT___ALTERNATIVE_DEF] THEN
       MATCH_MP_TAC SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___smallfoot_ap_tree_seg_num THEN
       ASM_SIMP_TAC std_ss [IS_SOME___SMALLFOOT_AE_USED_VARS___EVAL,
			    SMALLFOOT_AE_USED_VARS_SUBSET___UNIV_REWRITE]
   ]
) THEN
ASM_SIMP_TAC std_ss [smallfoot_ap_var_update___smallfoot_ap_bigstar_list,
		     GSYM smallfoot_ap_bigstar_list_def] THEN
REPEAT AP_TERM_TAC THEN
UNABBREV_ALL_TAC THEN
FULL_SIMP_TAC list_ss [MAP_MAP_o, combinTheory.o_DEF,
		       MEM_MAP, DISJ_IMP_THM,
		       FORALL_AND_THM, GSYM LEFT_FORALL_IMP_THM] THEN
CONJ_TAC THENL [
   ASM_SIMP_TAC list_ss [smallfoot_ap_var_update___smallfoot_ap_points_to,
		        FMAP_MAP___LISTS_TO_FMAP,
			MAP_MAP_o, combinTheory.o_DEF,
			smallfoot_ae_var_update_EVAL,
			ETA_THM],

   ASM_SIMP_TAC std_ss [IS_SOME___SMALLFOOT_AE_USED_VARS___EVAL,
		        smallfoot_ae_var_update_EVAL]
]);





val smallfoot_ap_var_update___data_list_seg_num =
store_thm ("smallfoot_ap_var_update___data_list_seg_num",
``!v n c e1 data e2 t.
(IS_SOME___SMALLFOOT_AE_USED_VARS e1 /\
IS_SOME___SMALLFOOT_AE_USED_VARS e2) ==>

(smallfoot_ap_var_update v c (smallfoot_ap_data_list_seg_num n t e1 data e2) =
smallfoot_ap_data_list_seg_num n t (smallfoot_ae_var_update v c e1) data
                        (smallfoot_ae_var_update v c e2))``,


Induct_on `n` THENL [
   SIMP_TAC std_ss [smallfoot_ap_data_list_seg_num_def,
		    smallfoot_ap_var_update___BOOL,
		    smallfoot_ap_var_update___compare] THEN
   REPEAT STRIP_TAC THEN
   BINOP_TAC THEN1 REWRITE_TAC[] THEN
   SIMP_TAC std_ss [smallfoot_ap_var_update_def,
		    SMALLFOOT_STATE_UPDATE_VAR_def, IN_ABS,
		    SMALLFOOT_STACK_UPDATE_VAR_def],




   SIMP_TAC std_ss [smallfoot_ap_data_list_seg_num_def,
		    smallfoot_ap_var_update___BOOL,
		    smallfoot_ap_var_update___compare,
		    EXTENSION, asl_bool_EVAL] THEN
   REPEAT STRIP_TAC THEN
   HO_MATCH_MP_TAC (prove (
                ``((B = B') /\ (!n. C n = C' n)) ==>
                  ((A /\ B  /\ (?n. C  n)) =
                   (A /\ B' /\ (?n. C' n)))``, METIS_TAC[])) THEN
   CONJ_TAC THEN1 (
      SIMP_TAC std_ss [smallfoot_ap_var_update_def, IN_ABS]
   ) THEN
   GEN_TAC THEN
   Q.ABBREV_TAC `data_pt = (FMAP_MAP (\dl. smallfoot_ae_const (HD dl)) data |+
               (t,smallfoot_ae_const n'))` THEN
   Q.ABBREV_TAC `data_tl = (FMAP_MAP TL data)` THEN
   `SMALLFOOT_AP_PERMISSION_UNIMPORTANT (smallfoot_ap_points_to e1 data_pt) /\
    SMALLFOOT_AP_PERMISSION_UNIMPORTANT 
          (smallfoot_ap_data_list_seg_num n t (smallfoot_ae_const n') data_tl
	    e2)` by ALL_TAC THEN1 (
       Q.UNABBREV_TAC `data_pt` THEN
       CONSEQ_REWRITE_TAC ([],[SMALLFOOT_AP_PERMISSION_UNIMPORTANT___data_list_seg_num,
			   SMALLFOOT_AP_PERMISSION_UNIMPORTANT___points_to,
			   FEVERY_STRENGTHEN_THM],[]) THEN
       ASM_SIMP_TAC std_ss [IS_SOME___SMALLFOOT_AE_USED_VARS___EVAL,
			    FEVERY_FMAP_MAP] THEN
       SIMP_TAC std_ss [FEVERY_DEF]
   ) THEN


   ASM_SIMP_TAC std_ss [smallfoot_ap_var_update___smallfoot_ap_star,
                        IS_SOME___SMALLFOOT_AE_USED_VARS___EVAL,
			smallfoot_ae_var_update_EVAL,
			smallfoot_ap_var_update___smallfoot_ap_points_to] THEN
      
   Tactical.REVERSE (`FMAP_MAP (smallfoot_ae_var_update v c) data_pt =
		      data_pt` by ALL_TAC) THEN1 (
      ASM_REWRITE_TAC[]
   ) THEN
   Q.UNABBREV_TAC `data_pt` THEN
   SIMP_TAC std_ss [FMAP_MAP_FUPDATE, combinTheory.o_DEF,
		    FMAP_MAP___FMAP_MAP,
		    smallfoot_ae_var_update_EVAL]
]);




val smallfoot_ap_var_update___data_list_seg =
store_thm ("smallfoot_ap_var_update___data_list_seg",
``!v c e1 data e2 t.
(IS_SOME___SMALLFOOT_AE_USED_VARS e1 /\
IS_SOME___SMALLFOOT_AE_USED_VARS e2) ==>

(smallfoot_ap_var_update v c (smallfoot_ap_data_list_seg t e1 data e2) =
smallfoot_ap_data_list_seg t (smallfoot_ae_var_update v c e1) data
                        (smallfoot_ae_var_update v c e2))``,


SIMP_TAC std_ss [smallfoot_ap_data_list_seg_def,
		 smallfoot_ap_var_update___BOOL,
		 smallfoot_ap_var_update___data_list_seg_num]);




val smallfoot_ap_var_update___data_list =
store_thm ("smallfoot_ap_var_update___data_list",
``!v c e data t.
(IS_SOME___SMALLFOOT_AE_USED_VARS e) ==>

(smallfoot_ap_var_update v c (smallfoot_ap_data_list t e data) =
smallfoot_ap_data_list t (smallfoot_ae_var_update v c e) data)``,


SIMP_TAC std_ss [smallfoot_ap_data_list_def,
		 smallfoot_ap_var_update___data_list_seg,
		 IS_SOME___SMALLFOOT_AE_USED_VARS___EVAL,
		 smallfoot_ae_var_update_EVAL]);



val smallfoot_ap_var_update___smallfoot_bintree =
store_thm ("smallfoot_ap_var_update___smallfoot_bintree",
``!v c e lt rt.
(IS_SOME___SMALLFOOT_AE_USED_VARS e) ==>

(smallfoot_ap_var_update v c (smallfoot_ap_bintree (lt,rt) e) =
smallfoot_ap_bintree (lt,rt) (smallfoot_ae_var_update v c e))``,


SIMP_TAC std_ss [smallfoot_ap_bintree_def,
		 smallfoot_ap_bintree_num_def,
		 smallfoot_ap_var_update___BOOL,
		 smallfoot_ap_var_update___smallfoot_ap_tree_seg_num,
		 IS_SOME___SMALLFOOT_AE_USED_VARS___EVAL,
		 smallfoot_ae_var_update_EVAL]);












val SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___smallfoot_ap_var_update =
store_thm ("SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___smallfoot_ap_var_update",
``!v c vs P.
(SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS vs P ==>
 SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS vs (smallfoot_ap_var_update v c P))
``,


SIMP_TAC std_ss [SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___ALTERNATIVE_DEF_2,
		 smallfoot_ap_var_update_def, IN_ABS,
		 SMALLFOOT_STATE_UPDATE_VAR_def,
		 SMALLFOOT_STACK_UPDATE_VAR_def] THEN
REPEAT STRIP_TAC THEN
Q.PAT_ASSUM `!s s2. X s s2` MATCH_MP_TAC THEN
Q.EXISTS_TAC `(FST s2 |+ (v,c,var_res_write_permission),SND s2)` THEN
FULL_SIMP_TAC std_ss [FDOM_FUPDATE, SUBSET_DEF, IN_INTER, IN_DELETE,
		      IN_INSERT, FAPPLY_FUPDATE_THM] THEN
METIS_TAC[]);




val SMALLFOOT_AP_PERMISSION_UNIMPORTANT___smallfoot_ap_var_update =
store_thm ("SMALLFOOT_AP_PERMISSION_UNIMPORTANT___smallfoot_ap_var_update",
``!v c P.
(SMALLFOOT_AP_PERMISSION_UNIMPORTANT P ==>
 SMALLFOOT_AP_PERMISSION_UNIMPORTANT (smallfoot_ap_var_update v c P))
``,

SIMP_TAC std_ss [SMALLFOOT_AP_PERMISSION_UNIMPORTANT___ALTERNATIVE_DEF,
		 SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___smallfoot_ap_var_update]);



val SMALLFOOT_AE_USED_VARS_SUBSET___smallfoot_ae_var_update =
store_thm ("SMALLFOOT_AE_USED_VARS_SUBSET___smallfoot_ae_var_update",
``!v c vs e.
(SMALLFOOT_AE_USED_VARS_SUBSET vs e ==>
 SMALLFOOT_AE_USED_VARS_SUBSET vs (smallfoot_ae_var_update v c e))
``,


SIMP_TAC std_ss [SMALLFOOT_AE_USED_VARS_SUBSET___REWRITE,
		 SMALLFOOT_AE_USED_VARS_REL___REWRITE,
		 smallfoot_ae_var_update_def, IN_ABS,
		 SMALLFOOT_STACK_UPDATE_VAR_def] THEN
REPEAT STRIP_TAC THEN
Q.EXISTS_TAC `vs' DELETE v` THEN
ASM_SIMP_TAC std_ss [FDOM_FUPDATE, FINITE_DELETE,
		     DELETE_SUBSET_INSERT] THEN
REPEAT STRIP_TAC THEN1 (
   FULL_SIMP_TAC std_ss [SUBSET_DEF, IN_INSERT]
) THEN
Q.PAT_ASSUM `!st1 st2. X st1 st2` MATCH_MP_TAC THEN

FULL_SIMP_TAC std_ss [IN_DELETE, SUBSET_DEF, FDOM_FUPDATE,
		      FAPPLY_FUPDATE_THM,
		      COND_RAND, COND_RATOR]);



val smallfoot_pe_var_update_def = Define `

(smallfoot_pe_var_update v c (smallfoot_p_var v') =
 if v = v' then smallfoot_p_const c else smallfoot_p_var v') /\

(smallfoot_pe_var_update v c (smallfoot_p_const c') =
 (smallfoot_p_const c')) /\

(smallfoot_pe_var_update v c (smallfoot_p_add e1 e2) =
(smallfoot_p_add (smallfoot_pe_var_update v c e1)
                 (smallfoot_pe_var_update v c e2))) /\

(smallfoot_pe_var_update v c (smallfoot_p_sub e1 e2) =
(smallfoot_p_sub (smallfoot_pe_var_update v c e1)
                 (smallfoot_pe_var_update v c e2)))`;



val smallfoot_ae_var_update___SMALLFOOT_P_EXPRESSION_EVAL =
store_thm ("smallfoot_ae_var_update___SMALLFOOT_P_EXPRESSION_EVAL",
``!v c e.
smallfoot_ae_var_update v c (SMALLFOOT_P_EXPRESSION_EVAL e) =
SMALLFOOT_P_EXPRESSION_EVAL (smallfoot_pe_var_update v c e)``,

Induct_on `e` THEN (
   ASM_SIMP_TAC std_ss [SMALLFOOT_P_EXPRESSION_EVAL_def,
		    smallfoot_pe_var_update_def,
		    smallfoot_ae_var_update_EVAL]
) THEN
SIMP_TAC std_ss [smallfoot_ae_var_update_EVAL,
          	 COND_RAND, COND_RATOR, 
		 SMALLFOOT_P_EXPRESSION_EVAL_def]);



val SMALLFOOT_PE_USED_VARS___smallfoot_pe_var_update =
store_thm ("SMALLFOOT_PE_USED_VARS___smallfoot_pe_var_update",
``!v c e.
(SMALLFOOT_PE_USED_VARS (smallfoot_pe_var_update v c e)) =
 SOME (THE (SMALLFOOT_PE_USED_VARS e) DELETE v)``,

Induct_on `e` THEN (
   ASM_SIMP_TAC std_ss [SMALLFOOT_PE_USED_VARS___REWRITE,
		    smallfoot_pe_var_update_def,
		        UNION_DELETE, EMPTY_DELETE]
) THEN
SIMP_TAC std_ss [COND_RATOR, COND_RAND,
		   SMALLFOOT_PE_USED_VARS___REWRITE] THEN
SIMP_TAC std_ss [EXTENSION, NOT_IN_EMPTY, IN_DELETE, IN_SING] THEN
METIS_TAC[]);



val smallfoot_ap_var_update___smallfoot_ap_bigstar___ap_true =
store_thm ("smallfoot_ap_var_update___smallfoot_ap_bigstar___ap_true",
``
!v c sfb. (FINITE_BAG sfb /\
          (!sf. BAG_IN sf sfb ==> SMALLFOOT_AP_PERMISSION_UNIMPORTANT sf))  ==>

(
smallfoot_ap_star smallfoot_ap_stack_true
      (smallfoot_ap_bigstar (BAG_IMAGE (smallfoot_ap_var_update v c) sfb)) =
smallfoot_ap_var_update v c
      (smallfoot_ap_star smallfoot_ap_stack_true (smallfoot_ap_bigstar sfb))
)``,


NTAC 2 GEN_TAC THEN
ONCE_REWRITE_TAC [GSYM AND_IMP_INTRO] THEN
HO_MATCH_MP_TAC FINITE_BAG_INDUCT___FINITE THEN
REPEAT STRIP_TAC THEN1 (
   SIMP_TAC std_ss [smallfoot_ap_bigstar_REWRITE,
		    smallfoot_ap_star___PROPERTIES,
		    bagTheory.BAG_IMAGE_EMPTY,
		    smallfoot_ap_var_update_def,
		    smallfoot_ap_stack_true_def,
		    IN_ABS, SMALLFOOT_STATE_UPDATE_VAR_def]
) THEN
FULL_SIMP_TAC std_ss [bagTheory.BAG_IN_BAG_INSERT, DISJ_IMP_THM,
		      FORALL_AND_THM, smallfoot_ap_bigstar_REWRITE,
		      bagTheory.BAG_IMAGE_FINITE_INSERT] THEN
ONCE_REWRITE_TAC[smallfoot_ap_star___swap] THEN
ASM_SIMP_TAC std_ss [] THEN
Q.ABBREV_TAC `P = smallfoot_ap_star smallfoot_ap_stack_true (smallfoot_ap_bigstar sfb)` THEN
`SMALLFOOT_AP_PERMISSION_UNIMPORTANT P` by ALL_TAC THEN1 (
   Q.UNABBREV_TAC `P` THEN
   SIMP_TAC std_ss [GSYM smallfoot_ap_bigstar_REWRITE] THEN
   MATCH_MP_TAC SMALLFOOT_AP_PERMISSION_UNIMPORTANT___bigstar THEN
   ASM_SIMP_TAC std_ss [bagTheory.BAG_INSERT_NOT_EMPTY,
		    bagTheory.BAG_IN_BAG_INSERT,
		    DISJ_IMP_THM,
		    SMALLFOOT_AP_PERMISSION_UNIMPORTANT___smallfoot_ap_stack_true]
) THEN
ASM_SIMP_TAC std_ss [smallfoot_ap_var_update___smallfoot_ap_star]);




val smallfoot_ap_cond_def = Define `
smallfoot_ap_cond e1 e2 p1 (p2:smallfoot_a_proposition) = 
\s. IS_SOME (e1 (FST s)) /\ IS_SOME (e2 (FST s)) /\ 
    asl_cond (smallfoot_ap_weak_equal e1 e2) p1 p2 s`;


val smallfoot_ap_binexpression_cond_def = Define `
smallfoot_ap_binexpression_cond p e1 e2 P =
\s. IS_SOME (e1 (FST s)) /\ IS_SOME (e2 (FST s)) /\
asl_cond (smallfoot_ap_binexpression F p e1 e2) 
(smallfoot_ap_star smallfoot_ap_stack_true P) smallfoot_ap_stack_true s`


val smallfoot_ap_equal_cond_def = Define `
smallfoot_ap_equal_cond = smallfoot_ap_binexpression_cond $=` 

val smallfoot_ap_unequal_cond_def = Define `
smallfoot_ap_unequal_cond = smallfoot_ap_binexpression_cond (\n1 n2. ~(n1 = n2))` 





val SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___smallfoot_ap_binexpression_cond =
store_thm ("SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___smallfoot_ap_binexpression_cond",
``!p e1 e2 vs P.
(SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS vs P /\
 SMALLFOOT_AE_USED_VARS_SUBSET vs e1 /\
 SMALLFOOT_AE_USED_VARS_SUBSET vs e2) ==>
 SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS vs (smallfoot_ap_binexpression_cond p e1 e2 P)
``,


REPEAT STRIP_TAC THEN
`SMALLFOOT_AP_PERMISSION_UNIMPORTANT P` by FULL_SIMP_TAC std_ss [SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS_def] THEN
FULL_SIMP_TAC std_ss [smallfoot_ap_cond_def, asl_cond_def, IN_ABS,
		 smallfoot_ap_binexpression_cond_def,
                 SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___ALTERNATIVE_DEF_2,
		      smallfoot_ap_star___ap_stack_true___PERMISSION_UNIMPORTANT] THEN
REPEAT GEN_TAC THEN STRIP_TAC THEN
`!e. (IS_SOME (e (FST s2)) /\ SMALLFOOT_AE_USED_VARS_SUBSET vs e) ==>
     (e (FST s) = e (FST s2))` by ALL_TAC THEN1 (

   SIMP_TAC std_ss [SMALLFOOT_AE_USED_VARS_SUBSET___REWRITE,
		    SMALLFOOT_AE_USED_VARS_REL___REWRITE] THEN
   REPEAT STRIP_TAC THEN
   Q.PAT_ASSUM `!st1 st2. X st1 st2 ==> (e st1 = e st2)` MATCH_MP_TAC THEN
   FULL_SIMP_TAC std_ss [SUBSET_DEF, IN_INTER]
) THEN
`s  IN smallfoot_ap_binexpression F p e1 e2 =
 s2 IN smallfoot_ap_binexpression F p e1 e2` by ALL_TAC THEN1 (

   SIMP_TAC std_ss [smallfoot_ap_binexpression_def, IN_ABS,
		    smallfoot_a_stack_proposition_def, LET_THM] THEN
   ASM_SIMP_TAC std_ss []
) THEN
ASM_SIMP_TAC std_ss [] THEN
Cases_on `s2 IN smallfoot_ap_binexpression F p e1 e2` THENL [
   FULL_SIMP_TAC std_ss [] THEN
   METIS_TAC[],


   FULL_SIMP_TAC std_ss [smallfoot_ap_stack_true_def,
			 IN_ABS]
]);





val SMALLFOOT_AP_PERMISSION_UNIMPORTANT___smallfoot_ap_binexpression_cond =
store_thm ("SMALLFOOT_AP_PERMISSION_UNIMPORTANT___smallfoot_ap_binexpression_cond",
``!p e1 e2 P.
(SMALLFOOT_AP_PERMISSION_UNIMPORTANT P /\
 IS_SOME___SMALLFOOT_AE_USED_VARS e1 /\
 IS_SOME___SMALLFOOT_AE_USED_VARS e2) ==>
 SMALLFOOT_AP_PERMISSION_UNIMPORTANT (smallfoot_ap_binexpression_cond p e1 e2 P)
``,

SIMP_TAC std_ss [SMALLFOOT_AP_PERMISSION_UNIMPORTANT___ALTERNATIVE_DEF] THEN
REPEAT STRIP_TAC THEN
MATCH_MP_TAC SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___smallfoot_ap_binexpression_cond THEN
ASM_REWRITE_TAC [SMALLFOOT_AE_USED_VARS_SUBSET___UNIV_REWRITE]);




val SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___smallfoot_ap_equal_cond =
save_thm ("SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___smallfoot_ap_equal_cond",
REWRITE_RULE [GSYM smallfoot_ap_equal_cond_def]
(SPEC ``($=):num -> num -> bool`` 
SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___smallfoot_ap_binexpression_cond));


val SMALLFOOT_AP_PERMISSION_UNIMPORTANT___smallfoot_ap_equal_cond =
save_thm ("SMALLFOOT_AP_PERMISSION_UNIMPORTANT___smallfoot_ap_equal_cond",
REWRITE_RULE [GSYM smallfoot_ap_equal_cond_def]
(SPEC ``($=):num -> num -> bool`` 
SMALLFOOT_AP_PERMISSION_UNIMPORTANT___smallfoot_ap_binexpression_cond));



val SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___smallfoot_ap_unequal_cond =
save_thm ("SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___smallfoot_ap_unequal_cond",
REWRITE_RULE [GSYM smallfoot_ap_unequal_cond_def]
(SPEC ``\n1:num n2. ~(n1 = n2)`` 
SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___smallfoot_ap_binexpression_cond));


val SMALLFOOT_AP_PERMISSION_UNIMPORTANT___smallfoot_ap_unequal_cond =
save_thm ("SMALLFOOT_AP_PERMISSION_UNIMPORTANT___smallfoot_ap_unequal_cond",
REWRITE_RULE [GSYM smallfoot_ap_unequal_cond_def]
(SPEC ``\n1:num n2. ~(n1 = n2)``
SMALLFOOT_AP_PERMISSION_UNIMPORTANT___smallfoot_ap_binexpression_cond));





val smallfoot_ap_cond___EXPAND = store_thm ("smallfoot_ap_cond___EXPAND",
``!e1 e2 P1 P2.
  (SMALLFOOT_AP_PERMISSION_UNIMPORTANT P1 /\
  SMALLFOOT_AP_PERMISSION_UNIMPORTANT P2 /\
  IS_SOME___SMALLFOOT_AE_USED_VARS e1 /\
  IS_SOME___SMALLFOOT_AE_USED_VARS e2) ==>

(smallfoot_ap_cond e1 e2 P1 P2 =
smallfoot_ap_star (smallfoot_ap_equal_cond e1 e2 P1)
                  (smallfoot_ap_unequal_cond e1 e2 P2))``,


ONCE_REWRITE_TAC[EXTENSION] THEN
SIMP_TAC std_ss [smallfoot_ap_star___PERMISSION_UNIMPORTANT,
		 smallfoot_ap_equal_cond_def,
		 smallfoot_ap_unequal_cond_def,
		 SMALLFOOT_AP_PERMISSION_UNIMPORTANT___smallfoot_ap_binexpression_cond] THEN
SIMP_TAC std_ss [smallfoot_ap_cond_def, IN_ABS,
		 asl_cond_def, 
		 asl_star_def, 
                 smallfoot_ap_binexpression_cond_def,
		 smallfoot_ap_weak_equal_def,
		 smallfoot_ap_star___ap_stack_true___PERMISSION_UNIMPORTANT] THEN
REPEAT STRIP_TAC THEN EQ_TAC THENL [
   STRIP_TAC THEN
   `?ec1 ec2. (e1 (FST x) = SOME ec1) /\ (e2 (FST x) = SOME ec2)` by ALL_TAC THEN1 (
       FULL_SIMP_TAC std_ss [IS_SOME_EXISTS]
   ) THEN
   FULL_SIMP_TAC std_ss [smallfoot_ap_binexpression_def, IN_ABS,
			 smallfoot_a_stack_proposition_def, LET_THM] THEN
   Cases_on `ec1 = ec2` THENL [
     Q.EXISTS_TAC `SND x` THEN
     Q.EXISTS_TAC `FEMPTY` THEN
     FULL_SIMP_TAC std_ss [smallfoot_ap_stack_true_def,
			   FDOM_FEMPTY, DISJOINT_EMPTY,
			   FUNION_FEMPTY_2, IN_ABS],

     Q.EXISTS_TAC `FEMPTY` THEN
     Q.EXISTS_TAC `SND x` THEN
     FULL_SIMP_TAC std_ss [smallfoot_ap_stack_true_def,
			   FDOM_FEMPTY, DISJOINT_EMPTY,
			   FUNION_FEMPTY_1, IN_ABS]
   ],



   STRIP_TAC THEN
   `?ec1 ec2. (e1 (FST x) = SOME ec1) /\ (e2 (FST x) = SOME ec2)` by ALL_TAC THEN1 (
       FULL_SIMP_TAC std_ss [IS_SOME_EXISTS]
   ) THEN
   FULL_SIMP_TAC std_ss [smallfoot_ap_binexpression_def, IN_ABS,
			 smallfoot_a_stack_proposition_def, LET_THM] THEN
   Cases_on `ec1 = ec2` THENL [ 
     FULL_SIMP_TAC std_ss [smallfoot_ap_stack_true_def, IN_ABS,
			   FUNION_FEMPTY_2] THEN
     Q.PAT_ASSUM `X = h1` (ASSUME_TAC o GSYM) THEN
     FULL_SIMP_TAC std_ss [],


     FULL_SIMP_TAC std_ss [smallfoot_ap_stack_true_def, IN_ABS,
			   FUNION_FEMPTY_1] THEN
     Q.PAT_ASSUM `X = h2` (ASSUME_TAC o GSYM) THEN
     FULL_SIMP_TAC std_ss []
   ]
]);



val smallfoot_ap_binexpression_cond___ap_star = 
store_thm ("smallfoot_ap_binexpression_cond___ap_star",
``!p e1 e2 P1 P2.
  (IS_SOME___SMALLFOOT_AE_USED_VARS e1 /\
   IS_SOME___SMALLFOOT_AE_USED_VARS e2 /\
   SMALLFOOT_AP_PERMISSION_UNIMPORTANT P1 /\
   SMALLFOOT_AP_PERMISSION_UNIMPORTANT P2) ==>

  (smallfoot_ap_binexpression_cond p e1 e2 (smallfoot_ap_star P1 P2) =
smallfoot_ap_star 
   (smallfoot_ap_binexpression_cond p e1 e2 P1)
   (smallfoot_ap_binexpression_cond p e1 e2 P2))``,


REPEAT STRIP_TAC THEN
`smallfoot_ap_star smallfoot_ap_stack_true (smallfoot_ap_star P1 P2) =
 (smallfoot_ap_star P1 P2)` by ALL_TAC THEN1 (
   MATCH_MP_TAC smallfoot_ap_star___ap_stack_true___PERMISSION_UNIMPORTANT THEN
   MATCH_MP_TAC SMALLFOOT_AP_PERMISSION_UNIMPORTANT___star THEN
   ASM_REWRITE_TAC[]
) THEN
POP_ASSUM MP_TAC THEN
ONCE_REWRITE_TAC[EXTENSION] THEN
ASM_SIMP_TAC std_ss [SMALLFOOT_AP_PERMISSION_UNIMPORTANT___smallfoot_ap_binexpression_cond,
		 smallfoot_ap_star___PERMISSION_UNIMPORTANT,
		     IN_ABS] THEN
ASM_SIMP_TAC std_ss [smallfoot_ap_binexpression_cond_def, IN_ABS,
		 smallfoot_ap_star___ap_stack_true___PERMISSION_UNIMPORTANT,
		 asl_cond_def, smallfoot_ap_binexpression_def,
		 LET_THM, smallfoot_a_stack_proposition_def] THEN
DISCH_TAC THEN POP_ASSUM (K ALL_TAC) THEN
GEN_TAC THEN
Cases_on `e1 (FST x)` THEN ASM_SIMP_TAC std_ss [] THEN
Cases_on `e2 (FST x)` THEN ASM_SIMP_TAC std_ss [] THEN
Cases_on `p x' x''` THEN ASM_REWRITE_TAC[] THEN

SIMP_TAC std_ss [smallfoot_ap_stack_true_def, IN_ABS, FDOM_FEMPTY,
		 DISJOINT_EMPTY, FUNION_FEMPTY_1]);



val smallfoot_ap_binexpression_cond___ap_emp =
store_thm ("smallfoot_ap_binexpression_cond___ap_emp",
``!p e1 e2.
(IS_SOME___SMALLFOOT_AE_USED_VARS e1 /\
   IS_SOME___SMALLFOOT_AE_USED_VARS e2) ==>

(smallfoot_ap_binexpression_cond p e1 e2 smallfoot_ap_emp =
 smallfoot_ap_star (smallfoot_ap_exp_is_defined e1) (smallfoot_ap_exp_is_defined e2))``,

ONCE_REWRITE_TAC[EXTENSION] THEN
SIMP_TAC std_ss [smallfoot_ap_binexpression_cond_def,
		 asl_cond_def, IN_ABS, smallfoot_ap_star___PROPERTIES] THEN
SIMP_TAC std_ss [SMALLFOOT_AP_PERMISSION_UNIMPORTANT___smallfoot_ap_exp_is_defined,
		 smallfoot_ap_star___PERMISSION_UNIMPORTANT] THEN
SIMP_TAC std_ss [smallfoot_ap_exp_is_defined_def, IN_ABS, FDOM_FEMPTY,
		 DISJOINT_EMPTY, FUNION_FEMPTY_1, smallfoot_ap_stack_true_def] THEN
SIMP_TAC (std_ss++bool_eq_imp_ss) []);





val smallfoot_ap_binexpression_cond___ap_stack_true =
store_thm ("smallfoot_ap_binexpression_cond___ap_stack_true",
``!p e1 e2.
(IS_SOME___SMALLFOOT_AE_USED_VARS e1 /\
   IS_SOME___SMALLFOOT_AE_USED_VARS e2) ==>

(smallfoot_ap_binexpression_cond p e1 e2 smallfoot_ap_stack_true =
 smallfoot_ap_star (smallfoot_ap_exp_is_defined e1) (smallfoot_ap_exp_is_defined e2))``,

ONCE_REWRITE_TAC[EXTENSION] THEN
SIMP_TAC std_ss [smallfoot_ap_binexpression_cond_def,
		 asl_cond_def, IN_ABS, smallfoot_ap_star___PROPERTIES] THEN
SIMP_TAC std_ss [SMALLFOOT_AP_PERMISSION_UNIMPORTANT___smallfoot_ap_exp_is_defined,
		 smallfoot_ap_star___PERMISSION_UNIMPORTANT,
		 smallfoot_ap_star___ap_stack_true___IDEM] THEN
SIMP_TAC std_ss [smallfoot_ap_exp_is_defined_def, IN_ABS, FDOM_FEMPTY,
		 DISJOINT_EMPTY, FUNION_FEMPTY_1, smallfoot_ap_stack_true_def] THEN
SIMP_TAC (std_ss++bool_eq_imp_ss) []);



val smallfoot_ap_binexpression_cond___true_cond =
store_thm ("smallfoot_ap_binexpression_cond___true_cond",
``!p e1 e2 ec1 ec2 s.
(IS_SOME___SMALLFOOT_AE_USED_VARS e1 /\
 IS_SOME___SMALLFOOT_AE_USED_VARS e2 /\
 (e1 (FST s) = SOME ec1) /\ (e2 (FST s) = SOME ec2) /\
 (p ec1 ec2)) ==>

(smallfoot_ap_binexpression_cond p e1 e2 P s = s IN (smallfoot_ap_star smallfoot_ap_stack_true P))``,


SIMP_TAC std_ss [smallfoot_ap_binexpression_cond_def,
		 asl_cond_def, smallfoot_ap_binexpression_def,
		 smallfoot_a_stack_proposition_def,
		 IN_ABS, LET_THM]);


val smallfoot_ap_binexpression_cond___false_cond =
store_thm ("smallfoot_ap_binexpression_cond___false_cond",
``!p e1 e2 ec1 ec2 s.
(IS_SOME___SMALLFOOT_AE_USED_VARS e1 /\
 IS_SOME___SMALLFOOT_AE_USED_VARS e2 /\
 (e1 (FST s) = SOME ec1) /\ (e2 (FST s) = SOME ec2) /\
 ~(p ec1 ec2)) ==>

(smallfoot_ap_binexpression_cond p e1 e2 P s = 
s IN smallfoot_ap_stack_true)``,


SIMP_TAC std_ss [smallfoot_ap_binexpression_cond_def,
		 asl_cond_def, smallfoot_ap_binexpression_def,
		 smallfoot_a_stack_proposition_def,
		 IN_ABS, LET_THM]);



val smallfoot_ap_var_update___smallfoot_ap_binexpression_cond =
store_thm ("smallfoot_ap_var_update___smallfoot_ap_binexpression_cond",
``!p v c e1 e2 P.

 SMALLFOOT_AP_PERMISSION_UNIMPORTANT P ==>
 (smallfoot_ap_var_update v c (smallfoot_ap_binexpression_cond p e1 e2 P) =
  smallfoot_ap_binexpression_cond p (smallfoot_ae_var_update v c e1) (smallfoot_ae_var_update v c e2)
                                   (smallfoot_ap_var_update v c P))

``,

REPEAT STRIP_TAC THEN
IMP_RES_TAC SMALLFOOT_AP_PERMISSION_UNIMPORTANT___smallfoot_ap_var_update THEN
ONCE_REWRITE_TAC[EXTENSION] THEN
FULL_SIMP_TAC std_ss [smallfoot_ap_var_update_def, IN_ABS,
		 SMALLFOOT_STATE_UPDATE_VAR_def,
		 smallfoot_ap_binexpression_cond_def,
		 SMALLFOOT_STACK_UPDATE_VAR_def,
		 smallfoot_ae_var_update_def,
		 asl_cond_def,
		 smallfoot_ap_binexpression_def,
		 smallfoot_a_stack_proposition_def,
		 smallfoot_ap_star___ap_stack_true___PERMISSION_UNIMPORTANT] THEN
SIMP_TAC (std_ss++bool_eq_imp_ss) [COND_EXPAND] THEN
REPEAT STRIP_TAC THEN (
   SIMP_TAC std_ss [smallfoot_ap_stack_true_def, IN_ABS]
));



val smallfoot_ap_var_update___smallfoot_ap_unequal_cond =
save_thm ("smallfoot_ap_var_update___smallfoot_ap_unequal_cond",
REWRITE_RULE [GSYM smallfoot_ap_unequal_cond_def]
(SPEC ``\n1:num n2. ~(n1 = n2)`` 
smallfoot_ap_var_update___smallfoot_ap_binexpression_cond));



val smallfoot_ap_var_update___smallfoot_ap_equal_cond =
save_thm ("smallfoot_ap_var_update___smallfoot_ap_equal_cond",
REWRITE_RULE [GSYM smallfoot_ap_equal_cond_def]
(SPEC ``($=):num -> num -> bool``
smallfoot_ap_var_update___smallfoot_ap_binexpression_cond));




val SMALLFOOT_INFERENCE_prog_slp___IMP = store_thm (
"SMALLFOOT_INFERENCE_prog_slp___IMP",
``
!res_env penv P Q p1 p2 slp.
         ((fasl_slp_opt (smallfoot_env,res_env) penv P p1 = SOME slp) /\
         SMALLFOOT_REL_HOARE_TRIPLE res_env penv P p1 /\
         SMALLFOOT_HOARE_TRIPLE res_env penv slp p2 Q) ==>
         SMALLFOOT_HOARE_TRIPLE res_env penv P (fasl_prog_seq p1 p2) Q``,

SIMP_TAC std_ss [SMALLFOOT_HOARE_TRIPLE_REWRITE,
		 FASL_INFERENCE_prog_slp___IMP] THEN
SIMP_TAC std_ss [SMALLFOOT_REL_HOARE_TRIPLE_def,
		 SMALLFOOT_PROGRAM_SEM_def,
		 FASL_PROGRAM_SEM___prog_seq,
		 fasl_slp_opt_def, COND_NONE_SOME_REWRITES,
		 LET_THM, IN_BIGINTER, IN_ABS,
		 SOME___fasla_seq,
		 GSYM RIGHT_EXISTS_AND_THM,
		 GSYM LEFT_FORALL_IMP_THM] THEN
SIMP_TAC std_ss [IN_BIGUNION, IN_IMAGE, GSYM RIGHT_EXISTS_AND_THM,
		 GSYM LEFT_FORALL_IMP_THM, HOARE_TRIPLE_def,
		 FASL_PROGRAM_HOARE_TRIPLE_def, IN_ABS,
		 fasl_order_THM, IN_BIGINTER] THEN
ONCE_REWRITE_TAC[EXTENSION] THEN
SIMP_TAC std_ss [IN_ABS, NOT_IN_EMPTY] THEN
REPEAT STRIP_TAC THEN
`?s'. FASL_PROGRAM_SEM (smallfoot_env,res_env) penv p2 x' = SOME s'` by PROVE_TAC[IS_SOME_EXISTS] THEN
Q.PAT_ASSUM `!s s'. X s s'` (MP_TAC o Q.SPECL [`x'`, `s'`]) THEN
FULL_SIMP_TAC std_ss [] THEN

MATCH_MP_TAC (prove (``((B ==> C) /\ A)  ==> ((A ==> B) ==> C)``, SIMP_TAC std_ss [])) THEN
CONJ_TAC THEN1 (
   REPEAT STRIP_TAC THEN
   Q.PAT_ASSUM `!s s'. X s s'` (MP_TAC o Q.SPECL [`s`, `s1`]) THEN    
   ASM_SIMP_TAC std_ss [GSYM LEFT_FORALL_IMP_THM] THEN
   REPEAT STRIP_TAC THEN
   RES_TAC THEN
   PROVE_TAC [VAR_RES_STACK___IS_EQUAL_UPTO_VALUES___TRANS]
) THEN

REPEAT STRIP_TAC THEN
Q.PAT_ASSUM `!s. s IN P ==> X s` (MP_TAC o Q.SPEC `s`) THEN
ASM_SIMP_TAC std_ss [SUBSET_DEF]);





val SMALLFOOT_COND_INFERENCE___prog_assign =
store_thm ("SMALLFOOT_COND_INFERENCE___prog_assign",
``
!wpb rpb v e c sfb prog Q.

((BAG_IN v wpb) /\
(THE (SMALLFOOT_PE_USED_VARS e) SUBSET (SET_OF_BAG (BAG_UNION wpb rpb)))) ==>
((SMALLFOOT_COND_HOARE_TRIPLE 
   (smallfoot_prop (wpb,rpb) 
      (BAG_INSERT (smallfoot_ap_equal (smallfoot_ae_var v) 
                                      (smallfoot_ae_var_update v c (SMALLFOOT_P_EXPRESSION_EVAL e))) 
         (BAG_IMAGE (smallfoot_ap_var_update v c) sfb)))
    prog Q) ==>


(SMALLFOOT_COND_HOARE_TRIPLE  
   (smallfoot_prop (wpb,rpb) 
      (BAG_INSERT (smallfoot_ap_equal (smallfoot_ae_var v) 
                                      (smallfoot_ae_const c)) 
       sfb))

   (fasl_prog_seq (smallfoot_prog_assign v e) prog)

   Q))``,

REPEAT STRIP_TAC THEN
`?Q_ap Q_cond. Q = (Q_cond, Q_ap)` by (Cases_on `Q` THEN SIMP_TAC std_ss []) THEN
FULL_SIMP_TAC std_ss [SMALLFOOT_COND_HOARE_TRIPLE_def, smallfoot_prop___REWRITE] THEN
REPEAT STRIP_TAC THEN
MATCH_MP_TAC SMALLFOOT_INFERENCE_prog_slp___IMP THEN
SIMP_TAC std_ss [fasl_slp_opt___smallfoot_prog_assign,
		 COND_NONE_SOME_REWRITES] THEN
REPEAT STRIP_TAC THENL [
   ASM_SIMP_TAC std_ss [smallfoot_ap_implies_writeperm_def,
		    smallfoot_prop___PROP___REWRITE],


   MATCH_MP_TAC smallfoot_ae_is_defined___IMPL THEN
   `?vs. SMALLFOOT_PE_USED_VARS e = SOME vs` by
      PROVE_TAC[SMALLFOOT_PE_USED_VARS___IS_SOME, IS_SOME_EXISTS] THEN
   Q.EXISTS_TAC `vs` THEN
   FULL_SIMP_TAC std_ss [GSYM SMALLFOOT_PE_USED_VARS_def],


   SIMP_TAC std_ss [SMALLFOOT_REL_HOARE_TRIPLE_def,
		    smallfoot_prog_assign_def,
		    SMALLFOOT_PROGRAM_SEM_def,
		    FASL_PROGRAM_SEM___prim_command,
		    FASL_ATOMIC_ACTION_SEM_def,
		    EVAL_fasl_prim_command_THM,
		    smallfoot_env_def, PAIR_FORALL_THM,
		    SMALLFOOT_action_map_def, LET_THM] THEN
   SIMP_TAC std_ss [COND_NONE_SOME_REWRITES, IN_SING,
		    VAR_RES_STACK___IS_EQUAL_UPTO_VALUES_def,
		    var_res_sl___has_write_permission_def] THEN
   SIMP_TAC (std_ss++boolSimps.CONJ_ss) [FDOM_FUPDATE, IN_INSERT,
					 FAPPLY_FUPDATE_THM] THEN
   REPEAT STRIP_TAC THEN
   Cases_on `x = v` THEN (
      ASM_SIMP_TAC std_ss []
   ),

   ALL_TAC
] THEN

FULL_SIMP_TAC std_ss [smallfoot_prop___COND_INSERT] THEN
`smallfoot_prop___COND (wpb,rpb)
            (BAG_IMAGE (smallfoot_ap_var_update v c) sfb) /\
          SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS
            (SET_OF_BAG (BAG_UNION wpb rpb))
            (smallfoot_ap_equal (smallfoot_ae_var v)
               (smallfoot_ae_var_update v c (SMALLFOOT_P_EXPRESSION_EVAL e)))` by ALL_TAC THEN1 (
   CONJ_TAC THENL [
      FULL_SIMP_TAC std_ss [smallfoot_prop___COND___REWRITE,
			    bagTheory.BAG_IN_FINITE_BAG_IMAGE,
			    GSYM LEFT_EXISTS_AND_THM, 
			    GSYM LEFT_FORALL_IMP_THM,
			    bagTheory.BAG_IMAGE_FINITE,
			    SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___smallfoot_ap_var_update],


      MATCH_MP_TAC (el 1 (CONJUNCTS SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___compare)) THEN
      ASM_SIMP_TAC std_ss [SMALLFOOT_AE_USED_VARS_SUBSET___EVAL,
			   bagTheory.IN_SET_OF_BAG, bagTheory.BAG_IN_BAG_UNION] THEN
      ASM_SIMP_TAC std_ss [SMALLFOOT_AE_USED_VARS_SUBSET_def,
			   smallfoot_ae_var_update___SMALLFOOT_P_EXPRESSION_EVAL,
        		   GSYM SMALLFOOT_PE_USED_VARS_def,
			   SMALLFOOT_PE_USED_VARS___smallfoot_pe_var_update] THEN
      FULL_SIMP_TAC std_ss [SUBSET_DEF, IN_DELETE]
  ]
) THEN 
FULL_SIMP_TAC std_ss [] THEN

Tactical.REVERSE (`(smallfoot_slp_assign v (SMALLFOOT_P_EXPRESSION_EVAL e)
         (smallfoot_prop___PROP (wpb,rpb)
            (BAG_INSERT
               (smallfoot_ap_equal (smallfoot_ae_var v)
                  (smallfoot_ae_const c)) sfb))) =
         (smallfoot_prop___PROP (wpb,rpb)
               (BAG_INSERT
                  (smallfoot_ap_equal (smallfoot_ae_var v)
                      (smallfoot_ae_var_update v c (SMALLFOOT_P_EXPRESSION_EVAL e)))
                  (BAG_IMAGE (smallfoot_ap_var_update v c) sfb)))` by ALL_TAC) THEN1 (
   ASM_REWRITE_TAC[]
) THEN

ONCE_REWRITE_TAC[EXTENSION] THEN GEN_TAC THEN
Cases_on `x` THEN
SIMP_TAC std_ss [smallfoot_slp_assign_def, IN_ABS,
		 smallfoot_prop___PROP___REWRITE,
		 var_res_sl___read_def,
		 COND_NONE_SOME_REWRITES,
		 LET_THM,
		 var_res_sl___has_write_permission_def,
		 var_res_sl___has_read_permission_def,
		 SMALLFOOT_STATE_UPDATE_VAR_def,
		 SMALLFOOT_STACK_UPDATE_VAR_def,
		 FDOM_FUPDATE, FAPPLY_FUPDATE_THM] THEN
Tactical.REVERSE (Cases_on `v IN FDOM q`) THEN1 (
   ASM_SIMP_TAC std_ss [] THEN
   METIS_TAC[]
) THEN
`?c1 perm. q ' v = (c1, perm)` by (Cases_on `q ' v` THEN SIMP_TAC std_ss []) THEN
Tactical.REVERSE (Cases_on `perm = var_res_write_permission`) THEN1 (
   ASM_SIMP_TAC std_ss [] THEN
   DISJ1_TAC THEN 
   Q.EXISTS_TAC `v` THEN
   ASM_SIMP_TAC std_ss []
) THEN
ASM_SIMP_TAC std_ss [IN_INSERT, COND_RAND, COND_RATOR] THEN


`!v'. ((v' = v) \/ v' IN FDOM q) = (v' IN FDOM q)` by METIS_TAC[] THEN
ASM_REWRITE_TAC[] THEN POP_ASSUM (K ALL_TAC) THEN

`!v'. ((v' = v) \/ (SND (q ' v') = var_res_write_permission)) = 
      (SND (q ' v') = var_res_write_permission)` by ALL_TAC THEN1 (
   GEN_TAC THEN EQ_TAC THEN 
   ASM_SIMP_TAC std_ss [DISJ_IMP_THM]) THEN
ASM_REWRITE_TAC[] THEN POP_ASSUM (K ALL_TAC) THEN

SIMP_TAC (std_ss++bool_eq_imp_ss) [] THEN
STRIP_TAC THEN


SIMP_TAC std_ss [smallfoot_ap_bigstar_REWRITE] THEN
ONCE_REWRITE_TAC[smallfoot_ap_star___swap] THEN
Q.ABBREV_TAC `P = (smallfoot_ap_star smallfoot_ap_stack_true
                   (smallfoot_ap_bigstar sfb))` THEN
Q.ABBREV_TAC `P2 = (smallfoot_ap_star smallfoot_ap_stack_true
         (smallfoot_ap_bigstar
            (BAG_IMAGE (smallfoot_ap_var_update v c) sfb)))` THEN

`SMALLFOOT_AP_PERMISSION_UNIMPORTANT P2 /\
 SMALLFOOT_AP_PERMISSION_UNIMPORTANT P` by ALL_TAC THEN1 (
  FULL_SIMP_TAC std_ss [smallfoot_prop___COND___EXPAND,
		        SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS_def]
) THEN

`P2 =
 smallfoot_ap_var_update v c P` by ALL_TAC THEN1 (

   Q.UNABBREV_TAC `P` THEN
   Q.UNABBREV_TAC `P2` THEN
   MATCH_MP_TAC smallfoot_ap_var_update___smallfoot_ap_bigstar___ap_true THEN
   FULL_SIMP_TAC std_ss [smallfoot_prop___COND___REWRITE,
			 SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS_def]
) THEN
FULL_SIMP_TAC std_ss [] THEN POP_ASSUM (K ALL_TAC) THEN


IMP_RES_TAC SMALLFOOT_AP_PERMISSION_UNIMPORTANT___IMP THEN
ASM_SIMP_TAC std_ss [smallfoot_ap_star___PERMISSION_UNIMPORTANT,
		     IN_ABS, smallfoot_ap_equal_def,
		     smallfoot_ap_binexpression_def,
		     smallfoot_a_stack_proposition_def,
		     LET_THM, smallfoot_ae_const_def,
		     smallfoot_ae_var_def,
		     FUNION_FEMPTY_1,
		     FDOM_FEMPTY, DISJOINT_EMPTY,
		     FDOM_FUPDATE, IN_INSERT,
		     FAPPLY_FUPDATE_THM] THEN

EQ_TAC THEN
SIMP_TAC std_ss [smallfoot_ae_var_update_def,
		 smallfoot_ap_var_update_def,
		 SMALLFOOT_STACK_UPDATE_VAR_def,
		 SMALLFOOT_STATE_UPDATE_VAR_def,
		 IN_ABS, SOME_THE_EQ]);









val SMALLFOOT_COND_INFERENCE___prog_new =
store_thm ("SMALLFOOT_COND_INFERENCE___prog_new",
``
 !wpb rpb v c sfb prog Q.

(BAG_IN v wpb) ==>
((SMALLFOOT_COND_HOARE_TRIPLE
   (smallfoot_prop (wpb,rpb) 
      (BAG_INSERT (smallfoot_ap_points_to (smallfoot_ae_var v) FEMPTY) 
         (BAG_IMAGE (smallfoot_ap_var_update v c) sfb)))
    prog Q) ==>


(SMALLFOOT_COND_HOARE_TRIPLE 
   (smallfoot_prop (wpb,rpb) 
      (BAG_INSERT (smallfoot_ap_equal (smallfoot_ae_var v) 
                                      (smallfoot_ae_const c)) 
       sfb))

   (fasl_prog_seq (smallfoot_prog_new v) prog)

   Q))
``,

REPEAT STRIP_TAC THEN
`?Q_ap Q_cond. Q = (Q_cond, Q_ap)` by (Cases_on `Q` THEN SIMP_TAC std_ss []) THEN
FULL_SIMP_TAC std_ss [SMALLFOOT_COND_HOARE_TRIPLE_def, smallfoot_prop___REWRITE] THEN
REPEAT STRIP_TAC THEN
MATCH_MP_TAC SMALLFOOT_INFERENCE_prog_slp___IMP THEN
SIMP_TAC std_ss [fasl_slp_opt___smallfoot_prog_new,
		 COND_NONE_SOME_REWRITES] THEN
REPEAT STRIP_TAC THENL [
   ASM_SIMP_TAC std_ss [smallfoot_ap_implies_writeperm_def,
		    smallfoot_prop___PROP___REWRITE],


   SIMP_TAC std_ss [SMALLFOOT_REL_HOARE_TRIPLE_def,
		    SMALLFOOT_PROGRAM_SEM_def,
		    smallfoot_prog_new_def,
		    FASL_PROGRAM_SEM___prim_command,
		    smallfoot_env_def, PAIR_FORALL_THM,
		    FASL_ATOMIC_ACTION_SEM_def,
		    EVAL_fasl_prim_command_THM,
		    SMALLFOOT_action_map_def,
		    COND_NONE_SOME_REWRITES, IN_ABS,
		    GSYM LEFT_FORALL_IMP_THM,
                    VAR_RES_STACK___IS_EQUAL_UPTO_VALUES_def,
		    var_res_sl___has_write_permission_def,
		    FAPPLY_FUPDATE_THM, FDOM_FUPDATE] THEN
   ONCE_REWRITE_TAC[EXTENSION] THEN
   SIMP_TAC (std_ss++bool_eq_imp_ss++boolSimps.CONJ_ss) 
        [IN_INSERT, COND_RATOR, COND_RAND],

   ALL_TAC
] THEN

FULL_SIMP_TAC std_ss [smallfoot_prop___COND_INSERT] THEN
`smallfoot_prop___COND (wpb,rpb)
            (BAG_IMAGE (smallfoot_ap_var_update v c) sfb) /\
          SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS
            (SET_OF_BAG (BAG_UNION wpb rpb))
            (smallfoot_ap_points_to (smallfoot_ae_var v)
               FEMPTY)` by ALL_TAC THEN1 (
   CONJ_TAC THENL [
      FULL_SIMP_TAC std_ss [smallfoot_prop___COND___REWRITE,
			    bagTheory.BAG_IN_FINITE_BAG_IMAGE,
			    GSYM LEFT_EXISTS_AND_THM, 
			    GSYM LEFT_FORALL_IMP_THM,
			    bagTheory.BAG_IMAGE_FINITE,
			    SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___smallfoot_ap_var_update],


      MATCH_MP_TAC SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___points_to THEN
      ASM_SIMP_TAC std_ss [SMALLFOOT_AE_USED_VARS_SUBSET___EVAL,
			   bagTheory.IN_SET_OF_BAG, bagTheory.BAG_IN_BAG_UNION,
			   FEVERY_FEMPTY]
  ]
) THEN 
FULL_SIMP_TAC std_ss [] THEN

Tactical.REVERSE (`(smallfoot_slp_new v 
         (smallfoot_prop___PROP (wpb,rpb)
            (BAG_INSERT
               (smallfoot_ap_equal (smallfoot_ae_var v)
                  (smallfoot_ae_const c)) sfb))) =
         (smallfoot_prop___PROP (wpb,rpb)
               (BAG_INSERT
                  (smallfoot_ap_points_to (smallfoot_ae_var v)
                      FEMPTY)
                  (BAG_IMAGE (smallfoot_ap_var_update v c) sfb)))` by ALL_TAC) THEN1 (
   ASM_REWRITE_TAC[]
) THEN

ONCE_REWRITE_TAC[EXTENSION] THEN GEN_TAC THEN
Cases_on `x` THEN
SIMP_TAC std_ss [smallfoot_slp_new_def, IN_ABS,
		 smallfoot_prop___PROP___REWRITE,
		 var_res_sl___read_def,
		 COND_NONE_SOME_REWRITES,
		 LET_THM,
		 var_res_sl___has_write_permission_def,
		 var_res_sl___has_read_permission_def,
		 FDOM_FUPDATE, FAPPLY_FUPDATE_THM] THEN
Tactical.REVERSE (Cases_on `v IN FDOM q`) THEN1 (
   ASM_SIMP_TAC std_ss [] THEN
   METIS_TAC[]
) THEN
`?c1 perm. q ' v = (c1, perm)` by (Cases_on `q ' v` THEN SIMP_TAC std_ss []) THEN
Tactical.REVERSE (Cases_on `perm = var_res_write_permission`) THEN1 (
   ASM_SIMP_TAC std_ss [] THEN
   DISJ1_TAC THEN 
   Q.EXISTS_TAC `v` THEN
   ASM_SIMP_TAC std_ss []
) THEN
ASM_SIMP_TAC std_ss [IN_INSERT, COND_RAND, COND_RATOR] THEN


`!v'. ((v' = v) \/ v' IN FDOM q) = (v' IN FDOM q)` by METIS_TAC[] THEN
ASM_REWRITE_TAC[] THEN POP_ASSUM (K ALL_TAC) THEN

`!v'. ((v' = v) \/ (SND (q ' v') = var_res_write_permission)) = 
      (SND (q ' v') = var_res_write_permission)` by ALL_TAC THEN1 (
   GEN_TAC THEN EQ_TAC THEN 
   ASM_SIMP_TAC std_ss [DISJ_IMP_THM]) THEN
ASM_REWRITE_TAC[] THEN POP_ASSUM (K ALL_TAC) THEN

SIMP_TAC (std_ss++bool_eq_imp_ss) [] THEN
STRIP_TAC THEN


SIMP_TAC std_ss [smallfoot_ap_bigstar_REWRITE] THEN
ONCE_REWRITE_TAC[smallfoot_ap_star___swap] THEN
Q.ABBREV_TAC `P = (smallfoot_ap_star smallfoot_ap_stack_true
                   (smallfoot_ap_bigstar sfb))` THEN
Q.ABBREV_TAC `P2 = (smallfoot_ap_star smallfoot_ap_stack_true
         (smallfoot_ap_bigstar
            (BAG_IMAGE (smallfoot_ap_var_update v c) sfb)))` THEN

`SMALLFOOT_AP_PERMISSION_UNIMPORTANT P2 /\
 SMALLFOOT_AP_PERMISSION_UNIMPORTANT P` by ALL_TAC THEN1 (
  FULL_SIMP_TAC std_ss [smallfoot_prop___COND___EXPAND,
		        SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS_def]
) THEN

`P2 =
 smallfoot_ap_var_update v c P` by ALL_TAC THEN1 (

   Q.UNABBREV_TAC `P` THEN
   Q.UNABBREV_TAC `P2` THEN
   MATCH_MP_TAC smallfoot_ap_var_update___smallfoot_ap_bigstar___ap_true THEN
   FULL_SIMP_TAC std_ss [smallfoot_prop___COND___REWRITE,
			 SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS_def]
) THEN
FULL_SIMP_TAC std_ss [] THEN POP_ASSUM (K ALL_TAC) THEN


IMP_RES_TAC SMALLFOOT_AP_PERMISSION_UNIMPORTANT___IMP THEN
ASM_SIMP_TAC std_ss [smallfoot_ap_star___PERMISSION_UNIMPORTANT,
		     IN_ABS, smallfoot_ap_equal_def,
		     smallfoot_ap_binexpression_def,
		     smallfoot_a_stack_proposition_def,
		     LET_THM, smallfoot_ae_const_def,
		     smallfoot_ae_var_def,
		     FUNION_FEMPTY_1,
		     FDOM_FEMPTY, DISJOINT_EMPTY,
		     FDOM_FUPDATE, IN_INSERT,
		     FAPPLY_FUPDATE_THM,
		     smallfoot_ap_points_to_def,
		     FEVERY_FEMPTY,
		     smallfoot_ap_var_update_def,
		     SMALLFOOT_STATE_UPDATE_VAR_def,
		     SMALLFOOT_STACK_UPDATE_VAR_def] THEN
EQ_TAC THENL [
   REPEAT STRIP_TAC THEN
   Q.EXISTS_TAC `DRESTRICT r {c1}` THEN
   Q.EXISTS_TAC `r \\ c1` THEN
   ASM_SIMP_TAC std_ss [DISJOINT_DEF, EXTENSION, NOT_IN_EMPTY,
		        FDOM_DRESTRICT, FDOM_DOMSUB,
		        FUNION_DEF, IN_SING, IN_INTER,
		        IN_DELETE, IN_UNION,
		        GSYM fmap_EQ_THM, DRESTRICT_DEF,
		        DOMSUB_FAPPLY_THM] THEN
   METIS_TAC[],



   STRIP_TAC THEN
   Tactical.REVERSE (`r \\ c1 = h2` by ALL_TAC) THEN1 (
      ASM_REWRITE_TAC[FUNION_DEF, IN_UNION, IN_SING]
   ) THEN
   Q.PAT_ASSUM `DISJOINT X Y` MP_TAC THEN
   ASM_SIMP_TAC std_ss [GSYM fmap_EQ_THM, DISJOINT_DEF,
		        EXTENSION, FUNION_DEF, DOMSUB_FAPPLY_THM,
		        FDOM_DOMSUB, IN_UNION, IN_DELETE, IN_SING,
		        NOT_IN_EMPTY, IN_SING, IN_INTER] THEN
   METIS_TAC[]
]);




val smallfoot_ap_implies_ae_equal_def = Define `
smallfoot_ap_implies_ae_equal P e1 e2 =
(!s. (FST P) /\ (s IN (SND P)) ==> (e1 (FST s) = e2 (FST s)))`;



val smallfoot_ap_implies_ae_equal___EQ = store_thm (
"smallfoot_ap_implies_ae_equal___EQ",
``!x P. 
smallfoot_ap_implies_ae_equal P x x``,

SIMP_TAC std_ss [smallfoot_ap_implies_ae_equal_def,
		 smallfoot_ae_const_def]);




val smallfoot_ap_implies_ae_equal___IN_SMALLFOOT_PROP = store_thm (
"smallfoot_ap_implies_ae_equal___IN_SMALLFOOT_PROP",
``!e1 e2 wpb rpb sfs. (BAG_IN (smallfoot_ap_equal e1 e2) sfs)  ==>
smallfoot_ap_implies_ae_equal (smallfoot_prop (wpb,rpb) sfs)
                              e1 e2``,


REPEAT STRIP_TAC THEN
IMP_RES_TAC bagTheory.BAG_IN_BAG_DELETE THEN
FULL_SIMP_TAC std_ss [bagTheory.BAG_DELETE,
		      bagTheory.BAG_IN_BAG_INSERT,
		      smallfoot_prop___REWRITE,
		      smallfoot_ap_implies_ae_equal_def] THEN
SIMP_TAC (std_ss++boolSimps.CONJ_ss) [smallfoot_prop___PROP_INSERT] THEN
SIMP_TAC std_ss [IN_ABS, smallfoot_ap_equal_def,
		 smallfoot_ap_binexpression_def,
		 smallfoot_a_stack_proposition_def,
		 FUNION_FEMPTY_1, DISJOINT_EMPTY,
		 FDOM_FEMPTY, LET_THM, IS_SOME_EXISTS] THEN
REPEAT STRIP_TAC THEN
Q.PAT_ASSUM `THE X = THE Y` MP_TAC THEN
ASM_SIMP_TAC std_ss []);






val SMALLFOOT_COND_INFERENCE___prog_field_lookup =
store_thm ("SMALLFOOT_COND_INFERENCE___prog_field_lookup",
``
 !wpb rpb v e t c sfb prog Q.

((BAG_IN v wpb) /\ (t IN FDOM L) /\
 SMALLFOOT_AE_USED_VARS_SUBSET (SET_OF_BAG (BAG_UNION wpb rpb)) (L ' t))
==>
((SMALLFOOT_COND_HOARE_TRIPLE 
   (smallfoot_prop (wpb,rpb) 
     (BAG_INSERT (smallfoot_ap_equal (smallfoot_ae_var v) 
                                     (smallfoot_ae_var_update v c (L ' t))) 
     (BAG_IMAGE (smallfoot_ap_var_update v c) 
       (BAG_INSERT (smallfoot_ap_points_to (SMALLFOOT_P_EXPRESSION_EVAL e) L) 
          sfb))))
    prog Q) ==>


(SMALLFOOT_COND_HOARE_TRIPLE 
   (smallfoot_prop (wpb,rpb) 
      (BAG_INSERT (smallfoot_ap_equal (smallfoot_ae_var v) 
                                      (smallfoot_ae_const c)) 
      (BAG_INSERT (smallfoot_ap_points_to (SMALLFOOT_P_EXPRESSION_EVAL e) L) 
       sfb)))

   (fasl_prog_seq (smallfoot_prog_field_lookup v e t) prog)

   Q))
``,

REPEAT STRIP_TAC THEN
`?Q_ap Q_cond. Q = (Q_cond, Q_ap)` by (Cases_on `Q` THEN SIMP_TAC std_ss []) THEN
FULL_SIMP_TAC std_ss [SMALLFOOT_COND_HOARE_TRIPLE_def, smallfoot_prop___REWRITE] THEN
REPEAT STRIP_TAC THEN
MATCH_MP_TAC SMALLFOOT_INFERENCE_prog_slp___IMP THEN
SIMP_TAC std_ss [fasl_slp_opt___smallfoot_prog_field_lookup,
		 COND_NONE_SOME_REWRITES] THEN
FULL_SIMP_TAC std_ss [smallfoot_ap_implies_ae_equal_def] THEN
REPEAT STRIP_TAC THENL [
   ASM_SIMP_TAC std_ss [smallfoot_ap_implies_writeperm_def,
		    smallfoot_prop___PROP___REWRITE],


   FULL_SIMP_TAC std_ss [smallfoot_ap_implies_in_heap_def,
		        smallfoot_ae_stack_read_def,
                        smallfoot_prop___COND_INSERT,
			COND_NONE_SOME_REWRITES] THEN
   ASM_SIMP_TAC std_ss [smallfoot_prop___PROP_INSERT,
		        smallfoot_prop___COND_INSERT] THEN
   SIMP_TAC (std_ss++boolSimps.CONJ_ss) [smallfoot_ap_equal_def,
		    smallfoot_ap_binexpression_def,
		    smallfoot_a_stack_proposition_def,
		    DISJOINT_EMPTY, FDOM_FEMPTY, FUNION_FEMPTY_1,
                    IN_ABS, LET_THM, GSYM RIGHT_EXISTS_AND_THM,
		    smallfoot_ae_const_def, smallfoot_ae_var_def,
		    COND_NONE_SOME_REWRITES, 
		    GSYM LEFT_FORALL_IMP_THM,
		    smallfoot_ap_points_to_def,
		    IS_SOME_EXISTS, GSYM LEFT_EXISTS_AND_THM,
		    FUNION_DEF, IN_SING, IN_UNION, FEVERY_DEF] THEN
   ASM_SIMP_TAC std_ss [],

 
   SIMP_TAC std_ss [SMALLFOOT_REL_HOARE_TRIPLE_def,
		    SMALLFOOT_PROGRAM_SEM_def,
		    smallfoot_prog_field_lookup_def,
		    FASL_PROGRAM_SEM___prim_command,
		    smallfoot_env_def, PAIR_FORALL_THM,
		    FASL_ATOMIC_ACTION_SEM_def,
		    EVAL_fasl_prim_command_THM,
		    SMALLFOOT_action_map_def,
		    COND_NONE_SOME_REWRITES, LET_THM, IN_ABS,
		    GSYM LEFT_FORALL_IMP_THM, IN_SING,
                    VAR_RES_STACK___IS_EQUAL_UPTO_VALUES_def,
		    var_res_sl___has_write_permission_def,
		    FAPPLY_FUPDATE_THM, FDOM_FUPDATE] THEN
   ONCE_REWRITE_TAC[EXTENSION] THEN
   SIMP_TAC (std_ss++bool_eq_imp_ss) [IN_INSERT, COND_RATOR,
				      COND_RAND, NOT_IN_EMPTY] THEN
   SIMP_TAC std_ss [IN_ABS, NOT_IN_EMPTY, COND_RAND, COND_RATOR] THEN
   REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN 
   Cases_on `t IN FDOM (x2 ' (THE (SMALLFOOT_P_EXPRESSION_EVAL e x1)))` THEN (
      ASM_SIMP_TAC (std_ss++bool_eq_imp_ss++boolSimps.CONJ_ss) 
                          [FDOM_FUPDATE, FAPPLY_FUPDATE_THM,
			   EXTENSION, IN_INSERT, COND_REWRITES,
			   GSYM LEFT_FORALL_IMP_THM]
   ),
	 
   ALL_TAC
] THEN

Q.PAT_ASSUM `A ==> B` MP_TAC THEN
MATCH_MP_TAC (prove (``(A /\ (A ==> (P1 = P2))) ==> ((A ==> (SMALLFOOT_HOARE_TRIPLE res_env penv P1 prog Q)) ==> (SMALLFOOT_HOARE_TRIPLE res_env penv P2 prog Q))``, SIMP_TAC std_ss [])) THEN
CONJ_TAC THEN1 (
   FULL_SIMP_TAC std_ss [smallfoot_prop___COND_INSERT] THEN
   CONJ_TAC THENL [
      FULL_SIMP_TAC std_ss [smallfoot_prop___COND___REWRITE,
			    bagTheory.BAG_IN_FINITE_BAG_IMAGE,
			    GSYM LEFT_EXISTS_AND_THM, 
			    GSYM LEFT_FORALL_IMP_THM,
			    bagTheory.BAG_IMAGE_FINITE,
			    bagTheory.FINITE_BAG_INSERT,
			    bagTheory.BAG_IN_BAG_INSERT, DISJ_IMP_THM,
			    FORALL_AND_THM,
			    SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___smallfoot_ap_var_update],


      MATCH_MP_TAC (el 1 (CONJUNCTS SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___compare)) THEN
      ASM_SIMP_TAC std_ss [SMALLFOOT_AE_USED_VARS_SUBSET___EVAL,
			   bagTheory.IN_SET_OF_BAG, bagTheory.BAG_IN_BAG_UNION,
			   SMALLFOOT_AE_USED_VARS_SUBSET___smallfoot_ae_var_update]
  ]
) THEN 
REPEAT STRIP_TAC THEN

ONCE_REWRITE_TAC[EXTENSION] THEN GEN_TAC THEN
Cases_on `x` THEN

SIMP_TAC std_ss [smallfoot_slp_field_lookup_def, IN_ABS,
		 smallfoot_prop___PROP___REWRITE,
		 LET_THM,
		 var_res_sl___read_def,
		 COND_NONE_SOME_REWRITES,
		 LET_THM,
		 var_res_sl___has_write_permission_def,
		 var_res_sl___has_read_permission_def,
		 FDOM_FUPDATE, FAPPLY_FUPDATE_THM,
		 SMALLFOOT_STACK_UPDATE_VAR_def,
		 SMALLFOOT_STATE_UPDATE_VAR_def,
		 IN_INSERT] THEN
Tactical.REVERSE (Cases_on `v IN FDOM q`) THEN1 (
   ASM_SIMP_TAC std_ss [] THEN
   METIS_TAC[]
) THEN
`?c1 perm. q ' v = (c1, perm)` by (Cases_on `q ' v` THEN SIMP_TAC std_ss []) THEN
Tactical.REVERSE (Cases_on `perm = var_res_write_permission`) THEN1 (
   ASM_SIMP_TAC std_ss [] THEN
   DISJ1_TAC THEN 
   Q.EXISTS_TAC `v` THEN
   ASM_SIMP_TAC std_ss []
) THEN

`!c2. ~ (
SMALLFOOT_STATE_REMOVE_HEAP_TAG
         (THE
            (SMALLFOOT_P_EXPRESSION_EVAL e
               (q |+ (v,c2,var_res_write_permission)))) t
         (q |+ (v,c2,var_res_write_permission),r) IN
       smallfoot_ap_star smallfoot_ap_stack_true
         (smallfoot_ap_bigstar
            (BAG_INSERT
               (smallfoot_ap_equal (smallfoot_ae_var v)
                  (smallfoot_ae_const c))
               (BAG_INSERT
                  (smallfoot_ap_points_to (SMALLFOOT_P_EXPRESSION_EVAL e) L)
                  sfb))))` by ALL_TAC THEN1 (

   GEN_TAC THEN 
   `?P. smallfoot_ap_star smallfoot_ap_stack_true
          (smallfoot_ap_star
             (smallfoot_ap_equal (smallfoot_ae_var v)
                (smallfoot_ae_const c))
             (smallfoot_ap_star
                (smallfoot_ap_points_to (SMALLFOOT_P_EXPRESSION_EVAL e) L)
                (smallfoot_ap_bigstar sfb))) =
        smallfoot_ap_star (smallfoot_ap_points_to (SMALLFOOT_P_EXPRESSION_EVAL e) L) P` by
        METIS_TAC[smallfoot_ap_star___PROPERTIES, COMM_DEF, ASSOC_DEF] THEN
   ASM_REWRITE_TAC[smallfoot_ap_bigstar_REWRITE] THEN (POP_ASSUM (K ALL_TAC)) THEN

   ASM_SIMP_TAC std_ss [smallfoot_ap_bigstar_REWRITE,
			 smallfoot_ap_star_def,
			 asl_star_def, IN_ABS, 
			 GSYM RIGHT_FORALL_OR_THM,
			 GSYM LEFT_FORALL_OR_THM,
			 smallfoot_ap_points_to_def,
			 LET_THM, PAIR_FORALL_THM] THEN
   CCONTR_TAC THEN
   FULL_SIMP_TAC std_ss [] THEN
   Cases_on `SMALLFOOT_P_EXPRESSION_EVAL e x1` THEN FULL_SIMP_TAC std_ss [] THEN
   `t IN FDOM (x2 ' x)` by FULL_SIMP_TAC std_ss [FEVERY_DEF] THEN
   FULL_SIMP_TAC std_ss [SOME___smallfoot_separation_combinator] THEN
   `x2 ' x = (FUNION x2 x2') ' x` by ASM_SIMP_TAC std_ss [FUNION_DEF, IN_SING] THEN
   FULL_SIMP_TAC std_ss [] THEN
   Q.PAT_ASSUM `t IN X` MP_TAC THEN
   Q.PAT_ASSUM `X = FUNION x2 x2'` (ASSUME_TAC o GSYM) THEN
   ASM_SIMP_TAC std_ss [] THEN

   SIMP_TAC std_ss [SMALLFOOT_STATE_REMOVE_HEAP_TAG_def, LET_THM,
		    FAPPLY_FUPDATE_THM, 
		    FDOM_DOMSUB, IN_DELETE] THEN
   Q.PAT_ASSUM `VAR_RES_STACK_COMBINE (SOME x1) (SOME x1') = X` MP_TAC THEN
   ASM_SIMP_TAC std_ss [SMALLFOOT_STATE_REMOVE_HEAP_TAG_def,
			 LET_THM] THEN
   STRIP_TAC THEN
   `VAR_RES_STACK_IS_SUBSTATE x1 (q |+ (v,c2,var_res_write_permission))` by
      METIS_TAC[VAR_RES_STACK_IS_SUBSTATE_INTRO] THEN
   IMP_RES_TAC SMALLFOOT_P_EXPRESSION_EVAL___VAR_RES_SUBSTATE THEN
   POP_ASSUM (MP_TAC o Q.SPEC `e`) THEN
   ASM_SIMP_TAC std_ss [FDOM_DOMSUB, IN_DELETE]
) THEN
ASM_SIMP_TAC std_ss [] THEN (POP_ASSUM (K ALL_TAC)) THEN

ASM_SIMP_TAC std_ss [COND_RAND, COND_RATOR,
		     SMALLFOOT_STATE_UPDATE_VAR_def,
		     SMALLFOOT_STACK_UPDATE_VAR_def,
		     FAPPLY_FUPDATE_THM, FDOM_FUPDATE] THEN


`!v'. ((v' = v) \/ v' IN FDOM q) = (v' IN FDOM q)` by METIS_TAC[] THEN
ASM_REWRITE_TAC[] THEN POP_ASSUM (K ALL_TAC) THEN

`!v'. ((v' = v) \/ (SND (q ' v') = var_res_write_permission)) = 
      (SND (q ' v') = var_res_write_permission)` by ALL_TAC THEN1 (
   GEN_TAC THEN EQ_TAC THEN 
   ASM_SIMP_TAC std_ss [DISJ_IMP_THM]) THEN
ASM_REWRITE_TAC[] THEN POP_ASSUM (K ALL_TAC) THEN

SIMP_TAC (std_ss++bool_eq_imp_ss) [] THEN
STRIP_TAC THEN


SIMP_TAC std_ss [smallfoot_ap_bigstar_REWRITE] THEN
ONCE_REWRITE_TAC[smallfoot_ap_star___swap] THEN
Q.ABBREV_TAC `P = (smallfoot_ap_star smallfoot_ap_stack_true
                   (smallfoot_ap_star
              (smallfoot_ap_points_to (SMALLFOOT_P_EXPRESSION_EVAL e) L)
              (smallfoot_ap_bigstar sfb)))` THEN
Q.ABBREV_TAC `P2 = (smallfoot_ap_star smallfoot_ap_stack_true
         (smallfoot_ap_bigstar
            (BAG_IMAGE (smallfoot_ap_var_update v c)
               (BAG_INSERT
                  (smallfoot_ap_points_to (SMALLFOOT_P_EXPRESSION_EVAL e) L)
                  sfb))))` THEN
Q.ABBREV_TAC `P3 = (smallfoot_ap_star smallfoot_ap_stack_true
              (smallfoot_ap_bigstar sfb))` THEN

`SMALLFOOT_AP_PERMISSION_UNIMPORTANT P2 /\
 SMALLFOOT_AP_PERMISSION_UNIMPORTANT P` by ALL_TAC THEN1 (
  FULL_SIMP_TAC std_ss [Once smallfoot_prop___COND_INSERT] THEN

  FULL_SIMP_TAC std_ss [smallfoot_prop___COND___EXPAND,
			smallfoot_ap_bigstar_REWRITE,
		        SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS_def]
) THEN

`SMALLFOOT_AP_PERMISSION_UNIMPORTANT P3` by ALL_TAC THEN1 (
  FULL_SIMP_TAC std_ss [smallfoot_prop___COND_INSERT] THEN

  FULL_SIMP_TAC std_ss [smallfoot_prop___COND___EXPAND,
			smallfoot_ap_bigstar_REWRITE,
		        SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS_def]
) THEN


`P2 =
 smallfoot_ap_var_update v c P` by ALL_TAC THEN1 (

   Q.UNABBREV_TAC `P` THEN
   Q.UNABBREV_TAC `P2` THEN
   SIMP_TAC std_ss [GSYM smallfoot_ap_bigstar_REWRITE] THEN
   ONCE_REWRITE_TAC [smallfoot_ap_bigstar_REWRITE] THEN
   MATCH_MP_TAC smallfoot_ap_var_update___smallfoot_ap_bigstar___ap_true THEN
   FULL_SIMP_TAC std_ss [smallfoot_prop___COND___REWRITE,
			 SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS_def,
			 bagTheory.FINITE_BAG_THM, bagTheory.BAG_IN_BAG_INSERT,
			 DISJ_IMP_THM, FORALL_AND_THM]
) THEN
Q.PAT_ASSUM `Abbrev (P2 = X)` (K ALL_TAC) THEN
FULL_SIMP_TAC std_ss [] THEN POP_ASSUM (K ALL_TAC) THEN

FULL_SIMP_TAC std_ss [smallfoot_ap_star___swap_ap_stack_true,
		      smallfoot_prop___COND_INSERT] THEN
Q.UNABBREV_TAC `P` THEN
IMP_RES_TAC SMALLFOOT_AP_PERMISSION_UNIMPORTANT___IMP THEN
ASM_SIMP_TAC std_ss [smallfoot_ap_star___PERMISSION_UNIMPORTANT] THEN
ASM_SIMP_TAC std_ss [IN_ABS, smallfoot_ap_equal_def,
		     smallfoot_ap_binexpression_def,
		     smallfoot_a_stack_proposition_def,
		     LET_THM, smallfoot_ae_const_def,
		     smallfoot_ae_var_def,
		     FUNION_FEMPTY_1,
		     FDOM_FEMPTY, DISJOINT_EMPTY,
		     FDOM_FUPDATE, IN_INSERT,
		     FAPPLY_FUPDATE_THM,
		     smallfoot_ap_points_to_def,
		     FEVERY_FEMPTY, smallfoot_ap_var_update_def,
		     SMALLFOOT_STATE_UPDATE_VAR_def,
		     SMALLFOOT_STACK_UPDATE_VAR_def,
		     COND_NONE_SOME_REWRITES,
		     smallfoot_ae_stack_read_def] THEN
SIMP_TAC (std_ss++bool_eq_imp_ss) [] THEN
REPEAT STRIP_TAC THEN
`?c2. SMALLFOOT_P_EXPRESSION_EVAL e
                  (q |+ (v,c,var_res_write_permission)) = SOME c2` by FULL_SIMP_TAC std_ss [IS_SOME_EXISTS] THEN
FULL_SIMP_TAC std_ss [FEVERY_DEF, FUNION_DEF, IN_SING, IN_UNION] THEN
Q.PAT_ASSUM `!x. x IN FDOM L ==> Y x` (MP_TAC o Q.SPEC `t`) THEN
ASM_SIMP_TAC std_ss [smallfoot_ae_var_update_def,
		     SMALLFOOT_STACK_UPDATE_VAR_def] THEN
METIS_TAC[]);






val SMALLFOOT_COND_INFERENCE___prog_field_lookup___intro_const =
store_thm ("SMALLFOOT_COND_INFERENCE___prog_field_lookup___intro_const",
``
 !wpb rpb v e t c sfb prog Q.

((BAG_IN v wpb) /\ ~(t IN FDOM L) /\
  (!c2. SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS
      (SET_OF_BAG (BAG_UNION wpb rpb))
      (smallfoot_ap_points_to (SMALLFOOT_P_EXPRESSION_EVAL e)
         (L |+ (t,smallfoot_ae_const c2)))))

==>
((!c2. (SMALLFOOT_COND_HOARE_TRIPLE 
   (smallfoot_prop (wpb,rpb) 
     (BAG_INSERT (smallfoot_ap_equal (smallfoot_ae_var v) 
                                     (smallfoot_ae_const c2)) 
     (BAG_IMAGE (smallfoot_ap_var_update v c) 
       (BAG_INSERT (smallfoot_ap_points_to (SMALLFOOT_P_EXPRESSION_EVAL e) 
					   (L |+ (t, smallfoot_ae_const c2))) 
          sfb))))
    prog Q)) ==>


(SMALLFOOT_COND_HOARE_TRIPLE 
   (smallfoot_prop (wpb,rpb) 
      (BAG_INSERT (smallfoot_ap_equal (smallfoot_ae_var v) 
                                      (smallfoot_ae_const c)) 
      (BAG_INSERT (smallfoot_ap_points_to (SMALLFOOT_P_EXPRESSION_EVAL e) L) 
       sfb)))

   (fasl_prog_seq (smallfoot_prog_field_lookup v e t) prog)

   Q))
``,

REPEAT STRIP_TAC THEN
`?Q_ap Q_cond. Q = (Q_cond, Q_ap)` by (Cases_on `Q` THEN SIMP_TAC std_ss []) THEN
FULL_SIMP_TAC std_ss [SMALLFOOT_COND_HOARE_TRIPLE_def, smallfoot_prop___REWRITE] THEN
REPEAT STRIP_TAC THEN
MATCH_MP_TAC SMALLFOOT_INFERENCE_prog_slp___IMP THEN
SIMP_TAC std_ss [fasl_slp_opt___smallfoot_prog_field_lookup,
		 COND_NONE_SOME_REWRITES] THEN
FULL_SIMP_TAC std_ss [smallfoot_ap_implies_ae_equal_def] THEN
REPEAT STRIP_TAC THENL [
   ASM_SIMP_TAC std_ss [smallfoot_ap_implies_writeperm_def,
		    smallfoot_prop___PROP___REWRITE],


   FULL_SIMP_TAC std_ss [smallfoot_ap_implies_in_heap_def,
		        smallfoot_ae_stack_read_def,
                        smallfoot_prop___COND_INSERT,
			COND_NONE_SOME_REWRITES] THEN
   ASM_SIMP_TAC std_ss [smallfoot_prop___PROP_INSERT,
		        smallfoot_prop___COND_INSERT] THEN
   SIMP_TAC (std_ss++boolSimps.CONJ_ss) [smallfoot_ap_equal_def,
		    smallfoot_ap_binexpression_def,
		    smallfoot_a_stack_proposition_def,
		    DISJOINT_EMPTY, FDOM_FEMPTY, FUNION_FEMPTY_1,
                    IN_ABS, LET_THM, GSYM RIGHT_EXISTS_AND_THM,
		    smallfoot_ae_const_def, smallfoot_ae_var_def,
		    COND_NONE_SOME_REWRITES, 
		    GSYM LEFT_FORALL_IMP_THM,
		    smallfoot_ap_points_to_def,
		    IS_SOME_EXISTS, GSYM LEFT_EXISTS_AND_THM,
		    FUNION_DEF, IN_SING, IN_UNION, FEVERY_DEF] THEN
   ASM_SIMP_TAC std_ss [],

 
   SIMP_TAC std_ss [SMALLFOOT_REL_HOARE_TRIPLE_def,
		    SMALLFOOT_PROGRAM_SEM_def,
		    smallfoot_prog_field_lookup_def,
		    FASL_PROGRAM_SEM___prim_command,
		    smallfoot_env_def, PAIR_FORALL_THM,
		    FASL_ATOMIC_ACTION_SEM_def,
		    EVAL_fasl_prim_command_THM,
		    SMALLFOOT_action_map_def,
		    COND_NONE_SOME_REWRITES, LET_THM, IN_ABS,
		    GSYM LEFT_FORALL_IMP_THM, IN_SING,
                    VAR_RES_STACK___IS_EQUAL_UPTO_VALUES_def,
		    var_res_sl___has_write_permission_def,
		    FAPPLY_FUPDATE_THM, FDOM_FUPDATE] THEN
   ONCE_REWRITE_TAC[EXTENSION] THEN
   SIMP_TAC (std_ss++bool_eq_imp_ss) [IN_INSERT, COND_RATOR,
				      COND_RAND] THEN
   SIMP_TAC std_ss [IN_ABS, NOT_IN_EMPTY, COND_RAND, COND_RATOR] THEN
   REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN 
   Cases_on `t IN FDOM (x2 ' (THE (SMALLFOOT_P_EXPRESSION_EVAL e x1)))` THEN (
      ASM_SIMP_TAC (std_ss++bool_eq_imp_ss++boolSimps.CONJ_ss) 
                          [FDOM_FUPDATE, FAPPLY_FUPDATE_THM,
			   EXTENSION, IN_INSERT, COND_REWRITES,
			   GSYM LEFT_FORALL_IMP_THM]
   ),
	 
   ALL_TAC
] THEN

Q.PAT_ASSUM `!c2. A ==> B` MP_TAC THEN
HO_MATCH_MP_TAC (prove (``((!n. A n) /\ ((!n. A n) ==> 
                       (!s. s IN P2 ==> ?n. s IN (P1 n)))) ==> 
((!n. A n ==> (SMALLFOOT_HOARE_TRIPLE res_env penv (P1 n) prog Q)) ==> 
 (SMALLFOOT_HOARE_TRIPLE res_env penv P2 prog Q))``, 

  SIMP_TAC (std_ss++boolSimps.CONJ_ss) [
     SMALLFOOT_HOARE_TRIPLE_def, FASL_PROGRAM_HOARE_TRIPLE_def,
     HOARE_TRIPLE_def, IN_ABS]
)) THEN
CONJ_TAC THEN1 (
   GEN_TAC THEN
   FULL_SIMP_TAC std_ss [smallfoot_prop___COND_INSERT] THEN
   CONJ_TAC THENL [
      FULL_SIMP_TAC std_ss [smallfoot_prop___COND___REWRITE,
			    bagTheory.BAG_IN_FINITE_BAG_IMAGE,
			    GSYM LEFT_EXISTS_AND_THM, 
			    GSYM LEFT_FORALL_IMP_THM,
			    bagTheory.BAG_IMAGE_FINITE,
			    bagTheory.FINITE_BAG_INSERT,
			    bagTheory.BAG_IN_BAG_INSERT, DISJ_IMP_THM,
			    FORALL_AND_THM,
			    SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___smallfoot_ap_var_update],


      MATCH_MP_TAC (el 1 (CONJUNCTS SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___compare)) THEN
      ASM_SIMP_TAC std_ss [SMALLFOOT_AE_USED_VARS_SUBSET___EVAL,
			   bagTheory.IN_SET_OF_BAG, bagTheory.BAG_IN_BAG_UNION,
			   SMALLFOOT_AE_USED_VARS_SUBSET___smallfoot_ae_var_update]
  ]
) THEN 
STRIP_TAC THEN GEN_TAC THEN

Cases_on `s` THEN
SIMP_TAC std_ss [smallfoot_slp_field_lookup_def, IN_ABS,
		 smallfoot_prop___PROP___REWRITE,
		 LET_THM,
		 var_res_sl___read_def,
		 COND_NONE_SOME_REWRITES,
		 LET_THM,
		 var_res_sl___has_write_permission_def,
		 var_res_sl___has_read_permission_def,
		 FDOM_FUPDATE, FAPPLY_FUPDATE_THM,
		 SMALLFOOT_STACK_UPDATE_VAR_def,
		 SMALLFOOT_STATE_UPDATE_VAR_def,
		 IN_INSERT] THEN
Tactical.REVERSE (Cases_on `v IN FDOM q`) THEN1 (
   ASM_SIMP_TAC std_ss [] THEN
   METIS_TAC[]
) THEN
`?c1 perm. q ' v = (c1, perm)` by (Cases_on `q ' v` THEN SIMP_TAC std_ss []) THEN
Tactical.REVERSE (Cases_on `perm = var_res_write_permission`) THEN1 (
   ASM_SIMP_TAC std_ss [] THEN
   DISJ1_TAC THEN 
   Q.EXISTS_TAC `v` THEN
   ASM_SIMP_TAC std_ss []
) THEN
ASM_SIMP_TAC std_ss [SMALLFOOT_STATE_REMOVE_HEAP_TAG_def,
		     LET_THM, FDOM_FUPDATE,
		     COND_REWRITES] THEN
`!v'. ((v' = v) \/ v' IN FDOM q) =
      (v' IN FDOM q)` by METIS_TAC[] THEN
ASM_SIMP_TAC std_ss [IN_INSERT, FAPPLY_FUPDATE_THM,
		     COND_REWRITES] THEN
SIMP_TAC (std_ss++boolSimps.CONJ_ss)
                [smallfoot_ae_stack_read_def,
		 COND_NONE_SOME_REWRITES,
		 GSYM LEFT_EXISTS_AND_THM,
		 GSYM RIGHT_EXISTS_AND_THM,
		 GSYM LEFT_FORALL_IMP_THM] THEN
Cases_on `!v'.
          BAG_IN v' wpb ==>
          v' IN FDOM q /\
          (~(v' = v) ==> (SND (q ' v') = var_res_write_permission))` THEN (
   ASM_REWRITE_TAC[]
) THEN
Cases_on `!v'. BAG_IN v' rpb ==> v' IN FDOM q` THEN ASM_REWRITE_TAC[] THEN
FULL_SIMP_TAC std_ss [IMP_CONJ_THM, FORALL_AND_THM] THEN
`!v'. BAG_IN v' wpb ==>
      (SND (q ' v') = var_res_write_permission)` by ALL_TAC THEN1 (
   GEN_TAC THEN
   Cases_on `v' = v` THEN
   ASM_SIMP_TAC std_ss []
) THEN
FULL_SIMP_TAC std_ss [] THEN
SIMP_TAC std_ss [GSYM RIGHT_EXISTS_IMP_THM] THEN
REPEAT GEN_TAC THEN
Q.EXISTS_TAC `c1` THEN


SIMP_TAC std_ss [smallfoot_ap_bigstar_REWRITE] THEN
ONCE_REWRITE_TAC[smallfoot_ap_star___swap] THEN
Q.ABBREV_TAC `P = (smallfoot_ap_star smallfoot_ap_stack_true
                   (smallfoot_ap_star
              (smallfoot_ap_points_to (SMALLFOOT_P_EXPRESSION_EVAL e) L)
              (smallfoot_ap_bigstar sfb)))` THEN
Q.ABBREV_TAC `P2 = (smallfoot_ap_star smallfoot_ap_stack_true
         (smallfoot_ap_bigstar
            (BAG_IMAGE (smallfoot_ap_var_update v c)
               (BAG_INSERT
                  (smallfoot_ap_points_to (SMALLFOOT_P_EXPRESSION_EVAL e) 
			(L |+ (t,smallfoot_ae_const c1)))
                  sfb))))` THEN
Q.ABBREV_TAC `P2' = (smallfoot_ap_star smallfoot_ap_stack_true
         (smallfoot_ap_bigstar
               (BAG_INSERT
                  (smallfoot_ap_points_to (SMALLFOOT_P_EXPRESSION_EVAL e) 
			(L |+ (t,smallfoot_ae_const c1)))
                  sfb)))` THEN
Q.ABBREV_TAC `P3 = (smallfoot_ap_star smallfoot_ap_stack_true
         (smallfoot_ap_bigstar sfb))` THEN


`SMALLFOOT_AP_PERMISSION_UNIMPORTANT P2 /\
 SMALLFOOT_AP_PERMISSION_UNIMPORTANT P2' /\
 SMALLFOOT_AP_PERMISSION_UNIMPORTANT P3 /\
 SMALLFOOT_AP_PERMISSION_UNIMPORTANT P` by ALL_TAC THEN1 (
    UNABBREV_ALL_TAC THEN
    FULL_SIMP_TAC std_ss [smallfoot_prop___COND___REWRITE,
			  GSYM smallfoot_ap_bigstar_REWRITE,
			  bagTheory.BAG_IN_BAG_INSERT,
			  DISJ_IMP_THM, FORALL_AND_THM,
			  SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS_def,
			  IMP_CONJ_THM, FORALL_AND_THM]  THEN
    REPEAT CONJ_TAC THEN (
       MATCH_MP_TAC SMALLFOOT_AP_PERMISSION_UNIMPORTANT___bigstar THEN
       ASM_SIMP_TAC std_ss [bagTheory.BAG_IN_BAG_INSERT,
			    DISJ_IMP_THM, FORALL_AND_THM,
			    bagTheory.BAG_INSERT_NOT_EMPTY,
			    SMALLFOOT_AP_PERMISSION_UNIMPORTANT___smallfoot_ap_stack_true] THEN
       METIS_TAC[]
    )
) THEN

`P2 = smallfoot_ap_var_update v c P2'` by ALL_TAC THEN1 (

   Q.UNABBREV_TAC `P2'` THEN
   Q.UNABBREV_TAC `P2` THEN
   SIMP_TAC std_ss [GSYM smallfoot_ap_bigstar_REWRITE] THEN
   ONCE_REWRITE_TAC [smallfoot_ap_bigstar_REWRITE] THEN
   MATCH_MP_TAC smallfoot_ap_var_update___smallfoot_ap_bigstar___ap_true THEN
   FULL_SIMP_TAC std_ss [smallfoot_prop___COND___REWRITE,
			 SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS_def,
			 bagTheory.FINITE_BAG_THM, bagTheory.BAG_IN_BAG_INSERT,
			 DISJ_IMP_THM, FORALL_AND_THM]
) THEN
Q.PAT_ASSUM `Abbrev (P2 = X)` (K ALL_TAC) THEN
FULL_SIMP_TAC std_ss [] THEN POP_ASSUM (K ALL_TAC) THEN

Q.UNABBREV_TAC `P` THEN
Q.UNABBREV_TAC `P2'` THEN
Q.PAT_ASSUM `Abbrev (P3 = X)` ASSUME_TAC THEN
FULL_SIMP_TAC std_ss [smallfoot_ap_star___swap_ap_stack_true,
		      smallfoot_prop___COND_INSERT, FORALL_AND_THM,
                      smallfoot_ap_bigstar_REWRITE] THEN
IMP_RES_TAC SMALLFOOT_AP_PERMISSION_UNIMPORTANT___IMP THEN

`!c2. SMALLFOOT_AP_PERMISSION_UNIMPORTANT
              (smallfoot_ap_equal (smallfoot_ae_var v)
                 (smallfoot_ae_const c2)) /\
      SMALLFOOT_AP_PERMISSION_UNIMPORTANT
              (smallfoot_ap_points_to (SMALLFOOT_P_EXPRESSION_EVAL e)
                 (L |+ (t,smallfoot_ae_const c2)))` by
   FULL_SIMP_TAC std_ss [SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS_def] THEN

ASM_SIMP_TAC std_ss [smallfoot_ap_star___PERMISSION_UNIMPORTANT] THEN
ASM_SIMP_TAC std_ss [IN_ABS, smallfoot_ap_equal_def,
		     smallfoot_ap_binexpression_def,
		     smallfoot_a_stack_proposition_def,
		     LET_THM, smallfoot_ae_const_def,
		     smallfoot_ae_var_def,
		     FUNION_FEMPTY_1,
		     FDOM_FEMPTY, DISJOINT_EMPTY,
		     FDOM_FUPDATE, IN_INSERT,
		     FAPPLY_FUPDATE_THM,
		     smallfoot_ap_points_to_def,
		     FEVERY_FEMPTY, smallfoot_ap_var_update_def,
		     SMALLFOOT_STATE_UPDATE_VAR_def,
		     SMALLFOOT_STACK_UPDATE_VAR_def,
		     COND_NONE_SOME_REWRITES,
		     smallfoot_ae_stack_read_def] THEN
SIMP_TAC (std_ss++bool_eq_imp_ss) [] THEN
Cases_on `c2 = c` THEN ASM_SIMP_TAC (std_ss++boolSimps.CONJ_ss) [] THEN
REPEAT STRIP_TAC THENL [
   Q.EXISTS_TAC `h1` THEN
   Q.EXISTS_TAC `h2'` THEN
   ASM_SIMP_TAC std_ss [] THEN
   FULL_SIMP_TAC std_ss [FEVERY_DEF,
                         FDOM_FUPDATE, IN_INSERT] THEN
   GEN_TAC THEN
   Cases_on `x = t` THEN (
     FULL_SIMP_TAC std_ss [FAPPLY_FUPDATE_THM,
			   FUNION_DEF, IN_SING]
   ),


   Q.EXISTS_TAC `DRESTRICT r {loc}` THEN
   Q.EXISTS_TAC `h2'` THEN
   ASM_SIMP_TAC std_ss [DRESTRICT_DEF, IN_INTER, IN_SING] THEN
   `(FDOM r INTER {loc} = {loc}) /\
    (loc INSERT FDOM r = FDOM r) /\
    ({loc} UNION FDOM r = FDOM r)` by ALL_TAC THEN1 (
     ASM_SIMP_TAC (std_ss++bool_eq_imp_ss) [EXTENSION, IN_INTER, IN_SING, IN_UNION, IN_INSERT]
   ) THEN
   ASM_SIMP_TAC std_ss [] THEN
   CONJ_TAC THENL [
     Q.PAT_ASSUM `X = FUNION h1 h2'` (MP_TAC o GSYM) THEN
     ASM_SIMP_TAC (std_ss++boolSimps.CONJ_ss) [GSYM fmap_EQ_THM,
			  FUNION_DEF, DRESTRICT_DEF,
			  FDOM_FUPDATE, IN_SING] THEN
     STRIP_TAC THEN GEN_TAC THEN STRIP_TAC THEN
     Q.PAT_ASSUM `!x. X x` (MP_TAC o Q.SPEC `x`) THEN
     Cases_on `x = loc` THEN (
        ASM_SIMP_TAC std_ss [FAPPLY_FUPDATE_THM]
     ),


     FULL_SIMP_TAC std_ss [FEVERY_DEF,
                         FDOM_FUPDATE, IN_INSERT] THEN
     GEN_TAC THEN
     Cases_on `x = t` THEN (
        FULL_SIMP_TAC std_ss [FAPPLY_FUPDATE_THM,
			   FUNION_DEF, IN_SING, IN_UNION]
     ) THEN
     `h1 ' loc = r ' loc \\ t` by ALL_TAC THEN1 (
        `h1 ' loc = (FUNION h1 h2' ' loc)` by ASM_SIMP_TAC std_ss [FUNION_DEF, IN_SING] THEN
	Q.PAT_ASSUM `X = FUNION h1 h2'` (ASSUME_TAC o GSYM) THEN
        FULL_SIMP_TAC std_ss [FAPPLY_FUPDATE_THM]
     ) THEN
     ASM_SIMP_TAC std_ss [DOMSUB_FAPPLY_THM] THEN
     STRIP_TAC THEN
     `x IN FDOM (h1 ' loc)` by RES_TAC THEN
     POP_ASSUM MP_TAC THEN
     ONCE_ASM_REWRITE_TAC[] THEN
     SIMP_TAC std_ss [FDOM_DOMSUB, IN_DELETE]
  ]
]);







val SMALLFOOT_COND_INFERENCE___prog_field_assign =
store_thm ("SMALLFOOT_COND_INFERENCE___prog_field_assign",
``
 !wpb rpb v e1 e2 t sfb prog Q.

(THE (SMALLFOOT_PE_USED_VARS e2) SUBSET (SET_OF_BAG (BAG_UNION wpb rpb)) /\
 SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS
      (SET_OF_BAG (BAG_UNION wpb rpb))
      (smallfoot_ap_points_to (SMALLFOOT_P_EXPRESSION_EVAL e1)
         (L |+ (t,SMALLFOOT_P_EXPRESSION_EVAL e2))))

==>
((SMALLFOOT_COND_HOARE_TRIPLE
   (smallfoot_prop (wpb,rpb) 
      (BAG_INSERT (smallfoot_ap_points_to (SMALLFOOT_P_EXPRESSION_EVAL e1) (L |+ (t, SMALLFOOT_P_EXPRESSION_EVAL e2))) 
       sfb))
    prog Q) ==>


(SMALLFOOT_COND_HOARE_TRIPLE 
   (smallfoot_prop (wpb,rpb) 
      (BAG_INSERT (smallfoot_ap_points_to (SMALLFOOT_P_EXPRESSION_EVAL e1) L) 
       sfb))

   (fasl_prog_seq (smallfoot_prog_field_assign e1 t e2) prog)

   Q))
``,

REPEAT STRIP_TAC THEN
`?Q_ap Q_cond. Q = (Q_cond, Q_ap)` by (Cases_on `Q` THEN SIMP_TAC std_ss []) THEN
FULL_SIMP_TAC std_ss [SMALLFOOT_COND_HOARE_TRIPLE_def, smallfoot_prop___REWRITE] THEN
REPEAT STRIP_TAC THEN
MATCH_MP_TAC SMALLFOOT_INFERENCE_prog_slp___IMP THEN
SIMP_TAC std_ss [fasl_slp_opt___smallfoot_prog_field_assign,
		 COND_NONE_SOME_REWRITES] THEN
`?e2vs. SMALLFOOT_PE_USED_VARS e2 = SOME e2vs` by
   PROVE_TAC [SMALLFOOT_PE_USED_VARS___IS_SOME, IS_SOME_EXISTS] THEN
REPEAT STRIP_TAC THENL [
   MATCH_MP_TAC smallfoot_ae_is_defined___IMPL THEN
   FULL_SIMP_TAC std_ss [GSYM SMALLFOOT_PE_USED_VARS_def],


   FULL_SIMP_TAC std_ss [smallfoot_ap_implies_in_heap_def,
			 smallfoot_prop___PROP_INSERT,
			 GSYM LEFT_FORALL_IMP_THM,
			 smallfoot_ap_points_to_def, IN_ABS,
			 LET_THM, FDOM_FUNION, IN_UNION,
			 IN_SING],
 

   SIMP_TAC std_ss [SMALLFOOT_REL_HOARE_TRIPLE_def,
		    SMALLFOOT_PROGRAM_SEM_def,
		    smallfoot_prog_field_assign_def,
		    FASL_PROGRAM_SEM___prim_command,
		    smallfoot_env_def, PAIR_FORALL_THM,
		    FASL_ATOMIC_ACTION_SEM_def,
		    EVAL_fasl_prim_command_THM,
		    SMALLFOOT_action_map_def,
		    COND_NONE_SOME_REWRITES, LET_THM, IN_ABS,
		    GSYM LEFT_FORALL_IMP_THM, IN_SING,
                    VAR_RES_STACK___IS_EQUAL_UPTO_VALUES___REFL],

   ALL_TAC
] THEN

Q.PAT_ASSUM `A ==> B` MP_TAC THEN
MATCH_MP_TAC (prove (``(A /\ (A ==> (!x. x IN P2 ==> x IN P1))) ==> ((A ==> (SMALLFOOT_HOARE_TRIPLE res_env penv P1 prog Q)) ==> (SMALLFOOT_HOARE_TRIPLE res_env penv P2 prog Q))``, 
		       SIMP_TAC std_ss [FASL_PROGRAM_HOARE_TRIPLE_REWRITE, SMALLFOOT_HOARE_TRIPLE_def, IN_ABS])) THEN
CONJ_TAC THEN1 (
   FULL_SIMP_TAC std_ss [smallfoot_prop___COND_INSERT]
) THEN
STRIP_TAC THEN GEN_TAC THEN
ASM_SIMP_TAC std_ss [smallfoot_prop___PROP_INSERT] THEN

Cases_on `x` THEN

Q.ABBREV_TAC `ee1 = SMALLFOOT_P_EXPRESSION_EVAL e1` THEN
Q.ABBREV_TAC `ee2 = SMALLFOOT_P_EXPRESSION_EVAL e2` THEN

ASM_SIMP_TAC std_ss [smallfoot_slp_field_assign_def, IN_ABS,
		     LET_THM, SMALLFOOT_STATE_UPDATE_HEAP_def,
      		 smallfoot_ap_points_to_def, FEVERY_DEF,
		 SMALLFOOT_STATE_REMOVE_HEAP_TAG_def,
		 FDOM_FUPDATE, IN_INSERT, DISJ_IMP_THM,
		 FORALL_AND_THM, FAPPLY_FUPDATE_THM] THEN

Cases_on `IS_SOME (ee1 q)` THEN ASM_REWRITE_TAC[] THEN
Cases_on `IS_SOME (ee2 q)` THEN ASM_REWRITE_TAC[] THEN
`?eev1. ee1 q = SOME eev1` by FULL_SIMP_TAC std_ss [IS_SOME_EXISTS] THEN
`?eev2. ee2 q = SOME eev2` by FULL_SIMP_TAC std_ss [IS_SOME_EXISTS] THEN
ASM_SIMP_TAC (std_ss++boolSimps.CONJ_ss) [smallfoot_ae_stack_read_def,
		     COND_NONE_SOME_REWRITES] THEN
REPEAT STRIP_TAC THEN (

   Q.EXISTS_TAC `FEMPTY |+ (eev1, r ' eev1)` THEN
   Q.EXISTS_TAC `h2` THEN
   Q.PAT_ASSUM `X = FUNION h1 h2` MP_TAC THEN
   ASM_SIMP_TAC std_ss [GSYM fmap_EQ_THM,
			   FDOM_FUPDATE, IN_INSERT,
			   DISJ_IMP_THM, FORALL_AND_THM,
			   FAPPLY_FUPDATE_THM, FUNION_DEF,
			   NOT_IN_EMPTY, FDOM_FEMPTY] THEN
   `eev1 INSERT FDOM r = FDOM r` by ALL_TAC THEN1 (
       SIMP_TAC (std_ss++bool_eq_imp_ss) [EXTENSION, IN_INSERT] THEN
       ASM_REWRITE_TAC[]
   ) THEN
   FULL_SIMP_TAC std_ss [] THEN POP_ASSUM (K ALL_TAC) THEN
   `t INSERT FDOM (r ' eev1) = FDOM (r ' eev1)` by ALL_TAC THEN1 (
       SIMP_TAC (std_ss++bool_eq_imp_ss) [EXTENSION, IN_INSERT] THEN
       ASM_SIMP_TAC std_ss []
   ) THEN
   FULL_SIMP_TAC std_ss [] THEN POP_ASSUM (K ALL_TAC) THEN
   STRIP_TAC THEN
   Q.PAT_ASSUM `FDOM r = X` ASSUME_TAC THEN
   TRY (Q.PAT_ASSUM `FDOM (r ' eev1) = X` ASSUME_TAC) THEN
   REPEAT (Q.PAT_ASSUM `!x. x IN X ==> Y x` MP_TAC) THEN
   Q.PAT_ASSUM `X = eev2` (ASSUME_TAC o GSYM) THEN

   `!x. x IN FDOM h2 ==> ~(x = eev1)` by ALL_TAC THEN1 (
      Q.PAT_ASSUM `DISJOINT X (FDOM h2)` MP_TAC THEN
      SIMP_TAC std_ss [EXTENSION, IN_INTER, IN_SING, NOT_IN_EMPTY,
		       DISJOINT_DEF]
   ) THEN

   ASM_SIMP_TAC std_ss [IN_UNION, IN_SING, DISJ_IMP_THM, 
			 FORALL_AND_THM, FDOM_FUPDATE,
		        IN_INSERT, FAPPLY_FUPDATE_THM,
		        DOMSUB_FAPPLY_THM]

) THENL [
   `t INSERT FDOM (h1 ' eev1) = FDOM (h1 ' eev1)` by ALL_TAC THEN1 (
       FULL_SIMP_TAC (std_ss++bool_eq_imp_ss) [EXTENSION, IN_INSERT]
   ) THEN
   FULL_SIMP_TAC std_ss [COND_RATOR, COND_RAND] THEN
   SIMP_TAC (std_ss++boolSimps.CONJ_ss) [] THEN
   METIS_TAC[],


   Q.PAT_ASSUM `X = FDOM (h1 ' eev1)` (ASSUME_TAC o GSYM) THEN
   ASM_SIMP_TAC std_ss [FDOM_DOMSUB, IN_DELETE]
]);
















val SMALLFOOT_COND_INFERENCE___prog_dispose =
store_thm ("SMALLFOOT_COND_INFERENCE___prog_dispose",
``
 !wpb rpb e sfb prog Q.

((SMALLFOOT_COND_HOARE_TRIPLE 
   (smallfoot_prop (wpb,rpb) sfb))
    prog Q) ==>


(SMALLFOOT_COND_HOARE_TRIPLE 
   (smallfoot_prop (wpb,rpb) (BAG_INSERT (smallfoot_ap_points_to (SMALLFOOT_P_EXPRESSION_EVAL e) L) 
       sfb))

   (fasl_prog_seq (smallfoot_prog_dispose e) prog)

   Q)
``,

REPEAT STRIP_TAC THEN
`?Q_ap Q_cond. Q = (Q_cond, Q_ap)` by (Cases_on `Q` THEN SIMP_TAC std_ss []) THEN
FULL_SIMP_TAC std_ss [SMALLFOOT_COND_HOARE_TRIPLE_def, smallfoot_prop___REWRITE] THEN
REPEAT STRIP_TAC THEN
MATCH_MP_TAC SMALLFOOT_INFERENCE_prog_slp___IMP THEN
SIMP_TAC std_ss [fasl_slp_opt___smallfoot_prog_dispose,
		 COND_NONE_SOME_REWRITES] THEN
REPEAT STRIP_TAC THENL [
   FULL_SIMP_TAC std_ss [smallfoot_ap_implies_in_heap_def,
			 smallfoot_prop___PROP_INSERT,
			 GSYM LEFT_FORALL_IMP_THM,
			 smallfoot_ap_points_to_def, IN_ABS,
			 LET_THM, FDOM_FUNION, IN_UNION,
			 IN_SING],


   SIMP_TAC std_ss [SMALLFOOT_REL_HOARE_TRIPLE_def,
		    SMALLFOOT_PROGRAM_SEM_def,
		    smallfoot_prog_dispose_def,
		    FASL_PROGRAM_SEM___prim_command,
		    smallfoot_env_def, PAIR_FORALL_THM,
		    FASL_ATOMIC_ACTION_SEM_def,
		    EVAL_fasl_prim_command_THM,
		    SMALLFOOT_action_map_def,
		    COND_NONE_SOME_REWRITES, LET_THM, IN_ABS,
		    GSYM LEFT_FORALL_IMP_THM, IN_SING,
                    VAR_RES_STACK___IS_EQUAL_UPTO_VALUES___REFL],

   ALL_TAC
] THEN
Q.PAT_ASSUM `A ==> B` MP_TAC THEN
MATCH_MP_TAC (prove (``(A /\ (A ==> (!x. x IN P2 ==> x IN P1))) ==> ((A ==> (SMALLFOOT_HOARE_TRIPLE res_env penv P1 prog Q)) ==> (SMALLFOOT_HOARE_TRIPLE res_env penv P2 prog Q))``, 
		       SIMP_TAC std_ss [FASL_PROGRAM_HOARE_TRIPLE_REWRITE, IN_ABS, SMALLFOOT_HOARE_TRIPLE_def])) THEN
CONJ_TAC THEN1 (
   FULL_SIMP_TAC std_ss [smallfoot_prop___COND_INSERT]
) THEN
STRIP_TAC THEN GEN_TAC THEN
ASM_SIMP_TAC std_ss [smallfoot_prop___PROP_INSERT] THEN

Cases_on `x` THEN
SIMP_TAC std_ss [smallfoot_slp_dispose_def, IN_ABS] THEN
REPEAT STRIP_TAC THEN
Q.PAT_ASSUM `DISJOINT X Y` MP_TAC THEN
Q.PAT_ASSUM `(q,h1) IN X` MP_TAC THEN
Q.PAT_ASSUM `(q,h2) IN X` MP_TAC THEN

ASM_SIMP_TAC std_ss [smallfoot_ap_points_to_def,
		     IN_ABS, LET_THM] THEN
REPEAT STRIP_TAC THEN
Tactical.REVERSE (`h2 = r` by ALL_TAC) THEN1 FULL_SIMP_TAC std_ss [] THEN
Q.PAT_ASSUM `X = FUNION h1 h2` MP_TAC THEN
FULL_SIMP_TAC std_ss [GSYM fmap_EQ_THM, FUNION_DEF, FDOM_FUPDATE,
		     INSERT_UNION, UNION_EMPTY, DISJOINT_DEF,
		     EXTENSION, NOT_IN_EMPTY, IN_INTER, IN_SING,
		      IN_INSERT, DISJ_IMP_THM, FORALL_AND_THM,
		      FAPPLY_FUPDATE_THM, IN_UNION] THEN
METIS_TAC[]);



(*
val asl_exists___OVER___asl_and = store_thm ("asl_exists___OVER___asl_and",
``asl_and (asl_exists x. P1 x) P2 =
  asl_exists x. (asl_and (P1 x) P2)``,

ONCE_REWRITE_TAC[EXTENSION] THEN
SIMP_TAC std_ss [asl_bool_EVAL, asl_exists_def, IN_ABS,
		 LEFT_EXISTS_AND_THM]);

*)



val smallfoot_ae_stack_read___SUBSTATE = store_thm (
"smallfoot_ae_stack_read___SUBSTATE",
``
!e t s s' y.
((smallfoot_ae_stack_read e t s = SOME y) /\
(SMALLFOOT_IS_SUBSTATE s s') /\
IS_SOME___SMALLFOOT_AE_USED_VARS e)

==>

(smallfoot_ae_stack_read e t s' = SOME y)
``,

SIMP_TAC std_ss [smallfoot_ae_stack_read_def, COND_RAND, COND_RATOR] THEN
REPEAT GEN_TAC THEN STRIP_TAC THEN
`e (FST s') = e (FST s)` by ALL_TAC THEN1 (
   `IS_SOME (e (FST s))` by ASM_SIMP_TAC std_ss [] THEN
   Q.PAT_ASSUM `X = SOME loc` (K ALL_TAC) THEN
   FULL_SIMP_TAC std_ss [IS_SOME___SMALLFOOT_AE_USED_VARS___REWRITE,
                         SMALLFOOT_AE_USED_VARS_REL___REWRITE] THEN
   Q.PAT_ASSUM `!st1 st2. X st1 st2` MATCH_MP_TAC THEN

   Q.PAT_ASSUM `IS_SOME X` MP_TAC THEN
   FULL_SIMP_TAC std_ss [SMALLFOOT_IS_SUBSTATE_REWRITE,
			 VAR_RES_STACK_IS_SUBSTATE_REWRITE] THEN
   METIS_TAC[SUBSET_DEF]
) THEN
ASM_SIMP_TAC std_ss [] THEN
FULL_SIMP_TAC std_ss [SMALLFOOT_IS_SUBSTATE_REWRITE,
		      ASL_IS_SUBSTATE_def,
		      DISJOINT_FMAP_UNION_def] THEN
FULL_SIMP_TAC std_ss [FUNION_DEF, IN_UNION, BIN_OPTION_MAP_THM]);






(*
val SMALLFOOT_CHOICE_IS_INDEPENDEND_FROM_SUBSTATE_def = Define
`SMALLFOOT_CHOICE_IS_INDEPENDEND_FROM_SUBSTATE qP =
 !s s1 s2 x1 x2. 
           (SMALLFOOT_IS_SUBSTATE s1 s /\ SMALLFOOT_IS_SUBSTATE s2 s /\
            (?y. s1 IN qP x1 y) /\ (?y. s2 IN qP x2 y)) ==>
            (?y. s1 IN qP x2 y)`;





val SMALLFOOT_COND_CHOICE_IS_INDEPENDEND_FROM_SUBSTATE_def = Define
`SMALLFOOT_COND_CHOICE_IS_INDEPENDEND_FROM_SUBSTATE qP =
 SMALLFOOT_CHOICE_IS_INDEPENDEND_FROM_SUBSTATE (\x y. (SND (qP x y)))`
*)

val smallfoot_prop___SUBSTATE = store_thm (
"smallfoot_prop___SUBSTATE",
``!wpb rpb sfb s1 s2.
(SMALLFOOT_IS_SUBSTATE s1 s2 /\
smallfoot_prop___COND (wpb,rpb) sfb /\
s1 IN smallfoot_prop___PROP (wpb,rpb) sfb) ==>
(FST s2, SND s1) IN smallfoot_prop___PROP (wpb,rpb) sfb``,


SIMP_TAC std_ss [smallfoot_prop___PROP___REWRITE, IN_ABS,
		 smallfoot_prop___COND___EXPAND] THEN
REPEAT STRIP_TAC THENL [
   RES_TAC THEN
   FULL_SIMP_TAC std_ss [SMALLFOOT_IS_SUBSTATE_REWRITE,
			 VAR_RES_STACK_IS_SUBSTATE_REWRITE,
			 var_res_sl___has_write_permission_def,
			 SUBSET_DEF] THEN
   METIS_TAC[IS_VAR_RES_SUBPERMISSION_THM],


   RES_TAC THEN
   FULL_SIMP_TAC std_ss [SMALLFOOT_IS_SUBSTATE_REWRITE,
			 VAR_RES_STACK_IS_SUBSTATE_REWRITE,
			 var_res_sl___has_read_permission_def,
			 SUBSET_DEF],


   Q.ABBREV_TAC `P = smallfoot_ap_star smallfoot_ap_stack_true
             (smallfoot_ap_bigstar sfb)` THEN
   Q.PAT_ASSUM `SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS X P`
      (MATCH_MP_TAC o REWRITE_RULE [SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___ALTERNATIVE_DEF_2]) THEN
   Q.EXISTS_TAC `s1` THEN
   FULL_SIMP_TAC std_ss [SMALLFOOT_IS_SUBSTATE_REWRITE,
			 VAR_RES_STACK_IS_SUBSTATE_REWRITE,
			 SUBSET_DEF, IN_INTER]
]);


(*
val SMALLFOOT_COND_CHOICE_IS_INDEPENDEND_FROM_SUBSTATE___not_used =
store_thm ("SMALLFOOT_COND_CHOICE_IS_INDEPENDEND_FROM_SUBSTATE___not_used",
``!P. SMALLFOOT_COND_CHOICE_IS_INDEPENDEND_FROM_SUBSTATE (\y z. P z)``,

SIMP_TAC std_ss [SMALLFOOT_COND_CHOICE_IS_INDEPENDEND_FROM_SUBSTATE_def,
		 SMALLFOOT_CHOICE_IS_INDEPENDEND_FROM_SUBSTATE_def]);





val SMALLFOOT_COND_CHOICE_IS_INDEPENDEND_FROM_SUBSTATE___points_to =
store_thm ("SMALLFOOT_COND_CHOICE_IS_INDEPENDEND_FROM_SUBSTATE___points_to",
``
!wpb rpb e L t sfb.

SMALLFOOT_COND_CHOICE_IS_INDEPENDEND_FROM_SUBSTATE (\y z.
  smallfoot_prop (wpb,rpb) (BAG_INSERT 
			       (smallfoot_ap_points_to e ((L y z) |+ (t, smallfoot_ae_const y)))
                               (sfb y z)))``,


SIMP_TAC std_ss [SMALLFOOT_COND_CHOICE_IS_INDEPENDEND_FROM_SUBSTATE_def,
		 SMALLFOOT_CHOICE_IS_INDEPENDEND_FROM_SUBSTATE_def,
		 smallfoot_prop___REWRITE] THEN
SIMP_TAC std_ss [COND_RAND, COND_RATOR, asl_bool_EVAL] THEN

REPEAT GEN_TAC THEN
Q.ABBREV_TAC `c = \z y. smallfoot_prop___COND (wpb,rpb)
           (BAG_INSERT
              (smallfoot_ap_points_to e (L y z |+ (t,smallfoot_ae_const y)))
              (sfb y z))` THEN
`!z y. smallfoot_prop___COND (wpb,rpb)
           (BAG_INSERT
              (smallfoot_ap_points_to e (L y z |+ (t,smallfoot_ae_const y)))
              (sfb y z)) = c z y` by ALL_TAC THEN1 (
  Q.UNABBREV_TAC `c` THEN SIMP_TAC std_ss []
) THEN
ASM_REWRITE_TAC[] THEN POP_ASSUM (K ALL_TAC) THEN

Q.ABBREV_TAC `P = \z y. smallfoot_prop___PROP (wpb,rpb)
           (BAG_INSERT
              (smallfoot_ap_points_to e (L y z |+ (t,smallfoot_ae_const y)))
              (sfb y z))` THEN
`!z y. smallfoot_prop___PROP (wpb,rpb)
           (BAG_INSERT
              (smallfoot_ap_points_to e (L y z |+ (t,smallfoot_ae_const y)))
              (sfb y z)) = P z y` by ALL_TAC THEN1 (
  Q.UNABBREV_TAC `P` THEN SIMP_TAC std_ss []
) THEN
ASM_REWRITE_TAC[] THEN POP_ASSUM (K ALL_TAC) THEN

REPEAT STRIP_TAC THEN
Tactical.REVERSE (`y = y'` by ALL_TAC) THEN1 METIS_TAC[] THEN

`!s' z y. c z y /\ s' IN P z y /\
          SMALLFOOT_IS_SUBSTATE s' s ==> (smallfoot_ae_stack_read e t s = SOME y)` by ALL_TAC THEN1 (


   Q.UNABBREV_TAC `P` THEN
   Q.UNABBREV_TAC `c` THEN
   REPEAT (POP_ASSUM (K ALL_TAC)) THEN
   SIMP_TAC std_ss [IN_ABS] THEN
   REPEAT STRIP_TAC THEN
   `(FST s, SND s') IN
          smallfoot_prop___PROP (wpb,rpb)
            (BAG_INSERT
               (smallfoot_ap_points_to e (L y z |+ (t,smallfoot_ae_const y)))
               (sfb y z))` by METIS_TAC[smallfoot_prop___SUBSTATE] THEN
   POP_ASSUM MP_TAC THEN
   ASM_SIMP_TAC std_ss [IN_ABS, smallfoot_prop___PROP_INSERT] THEN
   SIMP_TAC (std_ss++boolSimps.CONJ_ss) [smallfoot_ap_points_to_def, LET_THM,
		    pairTheory.ELIM_UNCURRY, FEVERY_DEF,
		    FDOM_FUPDATE, IN_INSERT, DISJ_IMP_THM,
		    FORALL_AND_THM, FAPPLY_FUPDATE_THM,
		    smallfoot_ae_const_def, IN_ABS,
		    IS_SOME_EXISTS, GSYM RIGHT_EXISTS_AND_THM,
		    GSYM LEFT_EXISTS_AND_THM] THEN
   REPEAT STRIP_TAC THEN
   `(SND s ' y' = h1 ' y') /\ (y' IN FDOM (SND s))` by ALL_TAC THEN1 (
      FULL_SIMP_TAC std_ss [SMALLFOOT_IS_SUBSTATE_REWRITE,
			    ASL_IS_SUBSTATE_def,
			    DISJOINT_FMAP_UNION_def, 
			    BIN_OPTION_MAP_THM, COND_RAND, COND_RATOR] THEN
      Q.PAT_ASSUM `X = SND s` (ASSUME_TAC o GSYM) THEN
      ASM_SIMP_TAC std_ss [FUNION_DEF, IN_UNION, IN_SING]
   ) THEN
 
   ASM_SIMP_TAC std_ss [smallfoot_ae_stack_read_def]  
) THEN


METIS_TAC[SOME_11]);


*)





val smallfoot_ap_bag_implies_in_heap_or_null_def = Define `
  smallfoot_ap_bag_implies_in_heap_or_null sfb e =
  (BAG_EVERY SMALLFOOT_AP_PERMISSION_UNIMPORTANT sfb ==>
  (!s. s IN (smallfoot_ap_bigstar (BAG_INSERT smallfoot_ap_stack_true sfb)) ==>
      (?c. (e (FST s) = SOME c) /\ (c IN 0 INSERT FDOM (SND s)))))`;


(*
val SMALLFOOT_COND_CHOICE_IS_INDEPENDEND_FROM_SUBSTATE___cyclic_list = 
store_thm ("SMALLFOOT_COND_CHOICE_IS_INDEPENDEND_FROM_SUBSTATE___cyclic_list",
``
!wpb rpb e1 data e2 L t sfb.

(IS_SOME___SMALLFOOT_AE_USED_VARS e1 /\
(!y z. ~(e1 = e2) ==> smallfoot_ap_bag_implies_in_heap_or_null (sfb y z) e2))
==>
SMALLFOOT_COND_CHOICE_IS_INDEPENDEND_FROM_SUBSTATE (\y z.
  smallfoot_prop (wpb,rpb) (BAG_INSERT 
                               (smallfoot_ap_data_list_seg t e1 data (smallfoot_ae_const y))
                            (BAG_INSERT 
			       (smallfoot_ap_points_to (smallfoot_ae_const y) ((L y z) |+ (t, e2)))
                               (sfb y z))))``,


SIMP_TAC std_ss [SMALLFOOT_COND_CHOICE_IS_INDEPENDEND_FROM_SUBSTATE_def,
		 SMALLFOOT_CHOICE_IS_INDEPENDEND_FROM_SUBSTATE_def,
                 smallfoot_prop___REWRITE] THEN
SIMP_TAC std_ss [COND_RAND, COND_RATOR, asl_bool_EVAL] THEN

REPEAT GEN_TAC THEN
Q.ABBREV_TAC `c = \z y. smallfoot_prop___COND (wpb,rpb)
           (BAG_INSERT (smallfoot_ap_data_list_seg t e1 data (smallfoot_ae_const y))
              (BAG_INSERT
                 (smallfoot_ap_points_to (smallfoot_ae_const y)
                    (L y z |+ (t,e2))) (sfb y z)))` THEN
`!z y. smallfoot_prop___COND (wpb,rpb)
           (BAG_INSERT (smallfoot_ap_data_list_seg t e1 data (smallfoot_ae_const y))
              (BAG_INSERT
                 (smallfoot_ap_points_to (smallfoot_ae_const y)
                    (L y z |+ (t,e2))) (sfb y z))) = c z y` by ALL_TAC THEN1 (
  Q.UNABBREV_TAC `c` THEN SIMP_TAC std_ss []
) THEN
ASM_REWRITE_TAC[] THEN POP_ASSUM (K ALL_TAC) THEN

Q.ABBREV_TAC `P = \z y. smallfoot_prop___PROP (wpb,rpb)
           (BAG_INSERT (smallfoot_ap_data_list_seg t e1 data (smallfoot_ae_const y))
              (BAG_INSERT
                 (smallfoot_ap_points_to (smallfoot_ae_const y)
                    (L y z |+ (t,e2))) (sfb y z)))` THEN
`!z y. smallfoot_prop___PROP (wpb,rpb)
           (BAG_INSERT (smallfoot_ap_data_list_seg t e1 data (smallfoot_ae_const y))
              (BAG_INSERT
                 (smallfoot_ap_points_to (smallfoot_ae_const y)
                    (L y z |+ (t,e2))) (sfb y z))) = P z y` by ALL_TAC THEN1 (
  Q.UNABBREV_TAC `P` THEN SIMP_TAC std_ss []
) THEN
ASM_REWRITE_TAC[] THEN POP_ASSUM (K ALL_TAC) THEN

REPEAT STRIP_TAC THEN
Tactical.REVERSE (`y = y'` by ALL_TAC) THEN1 METIS_TAC[] THEN

`?st h1 h2. (st = FST s) /\ (h1 = SND s1) /\ (h2 = SND s2)` by ALL_TAC THEN1 (
   Cases_on `s` THEN
   Cases_on `s1` THEN
   Cases_on `s2` THEN
   SIMP_TAC std_ss []
) THEN

`ASL_IS_SUBSTATE DISJOINT_FMAP_UNION h1 (SND s) /\
 ASL_IS_SUBSTATE DISJOINT_FMAP_UNION h2 (SND s)` by ALL_TAC THEN1 (
   FULL_SIMP_TAC std_ss [SMALLFOOT_IS_SUBSTATE_REWRITE]
) THEN
`(st,h1) IN P z y /\ (st,h2) IN P z' y'` by ALL_TAC THEN1 (
   Q.UNABBREV_TAC `P` THEN
   Q.UNABBREV_TAC `c` THEN
   FULL_SIMP_TAC std_ss [] THEN
   `(FST s = st) /\ (SND s1 = h1) /\ (SND s2 = h2)` by ASM_SIMP_TAC std_ss [] THEN
   METIS_TAC[smallfoot_prop___SUBSTATE]
) THEN

Q.PAT_ASSUM `s1 IN X` (K ALL_TAC) THEN
Q.PAT_ASSUM `s2 IN X` (K ALL_TAC) THEN


Q.ABBREV_TAC `P2 = \y'' z''. asl_and (\s. ~(e1 = e2) ==> ((THE (e2 (FST s)) = 0) \/ ~(THE (e2 (FST s)) IN FDOM (SND s))))
	(smallfoot_ap_star
        (smallfoot_ap_data_list_seg t e1 data (smallfoot_ae_const y''))
        (smallfoot_ap_points_to (smallfoot_ae_const y'') (L y'' z'' |+ (t,e2))))` THEN

`!s z y. c z y /\ s IN P z y ==> ?h. ASL_IS_SUBSTATE DISJOINT_FMAP_UNION h (SND s) /\
			    (FST s, h) IN P2 y z` by ALL_TAC THEN1 (

   Q.UNABBREV_TAC `P` THEN
   Q.UNABBREV_TAC `P2` THEN
   Q.UNABBREV_TAC `c` THEN
   SIMP_TAC (std_ss++boolSimps.CONJ_ss) [smallfoot_prop___PROP_INSERT, IN_ABS,
					 smallfoot_prop___COND_INSERT] THEN
   SIMP_TAC (std_ss++boolSimps.CONJ_ss) [smallfoot_ap_star___PERMISSION_UNIMPORTANT,
					 SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS_def,
					 IN_ABS, asl_bool_EVAL] THEN
   SIMP_TAC std_ss [GSYM RIGHT_EXISTS_AND_THM, PAIR_FORALL_THM,
		    GSYM LEFT_FORALL_IMP_THM] THEN
   REPEAT STRIP_TAC THEN
   Q.EXISTS_TAC `h1'` THEN
   Q.EXISTS_TAC `h1''` THEN 
   FULL_SIMP_TAC std_ss [FUNION_DEF, DISJOINT_UNION_BOTH, DISJOINT_SYM] THEN
   ASM_SIMP_TAC std_ss [ASL_IS_SUBSTATE___DISJOINT_FMAP_UNION,
		        FUNION_DEF, SUBSET_DEF, IN_UNION] THEN
   REPEAT CONJ_TAC THENL [
      METIS_TAC[],
      METIS_TAC[],
      

      STRIP_TAC THEN
      Tactical.REVERSE (`?e2_c. (e2 x1 = SOME e2_c) /\ (e2_c IN 0 INSERT FDOM h2')` by ALL_TAC) THEN1 (
         FULL_SIMP_TAC std_ss [DISJOINT_DEF, EXTENSION, NOT_IN_EMPTY, IN_INTER,
			       IN_INSERT] THEN
	 METIS_TAC[]        
      ) THEN
      FULL_SIMP_TAC std_ss [] THEN
      Q.PAT_ASSUM `!y z. smallfoot_ap_bag_implies_in_heap_or_null X e2` MP_TAC THEN

      SIMP_TAC std_ss [smallfoot_ap_bag_implies_in_heap_or_null_def,
		       GSYM RIGHT_EXISTS_AND_THM,
		       GSYM LEFT_EXISTS_IMP_THM, GSYM RIGHT_FORALL_IMP_THM] THEN
      Q.EXISTS_TAC `y''` THEN
      Q.EXISTS_TAC `z''` THEN
      Q.EXISTS_TAC `(x1, h2')` THEN
      Q.PAT_ASSUM `(x1,h2') IN X` MP_TAC THEN
      Q.PAT_ASSUM `smallfoot_prop___COND X (sfb y'' z'')` MP_TAC THEN
      FULL_SIMP_TAC std_ss [smallfoot_prop___PROP___REWRITE, IN_ABS,
			    smallfoot_ap_bigstar_REWRITE,
			    smallfoot_prop___COND___REWRITE,
			    BAG_EVERY_def] THEN
      METIS_TAC[SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS_def]
  ]
) THEN

`?h3 h4. ASL_IS_SUBSTATE DISJOINT_FMAP_UNION h3 (SND s) /\
         ASL_IS_SUBSTATE DISJOINT_FMAP_UNION h4 (SND s) /\
         (st,h4) IN P2 y' z' /\
         (st,h3) IN P2 y z` by ALL_TAC THEN1 ( 
   RES_TAC THEN
   FULL_SIMP_TAC std_ss [] THEN
   METIS_TAC[ASL_IS_SUBSTATE___DISJOINT_FMAP_UNION___TRANS]
) THEN
NTAC 2 (POP_ASSUM MP_TAC) THEN

`?h. h = DRESTRICT (SND s) (FDOM h3 UNION FDOM h4)` by METIS_TAC[] THEN
`ASL_IS_SUBSTATE DISJOINT_FMAP_UNION h3 h /\
 ASL_IS_SUBSTATE DISJOINT_FMAP_UNION h4 h /\
 (FDOM h = FDOM h3 UNION FDOM h4)` by ALL_TAC THEN1 (
    FULL_SIMP_TAC std_ss [ASL_IS_SUBSTATE___DISJOINT_FMAP_UNION,
			  DRESTRICT_DEF, EXTENSION, IN_INTER,
			  IN_UNION, SUBSET_DEF] THEN
    REPEAT (Q.PAT_ASSUM `!x. x IN FDOM X ==> x IN FDOM (SND s)` MP_TAC) THEN
    REPEAT (POP_ASSUM (K ALL_TAC)) THEN
    METIS_TAC[]
) THEN
NTAC 3 (POP_ASSUM MP_TAC) THEN

REPEAT (Q.PAT_ASSUM `c z'' y''` MP_TAC) THEN
Q.PAT_ASSUM `IS_SOME___SMALLFOOT_AE_USED_VARS e` MP_TAC THEN

Q.UNABBREV_TAC `P2` THEN
Q.UNABBREV_TAC `c` THEN
REPEAT (POP_ASSUM (K ALL_TAC)) THEN


SIMP_TAC std_ss [IN_ABS, smallfoot_prop___COND_INSERT,
		 SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS_def,
		 smallfoot_ap_star___PERMISSION_UNIMPORTANT,
		 asl_bool_EVAL] THEN

DISCH_TAC THEN
NTAC 2 (DISCH_TAC THEN (POP_ASSUM (K ALL_TAC))) THEN

SIMP_TAC (std_ss++boolSimps.CONJ_ss) [smallfoot_ap_points_to_def, LET_THM,
		 IN_ABS, smallfoot_ae_const_def,
		 FEVERY_FUPDATE, IS_SOME_EXISTS,
		 GSYM RIGHT_EXISTS_AND_THM,
		 GSYM LEFT_EXISTS_AND_THM] THEN

CONSEQ_REWRITE_TAC ([],[prove (``FEVERY X Y ==> T``, SIMP_TAC std_ss [])],[]) THEN

SIMP_TAC std_ss [AND_IMP_INTRO, GSYM CONJ_ASSOC,
		 GSYM RIGHT_EXISTS_AND_THM,
		 smallfoot_ap_data_list_seg_def,
		 asl_bool_EVAL,
		 GSYM LEFT_EXISTS_AND_THM,
		 GSYM LEFT_FORALL_IMP_THM] THEN


`(!e c data. IS_SOME___SMALLFOOT_AE_USED_VARS e ==> 
    SMALLFOOT_AP_PERMISSION_UNIMPORTANT (smallfoot_ap_points_to e 
      ((FMAP_MAP (\dl. smallfoot_ae_const (HD dl)) data) |+ 
      (t, smallfoot_ae_const c)))) /\
 (!c1 c2 data m. SMALLFOOT_AP_PERMISSION_UNIMPORTANT (smallfoot_ap_data_list_seg_num m t (smallfoot_ae_const c1) data (smallfoot_ae_const c2)))` by ALL_TAC THEN1 (
   CONSEQ_REWRITE_TAC ([],[SMALLFOOT_AP_PERMISSION_UNIMPORTANT___points_to,
		       SMALLFOOT_AP_PERMISSION_UNIMPORTANT___data_list_seg_num,
		       FEVERY_STRENGTHEN_THM],[]) THEN
   ASM_SIMP_TAC std_ss [IS_SOME___SMALLFOOT_AE_USED_VARS___EVAL,
		        FEVERY_FMAP_MAP] THEN
   SIMP_TAC std_ss [FEVERY_DEF]
) THEN

Q.SPEC_TAC (`h4`, `h4`) THEN
Q.SPEC_TAC (`h3`, `h3`) THEN
Q.SPEC_TAC (`y`, `y`) THEN
Q.SPEC_TAC (`y'`, `y'`) THEN
SIMP_TAC std_ss [] THEN

Q.ABBREV_TAC `e2_cond = \e z h:smallfoot_heap. ((z IN FDOM h) /\ ~(z = 0)) ==> (e st = SOME z)` THEN
Q.ABBREV_TAC `zCond = \z. (~(z = 0) /\ z IN FDOM h) ==> ~(h ' z ' t = z)` THEN

Tactical.REVERSE (
`!n n' z y' y h1 h1' e data.
      (ASL_IS_SUBSTATE DISJOINT_FMAP_UNION h1 h /\  
      ~(y IN FDOM h1) /\
      (st,h1) IN smallfoot_ap_data_list_seg_num n t e data (K (SOME y)) /\
      (h ' y ' t = z) /\ ~(y' = 0) /\ ~(y = 0) /\
      ASL_IS_SUBSTATE DISJOINT_FMAP_UNION h1' h /\
      ~(y' IN FDOM h1') /\
      IS_SOME___SMALLFOOT_AE_USED_VARS e /\
      (st,h1') IN smallfoot_ap_data_list_seg_num n' t e data (K (SOME y')) /\
      (zCond z) /\ y IN FDOM h /\ y' IN FDOM h /\
      (h ' y' ' t = z) /\ (e2_cond e z h1) /\ (e2_cond e z h1')) ==>
      (y = y')` by ALL_TAC) THEN1 (

  REPEAT STRIP_TAC THEN
  Cases_on `y = y'` THEN1 ASM_REWRITE_TAC[] THEN
  Q.PAT_ASSUM `!n n'. X n n'` MATCH_MP_TAC THEN
  Q.EXISTS_TAC `n'` THEN
  Q.EXISTS_TAC `n` THEN
  ASM_SIMP_TAC std_ss [] THEN
  Q.EXISTS_TAC `h1'` THEN
  Q.EXISTS_TAC `h1` THEN
  Q.EXISTS_TAC `e1` THEN
  Q.EXISTS_TAC `data` THEN
  ASM_SIMP_TAC std_ss [] THEN
  Q.UNABBREV_TAC `e2_cond` THEN
  Q.UNABBREV_TAC `zCond` THEN
  FULL_SIMP_TAC std_ss [ASL_IS_SUBSTATE___DISJOINT_FMAP_UNION,
			FUNION_DEF, IN_UNION, IN_SING, DISJ_IMP_THM,
                        FORALL_AND_THM, UNION_SUBSET,
			DISJOINT_DEF, EXTENSION, IN_INTER,
		        NOT_IN_EMPTY] THEN
  Q.ABBREV_TAC `z =  h ' y ' t` THEN
  Q.PAT_ASSUM `h2' ' y = X` ASSUME_TAC THEN
  Q.PAT_ASSUM `h2 ' y' = X` ASSUME_TAC THEN
  FULL_SIMP_TAC std_ss [] THEN
  Q.PAT_ASSUM `z = h ' y' ' t` (ASSUME_TAC o GSYM) THEN
  FULL_SIMP_TAC std_ss [] THEN
  Cases_on `z = 0` THEN (
     ASM_SIMP_TAC std_ss []
  ) THEN
  Cases_on `e1 = e2` THEN (
     FULL_SIMP_TAC std_ss []
  ) THEN
  DISCH_TAC THEN POP_ASSUM (K ALL_TAC) THEN
  CCONTR_TAC THEN
  FULL_SIMP_TAC std_ss [] THEN

  Tactical.REVERSE (`!m e1 h' data c. ((ASL_IS_SUBSTATE DISJOINT_FMAP_UNION h' h) /\ IS_SOME___SMALLFOOT_AE_USED_VARS e1 /\ 
                                (e1 st = SOME z) /\ (st,h') IN smallfoot_ap_data_list_seg_num m t e1 data (K (SOME c))) ==>
                     (c = z)` by ALL_TAC) THEN1 (
     METIS_TAC[ASL_IS_SUBSTATE___DISJOINT_FMAP_UNION] 
  ) THEN
  Induct_on `m` THEN1 (
     ASM_SIMP_TAC arith_ss [smallfoot_ap_equal_def, LET_THM, IN_ABS,
                            smallfoot_a_stack_proposition_def,
                            smallfoot_ap_binexpression_def,
			   smallfoot_ap_data_list_seg_num_def,
			    asl_bool_EVAL]
  ) THEN
  REPEAT STRIP_TAC THEN
  Q.PAT_ASSUM `!e'. X e'` MATCH_MP_TAC THEN
  Q.EXISTS_TAC `smallfoot_ae_const z` THEN
  SIMP_TAC std_ss [IS_SOME___SMALLFOOT_AE_USED_VARS___EVAL] THEN
  CCONTR_TAC THEN
  Q.PAT_ASSUM `(st, h') IN X` MP_TAC THEN
  REWRITE_TAC [] THEN
  ONCE_REWRITE_TAC[smallfoot_ap_data_list_seg_num_def] THEN
  ASM_SIMP_TAC (arith_ss++boolSimps.CONJ_ss) [asl_bool_EVAL,
			 smallfoot_ap_star___PERMISSION_UNIMPORTANT,
			 IS_SOME___SMALLFOOT_AE_USED_VARS___EVAL,
                         GSYM smallfoot_ae_const_def] THEN
  ASM_SIMP_TAC std_ss [IN_ABS, smallfoot_ae_const_def,
  		 smallfoot_ap_points_to_def, LET_THM,
			 FEVERY_FUPDATE, FEVERY_FEMPTY, DRESTRICT_FEMPTY] THEN
  CCONTR_TAC THEN
  Q.PAT_ASSUM `~?h'. X h'` MP_TAC THEN
  FULL_SIMP_TAC std_ss [] THEN
  Q.EXISTS_TAC `h2''` THEN
  Q.EXISTS_TAC `FMAP_MAP TL data'` THEN
  FULL_SIMP_TAC std_ss [ASL_IS_SUBSTATE___DISJOINT_FMAP_UNION___FUNION,
                        smallfoot_ae_const_def] THEN
  `h1'' ' z ' t = z` by FULL_SIMP_TAC std_ss [ASL_IS_SUBSTATE___DISJOINT_FMAP_UNION, IN_SING] THEN
  FULL_SIMP_TAC std_ss []
) THEN

HO_MATCH_MP_TAC (prove (``((!n:num n':num. (P n n' = P n' n)) /\ (!n n'. n <= n' ==> P n n')) ==>
			  (!n n'. P n n')``, 
		 METIS_TAC[LESS_EQ_CASES])) THEN
CONJ_TAC THEN1 METIS_TAC[] THEN
Induct_on `n` THENL [
   Cases_on `n'` THEN1 (
      ONCE_REWRITE_TAC [smallfoot_ap_data_list_seg_num_def] THEN
      ASM_SIMP_TAC std_ss [smallfoot_ap_equal_def, smallfoot_ap_binexpression_def,
		        smallfoot_a_stack_proposition_def, IN_ABS,
			   asl_bool_EVAL, LET_THM]
   ) THEN

   DISCH_TAC THEN REPEAT GEN_TAC THEN
   ONCE_REWRITE_TAC [smallfoot_ap_data_list_seg_num_def] THEN
   ASM_SIMP_TAC (arith_ss++boolSimps.CONJ_ss) [smallfoot_ap_equal_def, smallfoot_ap_binexpression_def,
		        smallfoot_a_stack_proposition_def, IN_ABS,
		        LET_THM, asl_bool_EVAL, FDOM_FEMPTY,
		        NOT_IN_EMPTY,
		        ASL_IS_SUBSTATE___DISJOINT_FMAP_UNION___FEMPTY] THEN
   Cases_on `IS_SOME___SMALLFOOT_AE_USED_VARS e` THEN ASM_REWRITE_TAC[] THEN
   ASM_SIMP_TAC std_ss [IS_SOME_EXISTS, GSYM RIGHT_EXISTS_AND_THM,
		    GSYM LEFT_EXISTS_AND_THM, IN_ABS,
		    GSYM LEFT_FORALL_IMP_THM, GSYM smallfoot_ae_const_def,
		    smallfoot_ap_star___PERMISSION_UNIMPORTANT] THEN
   SIMP_TAC (std_ss++boolSimps.CONJ_ss) [
      ASL_IS_SUBSTATE___DISJOINT_FMAP_UNION___FUNION,
      FDOM_FUNION, IN_UNION] THEN
   SIMP_TAC std_ss [IN_ABS, LET_THM, smallfoot_ap_points_to_def,
		    FEVERY_FUPDATE, FEVERY_FEMPTY, DRESTRICT_FEMPTY,
		    smallfoot_ae_const_def] THEN
   SIMP_TAC (std_ss++boolSimps.CONJ_ss) [
       smallfoot_ap_weak_unequal_def,
       smallfoot_a_stack_proposition_def,
       smallfoot_ap_binexpression_def, LET_THM, IN_ABS,
       DISJOINT_INSERT, DISJOINT_EMPTY, IN_SING,
       FDOM_FEMPTY, NOT_IN_EMPTY, ASL_IS_SUBSTATE___DISJOINT_FMAP_UNION___FEMPTY] THEN
   CCONTR_TAC THEN
   FULL_SIMP_TAC std_ss [IN_SING] THEN
   Q.PAT_ASSUM `(st,h2) IN X` MP_TAC THEN
   SIMP_TAC std_ss [GSYM smallfoot_ae_const_def] THEN
   ONCE_REWRITE_TAC[smallfoot_ap_data_list_seg_num_REWRITE] THEN
   SIMP_TAC std_ss [smallfoot_ap_equal_def,
		       smallfoot_a_stack_proposition_def,
		       smallfoot_ap_binexpression_def,
		       IN_ABS, LET_THM,
		       smallfoot_ae_const_def] THEN
   `h1'' ' y = h ' y` by ALL_TAC THEN1 (
      FULL_SIMP_TAC std_ss [ASL_IS_SUBSTATE___DISJOINT_FMAP_UNION,
			    IN_SING]
   ) THEN
   ASM_SIMP_TAC std_ss [COND_RAND, COND_RATOR,
			asl_bool_EVAL,
			smallfoot_ap_star___PERMISSION_UNIMPORTANT,
		       smallfoot_a_stack_proposition_def,
		       smallfoot_ap_binexpression_def,
		       IN_ABS, LET_THM,
                       smallfoot_ap_equal_def,
		       smallfoot_ap_weak_unequal_def,
		       IS_SOME___SMALLFOOT_AE_USED_VARS___EVAL,
		       GSYM smallfoot_ae_const_def] THEN
   `~(y' = z)` by ALL_TAC THEN1 (
      Q.PAT_ASSUM `zCond z` MP_TAC THEN
      Q.UNABBREV_TAC `zCond` THEN
      FULL_SIMP_TAC std_ss [FDOM_FUNION, IN_UNION, IN_SING, FDOM_FEMPTY,
			   NOT_IN_EMPTY] THEN
      METIS_TAC[]
   ) THEN

   Cases_on `n` THEN ASM_SIMP_TAC arith_ss [] THEN
   ASM_SIMP_TAC std_ss [smallfoot_ap_points_to_def,
      IN_ABS, LET_THM, smallfoot_ae_const_def,
      FEVERY_FUPDATE, FEVERY_FEMPTY, DRESTRICT_FEMPTY] THEN
   REPEAT STRIP_TAC THEN
   CCONTR_TAC THEN
   FULL_SIMP_TAC std_ss [] THEN
   Q.UNABBREV_TAC `e2_cond` THEN
   FULL_SIMP_TAC std_ss [FDOM_FUNION, IN_UNION, IN_SING],



   GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
   Cases_on `n'` THEN1 FULL_SIMP_TAC arith_ss [] THEN
   `n <= n''` by DECIDE_TAC THEN
   Q.PAT_ASSUM `!n. P n` (MP_TAC o SIMP_RULE std_ss [] o Q.SPEC `n''`) THEN
   ASM_REWRITE_TAC[] THEN
   REPEAT STRIP_TAC THEN

   Q.PAT_ASSUM `!y'. X y'` MATCH_MP_TAC THEN
   CCONTR_TAC THEN
   REPEAT (Q.PAT_ASSUM `(st, X) IN Y` MP_TAC) THEN 
   REWRITE_TAC [] THEN
   ONCE_REWRITE_TAC[smallfoot_ap_data_list_seg_num_REWRITE] THEN
   SIMP_TAC arith_ss [asl_bool_EVAL, GSYM smallfoot_ae_const_def] THEN
   ASM_SIMP_TAC std_ss [smallfoot_ap_star___PERMISSION_UNIMPORTANT] THEN
   SIMP_TAC std_ss [smallfoot_ap_weak_unequal_def,
		    smallfoot_ap_points_to_def,
		    LET_THM, IN_ABS, FEVERY_FEMPTY,
		    FEVERY_FUPDATE, DRESTRICT_FEMPTY,
                    smallfoot_ae_const_def, smallfoot_ap_binexpression_def,
                    smallfoot_a_stack_proposition_def] THEN
   Cases_on `e st` THEN ASM_SIMP_TAC std_ss [] THEN
   REPEAT STRIP_TAC THEN 
   CCONTR_TAC THEN
   Q.PAT_ASSUM `~?h1. X h1` MP_TAC THEN
   FULL_SIMP_TAC std_ss [] THEN
   Q.EXISTS_TAC `h2` THEN
   Q.EXISTS_TAC `h2'` THEN
   Q.EXISTS_TAC `K (SOME (h ' x ' t))` THEN
   
   FULL_SIMP_TAC std_ss [ASL_IS_SUBSTATE___DISJOINT_FMAP_UNION___FUNION] THEN
   `(h1''' ' x = h ' x) /\ (h1'' ' x = h ' x)` by FULL_SIMP_TAC std_ss [ASL_IS_SUBSTATE___DISJOINT_FMAP_UNION, IN_SING] THEN
   FULL_SIMP_TAC std_ss [GSYM smallfoot_ae_const_def,
			 IS_SOME___SMALLFOOT_AE_USED_VARS___EVAL,
			 FDOM_FUNION, IN_UNION] THEN
   REPEAT (Q.PAT_ASSUM `e2_cond e X Y` MP_TAC) THEN
   Q.UNABBREV_TAC `e2_cond` THEN
   FULL_SIMP_TAC std_ss [FDOM_FUNION, IN_UNION, IN_SING,
			 DISJOINT_INSERT, DISJOINT_EMPTY] THEN
   METIS_TAC[]
]);





val SMALLFOOT_COND_CHOICE_IS_INDEPENDEND_FROM_SUBSTATE___data_list_seg = 
store_thm ("SMALLFOOT_COND_CHOICE_IS_INDEPENDEND_FROM_SUBSTATE___data_list_seg",
``
!wpb rpb e1 data e2 t dt sfb.

(IS_SOME___SMALLFOOT_AE_USED_VARS e1 /\
 IS_SOME___SMALLFOOT_AE_USED_VARS e2 /\
 ~(dt = t)) ==>

SMALLFOOT_COND_CHOICE_IS_INDEPENDEND_FROM_SUBSTATE (\y z.
  smallfoot_prop (wpb,rpb) (BAG_INSERT 
                               (smallfoot_ap_data_list_seg t e1 ((data y z) |+ (dt, y)) e2)
                               (sfb y z)))``,


SIMP_TAC std_ss [SMALLFOOT_COND_CHOICE_IS_INDEPENDEND_FROM_SUBSTATE_def,
		 SMALLFOOT_CHOICE_IS_INDEPENDEND_FROM_SUBSTATE_def,
                 smallfoot_prop___REWRITE] THEN
SIMP_TAC std_ss [COND_RAND, COND_RATOR, asl_false_def, NOT_IN_EMPTY] THEN
REPEAT STRIP_TAC THEN
Tactical.REVERSE (`y' = y` by ALL_TAC) THEN1 (
   Q.EXISTS_TAC `z` THEN
   ASM_SIMP_TAC std_ss []
) THEN

Q.PAT_ASSUM `s1 IN X` MP_TAC THEN
Q.PAT_ASSUM `s2 IN X` MP_TAC THEN

ASM_SIMP_TAC std_ss [smallfoot_prop___PROP_INSERT, IN_ABS] THEN
REPEAT STRIP_TAC THEN
FULL_SIMP_TAC std_ss [SMALLFOOT_IS_SUBSTATE_REWRITE,
		      ASL_IS_SUBSTATE___DISJOINT_FMAP_UNION___FUNION] THEN

`((FST s,h1') IN (smallfoot_ap_data_list_seg t e1 ((data y z) |+ (dt,y)) e2)) /\
 ((FST s,h1)  IN (smallfoot_ap_data_list_seg t e1 ((data y' z') |+ (dt,y')) e2))` by ALL_TAC THEN1 (
   
   `(h1' = SND (FST s1, h1')) /\ (h1 = SND (FST s2, h1))` by SIMP_TAC std_ss [] THEN
   ONCE_ASM_REWRITE_TAC[] THEN
   NTAC 2 (POP_ASSUM (K ALL_TAC)) THEN
   CONSEQ_REWRITE_TAC ([],[SMALLFOOT_AP_PERMISSION_UNIMPORTANT___SUBSTATE],[]) THEN
   FULL_SIMP_TAC std_ss [SMALLFOOT_IS_SUBSTATE_REWRITE,
			 smallfoot_prop___COND_INSERT,
			 SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS_def]
) THEN

Q.PAT_ASSUM `(FST s, h1') IN X` MP_TAC THEN
Q.PAT_ASSUM `(FST s, h1) IN X` MP_TAC THEN
Q.PAT_ASSUM `ASL_IS_SUBSTATE DISJOINT_FMAP_UNION h1 (SND s)` MP_TAC THEN
Q.PAT_ASSUM `ASL_IS_SUBSTATE DISJOINT_FMAP_UNION h1' (SND s)` MP_TAC THEN
Q.PAT_ASSUM `IS_SOME___SMALLFOOT_AE_USED_VARS e1` MP_TAC THEN
Q.PAT_ASSUM `IS_SOME___SMALLFOOT_AE_USED_VARS e2` MP_TAC THEN
Q.PAT_ASSUM `~(dt = t)` MP_TAC THEN
Q.ABBREV_TAC `data1 = data y' z'` THEN
Q.ABBREV_TAC `data2 = data y z` THEN
REPEAT (POP_ASSUM (K ALL_TAC)) THEN

Cases_on `s` THEN
SIMP_TAC std_ss [] THEN

Q.SPEC_TAC (`r`, `h`) THEN
Q.SPEC_TAC (`h1`, `h1`) THEN
Q.SPEC_TAC (`h1'`, `h2`) THEN
Q.SPEC_TAC (`q`, `st`) THEN
Q.SPEC_TAC (`data2`, `data2`) THEN
Q.SPEC_TAC (`data1`, `data1`) THEN
Q.SPEC_TAC (`e1`, `e1`) THEN
Q.SPEC_TAC (`y`, `y2`) THEN
Q.SPEC_TAC (`y'`, `y1`) THEN

Induct_on `y1` THENL [
   ONCE_REWRITE_TAC [smallfoot_ap_data_list_seg_REWRITE] THEN
   SIMP_TAC std_ss [asl_bool_EVAL, FEVERY_FUPDATE,
		    IN_ABS] THEN
   REPEAT STRIP_TAC THEN ASM_SIMP_TAC std_ss [] THEN
   FULL_SIMP_TAC std_ss [smallfoot_ap_weak_unequal_def,
		    smallfoot_ap_equal_def, IN_ABS,
		    smallfoot_ap_binexpression_def,
		    smallfoot_a_stack_proposition_def,
		    LET_THM, IS_SOME_EXISTS],


   ONCE_REWRITE_TAC [smallfoot_ap_data_list_seg_REWRITE] THEN
   SIMP_TAC list_ss [asl_bool_EVAL, FEVERY_FUPDATE,
		    IN_ABS] THEN
   REPEAT STRIP_TAC THEN ASM_SIMP_TAC list_ss [] THEN1 (
      FULL_SIMP_TAC std_ss [smallfoot_ap_weak_unequal_def,
		    smallfoot_ap_equal_def, IN_ABS,
		    smallfoot_ap_binexpression_def,
		    smallfoot_a_stack_proposition_def,
		    LET_THM, IS_SOME_EXISTS]
   ) THEN
   Cases_on `y2` THEN1 FULL_SIMP_TAC std_ss [] THEN

   `(!data n' h y1. SMALLFOOT_AP_PERMISSION_UNIMPORTANT 
        (smallfoot_ap_points_to e1
               (FMAP_MAP (\dl. smallfoot_ae_const (HD dl))
                  (data |+ (dt,h::y1)) |+ (t,smallfoot_ae_const n')))) /\
    (!data n' h y1. SMALLFOOT_AP_PERMISSION_UNIMPORTANT 
       (smallfoot_ap_data_list_seg t (smallfoot_ae_const n')
                (FMAP_MAP TL (data |+ (dt,h::y1))) e2))` by ALL_TAC THEN1 (
      CONSEQ_REWRITE_TAC([],[SMALLFOOT_AP_PERMISSION_UNIMPORTANT___data_list_seg,
			 SMALLFOOT_AP_PERMISSION_UNIMPORTANT___points_to,
			 FEVERY_STRENGTHEN_THM],[]) THEN
      ASM_SIMP_TAC std_ss [IS_SOME___SMALLFOOT_AE_USED_VARS___EVAL,
		       FEVERY_DEF, FMAP_MAP_THM]
   ) THEN
   FULL_SIMP_TAC list_ss [smallfoot_ap_star___PERMISSION_UNIMPORTANT,
			 IN_ABS] THEN
   `(n'' = n') /\ (h'' = h)` by ALL_TAC THEN1 (
      Q.PAT_ASSUM `(st, h1'') IN X` MP_TAC THEN
      Q.PAT_ASSUM `(st, h1') IN X` MP_TAC THEN
      ASM_SIMP_TAC list_ss [smallfoot_ap_points_to_def,
			    IN_ABS, LET_THM,
			    FEVERY_DEF, FMAP_MAP_THM, FDOM_FUPDATE,
			    FAPPLY_FUPDATE_THM, IN_INSERT_EXPAND,
			   DISJ_IMP_THM, FORALL_AND_THM,
			   smallfoot_ae_const_def,
			   RIGHT_AND_OVER_OR, LEFT_AND_OVER_OR] THEN
      REPEAT STRIP_TAC THEN
      FULL_SIMP_TAC std_ss [ASL_IS_SUBSTATE___DISJOINT_FMAP_UNION___FUNION] THEN
      Q.PAT_ASSUM `ASL_IS_SUBSTATE___DISJOINT_FMAP_UNION h1' h'` MP_TAC THEN
      Q.PAT_ASSUM `ASL_IS_SUBSTATE___DISJOINT_FMAP_UNION h1'' h'` MP_TAC THEN
      ASM_SIMP_TAC std_ss [ASL_IS_SUBSTATE___DISJOINT_FMAP_UNION,
			   IN_SING]
   ) THEN

   FULL_SIMP_TAC list_ss [AND_IMP_INTRO, FMAP_MAP_FUPDATE] THEN
   Q.PAT_ASSUM `!y2 e1 data1 data2 st h2 h1 h. (XXX data1 data2 e1 y2 st h2 h1 h) ==> (y1 = y2)` MATCH_MP_TAC THEN
   Q.EXISTS_TAC `smallfoot_ae_const n'` THEN
   Q.EXISTS_TAC `FMAP_MAP TL data1` THEN
   Q.EXISTS_TAC `FMAP_MAP TL data2` THEN
   Q.EXISTS_TAC `st` THEN
   Q.EXISTS_TAC `h2''` THEN
   Q.EXISTS_TAC `h2'` THEN
   Q.EXISTS_TAC `h'` THEN
   FULL_SIMP_TAC std_ss [ASL_IS_SUBSTATE___DISJOINT_FMAP_UNION___FUNION,
			 IS_SOME___SMALLFOOT_AE_USED_VARS___EVAL]
]);




val SMALLFOOT_COND_CHOICE_IS_INDEPENDEND_FROM_SUBSTATE___data_list = 
store_thm ("SMALLFOOT_COND_CHOICE_IS_INDEPENDEND_FROM_SUBSTATE___data_list",
``
!wpb rpb e data t dt sfb.

(IS_SOME___SMALLFOOT_AE_USED_VARS e /\
 ~(dt = t)) ==>

SMALLFOOT_COND_CHOICE_IS_INDEPENDEND_FROM_SUBSTATE (\y z.
  smallfoot_prop (wpb,rpb) (BAG_INSERT 
                               (smallfoot_ap_data_list t e ((data y z)|+ (dt, y)))
                               (sfb y z)))``,


REPEAT STRIP_TAC THEN
REWRITE_TAC[smallfoot_ap_data_list_def] THEN
MATCH_MP_TAC SMALLFOOT_COND_CHOICE_IS_INDEPENDEND_FROM_SUBSTATE___data_list_seg THEN
ASM_SIMP_TAC std_ss [IS_SOME___SMALLFOOT_AE_USED_VARS___EVAL]);





val SMALLFOOT_CHOICE_IS_INDEPENDEND_FROM_SUBSTATE___asl_exists =
store_thm ("SMALLFOOT_CHOICE_IS_INDEPENDEND_FROM_SUBSTATE___asl_exists",
``!P.
SMALLFOOT_CHOICE_IS_INDEPENDEND_FROM_SUBSTATE (\y z. (asl_exists x. P x y z)) =
SMALLFOOT_CHOICE_IS_INDEPENDEND_FROM_SUBSTATE (\y z. P (FST z) y (SND z))
``,

SIMP_TAC std_ss [SMALLFOOT_CHOICE_IS_INDEPENDEND_FROM_SUBSTATE_def,
		 asl_bool_EVAL, PAIR_EXISTS_THM] THEN
METIS_TAC[]);




val SMALLFOOT_COND_CHOICE_IS_INDEPENDEND_FROM_SUBSTATE___asl_exists =
store_thm ("SMALLFOOT_COND_CHOICE_IS_INDEPENDEND_FROM_SUBSTATE___asl_exists",
``!P.
SMALLFOOT_COND_CHOICE_IS_INDEPENDEND_FROM_SUBSTATE (\y z. (COND_PROP___STRONG_EXISTS (\x. P x y z))) =
SMALLFOOT_COND_CHOICE_IS_INDEPENDEND_FROM_SUBSTATE (\y z. P (FST z) y (SND z))
``,

SIMP_TAC std_ss [SMALLFOOT_COND_CHOICE_IS_INDEPENDEND_FROM_SUBSTATE_def,
		 COND_PROP___STRONG_EXISTS_def,
		 SMALLFOOT_CHOICE_IS_INDEPENDEND_FROM_SUBSTATE___asl_exists]);





val SMALLFOOT_COND_INFERENCE___cond_best_local_action___FORALL_INTRO =
store_thm ("SMALLFOOT_COND_INFERENCE___cond_best_local_action___FORALL_INTRO",
``!P prog Q pre post.

 (SMALLFOOT_COND_CHOICE_IS_INDEPENDEND_FROM_SUBSTATE (\x y:unit. post x) /\
  !x. SMALLFOOT_COND_HOARE_TRIPLE P 
   (fasl_prog_seq (smallfoot_cond_best_local_action pre (post x)) prog) Q) ==>
 (SMALLFOOT_COND_HOARE_TRIPLE P 
   (fasl_prog_seq (smallfoot_cond_best_local_action
       pre (COND_PROP___STRONG_EXISTS (\x. post x))) prog) Q)
``,


REPEAT GEN_TAC THEN 
Cases_on `SMALLFOOT_COND_CHOICE_IS_INDEPENDEND_FROM_SUBSTATE (\x y:unit. post x)` THEN ASM_REWRITE_TAC[] THEN
`?Q_ap Q_cond. Q = (Q_cond, Q_ap)` by (Cases_on `Q` THEN SIMP_TAC std_ss []) THEN
`?P_ap P_cond. P = (P_cond, P_ap)` by (Cases_on `P` THEN SIMP_TAC std_ss []) THEN
ASM_SIMP_TAC std_ss [SMALLFOOT_COND_HOARE_TRIPLE_def,
		     IN_ABS,
		     smallfoot_cond_choose_const_best_local_action_def,
		     COND_PROP___STRONG_EXISTS_def] THEN
Cases_on `P_cond` THEN ASM_REWRITE_TAC[] THEN
Cases_on `Q_cond` THEN ASM_REWRITE_TAC[] THEN

SIMP_TAC std_ss [GSYM LEFT_FORALL_IMP_THM,
		 SMALLFOOT_HOARE_TRIPLE_def,
		 FASL_PROGRAM_HOARE_TRIPLE_def,
		 HOARE_TRIPLE_def, IN_ABS,
		 FASL_PROGRAM_SEM___prog_seq] THEN
HO_MATCH_MP_TAC (prove (``
   (!x'. x' IN P_ap ==> (((!x. XX x x') ==> YY x'))) ==>
   ((!x x'. x' IN P_ap ==> XX x x') ==> (!x'. x' IN P_ap ==> YY x'))``,
   METIS_TAC[])) THEN
GEN_TAC THEN STRIP_TAC THEN

Q.ABBREV_TAC `prog_sem = 
              FASL_PROGRAM_SEM (smallfoot_env,K smallfoot_ap_true) FEMPTY prog` THEN
Q.ABBREV_TAC `Q'_ap = (\s.
            s IN Q_ap /\
            VAR_RES_STACK___IS_EQUAL_UPTO_VALUES (FST x) (FST s))` THEN


SIMP_TAC std_ss [smallfoot_cond_best_local_action_def] THEN
Cases_on `~FST pre \/ ?x. ~FST (post x)` THEN1 (
   ASM_REWRITE_TAC[] THEN
   SIMP_TAC std_ss [FASL_PROGRAM_SEM___diverge,
		    SOME___fasla_seq, fasl_order_THM,
		    fasla_diverge_def, NOT_IN_EMPTY,
		    IMAGE_EMPTY, BIGUNION_EMPTY,
		    EMPTY_SUBSET]
) THEN
FULL_SIMP_TAC std_ss [] THEN

SIMP_TAC std_ss [smallfoot_prog_best_local_action_def,
		 asl_bool_EVAL, fasl_prog_quant_best_local_action_def,
		 FASL_PROGRAM_SEM___prim_command,
		 FASL_ATOMIC_ACTION_SEM_def,
		 EVAL_fasl_prim_command_THM,
		 SMALLFOOT_SEPARATION_COMBINATOR___EXTRACT,
		 IS_SEPARATION_COMBINATOR___smallfoot_separation_combinator,
		 quant_best_local_action_THM] THEN


SIMP_TAC std_ss [fasl_order_THM, SOME___fasla_seq,
		 GSYM RIGHT_EXISTS_AND_THM,
		 GSYM LEFT_EXISTS_AND_THM] THEN



Q.ABBREV_TAC `Q'' = \s1. (!e. e IN s1 ==> IS_SOME (prog_sem e)) /\
         BIGUNION (IMAGE THE (IMAGE prog_sem s1)) SUBSET Q'_ap` THEN
`!s1.  (!e. e IN s1 ==> IS_SOME (prog_sem e)) /\
        BIGUNION (IMAGE THE (IMAGE prog_sem s1)) SUBSET Q'_ap = Q'' s1` by ALL_TAC THEN1 (
   Q.UNABBREV_TAC `Q''` THEN
   SIMP_TAC std_ss []
) THEN
ASM_REWRITE_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN



Q.ABBREV_TAC `post' = \x':smallfoot_state s x. s IN SND (post x) /\
              VAR_RES_STACK___IS_EQUAL_UPTO_VALUES (FST x') (FST s)` THEN
`!x' s x.  (s IN SND (post x) /\
              VAR_RES_STACK___IS_EQUAL_UPTO_VALUES (FST x') (FST s)) = post' x' s x` by ALL_TAC THEN1 (
   Q.UNABBREV_TAC `post'` THEN
   SIMP_TAC std_ss []
) THEN
ASM_REWRITE_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN


SIMP_TAC std_ss [SOME___quant_best_local_action, IN_ABS, FORALL_AND_THM] THEN

`!s1. Q'' s1 = (!e. e IN s1 ==> ?s2. (prog_sem e = SOME s2) /\ s2 SUBSET Q'_ap)` by 
   ALL_TAC THEN1 (
   Q.UNABBREV_TAC `Q''` THEN
   SIMP_TAC std_ss [SUBSET_DEF, IN_BIGUNION, IN_IMAGE, GSYM RIGHT_EXISTS_AND_THM,
		    IS_SOME_EXISTS, GSYM LEFT_EXISTS_AND_THM,
		    GSYM LEFT_FORALL_IMP_THM] THEN
   METIS_TAC[optionTheory.option_CLAUSES]
) THEN
ASM_SIMP_TAC std_ss [IN_ABS, GSYM LEFT_FORALL_IMP_THM] THEN

SIMP_TAC std_ss [asl_star_def, IN_ABS, IN_SING] THEN
REPEAT STRIP_TAC THEN
Q.PAT_ASSUM `!x' e. X x' e ==> ?s2. Y x' e s2 /\ s2 SUBSET Q'_ap` MATCH_MP_TAC THEN

Q.UNABBREV_TAC `post'` THEN
FULL_SIMP_TAC std_ss [GSYM RIGHT_EXISTS_AND_THM] THEN

`?p x. (SOME e = smallfoot_separation_combinator (SOME p) (SOME s0)) /\
        p IN SND (post x) /\
        VAR_RES_STACK___IS_EQUAL_UPTO_VALUES (FST x') (FST p)` by METIS_TAC[] THEN

Q.EXISTS_TAC `x''` THEN
REPEAT STRIP_TAC THEN
Q.PAT_ASSUM `!x'' s0. X x'' s0` (MP_TAC o Q.SPECL [`x'''`, `s0'`]) THEN
ASM_SIMP_TAC std_ss [] THEN
STRIP_TAC THEN
Q.EXISTS_TAC `p'` THEN 
ASM_REWRITE_TAC[] THEN


Q.PAT_ASSUM `SMALLFOOT_COND_CHOICE_IS_INDEPENDEND_FROM_SUBSTATE X` (
MATCH_MP_TAC o SIMP_RULE std_ss [SMALLFOOT_CHOICE_IS_INDEPENDEND_FROM_SUBSTATE_def,
			         SMALLFOOT_COND_CHOICE_IS_INDEPENDEND_FROM_SUBSTATE_def]) THEN

Q.EXISTS_TAC `e` THEN
Q.EXISTS_TAC `p` THEN
Q.EXISTS_TAC `x''''` THEN

ASM_SIMP_TAC std_ss [SMALLFOOT_IS_SUBSTATE_def,
		     ASL_IS_SUBSTATE_def] THEN
METIS_TAC[]);



*)




val smallfoot_cond_best_local_action___STRONG_EQUIV___pre_post =
store_thm ("smallfoot_cond_best_local_action___STRONG_EQUIV___pre_post",
``!pre post pre' post'.
   (SMALLFOOT_COND_PROP___STRONG_EQUIV pre pre' /\ 
    SMALLFOOT_COND_PROP___STRONG_EQUIV post post') ==>

   (smallfoot_cond_best_local_action pre post =
    smallfoot_cond_best_local_action pre' post')``,


SIMP_TAC std_ss [smallfoot_cond_best_local_action_def,
                 SMALLFOOT_COND_PROP___STRONG_EQUIV_REWRITE]);









val SMALLFOOT_COND_INFERENCE___cond_best_local_action___EXISTS_INTRO =
store_thm ("SMALLFOOT_COND_INFERENCE___cond_best_local_action___EXISTS_INTRO",
``!P prog Q pre post.

 (?x. SMALLFOOT_COND_HOARE_TRIPLE P 
   (fasl_prog_seq (smallfoot_cond_best_local_action (pre x) post) prog) Q) ==>
 (SMALLFOOT_COND_HOARE_TRIPLE P 
   (fasl_prog_seq (smallfoot_cond_best_local_action
       (COND_PROP___STRONG_EXISTS (\x. pre x)) post) prog) Q)
``,


REPEAT GEN_TAC THEN
`?Q_ap Q_cond. Q = (Q_cond, Q_ap)` by (Cases_on `Q` THEN SIMP_TAC std_ss []) THEN
`?P_ap P_cond. P = (P_cond, P_ap)` by (Cases_on `P` THEN SIMP_TAC std_ss []) THEN
ASM_SIMP_TAC std_ss [SMALLFOOT_COND_HOARE_TRIPLE_def,
		     IN_ABS,
		     smallfoot_cond_choose_const_best_local_action_def,
		     COND_PROP___STRONG_EXISTS_def] THEN
Cases_on `P_cond` THEN ASM_REWRITE_TAC[] THEN
Cases_on `Q_cond` THEN ASM_REWRITE_TAC[] THEN

SIMP_TAC std_ss [GSYM LEFT_FORALL_IMP_THM,
		 SMALLFOOT_HOARE_TRIPLE_def,
		 FASL_PROGRAM_HOARE_TRIPLE_def,
		 HOARE_TRIPLE_def, IN_ABS,
		 FASL_PROGRAM_SEM___prog_seq] THEN
GEN_TAC THEN
HO_MATCH_MP_TAC (prove (``
   (!x. x IN P_ap ==> (XX x ==> YY x)) ==>
   ((!x'. x' IN P_ap ==> XX x') ==> (!x. x IN P_ap ==> YY x))``,
   METIS_TAC[])) THEN
GEN_TAC THEN STRIP_TAC THEN

Q.ABBREV_TAC `prog_sem = 
              FASL_PROGRAM_SEM (smallfoot_env,K smallfoot_ap_true) FEMPTY prog` THEN
Q.ABBREV_TAC `Q'_ap = (\s.
            s IN Q_ap /\
            VAR_RES_STACK___IS_EQUAL_UPTO_VALUES (FST x') (FST s))` THEN


SIMP_TAC std_ss [smallfoot_cond_best_local_action_def] THEN
Cases_on `(?x. ~FST (pre x)) \/ ~FST post` THEN1 (
   ASM_REWRITE_TAC[] THEN
   SIMP_TAC std_ss [FASL_PROGRAM_SEM___diverge,
		    SOME___fasla_seq, fasl_order_THM,
		    fasla_diverge_def, NOT_IN_EMPTY,
		    IMAGE_EMPTY, BIGUNION_EMPTY,
		    EMPTY_SUBSET]
) THEN
FULL_SIMP_TAC std_ss [] THEN

SIMP_TAC std_ss [smallfoot_prog_best_local_action_def,
		 asl_bool_EVAL, fasl_prog_quant_best_local_action_def,
		 FASL_PROGRAM_SEM___prim_command,
		 FASL_ATOMIC_ACTION_SEM_def,
		 EVAL_fasl_prim_command_THM,
		 SMALLFOOT_SEPARATION_COMBINATOR___EXTRACT,
		 IS_SEPARATION_COMBINATOR___smallfoot_separation_combinator,
		 quant_best_local_action_THM] THEN

Q.ABBREV_TAC `post' = (\x:smallfoot_state s.
               s IN SND post /\
               VAR_RES_STACK___IS_EQUAL_UPTO_VALUES (FST x) (FST s))` THEN


SIMP_TAC std_ss [fasl_order_THM, SOME___fasla_seq,
		 GSYM RIGHT_EXISTS_AND_THM,
		 GSYM LEFT_EXISTS_AND_THM] THEN
Q.ABBREV_TAC `Q'' = \s1. (!e. e IN s1 ==> IS_SOME (prog_sem e)) /\
         BIGUNION (IMAGE THE (IMAGE prog_sem s1)) SUBSET Q'_ap` THEN
`!s1.  (!e. e IN s1 ==> IS_SOME (prog_sem e)) /\
        BIGUNION (IMAGE THE (IMAGE prog_sem s1)) SUBSET Q'_ap = Q'' s1` by ALL_TAC THEN1 (
   Q.UNABBREV_TAC `Q''` THEN
   SIMP_TAC std_ss []
) THEN
ASM_REWRITE_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN


SIMP_TAC std_ss [SOME___quant_best_local_action,
		 IN_ABS, GSYM RIGHT_EXISTS_AND_THM,
		 GSYM LEFT_EXISTS_AND_THM] THEN

STRIP_TAC THEN

Q.EXISTS_TAC `x''` THEN
Q.EXISTS_TAC `s0` THEN
Q.EXISTS_TAC `x` THEN
ASM_REWRITE_TAC [] THEN
Q.PAT_ASSUM `Q'' X` MP_TAC THEN

`!s1 s2. (s1 SUBSET s2) ==> ((Q'' s2) ==> Q'' s1)` by ALL_TAC THEN1 (
   Q.UNABBREV_TAC `Q''` THEN
   SIMP_TAC std_ss [SUBSET_DEF, IN_BIGUNION,
		    IN_IMAGE, IN_ABS, GSYM RIGHT_EXISTS_AND_THM,
		    GSYM LEFT_FORALL_IMP_THM] THEN
   METIS_TAC[]
) THEN
POP_ASSUM MATCH_MP_TAC THEN

ASM_SIMP_TAC std_ss [SUBSET_DEF, IN_ABS,
		 GSYM LEFT_FORALL_IMP_THM] THEN
METIS_TAC[]);










val SMALLFOOT_COND_INFERENCE___cond_choose_const___free_param_ELIM =
store_thm ("SMALLFOOT_COND_INFERENCE___cond_choose_const___free_param_ELIM",
``
 !P prog Q c pre post fpL expL fpt fpn.

 (?fpn_data. smallfoot_data_IS_WELL_TYPED (fpt,fpn_data) /\

SMALLFOOT_COND_HOARE_TRIPLE 
   P 
   (fasl_prog_seq (smallfoot_cond_choose_const_best_local_action c 
  (\args. pre (FST args, fpn_data::(SND args))) 
  (\args. post (FST args, fpn_data::(SND args))) fpL expL) prog)

   Q) ==>


 (SMALLFOOT_COND_HOARE_TRIPLE 
   P 
   (fasl_prog_seq (smallfoot_cond_choose_const_best_local_action
c pre post ((fpt,fpn)::fpL) expL) prog)

   Q)
``,



REPEAT GEN_TAC THEN
`?P_ap P_cond. P = (P_cond, P_ap)` by (Cases_on `P` THEN SIMP_TAC std_ss []) THEN
`?Q_ap Q_cond. Q = (Q_cond, Q_ap)` by (Cases_on `Q` THEN SIMP_TAC std_ss []) THEN
FULL_SIMP_TAC std_ss [SMALLFOOT_COND_HOARE_TRIPLE_def, smallfoot_prop___REWRITE] THEN
Cases_on `P_cond` THEN ASM_REWRITE_TAC[] THEN
Cases_on `Q_cond` THEN ASM_REWRITE_TAC[] THEN

SIMP_TAC std_ss [SMALLFOOT_HOARE_TRIPLE_def,
		 FASL_PROGRAM_HOARE_TRIPLE_def,
		 FASL_PROGRAM_SEM___prog_seq,
		 HOARE_TRIPLE_def,
		 fasl_order_THM, IN_ABS] THEN
SIMP_TAC std_ss [GSYM RIGHT_FORALL_IMP_THM,
		 GSYM LEFT_FORALL_IMP_THM] THEN
REPEAT GEN_TAC THEN
Cases_on `smallfoot_data_IS_WELL_TYPED (fpt,fpn_data)` THEN ASM_REWRITE_TAC[] THEN

SIMP_TAC std_ss [GSYM LEFT_EXISTS_IMP_THM] THEN
Q.EXISTS_TAC `x` THEN
Cases_on `x IN P_ap` THEN ASM_REWRITE_TAC[] THEN


SIMP_TAC std_ss [SOME___fasla_seq, LEFT_EXISTS_IMP_THM,
		 GSYM LEFT_EXISTS_AND_THM] THEN
Q.ABBREV_TAC `prog_sem = (FASL_PROGRAM_SEM (smallfoot_env,K smallfoot_ap_true) FEMPTY prog)` THEN
Q.ABBREV_TAC `Q' = (\s. s IN Q_ap /\ VAR_RES_STACK___IS_EQUAL_UPTO_VALUES (FST x) (FST s))` THEN
Q.ABBREV_TAC `Q'' = \s1. (!e. e IN s1 ==> IS_SOME (prog_sem e)) /\
         BIGUNION (IMAGE THE (IMAGE prog_sem s1)) SUBSET Q'` THEN
`!s1.  (!e. e IN s1 ==> IS_SOME (prog_sem e)) /\
        BIGUNION (IMAGE THE (IMAGE prog_sem s1)) SUBSET Q' = Q'' s1` by ALL_TAC THEN1 (
   Q.UNABBREV_TAC `Q''` THEN
   SIMP_TAC std_ss []
) THEN
ASM_REWRITE_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN


SIMP_TAC std_ss [smallfoot_cond_choose_const_best_local_action_def] THEN
Tactical.REVERSE (Cases_on `c`) THEN1 (
   SIMP_TAC std_ss [FASL_PROGRAM_SEM___prog_shallow_fail, fasla_fail_def,
		    smallfoot_data_IS_WELL_TYPED___SATISFYABLE___THM]
) THEN
Cases_on `?arg. ~FST (pre arg) \/ ~FST (post arg)` THEN1 (
   ASM_REWRITE_TAC[] THEN
   Q.UNABBREV_TAC `Q''` THEN
   SIMP_TAC std_ss [FASL_PROGRAM_SEM___diverge, fasla_diverge_def,
		    NOT_IN_EMPTY, IMAGE_EMPTY, BIGUNION_EMPTY,
		    EMPTY_SUBSET]
) THEN
FULL_SIMP_TAC std_ss [] THEN


SIMP_TAC std_ss [smallfoot_choose_const_best_local_action_def,
		 fasl_prog_quant_best_local_action_def,
		 FASL_PROGRAM_SEM___prim_command,
		 FASL_ATOMIC_ACTION_SEM_def,
		 EVAL_fasl_prim_command_THM,
		 SMALLFOOT_SEPARATION_COMBINATOR___EXTRACT,
		 quant_best_local_action_THM,
		 IS_SEPARATION_COMBINATOR___smallfoot_separation_combinator] THEN

SIMP_TAC std_ss [SOME___quant_best_local_action, IN_ABS,
		 pairTheory.ELIM_UNCURRY, asl_bool_EVAL] THEN
SIMP_TAC std_ss [PAIR_FORALL_THM, PAIR_EXISTS_THM] THEN

Q.ABBREV_TAC `P2 = \x1 x2 x1' x2' x1'' x2'' fpL x2'''.
       ((SOME x =
        smallfoot_separation_combinator (SOME (x1'',x2''))
          (SOME (x1',x2'))) /\
       LIST_UNROLL_GIVEN_ELEMENT_NAMES___TYPES x2 fpL /\
       (x1',x2') IN smallfoot_ap_equal___P_EXPRESSION_LIST expL x1 /\
       (x1',x2') IN SND (pre (x1,x2''')))` THEN

`!x1 x2 x1' x2' x1'' x2'' fpL x2'''. (((SOME x =
        smallfoot_separation_combinator (SOME (x1'',x2''))
          (SOME (x1',x2'))) /\
       LIST_UNROLL_GIVEN_ELEMENT_NAMES___TYPES x2 fpL /\
       (x1',x2') IN smallfoot_ap_equal___P_EXPRESSION_LIST expL x1 /\
       (x1',x2') IN SND (pre (x1,x2'''))) =
       P2 x1 x2 x1' x2' x1'' x2'' fpL x2''') /\

(((smallfoot_separation_combinator (SOME (x1'',x2''))
          (SOME (x1',x2')) = SOME x) /\
       LIST_UNROLL_GIVEN_ELEMENT_NAMES___TYPES x2 fpL /\
       (x1',x2') IN smallfoot_ap_equal___P_EXPRESSION_LIST expL x1 /\
       (x1',x2') IN SND (pre (x1,x2'''))) =
       P2 x1 x2 x1' x2' x1'' x2'' fpL x2''')` by ALL_TAC THEN1 (
  Q.UNABBREV_TAC `P2` THEN
  SIMP_TAC std_ss [] THEN
  METIS_TAC[]
) THEN
ASM_REWRITE_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN


`!x1 x2 x1' x2' x1'' x2'' fpt fpn fpL x2'''.
 P2 x1 x2 x1' x2' x1'' x2'' ((fpt,fpn)::fpL) x2''' =

 ?fpn_data x2''''. (x2 = fpn_data::x2'''') /\
                   smallfoot_data_IS_WELL_TYPED (fpt,fpn_data) /\
 P2 x1 x2'''' x1' x2' x1'' x2'' fpL x2'''` by ALL_TAC THEN1 (

   Q.UNABBREV_TAC `P2` THEN
   SIMP_TAC (std_ss++bool_eq_imp_ss) [] THEN
   REPEAT STRIP_TAC THEN
   Cases_on `x2` THENL [
      SIMP_TAC list_ss [LIST_UNROLL_GIVEN_ELEMENT_NAMES___TYPES_def],

      SIMP_TAC list_ss [LIST_UNROLL_GIVEN_ELEMENT_NAMES___TYPES_REWRITE]
   ]
) THEN
ASM_SIMP_TAC std_ss [IN_ABS, IMP_CONJ_THM, FORALL_AND_THM] THEN
REPEAT STRIP_TAC THEN1 (
   METIS_TAC[smallfoot_data_IS_WELL_TYPED___SATISFYABLE___THM]
) THEN
Q.PAT_ASSUM `Q'' X` MP_TAC THEN

`!s1. Q'' s1 = (!e. e IN s1 ==> ?s2. (prog_sem e = SOME s2) /\ s2 SUBSET Q')` by 
   ALL_TAC THEN1 (
   Q.UNABBREV_TAC `Q''` THEN
   SIMP_TAC std_ss [SUBSET_DEF, IN_BIGUNION, IN_IMAGE, GSYM RIGHT_EXISTS_AND_THM,
		    IS_SOME_EXISTS, GSYM LEFT_EXISTS_AND_THM,
		    GSYM LEFT_FORALL_IMP_THM] THEN
   METIS_TAC[optionTheory.option_CLAUSES]
) THEN
ASM_SIMP_TAC std_ss [IN_ABS, GSYM LEFT_FORALL_IMP_THM] THEN
METIS_TAC[smallfoot_data_IS_WELL_TYPED___SATISFYABLE___THM]);













val SMALLFOOT_COND_INFERENCE___cond_choose_const_ELIM =
store_thm ("SMALLFOOT_COND_INFERENCE___cond_choose_const_ELIM",
``
 !wpb rpb sfb prog Q c pre post expL cL.

(
(LENGTH expL = LENGTH cL) /\
(EVERY (\e. smallfoot_ap_implies_ae_equal (smallfoot_prop (wpb,rpb) sfb) (SMALLFOOT_P_EXPRESSION_EVAL (FST e))
		(smallfoot_ae_const (SND e))) (ZIP (expL,cL))) /\     
(smallfoot_prop___WEAK_COND wpb rpb ==> c))

 ==>

((SMALLFOOT_COND_HOARE_TRIPLE  
   (smallfoot_prop (wpb,rpb) sfb) 

   (fasl_prog_seq (smallfoot_cond_best_local_action
(smallfoot_ae_is_list_cond_defined (pre (cL,[])) (MAP SMALLFOOT_P_EXPRESSION_EVAL expL))
   (post (cL, []))) prog)

   Q) ==>
 (SMALLFOOT_COND_HOARE_TRIPLE 
   (smallfoot_prop (wpb,rpb) sfb) 

   (fasl_prog_seq (smallfoot_cond_choose_const_best_local_action
c pre post [] expL) prog)

   Q))
``,

REPEAT GEN_TAC THEN STRIP_TAC THEN
`?Q_ap Q_cond. Q = (Q_cond, Q_ap)` by (Cases_on `Q` THEN SIMP_TAC std_ss []) THEN
FULL_SIMP_TAC std_ss [SMALLFOOT_COND_HOARE_TRIPLE_def, smallfoot_prop___REWRITE] THEN
Cases_on `smallfoot_prop___COND (wpb,rpb) sfb` THEN ASM_REWRITE_TAC[] THEN
Cases_on `Q_cond` THEN ASM_REWRITE_TAC[] THEN
IMP_RES_TAC smallfoot_prop___WEAK_COND_IMP THEN
FULL_SIMP_TAC std_ss [SMALLFOOT_HOARE_TRIPLE_def,
                      FASL_PROGRAM_HOARE_TRIPLE_def,
		      FASL_PROGRAM_SEM___prog_seq,
		      HOARE_TRIPLE_def, fasl_order_THM,
		      fasla_seq_def, IN_ABS] THEN

Tactical.REVERSE (
`!s s1. (s IN smallfoot_prop___PROP (wpb,rpb) sfb /\
     ((FASL_PROGRAM_SEM (smallfoot_env, K smallfoot_ap_true) FEMPTY
           (smallfoot_cond_best_local_action  (smallfoot_ae_is_list_cond_defined (pre (cL,[]))
                     (MAP SMALLFOOT_P_EXPRESSION_EVAL expL))
              (post (cL,[]))) s) = SOME s1)) ==>

     ?s2. ((FASL_PROGRAM_SEM (smallfoot_env, K smallfoot_ap_true) FEMPTY
                       (smallfoot_cond_choose_const_best_local_action T pre
                          post [] expL) s) = SOME s2) /\
          (s2 SUBSET s1)` by ALL_TAC) THEN1 (

   SIMP_TAC std_ss [COND_RAND, COND_RATOR, SUBSET_DEF, IN_ABS] THEN
   REPEAT STRIP_TAC THEN
   REPEAT (Q.PAT_ASSUM `!s. X s` (MP_TAC o Q.SPEC `x`)) THEN
   ASM_SIMP_TAC std_ss [NOT_NONE_IS_SOME, IS_SOME_EXISTS] THEN
   REPEAT STRIP_TAC THEN   
   Q.PAT_ASSUM `X = SOME s1` MP_TAC THEN
   FULL_SIMP_TAC std_ss [SUP_fasl_order_def, COND_NONE_SOME_REWRITES,
		        IN_IMAGE, SUBSET_DEF, NOT_NONE_IS_SOME] THEN
   ONCE_REWRITE_TAC [EXTENSION] THEN
   SIMP_TAC std_ss [IN_BIGUNION, GSYM RIGHT_EXISTS_AND_THM,
		    IN_IMAGE] THEN
   METIS_TAC[]
) THEN


ASM_SIMP_TAC std_ss [smallfoot_cond_best_local_action_def,
		     smallfoot_cond_choose_const_best_local_action_def,
		     smallfoot_ae_is_list_cond_defined_def] THEN
Cases_on `?arg. ~FST (pre arg) \/ ~FST (post arg)` THEN1 (
   ASM_SIMP_TAC std_ss [FASL_PROGRAM_SEM___diverge, fasla_diverge_def,
	         	EMPTY_SUBSET]
) THEN
ASM_REWRITE_TAC[] THEN
FULL_SIMP_TAC std_ss [FORALL_AND_THM] THEN


REPEAT STRIP_TAC THEN
Q.EXISTS_TAC `s1` THEN
FULL_SIMP_TAC std_ss [smallfoot_choose_const_best_local_action_def,
		      fasl_prog_quant_best_local_action_def,
		      FASL_PROGRAM_SEM___prim_command,
		      FASL_ATOMIC_ACTION_SEM_def,
		      SUBSET_REFL,
		      fasl_prog_best_local_action_def,
		      EVAL_fasl_prim_command_THM,
		      best_local_action_IS_LOCAL,
		      smallfoot_prog_best_local_action_def,
		      SMALLFOOT_SEPARATION_COMBINATOR___EXTRACT,
		      IS_SEPARATION_COMBINATOR___smallfoot_separation_combinator,
		      quant_best_local_action_THM,
		      IN_ABS] THEN

Q.PAT_ASSUM `X = SOME s1` (ASSUME_TAC o GSYM) THEN
ASM_REWRITE_TAC[] THEN POP_ASSUM (K ALL_TAC) THEN

HO_MATCH_MP_TAC quant_best_local_action___QUANT_ELIM_3 THEN

Q.EXISTS_TAC `(cL,[])` THEN
ASM_SIMP_TAC list_ss [IS_SEPARATION_COMBINATOR___smallfoot_separation_combinator,
		     asl_bool_EVAL, LIST_UNROLL_GIVEN_ELEMENT_NAMES_def,
		      LENGTH_NIL, GSYM_LENGTH_NIL, IN_ABS, asl_and_def,
		     LIST_UNROLL_GIVEN_ELEMENT_NAMES___TYPES_def] THEN

Tactical.REVERSE (`!s' x. ASL_IS_SUBSTATE smallfoot_separation_combinator s' s ==>
                          (s' IN smallfoot_ap_equal___P_EXPRESSION_LIST expL x =
                            EVERY (\e. IS_SOME (e (FST s')))
         (MAP SMALLFOOT_P_EXPRESSION_EVAL expL) /\ (x = cL))` by ALL_TAC) THEN1 (
   ASM_SIMP_TAC (std_ss++boolSimps.CONJ_ss) [PAIR_FORALL_THM] THEN
   METIS_TAC[]
) THEN

REPEAT STRIP_TAC THEN
Q.PAT_ASSUM `EVERY X1 X2` MP_TAC THEN
SIMP_TAC std_ss [smallfoot_ap_equal___P_EXPRESSION_LIST_def, IN_ABS] THEN
Tactical.REVERSE (Cases_on `LENGTH cL = LENGTH x`) THEN1 (
   ASM_SIMP_TAC std_ss [] THEN
   METIS_TAC[]
) THEN

ASM_SIMP_TAC std_ss [EVERY_MEM, MEM_ZIP, GSYM LEFT_FORALL_IMP_THM,
		     smallfoot_ap_implies_ae_equal_def,
		     smallfoot_ae_const_def, MEM_MAP,
		     MEM_EL, LIST_EQ_REWRITE, GSYM FORALL_AND_THM] THEN
HO_MATCH_MP_TAC (prove (``(!n. (X1 n) ==> ((X2 n) = (X3 n))) ==>
		          ((!n. X1 n) ==> ((!n. X2 n) = (!n. X3 n)))``,
			  METIS_TAC[])) THEN
GEN_TAC THEN
Cases_on `x' < LENGTH x` THEN ASM_REWRITE_TAC[] THEN
REPEAT STRIP_TAC THEN
RES_TAC THEN

Cases_on `SMALLFOOT_P_EXPRESSION_EVAL (EL x' expL) (FST s')` THEN ASM_SIMP_TAC std_ss [] THEN
Tactical.REVERSE (
`SMALLFOOT_P_EXPRESSION_EVAL (EL x' expL) (FST s) =
 SMALLFOOT_P_EXPRESSION_EVAL (EL x' expL) (FST s')` by ALL_TAC) THEN1 (

   FULL_SIMP_TAC std_ss [] THEN
   METIS_TAC[]
) THEN

REPEAT (Q.PAT_ASSUM `X = SOME Y` (ASSUME_TAC o GSYM)) THEN
Q.PAT_ASSUM `!s'. X s' ==> (Y s' = SOME (EL x' cL))` (K ALL_TAC) THEN
`?ps. (SMALLFOOT_PE_USED_VARS (EL x' expL)) = SOME ps` by 
      METIS_TAC[SMALLFOOT_PE_USED_VARS___IS_SOME, IS_SOME_EXISTS] THEN
FULL_SIMP_TAC std_ss [SMALLFOOT_PE_USED_VARS_def,
         	      SMALLFOOT_AE_USED_VARS_THM, SMALLFOOT_AE_USED_VARS_REL___REWRITE,
		      GSYM SMALLFOOT_IS_SUBSTATE_def, SMALLFOOT_IS_SUBSTATE_REWRITE] THEN
Q.PAT_ASSUM `!st1 st2. X st1 st2` MATCH_MP_TAC THEN
Q.PAT_ASSUM `!st. X st = ps SUBSET FDOM st` (ASSUME_TAC o GSYM) THEN
REPEAT (Q.PAT_ASSUM `SOME Y = X` (ASSUME_TAC o GSYM)) THEN
FULL_SIMP_TAC std_ss [VAR_RES_STACK_IS_SUBSTATE_REWRITE] THEN
REPEAT STRIP_TAC THEN
Tactical.REVERSE (`v IN FDOM (FST s')` by ALL_TAC) THEN1 (
   ASM_SIMP_TAC std_ss []
) THEN
Tactical.REVERSE (`ps SUBSET FDOM (FST s')` by ALL_TAC) THEN1 (
   FULL_SIMP_TAC std_ss [SUBSET_DEF]
) THEN
ASM_SIMP_TAC std_ss []);









val smallfoot_ap_fix_varset_def = Define 
`smallfoot_ap_fix_varset vs P =
 \s:smallfoot_state. (FDOM (FST s) = vs) /\ s IN P`


val smallfoot_prog_aquire_resource_internal_def =
Define `smallfoot_prog_aquire_resource_internal c wp P =
        if (~FST P) then
           fasl_prog_diverge
        else
           fasl_prog_seq (
        (fasl_prog_best_local_action
	    smallfoot_ap_emp
	    (smallfoot_ap_fix_varset wp (SND P))):smallfoot_prog)
        (fasl_prog_prim_command (fasl_pc_assume c))`;


val smallfoot_prog_aquire_resource_def =
Define `smallfoot_prog_aquire_resource c wpb sfb =
        smallfoot_prog_aquire_resource_internal c (SET_OF_BAG wpb)
           (smallfoot_prop (wpb,EMPTY_BAG) sfb)`


val smallfoot_ap_resource_invariant___ALTERNATIVE_DEF =
store_thm ("smallfoot_ap_resource_invariant___ALTERNATIVE_DEF",
``smallfoot_ap_resource_invariant wp P =
  smallfoot_ap_fix_varset wp (smallfoot_prop_input_ap (wp,{}) P)``,

ONCE_REWRITE_TAC[EXTENSION] THEN
SIMP_TAC std_ss [smallfoot_ap_resource_invariant_def, IN_ABS,
		 smallfoot_prop_input_ap___REWRITE,
		 smallfoot_ap_fix_varset_def,
		 NOT_IN_EMPTY, var_res_sl___has_write_permission_def] THEN
SIMP_TAC (std_ss++bool_eq_imp_ss) []);




val smallfoot_prog_aquire_resource_input___REWRITE =
store_thm ("smallfoot_prog_aquire_resource_input___REWRITE",
``!c wp P.
     (smallfoot_prog_aquire_resource_input c wp P) =
     (smallfoot_prog_aquire_resource_internal c wp
    (smallfoot_prop_internal (EMPTY_BAG, EMPTY_BAG) (wp, EMPTY) T [] EMPTY_BAG P))``,

REPEAT STRIP_TAC THEN
SIMP_TAC std_ss [smallfoot_prog_aquire_resource_internal_def,
		 smallfoot_prop_internal_def, smallfoot_prop_internal___COND_def,
		 bagTheory.NOT_IN_EMPTY_BAG,
		 BAG_ALL_DISTINCT_THM, bagTheory.FINITE_EMPTY_BAG,
		 smallfoot_prog_aquire_resource_input_def,
		 smallfoot_ap_resource_invariant___ALTERNATIVE_DEF,
		 GSYM smallfoot_prop_input_ap_def]);



val smallfoot_prog_aquire_resource___INTRO =
store_thm ("smallfoot_prog_aquire_resource___INTRO",
``!c wpb wp P.
     (SET_OF_BAG wpb = wp) ==>

     ((smallfoot_prog_aquire_resource_internal c wp
         (smallfoot_prop (wpb, EMPTY_BAG) sfb)) =
     (smallfoot_prog_aquire_resource c wpb sfb))``,

SIMP_TAC std_ss [smallfoot_prog_aquire_resource_def]);




val smallfoot_prog_release_resource_internal_def =
Define `smallfoot_prog_release_resource_internal wp P =
        if (~FST P) then
           fasl_prog_diverge
        else
        ((fasl_prog_best_local_action
	    (smallfoot_ap_fix_varset wp (SND P)) smallfoot_ap_emp):smallfoot_prog)`;





val smallfoot_prog_release_resource_def =
Define `smallfoot_prog_release_resource wpb sfb =
        smallfoot_prog_release_resource_internal (SET_OF_BAG wpb)
           (smallfoot_prop (wpb,EMPTY_BAG) sfb)`



val smallfoot_prog_release_resource_input___REWRITE =
store_thm ("smallfoot_prog_release_resource_input___REWRITE",
``!wp P.
     (smallfoot_prog_release_resource_input wp P) =
     (smallfoot_prog_release_resource_internal wp
    (smallfoot_prop_internal (EMPTY_BAG, EMPTY_BAG) (wp, EMPTY) T [] EMPTY_BAG P))``,

REPEAT STRIP_TAC THEN
SIMP_TAC std_ss [smallfoot_prog_release_resource_internal_def,
		 smallfoot_prop_internal_def, smallfoot_prop_internal___COND_def,
		 bagTheory.NOT_IN_EMPTY_BAG,
		 BAG_ALL_DISTINCT_THM, bagTheory.FINITE_EMPTY_BAG,
		 smallfoot_prog_release_resource_input_def,
		 smallfoot_ap_resource_invariant___ALTERNATIVE_DEF,
		 GSYM smallfoot_prop_input_ap_def]);




val smallfoot_prog_release_resource___INTRO =
store_thm ("smallfoot_prog_release_resource___INTRO",
``!wpb wp P.
     (SET_OF_BAG wpb = wp) ==>

     ((smallfoot_prog_release_resource_internal wp
         (smallfoot_prop (wpb, EMPTY_BAG) sfb)) =
     (smallfoot_prog_release_resource wpb sfb))``,

SIMP_TAC std_ss [smallfoot_prog_release_resource_def]);










val SMALLFOOT_COND_PROP___STRONG_IMP___VAR_EQ_CONST_REWRITE =
store_thm ("SMALLFOOT_COND_PROP___STRONG_IMP___VAR_EQ_CONST_REWRITE",
``!wpb rpb v c sfb.
  SMALLFOOT_COND_PROP___STRONG_IMP
  (smallfoot_prop (wpb,rpb) (BAG_INSERT
                            (smallfoot_ap_equal (smallfoot_ae_var v) (smallfoot_ae_const c))
                            sfb))
  (smallfoot_prop (wpb,rpb) (BAG_INSERT 
                            (smallfoot_ap_equal (smallfoot_ae_var v) (smallfoot_ae_const c))
                            (BAG_IMAGE (smallfoot_ap_var_update v c) sfb)))``,

REPEAT GEN_TAC THEN
SIMP_TAC std_ss [SMALLFOOT_COND_PROP___STRONG_IMP_def,
		 smallfoot_prop___REWRITE,
		 smallfoot_prop___COND_INSERT] THEN
REPEAT STRIP_TAC THEN1 (
   FULL_SIMP_TAC std_ss [smallfoot_prop___COND___REWRITE,
           		 bagTheory.BAG_IN_FINITE_BAG_IMAGE,
			 GSYM LEFT_EXISTS_AND_THM, 
			 GSYM LEFT_FORALL_IMP_THM,
			 bagTheory.BAG_IMAGE_FINITE,
			 SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___smallfoot_ap_var_update]
) THEN

ONCE_REWRITE_TAC[EXTENSION] THEN
SIMP_TAC std_ss [smallfoot_prop___PROP___REWRITE,
		 IN_ABS, smallfoot_ap_bigstar_REWRITE] THEN
ONCE_REWRITE_TAC [smallfoot_ap_star___swap] THEN
Q.ABBREV_TAC `P = smallfoot_ap_star smallfoot_ap_stack_true
                     (smallfoot_ap_bigstar sfb)` THEN
Q.ABBREV_TAC `P' = smallfoot_ap_star smallfoot_ap_stack_true
                     (smallfoot_ap_bigstar (BAG_IMAGE (smallfoot_ap_var_update v c) sfb))` THEN

SIMP_TAC (std_ss++bool_eq_imp_ss) [] THEN
REPEAT STRIP_TAC THEN

`SMALLFOOT_AP_PERMISSION_UNIMPORTANT P /\
 SMALLFOOT_AP_PERMISSION_UNIMPORTANT P'` by ALL_TAC THEN1 (
   FULL_SIMP_TAC std_ss [smallfoot_prop___COND___EXPAND,
			 SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS_def]
) THEN

`SMALLFOOT_AP_PERMISSION_UNIMPORTANT (smallfoot_ap_equal (smallfoot_ae_var v) (smallfoot_ae_const c))` by ALL_TAC THEN1 (
   REWRITE_TAC[SMALLFOOT_AP_PERMISSION_UNIMPORTANT___ALTERNATIVE_DEF] THEN
   MATCH_MP_TAC (el 1 (CONJUNCTS SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___compare)) THEN
   SIMP_TAC std_ss [SMALLFOOT_AE_USED_VARS_SUBSET___EVAL, IN_UNIV]
) THEN
ASM_SIMP_TAC std_ss [smallfoot_ap_star___PERMISSION_UNIMPORTANT,
		     IN_ABS, smallfoot_ap_equal_def,
		     smallfoot_ap_binexpression_def,
		     smallfoot_a_stack_proposition_def,
		     LET_THM, smallfoot_ae_const_def,
                     FUNION_FEMPTY_1, FDOM_FEMPTY,
		     DISJOINT_EMPTY] THEN
SIMP_TAC (std_ss++boolSimps.CONJ_ss) [IS_SOME_EXISTS, GSYM LEFT_EXISTS_AND_THM] THEN
SIMP_TAC (std_ss++bool_eq_imp_ss) [smallfoot_ae_var_def, COND_NONE_SOME_REWRITES] THEN
REPEAT STRIP_TAC THEN

`P' = smallfoot_ap_var_update v c P` by ALL_TAC THEN1 (
   UNABBREV_ALL_TAC THEN
   FULL_SIMP_TAC std_ss [smallfoot_prop___COND___REWRITE,
	             smallfoot_ap_var_update___smallfoot_ap_bigstar___ap_true,
		     SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS_def]
) THEN
`?st h. (x = (st,h))` by ALL_TAC THEN1 (
   Cases_on `x` THEN SIMP_TAC std_ss []
) THEN
ASM_SIMP_TAC std_ss [SMALLFOOT_STATE_UPDATE_VAR_def,
		     smallfoot_ap_var_update_def, IN_ABS] THEN

Q.PAT_ASSUM `SMALLFOOT_AP_PERMISSION_UNIMPORTANT P` 
   (MATCH_MP_TAC o CONJUNCT1 o REWRITE_RULE [SMALLFOOT_AP_PERMISSION_UNIMPORTANT_def]) THEN

FULL_SIMP_TAC std_ss [VAR_RES_STACK___IS_EQUAL_UPTO_PERMISSIONS_def,
		 NOT_IN_EMPTY, SMALLFOOT_STACK_UPDATE_VAR_def,
		      FDOM_FUPDATE, FAPPLY_FUPDATE_THM,
		      EXTENSION, IN_INSERT,
		      COND_RATOR, COND_RAND] THEN
ASM_SIMP_TAC (std_ss++bool_eq_imp_ss) []);











val SMALLFOOT_COND_PROP___IMP___VAR_EQ_CONST_REWRITE =
store_thm ("SMALLFOOT_COND_PROP___IMP___VAR_EQ_CONST_REWRITE",
``!wpb rpb v c sfb.
  SMALLFOOT_COND_PROP___IMP
  (smallfoot_prop (wpb,rpb) (BAG_INSERT
                            (smallfoot_ap_equal (smallfoot_ae_var v) (smallfoot_ae_const c))
                            sfb))
  (smallfoot_prop (wpb,rpb) (BAG_INSERT 
                            (smallfoot_ap_equal (smallfoot_ae_var v) (smallfoot_ae_const c))
                            (BAG_IMAGE (smallfoot_ap_var_update v c) sfb)))``,

REPEAT STRIP_TAC THEN
MATCH_MP_TAC SMALLFOOT_COND_PROP___STRONG_IMP_IMP THEN
ASM_SIMP_TAC std_ss [SMALLFOOT_COND_PROP___STRONG_IMP___VAR_EQ_CONST_REWRITE]);


   

val SMALLFOOT_COND_INFERENCE___prog_cond =
store_thm ("SMALLFOOT_COND_INFERENCE___prog_cond",
``
 !wpb rpb v c sfb prog Q.

(SMALLFOOT_PP_USED_VARS c SUBSET (SET_OF_BAG (BAG_UNION wpb rpb))) ==>


(((SMALLFOOT_COND_HOARE_TRIPLE 
   (smallfoot_prop (wpb,rpb) 
      (BAG_INSERT (SMALLFOOT_P_PROPOSITION_EVAL c) sfb))
    (fasl_prog_seq pT prog)
    Q) /\
 (SMALLFOOT_COND_HOARE_TRIPLE  
   (smallfoot_prop (wpb,rpb) 
      (BAG_INSERT (SMALLFOOT_P_PROPOSITION_EVAL (fasl_pred_neg c)) sfb))
    (fasl_prog_seq pF prog)
    Q)) ==>


(SMALLFOOT_COND_HOARE_TRIPLE  
   (smallfoot_prop (wpb,rpb) sfb))

   (fasl_prog_seq (smallfoot_prog_cond c pT pF) prog)

   Q)
``,

REPEAT GEN_TAC THEN STRIP_TAC THEN
ASM_SIMP_TAC std_ss [smallfoot_prop_def,
                     GSYM smallfoot_prop_internal___PROG_PROP_TO_BAG,
		     SMALLFOOT_PP_USED_VARS_def] THEN
REPEAT STRIP_TAC THEN
`?Q_ap Q_cond. Q = (Q_cond, Q_ap)` by (Cases_on `Q` THEN SIMP_TAC std_ss []) THEN
FULL_SIMP_TAC std_ss [SMALLFOOT_COND_HOARE_TRIPLE_def, smallfoot_prop___REWRITE,
		      SMALLFOOT_HOARE_TRIPLE_def,
		      smallfoot_prop_internal_def,
		      smallfoot_prog_cond_def] THEN
REPEAT STRIP_TAC THEN
MATCH_MP_TAC FASL_INFERENCE_prog_cond_seq THEN
FULL_SIMP_TAC std_ss [smallfoot_prop_internal___PROP___INSERT_PROP,
		     FASL_IS_LOCAL_EVAL_ENV___smallfoot_env,
		     FASL_IS_LOCAL_EVAL_XENV_def,
		     fasl_predicate_IS_DECIDED_def,
		     GSYM fasl_predicate_IS_DECIDED_IN_STATE_def,
		     IN_ABS, asl_and_def] THEN
REPEAT STRIP_TAC THENL [
   MATCH_MP_TAC smallfoot_predicate_IS_DECIDED_IN_STATE THEN
   FULL_SIMP_TAC std_ss [smallfoot_prop_internal___PROP_def,
		      IN_ABS,
		      SUBSET_DEF, NOT_IN_EMPTY,
		      var_res_sl___has_read_permission_def,
		      var_res_sl___has_write_permission_def,
		      bagTheory.BAG_IN_BAG_UNION,
		      bagTheory.IN_SET_OF_BAG] THEN
   METIS_TAC[],

   
   Q.PAT_ASSUM `!x. X s` (K ALL_TAC) THEN
   Q.PAT_ASSUM `!x. X s` (MP_TAC o Q.SPEC `x`) THEN
   HO_MATCH_MP_TAC (prove (
    ``(P = P') ==>
    (FASL_PROGRAM_HOARE_TRIPLE xenv penv P prog Q ==>
    FASL_PROGRAM_HOARE_TRIPLE xenv penv P' prog Q)``,
    SIMP_TAC std_ss [])) THEN
   ONCE_REWRITE_TAC[EXTENSION] THEN
   SIMP_TAC (std_ss++bool_eq_imp_ss) [IN_ABS],


   Q.PAT_ASSUM `!x. X s` (MP_TAC o Q.SPEC `x`) THEN
   HO_MATCH_MP_TAC (prove (
    ``(P = P') ==>
    (FASL_PROGRAM_HOARE_TRIPLE xenv penv P prog Q ==>
    FASL_PROGRAM_HOARE_TRIPLE xenv penv P' prog Q)``,
    SIMP_TAC std_ss [])) THEN
   ONCE_REWRITE_TAC[EXTENSION] THEN
   SIMP_TAC (std_ss++bool_eq_imp_ss) [IN_ABS]
]);














 






val SMALLFOOT_COND_HOARE_TRIPLE___EQUIV_PROGRAM =
store_thm ("SMALLFOOT_COND_HOARE_TRIPLE___EQUIV_PROGRAM",
``!P prog1 prog2 Q.

(SMALLFOOT_PROGRAM_SEM (K smallfoot_ap_true) FEMPTY prog1 =
 SMALLFOOT_PROGRAM_SEM (K smallfoot_ap_true) FEMPTY prog2) ==>
(SMALLFOOT_COND_HOARE_TRIPLE P prog1 Q =
 SMALLFOOT_COND_HOARE_TRIPLE P prog2 Q)``,

Cases_on `P` THEN Cases_on `Q` THEN
SIMP_TAC std_ss [SMALLFOOT_COND_HOARE_TRIPLE_def,
		 SMALLFOOT_HOARE_TRIPLE_def,
		 FASL_PROGRAM_HOARE_TRIPLE_def,
		 SMALLFOOT_PROGRAM_SEM_def]);





val SMALLFOOT_COND_HOARE_TRIPLE___BLOCK_FIRST_SPLIT =
store_thm ("SMALLFOOT_COND_HOARE_TRIPLE___BLOCK_FIRST_SPLIT",
``!P c1 cL Q.
SMALLFOOT_COND_HOARE_TRIPLE P (smallfoot_prog_block (c1::cL)) Q =
SMALLFOOT_COND_HOARE_TRIPLE P (fasl_prog_seq c1 (smallfoot_prog_block cL)) Q``,


REPEAT GEN_TAC THEN
MATCH_MP_TAC SMALLFOOT_COND_HOARE_TRIPLE___EQUIV_PROGRAM THEN
SIMP_TAC std_ss [SMALLFOOT_PROGRAM_SEM_def,
		 smallfoot_prog_block_def,
		 FASL_PROGRAM_SEM___prog_block,
		 FASL_PROGRAM_SEM___prog_seq]);





val SMALLFOOT_COND_HOARE_TRIPLE___fasl_prog_seq___block =
store_thm ("SMALLFOOT_COND_HOARE_TRIPLE___fasl_prog_seq___block",
``!P p b Q.
SMALLFOOT_COND_HOARE_TRIPLE P (fasl_prog_seq p (smallfoot_prog_block b)) Q =
SMALLFOOT_COND_HOARE_TRIPLE P (smallfoot_prog_block (p::b)) Q``,

REPEAT GEN_TAC THEN
MATCH_MP_TAC SMALLFOOT_COND_HOARE_TRIPLE___EQUIV_PROGRAM THEN
SIMP_TAC std_ss [smallfoot_prog_block_def, SMALLFOOT_PROGRAM_SEM_def,
	         FASL_PROGRAM_SEM___prog_block,
	         FASL_PROGRAM_SEM___prog_seq]);



val SMALLFOOT_COND_HOARE_TRIPLE___fasl_prog_seq___block_block =
store_thm ("SMALLFOOT_COND_HOARE_TRIPLE___fasl_prog_seq___block_block",
``!P b1 b2 Q.
SMALLFOOT_COND_HOARE_TRIPLE P (smallfoot_prog_block ((smallfoot_prog_block b1)::b2)) Q =
SMALLFOOT_COND_HOARE_TRIPLE P (smallfoot_prog_block (b1++b2)) Q``,


REPEAT GEN_TAC THEN
MATCH_MP_TAC SMALLFOOT_COND_HOARE_TRIPLE___EQUIV_PROGRAM THEN
SIMP_TAC std_ss [SMALLFOOT_PROGRAM_SEM_def,
		 FASL_PROGRAM_SEM___prog_block,
		 FASL_PROGRAM_SEM___prog_seq,
		 GSYM FASL_PROGRAM_SEM___prog_seq___blocks,
		 smallfoot_prog_block_def]);














val SMALLFOOT_COND_PROP___STRONG_EQUIV___WEAK_COND_REWRITE =
store_thm ("SMALLFOOT_COND_PROP___STRONG_EQUIV___WEAK_COND_REWRITE",
``
!wpb rpb sfb sfb'.

(smallfoot_prop___WEAK_COND wpb rpb ==> (sfb = sfb')) ==>

(SMALLFOOT_COND_PROP___STRONG_EQUIV (smallfoot_prop (wpb,rpb) sfb)
                 (smallfoot_prop (wpb,rpb) sfb'))``,

SIMP_TAC std_ss [smallfoot_prop___REWRITE,
		 smallfoot_prop___WEAK_COND_def,
		 smallfoot_prop___COND___REWRITE,
		 SMALLFOOT_COND_PROP___STRONG_EQUIV_REWRITE] THEN
METIS_TAC[]);





val SMALLFOOT_COND_PROP___EQUIV___WEAK_COND_REWRITE =
store_thm ("SMALLFOOT_COND_PROP___EQUIV___WEAK_COND_REWRITE",
``
!wpb rpb sfb sfb'.

(smallfoot_prop___WEAK_COND wpb rpb ==> (sfb = sfb')) ==>

(SMALLFOOT_COND_PROP___EQUIV (smallfoot_prop (wpb,rpb) sfb)
                 (smallfoot_prop (wpb,rpb) sfb'))``,

REPEAT STRIP_TAC THEN
MATCH_MP_TAC SMALLFOOT_COND_PROP___STRONG_EQUIV_IMP THEN
ASM_SIMP_TAC std_ss [SMALLFOOT_COND_PROP___STRONG_EQUIV___WEAK_COND_REWRITE]);









val SMALLFOOT_COND_HOARE_TRIPLE___WEAK_COND_REWRITE =
store_thm ("SMALLFOOT_COND_HOARE_TRIPLE___WEAK_COND_REWRITE",
``
!wpb rpb sfb prog Q sfb'.

(smallfoot_prop___WEAK_COND wpb rpb ==> (sfb = sfb')) ==>

(SMALLFOOT_COND_HOARE_TRIPLE (smallfoot_prop (wpb,rpb) sfb) prog Q =
 SMALLFOOT_COND_HOARE_TRIPLE (smallfoot_prop (wpb,rpb) sfb') prog Q)``,

REPEAT STRIP_TAC THEN
MATCH_MP_TAC SMALLFOOT_COND_HOARE_TRIPLE___COND_PROP_EQUIV THEN
MATCH_MP_TAC SMALLFOOT_COND_PROP___STRONG_EQUIV_IMP THEN
MATCH_MP_TAC SMALLFOOT_COND_PROP___STRONG_EQUIV___WEAK_COND_REWRITE THEN
ASM_SIMP_TAC std_ss []);











val smallfoot_ap_equal___COMM = store_thm ("smallfoot_ap_equal___COMM",
``!e1 e2. smallfoot_ap_equal e1 e2 = smallfoot_ap_equal e2 e1``,

SIMP_TAC std_ss [smallfoot_ap_equal_def,
		 smallfoot_ap_binexpression_def,
		 smallfoot_a_stack_proposition_def,
		 LET_THM, FUN_EQ_THM] THEN
SIMP_TAC (std_ss++bool_eq_imp_ss) []);



val smallfoot_ap_unequal___COMM = store_thm ("smallfoot_ap_unequal___COMM",
``!e1 e2. smallfoot_ap_unequal e1 e2 = smallfoot_ap_unequal e2 e1``,

SIMP_TAC std_ss [smallfoot_ap_unequal_def,
		 smallfoot_ap_binexpression_def,
		 smallfoot_a_stack_proposition_def,
		 LET_THM, FUN_EQ_THM] THEN
SIMP_TAC (std_ss++bool_eq_imp_ss) []);


val smallfoot_ap_weak_unequal___COMM = store_thm ("smallfoot_ap_weak_unequal___COMM",
``!e1 e2. smallfoot_ap_weak_unequal e1 e2 = smallfoot_ap_weak_unequal e2 e1``,

SIMP_TAC std_ss [smallfoot_ap_weak_unequal_def,
		 smallfoot_ap_binexpression_def,
		 smallfoot_a_stack_proposition_def,
		 LET_THM, FUN_EQ_THM] THEN
SIMP_TAC (std_ss++bool_eq_imp_ss) []);




val smallfoot_ap_stack_true_REWRITE = store_thm ("smallfoot_ap_stack_true_REWRITE",
``smallfoot_ap_stack_true = smallfoot_ap_empty_heap_cond T``,

SIMP_TAC std_ss [smallfoot_ap_stack_true_def,
		 smallfoot_ap_empty_heap_cond_def]);


val smallfoot_ap_exp_is_defined___const = store_thm (
"smallfoot_ap_exp_is_defined___const",

``(!c. smallfoot_ap_exp_is_defined (smallfoot_ae_const c) =
       smallfoot_ap_stack_true) /\
  ((smallfoot_ap_exp_is_defined smallfoot_ae_null) = 
   smallfoot_ap_stack_true)``,

SIMP_TAC std_ss [smallfoot_ap_exp_is_defined_def,
		 smallfoot_ae_const_def,
		 smallfoot_ae_null_def,
		 smallfoot_ap_stack_true_def]);



val smallfoot_ap_empty_heap_cond___false = store_thm (
"smallfoot_ap_empty_heap_cond___false",
``(smallfoot_ap_false = smallfoot_ap_empty_heap_cond F)``,

SIMP_TAC std_ss [smallfoot_ap_false_def,
		 smallfoot_ap_empty_heap_cond_def,
		 asl_false_def, EMPTY_DEF]);



val COND_PROP___ADD_COND___true = 
store_thm ("COND_PROP___ADD_COND___true",
``!p. COND_PROP___ADD_COND T p = p``,
SIMP_TAC std_ss [COND_PROP___ADD_COND_def]);



val COND_PROP___ADD_COND___false = 
store_thm ("COND_PROP___ADD_COND___false",
``!p. SMALLFOOT_COND_PROP___EQUIV (COND_PROP___ADD_COND F p) 
                                  cond_prop_false``,

SIMP_TAC std_ss [COND_PROP___ADD_COND_def,
	         cond_prop_false_def,
	         SMALLFOOT_COND_PROP___EQUIV_REWRITE]);


val COND_PROP___ADD_COND___COND_PROP_FALSE =
store_thm ("COND_PROP___ADD_COND___COND_PROP_FALSE",
``!c. SMALLFOOT_COND_PROP___EQUIV (COND_PROP___ADD_COND c cond_prop_false)
                                  cond_prop_false``,

SIMP_TAC std_ss [COND_PROP___ADD_COND_def,
	         cond_prop_false_def,
	         SMALLFOOT_COND_PROP___EQUIV_REWRITE]);


val COND_PROP___ADD_COND___ADD_COND = 
store_thm ("COND_PROP___ADD_COND___ADD_COND",
``!p c1 c2.
  ((COND_PROP___ADD_COND c1 (COND_PROP___ADD_COND c2 p)) =
    COND_PROP___ADD_COND (c1 /\ c2) p)``,

SIMP_TAC std_ss [COND_PROP___ADD_COND_def,
		 CONJ_ASSOC]);



val COND_PROP___ADD_COND___EXISTS =
store_thm ("COND_PROP___ADD_COND___EXISTS",
``!p c.

  SMALLFOOT_COND_PROP___EQUIV
  (COND_PROP___ADD_COND c (COND_PROP___EXISTS x. (p x))) 
  (COND_PROP___EXISTS x. (COND_PROP___ADD_COND c (p x)))``,

REPEAT GEN_TAC THEN
SIMP_TAC std_ss [COND_PROP___EXISTS_def,
	         COND_PROP___ADD_COND_def,
		 SMALLFOOT_COND_PROP___EQUIV_REWRITE,
		 IN_ABS, GSYM RIGHT_EXISTS_AND_THM,
		 GSYM LEFT_EXISTS_AND_THM,
		 CONJ_ASSOC]);




val COND_PROP___EXISTS___ADD_COND =
store_thm ("COND_PROP___EXISTS___ADD_COND",
``!p c x_const.

   (!x. c x ==> (x = x_const)) ==>

  (SMALLFOOT_COND_PROP___EQUIV
   (COND_PROP___EXISTS x. (COND_PROP___ADD_COND (c x) (p x))) 
   (COND_PROP___ADD_COND (c x_const) (p x_const)))``,

REPEAT GEN_TAC THEN
SIMP_TAC std_ss [COND_PROP___EXISTS_def,
	         COND_PROP___ADD_COND_def,
		 FORALL_AND_THM, IN_ABS,
		 SMALLFOOT_COND_PROP___IMP_def,
		 SMALLFOOT_COND_PROP___EQUIV_def] THEN
METIS_TAC[]);






val smallfoot_ap_equal___EQ_REWRITE =
store_thm ("smallfoot_ap_equal___EQ_REWRITE",

``(!e. smallfoot_ap_equal e e = smallfoot_ap_exp_is_defined e)``,
SIMP_TAC std_ss [smallfoot_ap_equal_def,
		 smallfoot_ap_binexpression_def,
		 smallfoot_a_stack_proposition_def,
		 LET_THM,
		 smallfoot_ap_exp_is_defined_def]);




val smallfoot_ap_equal___EQ_REWRITE___const =
store_thm ("smallfoot_ap_equal___EQ_REWRITE___const",

``!c1 c2. smallfoot_ap_equal (smallfoot_ae_const c1) (smallfoot_ae_const c2) =
           smallfoot_ap_empty_heap_cond (c1 = c2)``,

SIMP_TAC std_ss [smallfoot_ap_equal_def,
		 smallfoot_ap_binexpression_def,
		 smallfoot_a_stack_proposition_def,
		 LET_THM,
		 smallfoot_ae_const_def,
		 smallfoot_ap_empty_heap_cond_def]);



val smallfoot_ap_unequal___EQ_REWRITES =
store_thm ("smallfoot_ap_unequal___EQ_REWRITES",

``(!e. smallfoot_ap_unequal e e = smallfoot_ap_false) /\
  (!e. smallfoot_ap_weak_unequal e e = smallfoot_ap_false)``,

SIMP_TAC std_ss [smallfoot_ap_unequal_def,
                 smallfoot_ap_weak_unequal_def,
		 smallfoot_ap_binexpression_def,
		 smallfoot_a_stack_proposition_def,
		 LET_THM,
		 smallfoot_ap_exp_is_defined_def,
		 smallfoot_ae_const_def,
		 smallfoot_ap_empty_heap_cond_def,
	         smallfoot_ap_false_def,
	         asl_false_def, EMPTY_DEF]);


val smallfoot_ap_unequal___EQ_REWRITE___const =
store_thm ("smallfoot_ap_unequal___EQ_REWRITE___const",
``!c1 c2. smallfoot_ap_unequal (smallfoot_ae_const c1) (smallfoot_ae_const c2) =
           smallfoot_ap_empty_heap_cond (~(c1 = c2))``,
SIMP_TAC std_ss [smallfoot_ap_unequal_def,
                 smallfoot_ap_weak_unequal_def,
		 smallfoot_ap_binexpression_def,
		 smallfoot_a_stack_proposition_def,
		 LET_THM,
		 smallfoot_ap_exp_is_defined_def,
		 smallfoot_ae_const_def,
		 smallfoot_ap_empty_heap_cond_def,
	         smallfoot_ap_false_def,
	         asl_false_def, EMPTY_DEF]);




val smallfoot_ap_compare___EQ_REWRITE___const =
store_thm ("smallfoot_ap_compare___EQ_REWRITE___const",
``
(smallfoot_ap_less (smallfoot_ae_const c1) (smallfoot_ae_const c2) =
                    smallfoot_ap_empty_heap_cond ((c1 < c2))) /\
(smallfoot_ap_lesseq (smallfoot_ae_const c1) (smallfoot_ae_const c2) =
                    smallfoot_ap_empty_heap_cond ((c1 <= c2))) /\
(smallfoot_ap_greater (smallfoot_ae_const c1) (smallfoot_ae_const c2) =
                    smallfoot_ap_empty_heap_cond ((c1 > c2))) /\
(smallfoot_ap_greatereq (smallfoot_ae_const c1) (smallfoot_ae_const c2) =
                    smallfoot_ap_empty_heap_cond ((c1 >= c2)))``,

SIMP_TAC std_ss [smallfoot_ap_equal_def,
		 smallfoot_ap_unequal_def,
		 smallfoot_ap_less_def,
		 smallfoot_ap_lesseq_def,
		 smallfoot_ap_greater_def,
		 smallfoot_ap_greatereq_def,
		 smallfoot_ap_binexpression_def,
		 smallfoot_a_stack_proposition_def,
		 LET_THM, smallfoot_ae_const_def,
		 smallfoot_ap_empty_heap_cond_def]);





val smallfoot_ap_tree_seg_num___EQ_REWRITE =
store_thm ("smallfoot_ap_tree_seg_num___EQ_REWRITE",
``!e n bal tagL.
  ((smallfoot_ap_tree_seg_num n bal tagL e e) =
  asl_and (K ((n = 0) \/ ~bal)) (smallfoot_ap_exp_is_defined e))``,


REPEAT STRIP_TAC THEN
SIMP_TAC std_ss [smallfoot_ap_tree_seg_num_def,
		 asl_rec_pred_num_REWRITE_BOTH,
		 smallfoot_ap_equal___EQ_REWRITE,
		 smallfoot_ap_unequal___EQ_REWRITES,
		 asl_bool_REWRITES,
		 smallfoot_ap_false_def] THEN
Cases_on `n` THEN (
   SIMP_TAC list_ss [asl_bool_REWRITES]
) THEN
ONCE_REWRITE_TAC [EXTENSION] THEN
SIMP_TAC (std_ss++bool_eq_imp_ss) [asl_bool_EVAL]);



val asl_and___smallfoot_true_false =
store_thm ("asl_and___smallfoot_true_false",
``((asl_and (K c) smallfoot_ap_stack_true) =
   smallfoot_ap_empty_heap_cond c) /\
  ((asl_and smallfoot_ap_stack_true (K c)) =
   smallfoot_ap_empty_heap_cond c) /\
  ((asl_and P smallfoot_ap_false) =
   smallfoot_ap_false) /\
  ((asl_and smallfoot_ap_false P) =
   smallfoot_ap_false)``,

SIMP_TAC std_ss [EXTENSION, asl_bool_EVAL,
		 smallfoot_ap_stack_true_def,
		 smallfoot_ap_empty_heap_cond_def,
		 IN_ABS, smallfoot_ap_false___NOT_IN] THEN
PROVE_TAC[])


val asl_and___smallfoot_ap_empty_heap_cond =
store_thm ("asl_and___smallfoot_ap_empty_heap_cond",
``((asl_and (K c1) (smallfoot_ap_empty_heap_cond c2)) =
   smallfoot_ap_empty_heap_cond (c1 /\ c2)) /\
  ((asl_and (smallfoot_ap_empty_heap_cond c1) (K c2)) =
   smallfoot_ap_empty_heap_cond (c1 /\ c2)) /\
  ((asl_and (smallfoot_ap_empty_heap_cond c) smallfoot_ap_stack_true) =
   smallfoot_ap_empty_heap_cond c) /\
  ((asl_and smallfoot_ap_stack_true (smallfoot_ap_empty_heap_cond c)) =
   smallfoot_ap_empty_heap_cond c) /\
  ((asl_and (smallfoot_ap_empty_heap_cond c1) (smallfoot_ap_empty_heap_cond c2)) =
   smallfoot_ap_empty_heap_cond (c1 /\ c2))``,

SIMP_TAC std_ss [EXTENSION, asl_bool_EVAL,
		 smallfoot_ap_stack_true_def,
		 smallfoot_ap_empty_heap_cond_def,
		 IN_ABS, smallfoot_ap_false___NOT_IN] THEN
PROVE_TAC[])


val smallfoot_ap_data_list_seg_num___EQ_REWRITE =
store_thm ("smallfoot_ap_data_list_seg_num___EQ_REWRITE",
``!n e tl data.
  (smallfoot_ap_data_list_seg_num n tl e data e = 
   asl_and (K ((n = 0) /\ (FEVERY (\x. (SND x) = []) data))) 
           (smallfoot_ap_exp_is_defined e))``,

  ONCE_REWRITE_TAC[smallfoot_ap_data_list_seg_num_REWRITE] THEN
  SIMP_TAC std_ss [smallfoot_ap_unequal___EQ_REWRITES,
		   asl_bool_REWRITES, smallfoot_ap_false_def,
		   smallfoot_ap_equal___EQ_REWRITE,
		   EXTENSION] THEN
  REPEAT GEN_TAC THEN
  Cases_on `n` THEN (
     SIMP_TAC arith_ss [asl_bool_EVAL, IN_ABS] THEN
     PROVE_TAC[]
  )
);




val smallfoot_ap_data_list_seg___EQ_REWRITE =
store_thm ("smallfoot_ap_data_list_seg___EQ_REWRITE",
``!e tl data.
  (smallfoot_ap_data_list_seg tl e data e = 
   asl_and (K (FEVERY (\x. (SND x) = []) data)) 
           (smallfoot_ap_exp_is_defined e))``,

SIMP_TAC std_ss [smallfoot_ap_data_list_seg_def, EXTENSION,
		 smallfoot_ap_data_list_seg_num___EQ_REWRITE,
		 asl_bool_EVAL]);







val smallfoot_ap_points_to___smallfoot_ae_null =
store_thm ("smallfoot_ap_points_to___smallfoot_ae_null",

``!L. smallfoot_ap_points_to smallfoot_ae_null L =
  smallfoot_ap_false``,

SIMP_TAC std_ss [smallfoot_ap_points_to_def, smallfoot_ae_null_def,
		 smallfoot_ae_const_def, LET_THM,
		 smallfoot_ap_false_def, asl_false_def,
		 EMPTY_DEF] THEN
ONCE_REWRITE_TAC[EXTENSION] THEN
SIMP_TAC std_ss [PAIR_FORALL_THM, IN_ABS]);






val smallfoot_ap_tree_seg_num___smallfoot_ae_null =
store_thm ("smallfoot_ap_tree_seg_num___smallfoot_ae_null",
``!n bal tagL e.
  (smallfoot_ap_tree_seg_num n bal tagL smallfoot_ae_null e) =
  asl_and (K ((n = 0) \/ ~bal)) (smallfoot_ap_equal e smallfoot_ae_null)``,


SIMP_TAC std_ss [smallfoot_ap_tree_seg_num_def,
		 asl_rec_pred_num_REWRITE_BOTH] THEN
Cases_on `n` THEN (
   SIMP_TAC list_ss [asl_bool_REWRITES]
) THEN
ONCE_REWRITE_TAC [EXTENSION] THEN
SIMP_TAC std_ss [asl_bool_EVAL] THEN
REPEAT STRIP_TAC THEN 
Tactical.REVERSE EQ_TAC THEN1(
  REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[]
) THEN
SIMP_TAC std_ss [DISJ_IMP_THM] THEN
MATCH_MP_TAC (prove (``~A ==> (A ==> B)``, SIMP_TAC std_ss [])) THEN
SIMP_TAC list_ss [asl_choose_pred_args_def, asl_bool_EVAL,
		  IN_ABS, MAP_MAP_o, combinTheory.o_DEF,
		  smallfoot_ap_points_to___smallfoot_ae_null,
		  asl_bigstar_list_REWRITE,
		  GSYM smallfoot_ap_star_def,
		  smallfoot_ap_false___smallfoot_ap_star_THM] THEN
SIMP_TAC std_ss [smallfoot_ap_false_def, asl_bool_EVAL]);





val smallfoot_ap_data_list_seg_num___smallfoot_ae_null =
store_thm ("smallfoot_ap_data_list_seg_num___smallfoot_ae_null",
``!tl n data e.
  (smallfoot_ap_data_list_seg_num n tl smallfoot_ae_null data e) =
  (asl_and (K ((n = 0) /\ (FEVERY (\x. SND x = []) data)))
           ((smallfoot_ap_equal e smallfoot_ae_null)))``,

ONCE_REWRITE_TAC[smallfoot_ap_data_list_seg_num_REWRITE] THEN
SIMP_TAC std_ss [smallfoot_ap_points_to___smallfoot_ae_null,
		 smallfoot_ap_false___smallfoot_ap_star_THM] THEN
SIMP_TAC std_ss [asl_bool_REWRITES, smallfoot_ap_false_def,
		 asl_exists_def, asl_bool_EVAL, EXTENSION,
		 COND_RAND, COND_RATOR, IN_ABS] THEN
METIS_TAC[]);


val smallfoot_ap_data_list_seg___smallfoot_ae_null =
store_thm ("smallfoot_ap_data_list_seg___smallfoot_ae_null",
``!tl data e.
  (smallfoot_ap_data_list_seg tl smallfoot_ae_null data e) =
  (asl_and (K ((FEVERY (\x. SND x = []) data)))
           ((smallfoot_ap_equal e smallfoot_ae_null)))``,


SIMP_TAC std_ss [smallfoot_ap_data_list_seg_def,
		 smallfoot_ap_data_list_seg_num___smallfoot_ae_null,
		 asl_exists_def, asl_and_def, IN_ABS,
		 combinTheory.K_DEF, IN_ABS3]);



val smallfoot_ap_data_list___smallfoot_ae_null =
store_thm ("smallfoot_ap_data_list___smallfoot_ae_null",
``!tl data.
  (smallfoot_ap_data_list tl smallfoot_ae_null data) = 
   asl_and (K (FEVERY (\x. SND x = []) data)) smallfoot_ap_stack_true``,

SIMP_TAC std_ss [smallfoot_ap_data_list_def,
		 smallfoot_ap_data_list_seg___smallfoot_ae_null,
                 smallfoot_ap_equal___EQ_REWRITE,
		 smallfoot_ap_exp_is_defined___const]);



val smallfoot_ap_bintree___smallfoot_ae_null =
store_thm ("smallfoot_ap_bintree___smallfoot_ae_null",
``!lt rt.
  (smallfoot_ap_bintree (lt,rt) smallfoot_ae_null) = smallfoot_ap_stack_true``,


SIMP_TAC std_ss [smallfoot_ap_bintree_def,
		 smallfoot_ap_bintree_num_def,
		 smallfoot_ap_tree_seg_num___smallfoot_ae_null,
		 asl_exists_def, asl_and_def, IN_ABS,
		 combinTheory.K_DEF, IN_ABS3,
                 smallfoot_ap_equal___EQ_REWRITE,
		 smallfoot_ap_exp_is_defined___const]);



val SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___smallfoot_ap_empty_heap_cond =
store_thm ("SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___smallfoot_ap_empty_heap_cond",
``!vs c.
SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS vs (smallfoot_ap_empty_heap_cond c)``,

SIMP_TAC std_ss [SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___ALTERNATIVE_DEF_2,
		 smallfoot_ap_empty_heap_cond_def, IN_ABS,
		 PAIR_FORALL_THM]);


val SMALLFOOT_AP_PERMISSION_UNIMPORTANT___smallfoot_ap_empty_heap_cond =
store_thm ("SMALLFOOT_AP_PERMISSION_UNIMPORTANT___smallfoot_ap_empty_heap_cond",
``!c. SMALLFOOT_AP_PERMISSION_UNIMPORTANT (smallfoot_ap_empty_heap_cond c)``,

SIMP_TAC std_ss [SMALLFOOT_AP_PERMISSION_UNIMPORTANT___ALTERNATIVE_DEF,
                 SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___smallfoot_ap_empty_heap_cond]);




val SMALLFOOT_COND_PROP___EQUIV___empty_heap_cond =
store_thm ("SMALLFOOT_COND_PROP___EQUIV___empty_heap_cond",
``!wpb rpb c sfb.
  SMALLFOOT_COND_PROP___EQUIV
  (smallfoot_prop (wpb,rpb) (BAG_INSERT
                            (smallfoot_ap_empty_heap_cond c)
                            sfb)) 
  (COND_PROP___ADD_COND c (smallfoot_prop (wpb,rpb) sfb))``,



SIMP_TAC std_ss [smallfoot_prop___REWRITE,
		 smallfoot_prop___COND_INSERT,
		 SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___smallfoot_ap_empty_heap_cond,
		 SMALLFOOT_COND_PROP___EQUIV_REWRITE,
		 COND_PROP___ADD_COND_def] THEN
SIMP_TAC (std_ss++bool_eq_imp_ss) [] THEN
REPEAT STRIP_TAC THEN

FULL_SIMP_TAC std_ss [smallfoot_prop___PROP___REWRITE,
           	      IN_ABS, smallfoot_ap_bigstar_REWRITE] THEN
SIMP_TAC (std_ss++bool_eq_imp_ss) [] THEN
REPEAT STRIP_TAC THEN

ONCE_REWRITE_TAC [smallfoot_ap_star___swap] THEN
Q.ABBREV_TAC `P = smallfoot_ap_star smallfoot_ap_stack_true
                     (smallfoot_ap_bigstar sfb)` THEN

`SMALLFOOT_AP_PERMISSION_UNIMPORTANT P` by ALL_TAC THEN1 (
   FULL_SIMP_TAC std_ss [smallfoot_prop___COND___EXPAND,
			 SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS_def]
) THEN

`SMALLFOOT_AP_PERMISSION_UNIMPORTANT (smallfoot_ap_empty_heap_cond c)` by ALL_TAC THEN1 (
   REWRITE_TAC[SMALLFOOT_AP_PERMISSION_UNIMPORTANT___ALTERNATIVE_DEF,
	       SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___smallfoot_ap_empty_heap_cond]
) THEN
ASM_SIMP_TAC std_ss [smallfoot_ap_star___PERMISSION_UNIMPORTANT,
		     IN_ABS, smallfoot_ap_empty_heap_cond_def,
                     FUNION_FEMPTY_1, FDOM_FEMPTY,
		     DISJOINT_EMPTY]);



val SMALLFOOT_COND_PROP___EQUIV___empty_heap_cond___REWRITE =
store_thm ("SMALLFOOT_COND_PROP___EQUIV___empty_heap_cond___REWRITE",
``!wpb rpb a b sfb.
  SMALLFOOT_COND_PROP___EQUIV
  (smallfoot_prop (wpb,rpb) (BAG_INSERT
                            (smallfoot_ap_empty_heap_cond (a = b))
                            (sfb a))) 
  (COND_PROP___ADD_COND (a = b) (smallfoot_prop (wpb,rpb) (sfb b)))``,



REPEAT GEN_TAC THEN
MATCH_MP_TAC (REWRITE_RULE [AND_IMP_INTRO] SMALLFOOT_COND_PROP___EQUIV___TRANS) THEN
Q.EXISTS_TAC `COND_PROP___ADD_COND (a = b) (smallfoot_prop (wpb,rpb) (sfb a))` THEN
ASM_REWRITE_TAC[SMALLFOOT_COND_PROP___EQUIV___empty_heap_cond] THEN

SIMP_TAC std_ss [SMALLFOOT_COND_PROP___EQUIV_REWRITE,
		 COND_PROP___ADD_COND_def] THEN
SIMP_TAC (std_ss++bool_eq_imp_ss) []);




val smallfoot_prop___smallfoot_ap_stack_true =
store_thm ("smallfoot_prop___smallfoot_ap_stack_true",
``!wpb rpb sfb.
  (smallfoot_prop (wpb,rpb) (BAG_INSERT
                            (smallfoot_ap_stack_true)
                            sfb)) = 
  (smallfoot_prop (wpb,rpb) sfb)``,


SIMP_TAC (std_ss++bool_eq_imp_ss) [smallfoot_prop___REWRITE, smallfoot_ap_stack_true_REWRITE,
				   smallfoot_prop___COND_INSERT,
				   SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___smallfoot_ap_empty_heap_cond,
				   smallfoot_prop___PROP_INSERT] THEN
SIMP_TAC std_ss [smallfoot_ap_empty_heap_cond_def,
		 IN_ABS, FUNION_FEMPTY_1, FDOM_FEMPTY,
		 DISJOINT_EMPTY, IN_ABS3]);



val SMALLFOOT_COND_PROP___STRONG_EQUIV___smallfoot_ap_stack_true =
store_thm ("SMALLFOOT_COND_PROP___STRONG_EQUIV___smallfoot_ap_stack_true",
``!wpb rpb sfb.
  SMALLFOOT_COND_PROP___STRONG_EQUIV
  (smallfoot_prop (wpb,rpb) (BAG_INSERT
                            (smallfoot_ap_stack_true)
                            sfb)) 
  (smallfoot_prop (wpb,rpb) sfb)``,

SIMP_TAC std_ss [smallfoot_prop___smallfoot_ap_stack_true,
		 SMALLFOOT_COND_PROP___STRONG_EQUIV___REFL]);



val SMALLFOOT_COND_PROP___EQUIV___smallfoot_ap_stack_true =
store_thm ("SMALLFOOT_COND_PROP___EQUIV___smallfoot_ap_stack_true",
``!wpb rpb sfb.
  SMALLFOOT_COND_PROP___EQUIV
  (smallfoot_prop (wpb,rpb) (BAG_INSERT
                            (smallfoot_ap_stack_true)
                            sfb)) 
  (smallfoot_prop (wpb,rpb) sfb)``,

SIMP_TAC std_ss [smallfoot_prop___smallfoot_ap_stack_true,
		 SMALLFOOT_COND_PROP___EQUIV___REFL]);




    

val smallfoot_prop___PROP___smallfoot_ap_false =
store_thm ("smallfoot_prop___PROP___smallfoot_ap_false",
``!wpb rpb sfb.
  (smallfoot_prop___PROP (wpb,rpb) (BAG_INSERT
                            (smallfoot_ap_false)
                            sfb)) = smallfoot_ap_false``,
  
SIMP_TAC std_ss [smallfoot_prop___REWRITE,
		 smallfoot_prop___PROP___REWRITE,
		 smallfoot_ap_bigstar_REWRITE,
		 smallfoot_ap_false___smallfoot_ap_star_THM,
		 smallfoot_ap_false___NOT_IN, EXTENSION,
		 IN_ABS]);



val SMALLFOOT_COND_PROP___EQUIV___smallfoot_ap_false =
store_thm ("SMALLFOOT_COND_PROP___EQUIV___smallfoot_ap_false",
``!wpb rpb sfb.
  SMALLFOOT_COND_PROP___EQUIV
  (smallfoot_prop (wpb,rpb) (BAG_INSERT
                            (smallfoot_ap_false)
                            sfb)) 
  cond_prop_false``,

SIMP_TAC std_ss [SMALLFOOT_COND_PROP___EQUIV_REWRITE,
		 smallfoot_prop___REWRITE,
		 smallfoot_prop___PROP___smallfoot_ap_false,
		 GSYM smallfoot_ap_false_def,
		 smallfoot_ap_false___NOT_IN,
		 cond_prop_false_def]);







val SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___smallfoot_ap_exp_is_defined =
store_thm ("SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___smallfoot_ap_exp_is_defined",
``
(SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS vs 
   (smallfoot_ap_exp_is_defined (smallfoot_ae_var v))) =
 v IN vs``,

SIMP_TAC std_ss [SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___ALTERNATIVE_DEF_2,
		 smallfoot_ap_exp_is_defined_def, IN_ABS,
		 PAIR_FORALL_THM, smallfoot_ae_var_def,
		 COND_NONE_SOME_REWRITES, SUBSET_DEF, IN_INTER] THEN
EQ_TAC THEN SIMP_TAC std_ss [] THEN
REPEAT STRIP_TAC THEN
POP_ASSUM (MP_TAC o Q.SPECL [ `FEMPTY`, `FEMPTY |+ (v,ARB)`]) THEN
SIMP_TAC std_ss [FDOM_FEMPTY, FDOM_FUPDATE, IN_SING,
		 NOT_IN_EMPTY, DISJ_IMP_THM]);





val smallfoot_prop___smallfoot_ap_exp_is_defined =
store_thm ("smallfoot_prop___smallfoot_ap_exp_is_defined",
``!wpb v rpb sfb.
  (v IN SET_OF_BAG (BAG_UNION wpb rpb)) ==>
  ((smallfoot_prop (wpb,rpb) (BAG_INSERT
                            (smallfoot_ap_exp_is_defined (smallfoot_ae_var v))
                            sfb)) = 
  (smallfoot_prop (wpb,rpb) sfb))``,

REPEAT STRIP_TAC THEN
ASM_SIMP_TAC std_ss [
		 smallfoot_prop___REWRITE,
		 smallfoot_prop___COND_INSERT,
                 smallfoot_prop___PROP_INSERT,
		 SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___smallfoot_ap_exp_is_defined] THEN
Cases_on `smallfoot_prop___COND (wpb,rpb) sfb` THEN ASM_REWRITE_TAC[] THEN

SIMP_TAC std_ss [smallfoot_ap_exp_is_defined_def,
		 IN_ABS, FUNION_FEMPTY_1,
		 FDOM_FEMPTY, DISJOINT_EMPTY,
		 smallfoot_ae_var_def] THEN
ONCE_REWRITE_TAC[EXTENSION] THEN
SIMP_TAC std_ss [COND_RATOR, COND_RAND, IN_ABS] THEN

SIMP_TAC (std_ss++bool_eq_imp_ss) [] THEN
FULL_SIMP_TAC std_ss [var_res_sl___has_write_permission_def,
		      var_res_sl___has_read_permission_def,
		      bagTheory.IN_SET_OF_BAG, IN_ABS,
		      smallfoot_prop___PROP___REWRITE,
		      bagTheory.BAG_IN_BAG_UNION]);





val SMALLFOOT_COND_PROP___EQUIV___smallfoot_ap_exp_is_defined =
store_thm ("SMALLFOOT_COND_PROP___EQUIV___smallfoot_ap_exp_is_defined",
``!wpb v rpb sfb.
  (v IN SET_OF_BAG (BAG_UNION wpb rpb)) ==>
  SMALLFOOT_COND_PROP___EQUIV
  (smallfoot_prop (wpb,rpb) (BAG_INSERT
                            (smallfoot_ap_exp_is_defined (smallfoot_ae_var v))
                            sfb)) 
  (smallfoot_prop (wpb,rpb) sfb)``,

SIMP_TAC std_ss [smallfoot_prop___smallfoot_ap_exp_is_defined,
		 SMALLFOOT_COND_PROP___EQUIV___REFL]);





val SMALLFOOT_COND_PROP___IMP___smallfoot_ap_exp_is_defined =
store_thm ("SMALLFOOT_COND_PROP___IMP___smallfoot_ap_exp_is_defined",
``!wpb v rpb sfb.
  SMALLFOOT_COND_PROP___IMP
  (smallfoot_prop (wpb,rpb) (BAG_INSERT
                            (smallfoot_ap_exp_is_defined (smallfoot_ae_var v))
                            sfb)) 
  (smallfoot_prop (wpb,rpb) sfb)``,

REPEAT STRIP_TAC THEN
ASM_SIMP_TAC std_ss [SMALLFOOT_COND_PROP___IMP_def,
		 smallfoot_prop___REWRITE,
		 smallfoot_prop___COND_INSERT,
		 SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___smallfoot_ap_exp_is_defined] THEN
SIMP_TAC (std_ss++boolSimps.CONJ_ss) [] THEN


FULL_SIMP_TAC std_ss [smallfoot_prop___PROP___REWRITE,
           	      IN_ABS, smallfoot_ap_bigstar_REWRITE] THEN
ONCE_REWRITE_TAC [smallfoot_ap_star___swap] THEN
Q.ABBREV_TAC `P = smallfoot_ap_star smallfoot_ap_stack_true
                     (smallfoot_ap_bigstar sfb)` THEN

REPEAT STRIP_TAC THEN
`SMALLFOOT_AP_PERMISSION_UNIMPORTANT P` by ALL_TAC THEN1 (
   FULL_SIMP_TAC std_ss [smallfoot_prop___COND___EXPAND,
			 SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS_def] THEN
   METIS_TAC[]
) THEN

`SMALLFOOT_AP_PERMISSION_UNIMPORTANT (smallfoot_ap_exp_is_defined (smallfoot_ae_var v))` by ALL_TAC THEN1 (
   REWRITE_TAC[SMALLFOOT_AP_PERMISSION_UNIMPORTANT___ALTERNATIVE_DEF,
	       SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___smallfoot_ap_exp_is_defined,
	       IN_UNIV]
) THEN
FULL_SIMP_TAC std_ss [smallfoot_ap_star___PERMISSION_UNIMPORTANT,
		     IN_ABS, smallfoot_ap_exp_is_defined_def,
                     FUNION_FEMPTY_1, FDOM_FEMPTY,
		     smallfoot_ae_var_def,
		     COND_NONE_SOME_REWRITES,
		     DISJOINT_EMPTY]);






val smallfoot_ap_star___points_to_points_to =
store_thm ("smallfoot_ap_star___points_to_points_to",
``
!e1 e2 L1 L2.
(SMALLFOOT_AP_PERMISSION_UNIMPORTANT (smallfoot_ap_points_to e1 L1) /\
 SMALLFOOT_AP_PERMISSION_UNIMPORTANT (smallfoot_ap_points_to e2 L2) /\
 ((IS_SOME___SMALLFOOT_AE_USED_VARS e1 /\ 
   IS_SOME___SMALLFOOT_AE_USED_VARS e2) \/ (e1 = e2))) ==>

(smallfoot_ap_star (smallfoot_ap_points_to e1 L1) (smallfoot_ap_points_to e2 L2) =
 smallfoot_ap_star (smallfoot_ap_points_to e1 L1) 
 (smallfoot_ap_star (smallfoot_ap_points_to e2 L2) 
                   (smallfoot_ap_unequal e1 e2)))``,


REPEAT GEN_TAC THEN
Q.ABBREV_TAC `P = (IS_SOME___SMALLFOOT_AE_USED_VARS e1 /\ 
                   IS_SOME___SMALLFOOT_AE_USED_VARS e2) \/
                  (e1 = e2)` THEN
STRIP_TAC THEN
`SMALLFOOT_AP_PERMISSION_UNIMPORTANT (smallfoot_ap_unequal e1 e2)` by ALL_TAC THEN1 (
   Q.UNABBREV_TAC `P` THEN
   FULL_SIMP_TAC std_ss [SMALLFOOT_AP_PERMISSION_UNIMPORTANT___compare,
			 smallfoot_ap_unequal___EQ_REWRITES,
			 SMALLFOOT_AP_PERMISSION_UNIMPORTANT___asl_false]
) THEN
ASM_SIMP_TAC std_ss [smallfoot_ap_star___PERMISSION_UNIMPORTANT,
		     SMALLFOOT_AP_PERMISSION_UNIMPORTANT___compare,
		     SMALLFOOT_AP_PERMISSION_UNIMPORTANT___star] THEN
ONCE_REWRITE_TAC [EXTENSION] THEN
REPEAT STRIP_TAC THEN
SIMP_TAC std_ss [IN_ABS, asl_bool_EVAL,
		 smallfoot_ap_points_to_def, LET_THM,
		 smallfoot_ap_unequal_def,
		 smallfoot_ap_binexpression_def,
		 smallfoot_a_stack_proposition_def,
		 FUNION_FEMPTY_2, FDOM_FEMPTY,
		 DISJOINT_EMPTY] THEN
HO_MATCH_MP_TAC (prove (``(!h1 h2. (X h1 h2 = Y h1 h2)) ==>
                          ((?h1 h2. X h1 h2) = (?h1 h2. Y h1 h2))``, METIS_TAC[])) THEN
SIMP_TAC (std_ss++bool_eq_imp_ss) [] THEN
REPEAT STRIP_TAC THEN
Q.PAT_ASSUM `DISJOINT X Y` MP_TAC THEN
ASM_SIMP_TAC std_ss [DISJOINT_DEF, EXTENSION,
		     IN_INTER, IN_SING, NOT_IN_EMPTY]);



val smallfoot_ap_cond_equal___HEAP_EMPTY_REWRITE =
store_thm ("smallfoot_ap_cond_equal___HEAP_EMPTY_REWRITE",
``!e1 e2 e3 st h. ((st,h) IN smallfoot_ap_cond_equal e1 e2 e3) =
                  ((st,FEMPTY) IN smallfoot_ap_cond_equal e1 e2 e3 /\
                   (h = FEMPTY))``,

SIMP_TAC std_ss [smallfoot_ap_cond_equal_def, asl_bool_EVAL,
		 smallfoot_ap_unequal_def,
		 smallfoot_ap_equal_def,
		 smallfoot_ap_binexpression_def,
		 smallfoot_a_stack_proposition_def, 
		 IN_ABS, LET_THM] THEN
SIMP_TAC (std_ss++bool_eq_imp_ss) []);



val smallfoot_ap_equal___HEAP_EMPTY_REWRITE =
store_thm ("smallfoot_ap_equal___HEAP_EMPTY_REWRITE",
``!e1 e2 st h. ((st,h) IN smallfoot_ap_equal e1 e2) =
                 ((st,FEMPTY) IN smallfoot_ap_equal e1 e2 /\
                  (h = FEMPTY))``,

SIMP_TAC std_ss [asl_bool_EVAL,
		 smallfoot_ap_unequal_def,
		 smallfoot_ap_equal_def,
		 smallfoot_ap_binexpression_def,
		 smallfoot_a_stack_proposition_def, 
		 IN_ABS, LET_THM] THEN
SIMP_TAC (std_ss++bool_eq_imp_ss) []);



val smallfoot_ap_unequal___HEAP_EMPTY_REWRITE =
store_thm ("smallfoot_ap_unequal___HEAP_EMPTY_REWRITE",
``!e1 e2 st h. ((st,h) IN smallfoot_ap_unequal e1 e2) =
                 ((st,FEMPTY) IN smallfoot_ap_unequal e1 e2 /\
                  (h = FEMPTY))``,

SIMP_TAC std_ss [asl_bool_EVAL,
		 smallfoot_ap_unequal_def,
		 smallfoot_ap_equal_def,
		 smallfoot_ap_binexpression_def,
		 smallfoot_a_stack_proposition_def, 
		 IN_ABS, LET_THM] THEN
SIMP_TAC (std_ss++bool_eq_imp_ss) [])



val smallfoot_ap_cond_equal___EQ_REWRITES =
store_thm ("smallfoot_ap_cond_equal___EQ_REWRITES",
``!e1 e2. (smallfoot_ap_cond_equal e1 e1 e2 =
          (smallfoot_ap_equal e1 e2)) /\

	  (smallfoot_ap_cond_equal e1 e2 e2 = smallfoot_ap_exp_is_defined e2)``,


SIMP_TAC std_ss [smallfoot_ap_cond_equal_def,
		 smallfoot_ap_unequal___EQ_REWRITES,
		 smallfoot_ap_false_def,
		 asl_bool_REWRITES,
		 smallfoot_ap_equal___EQ_REWRITE] THEN
ONCE_REWRITE_TAC[EXTENSION] THEN
SIMP_TAC (std_ss++bool_eq_imp_ss) [asl_bool_EVAL] THEN
SIMP_TAC std_ss [smallfoot_ap_exp_is_defined_def, IN_ABS,
		 smallfoot_ap_unequal_def,
		 smallfoot_ap_binexpression_def,
		 smallfoot_a_stack_proposition_def,
		 LET_THM, DISJ_IMP_THM]
);















val smallfoot_ap_star___data_list_seg_unroll =
store_thm ("smallfoot_ap_star___data_list_seg_unroll",
``
!e1 data e2 tl.
(IS_SOME___SMALLFOOT_AE_USED_VARS e1 /\
 IS_SOME___SMALLFOOT_AE_USED_VARS e2) ==>

(smallfoot_ap_star (smallfoot_ap_unequal e1 e2) (smallfoot_ap_data_list_seg tl e1 data e2) =
 asl_and (K (FEVERY (\x. ~(SND x = [])) data))
 (asl_exists n. smallfoot_ap_star (smallfoot_ap_unequal e1 e2) 
               (smallfoot_ap_star (smallfoot_ap_points_to e1 ((FMAP_MAP (\dl. smallfoot_ae_const (HD dl)) data) |+ (tl, smallfoot_ae_const n)))
                                  (smallfoot_ap_data_list_seg tl (smallfoot_ae_const n) (FMAP_MAP TL data) e2))))``,

ONCE_REWRITE_TAC [EXTENSION] THEN
REPEAT STRIP_TAC THEN

`!n data. SMALLFOOT_AP_PERMISSION_UNIMPORTANT 
       (smallfoot_ap_points_to e1 ((FMAP_MAP (\dl. smallfoot_ae_const (HD dl)) data) |+ (tl,smallfoot_ae_const n)))` by ALL_TAC THEN1 (
   CONSEQ_REWRITE_TAC ([],[SMALLFOOT_AP_PERMISSION_UNIMPORTANT___points_to,
	   	       FEVERY_STRENGTHEN_THM],[]) THEN
   ASM_SIMP_TAC std_ss [FEVERY_FMAP_MAP, IS_SOME___SMALLFOOT_AE_USED_VARS___EVAL] THEN
   SIMP_TAC std_ss [FEVERY_DEF]
) THEN

ASM_SIMP_TAC std_ss [smallfoot_ap_star___PERMISSION_UNIMPORTANT,
		     SMALLFOOT_AP_PERMISSION_UNIMPORTANT___data_list_seg,
     		     SMALLFOOT_AP_PERMISSION_UNIMPORTANT___star,
    		     SMALLFOOT_AP_PERMISSION_UNIMPORTANT___compare,
		     IS_SOME___SMALLFOOT_AE_USED_VARS___EVAL] THEN

CONV_TAC (LHS_CONV (ONCE_REWRITE_CONV [smallfoot_ap_data_list_seg_REWRITE])) THEN
ASM_SIMP_TAC std_ss [smallfoot_ap_star___PERMISSION_UNIMPORTANT,
		     SMALLFOOT_AP_PERMISSION_UNIMPORTANT___data_list_seg,
		     IS_SOME___SMALLFOOT_AE_USED_VARS___EVAL] THEN
SIMP_TAC std_ss [asl_bool_EVAL, IN_ABS, GSYM RIGHT_EXISTS_AND_THM,
		 LEFT_AND_OVER_OR, RIGHT_AND_OVER_OR,
		 EXISTS_OR_THM] THEN
HO_MATCH_MP_TAC (prove (``(~A /\ ((!n h1' h1 h2. (B h1 n h1' h2 = C h1 n h1' h2))) ==>
                       ((A \/ (?h1 n h1' h2. B h1 n h1' h2)) = 
                             (?n h1 h1' h2. C h1 n h1' h2)))``, 
                     METIS_TAC[])) THEN
SIMP_TAC std_ss [smallfoot_ap_unequal_def,
		    smallfoot_ap_equal_def,
		    smallfoot_ap_weak_unequal_def,
		    smallfoot_ap_binexpression_def,
		    smallfoot_a_stack_proposition_def,
		    LET_THM, IN_ABS] THEN
CONJ_TAC THENL [
   METIS_TAC[],
   SIMP_TAC (std_ss++bool_eq_imp_ss) []
]);



val smallfoot_ap_star___data_list_seg_data_unroll_empty =
store_thm ("smallfoot_ap_star___data_list_seg_data_unroll_empty",
``
!e1 data e2 tl.
((smallfoot_ap_data_list_seg tl e1 (data |+ (t, [])) e2) =
  asl_and  (smallfoot_ap_equal e2 e1) (K (FEVERY (\x. (SND x = [])) (data |+ (t, [])))))``,

SIMP_TAC list_ss [smallfoot_ap_data_list_seg___NOT_EMPTY_DATA_DEF,
            smallfoot_ap_data_list_seg_num_def,
            combinTheory.K_DEF]);




val smallfoot_ap_star___data_list_seg_data_unroll_non_empty =
store_thm ("smallfoot_ap_star___data_list_seg_data_unroll_non_empty",
``
!t h L e1 data e2 tl.
((smallfoot_ap_data_list_seg tl e1 (data |+ (t, h::L)) e2) =

 asl_and (smallfoot_ap_weak_unequal e2 e1)
        (asl_and (K (FEVERY (\x. ~(SND x = [])) (data |+ (t,h::L))))
           asl_exists n'.
             smallfoot_ap_star
               (smallfoot_ap_points_to e1
                  ((FMAP_MAP (\dl. smallfoot_ae_const (HD dl))
                     data) |+ (t,smallfoot_ae_const h) |+ (tl,smallfoot_ae_const n'))
               )
               (smallfoot_ap_data_list_seg tl
                  (smallfoot_ae_const n') ((FMAP_MAP TL data) |+ (t,L))
                  e2)))``,

SIMP_TAC list_ss [smallfoot_ap_data_list_seg___NOT_EMPTY_DATA_DEF,
            smallfoot_ap_data_list_seg_num_def,
            combinTheory.K_DEF, FMAP_MAP_FUPDATE]);






val SMALLFOOT_COND_PROP___STRONG_IMP___data_list_seg_split =
store_thm ("SMALLFOOT_COND_PROP___STRONG_IMP___data_list_seg_split",
``!wpb rpb sfb e1 data e2 tl.
  (SMALLFOOT_AE_USED_VARS_SUBSET (SET_OF_BAG (BAG_UNION wpb rpb)) e1 /\
   SMALLFOOT_AE_USED_VARS_SUBSET (SET_OF_BAG (BAG_UNION wpb rpb)) e2)
  ==>
  SMALLFOOT_COND_PROP___STRONG_IMP
  (smallfoot_prop (wpb,rpb) (BAG_INSERT (smallfoot_ap_unequal e1 e2)
                            (BAG_INSERT (smallfoot_ap_data_list_seg tl e1 data e2)
                             sfb))) 
  (COND_PROP___EXISTS n.
   smallfoot_prop (wpb,rpb) (BAG_INSERT (smallfoot_ap_points_to e1 ((FMAP_MAP (\dl. smallfoot_ae_const (HD dl)) data) |+ (tl, smallfoot_ae_const n)))
                            (BAG_INSERT (smallfoot_ap_empty_heap_cond (FEVERY (\x. ~(SND x = [])) data))
                            (BAG_INSERT (smallfoot_ap_unequal e1 e2)
                            (BAG_INSERT (smallfoot_ap_data_list_seg tl (smallfoot_ae_const n) (FMAP_MAP TL data) e2)
                             sfb)))))``,


SIMP_TAC std_ss [SMALLFOOT_COND_PROP___STRONG_IMP_def,
		 smallfoot_prop___REWRITE,
		 COND_RATOR, COND_RAND,
		 asl_bool_EVAL, IN_ABS,
		 smallfoot_prop___COND_INSERT,
		 COND_PROP___EXISTS_def,
		 SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___compare,
		 SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___smallfoot_ap_empty_heap_cond,
 		 SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___data_list_seg,
		 SMALLFOOT_AE_USED_VARS_SUBSET___EVAL] THEN
REPEAT STRIP_TAC THEN

`!n.
SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS
        (SET_OF_BAG (BAG_UNION wpb rpb))
        (smallfoot_ap_points_to e1 
           ((FMAP_MAP (\dl. smallfoot_ae_const (HD dl)) data) |+ (tl,smallfoot_ae_const n)))` by ALL_TAC THEN1 (
  CONSEQ_REWRITE_TAC ([],[SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___points_to,
                      FEVERY_STRENGTHEN_THM],[]) THEN
  ASM_SIMP_TAC std_ss [FEVERY_FMAP_MAP, SMALLFOOT_AE_USED_VARS_SUBSET___EVAL] THEN
  SIMP_TAC std_ss [FEVERY_DEF]
) THEN
ASM_REWRITE_TAC[] THEN

ONCE_REWRITE_TAC[EXTENSION] THEN
SIMP_TAC (std_ss++bool_eq_imp_ss) [IN_ABS,
   smallfoot_prop___PROP___REWRITE,
   smallfoot_ap_bigstar_REWRITE] THEN

Q.ABBREV_TAC `P = smallfoot_ap_star (smallfoot_ap_unequal e1 e2)
                  (smallfoot_ap_data_list_seg tl e1 data e2)` THEN
`smallfoot_ap_star smallfoot_ap_stack_true
         (smallfoot_ap_star (smallfoot_ap_unequal e1 e2)
            (smallfoot_ap_star (smallfoot_ap_data_list_seg tl e1 data e2)
               (smallfoot_ap_bigstar sfb))) =
smallfoot_ap_star P (smallfoot_ap_star smallfoot_ap_stack_true
                    (smallfoot_ap_bigstar sfb))` by ALL_TAC THEN1 (
   METIS_TAC[smallfoot_ap_star___PROPERTIES, 
	     COMM_DEF, ASSOC_DEF]
) THEN
ASM_REWRITE_TAC[] THEN (POP_ASSUM (K ALL_TAC)) THEN

MP_TAC (Q.SPECL [`e1`, `data`, `e2`, `tl`] smallfoot_ap_star___data_list_seg_unroll) THEN

`IS_SOME___SMALLFOOT_AE_USED_VARS e1 /\
 IS_SOME___SMALLFOOT_AE_USED_VARS e2` by 
   FULL_SIMP_TAC std_ss [IS_SOME___SMALLFOOT_AE_USED_VARS_def,
	  	     SMALLFOOT_AE_USED_VARS_SUBSET_def] THEN


ASM_SIMP_TAC std_ss [smallfoot_ap_star_def,
                     GSYM asl_exists___asl_star_THM] THEN

Q.UNABBREV_TAC `P` THEN
DISCH_TAC THEN (POP_ASSUM (K ALL_TAC)) THEN

Tactical.REVERSE (
   Cases_on `FEVERY (\x. ~(SND x = [])) data`) THEN (
   FULL_SIMP_TAC std_ss [GSYM smallfoot_ap_empty_heap_cond___false,
			 smallfoot_ap_false_def, asl_bool_REWRITES,
			 asl_false___asl_star_THM]
) THEN

`ASSOC smallfoot_ap_star` by REWRITE_TAC[smallfoot_ap_star___PROPERTIES] THEN
ASM_SIMP_TAC std_ss [smallfoot_ap_star_def,
                     GSYM asl_exists___asl_star_THM] THEN

FULL_SIMP_TAC std_ss [GSYM smallfoot_ap_star_def,
		      ASSOC_SYM, asl_exists_def, IN_ABS,
		      GSYM smallfoot_ap_stack_true_REWRITE,
                      smallfoot_ap_star___swap_ap_stack_true,
                      smallfoot_ap_star___ap_stack_true___IDEM2] THEN
SIMP_TAC std_ss [GSYM smallfoot_ap_bigstar_REWRITE] THEN
REPEAT STRIP_TAC THEN
METIS_TAC[bagTheory.BAG_INSERT_commutes]);





val SMALLFOOT_COND_PROP___IMP___data_list_seg_split =
store_thm ("SMALLFOOT_COND_PROP___IMP___data_list_seg_split",
``!wpb rpb sfb e1 data e2 tl.
  (SMALLFOOT_AE_USED_VARS_SUBSET (SET_OF_BAG (BAG_UNION wpb rpb)) e1 /\
   SMALLFOOT_AE_USED_VARS_SUBSET (SET_OF_BAG (BAG_UNION wpb rpb)) e2)
  ==>
  SMALLFOOT_COND_PROP___IMP
  (smallfoot_prop (wpb,rpb) (BAG_INSERT (smallfoot_ap_unequal e1 e2)
                            (BAG_INSERT (smallfoot_ap_data_list_seg tl e1 data e2)
                             sfb))) 
  (COND_PROP___EXISTS n.
   smallfoot_prop (wpb,rpb) (BAG_INSERT (smallfoot_ap_points_to e1 ((FMAP_MAP (\dl. smallfoot_ae_const (HD dl)) data) |+ (tl, smallfoot_ae_const n)))
                            (BAG_INSERT (smallfoot_ap_empty_heap_cond (FEVERY (\x. ~(SND x = [])) data))
                            (BAG_INSERT (smallfoot_ap_unequal e1 e2)
                            (BAG_INSERT (smallfoot_ap_data_list_seg tl (smallfoot_ae_const n) (FMAP_MAP TL data) e2)
                             sfb)))))``,

REPEAT STRIP_TAC THEN
MATCH_MP_TAC SMALLFOOT_COND_PROP___STRONG_IMP_IMP THEN
ASM_SIMP_TAC std_ss [SMALLFOOT_COND_PROP___STRONG_IMP___data_list_seg_split]);




val SMALLFOOT_COND_PROP___IMP___data_list_split =
store_thm ("SMALLFOOT_COND_PROP___IMP___data_list_split",
``!wpb rpb sfb e data tl.
  SMALLFOOT_AE_USED_VARS_SUBSET (SET_OF_BAG (BAG_UNION wpb rpb)) e
  ==>
  SMALLFOOT_COND_PROP___IMP
  (smallfoot_prop (wpb,rpb) (BAG_INSERT (smallfoot_ap_unequal e smallfoot_ae_null)
                            (BAG_INSERT (smallfoot_ap_data_list tl e data)
                             sfb))) 
  (COND_PROP___EXISTS n.
   smallfoot_prop (wpb,rpb) (BAG_INSERT (smallfoot_ap_points_to e ((FMAP_MAP (\dl. smallfoot_ae_const (HD dl)) data) |+ (tl, smallfoot_ae_const n)))
                            (BAG_INSERT (smallfoot_ap_empty_heap_cond (FEVERY (\x. ~(SND x = [])) data))
                            (BAG_INSERT (smallfoot_ap_unequal e smallfoot_ae_null)
                            (BAG_INSERT (smallfoot_ap_data_list tl (smallfoot_ae_const n) (FMAP_MAP TL data))
                             sfb)))))``,

SIMP_TAC std_ss [smallfoot_ap_data_list_def,
		 SMALLFOOT_COND_PROP___IMP___data_list_seg_split,
		 SMALLFOOT_AE_USED_VARS_SUBSET___EVAL]);





val smallfoot_ap_star___bintree_unroll =
store_thm ("smallfoot_ap_star___bintree_unroll",
``
!e lt rt.
(IS_SOME___SMALLFOOT_AE_USED_VARS e) ==>

(smallfoot_ap_star (smallfoot_ap_unequal e smallfoot_ae_null) (smallfoot_ap_bintree (lt,rt) e) =
 asl_exists n n'. smallfoot_ap_bigstar_list [
	    smallfoot_ap_unequal e smallfoot_ae_null;
	    smallfoot_ap_points_to e (FEMPTY |+ (rt, smallfoot_ae_const n) |+ (lt, smallfoot_ae_const n'));
	    smallfoot_ap_bintree (lt,rt) (smallfoot_ae_const n);
            smallfoot_ap_bintree (lt,rt) (smallfoot_ae_const n')])``,

ONCE_REWRITE_TAC [EXTENSION] THEN
REPEAT STRIP_TAC THEN

`!n n' lt rt. SMALLFOOT_AP_PERMISSION_UNIMPORTANT 
       (smallfoot_ap_points_to e (FEMPTY |+ (lt,smallfoot_ae_const n) |+ (rt,smallfoot_ae_const n')))` by ALL_TAC THEN1 (
  REPEAT GEN_TAC THEN
  MATCH_MP_TAC SMALLFOOT_AP_PERMISSION_UNIMPORTANT___points_to THEN
  ASM_SIMP_TAC std_ss [FEVERY_FEMPTY, FEVERY_FUPDATE, DRESTRICT_FEMPTY,
		       IS_SOME___SMALLFOOT_AE_USED_VARS___EVAL,
		       DRESTRICT_FUPDATE, COND_RAND, COND_RATOR]
) THEN           
SIMP_TAC std_ss [smallfoot_ap_bigstar_list_def,
		 asl_bigstar_list_REWRITE,
		 GSYM smallfoot_ap_star_def,
		 GSYM smallfoot_ap_emp_def,
		 smallfoot_ap_star___PROPERTIES] THEN
ASM_SIMP_TAC std_ss [smallfoot_ap_star___PERMISSION_UNIMPORTANT,
		     SMALLFOOT_AP_PERMISSION_UNIMPORTANT___bintree,
     		     SMALLFOOT_AP_PERMISSION_UNIMPORTANT___star,
    		     SMALLFOOT_AP_PERMISSION_UNIMPORTANT___compare,
		     smallfoot_ae_null_def,
		     IS_SOME___SMALLFOOT_AE_USED_VARS___EVAL] THEN

CONV_TAC (LHS_CONV (ONCE_REWRITE_CONV [smallfoot_ap_bintree_REWRITE])) THEN
ASM_SIMP_TAC std_ss [smallfoot_ap_star___PERMISSION_UNIMPORTANT,
		     SMALLFOOT_AP_PERMISSION_UNIMPORTANT___bintree,
                     SMALLFOOT_AP_PERMISSION_UNIMPORTANT___star,
		     IS_SOME___SMALLFOOT_AE_USED_VARS___EVAL] THEN
SIMP_TAC std_ss [asl_bool_EVAL, IN_ABS, GSYM RIGHT_EXISTS_AND_THM,
		 LEFT_AND_OVER_OR, RIGHT_AND_OVER_OR,
		 EXISTS_OR_THM] THEN
SIMP_TAC std_ss [smallfoot_ap_unequal_def,
		    smallfoot_ap_equal_def,
		    smallfoot_ap_weak_unequal_def,
		    smallfoot_ap_binexpression_def,
		    smallfoot_a_stack_proposition_def,
		    LET_THM, IN_ABS,
		    FUNION_FEMPTY_2, FUNION_FEMPTY_1,
		    smallfoot_ae_const_def,
		    smallfoot_ae_null_def,
		    FDOM_FEMPTY, DISJOINT_EMPTY] THEN
SIMP_TAC (std_ss++bool_neg_pair_ss) [] THEN

HO_MATCH_MP_TAC (prove (``((!n n' h1' h1'' h2''. 
			     A n n' h1' h1'' h2'' =
			     B n' n h1' h2'' h1'')) ==>
                       ((?n n' h1' h1'' h2''. A n n' h1' h1'' h2'') =
                        (?n n' h1' h1'' h2''. B n n' h1' h1'' h2''))``, 
                 METIS_TAC[])) THEN

SIMP_TAC (std_ss++bool_eq_imp_ss) [FUNION_DEF, DISJOINT_UNION_BOTH] THEN
REPEAT STRIP_TAC THEN
METIS_TAC[FUNION___COMM, DISJOINT_SYM]);











val SMALLFOOT_COND_PROP___STRONG_IMP___bintree_split =
store_thm ("SMALLFOOT_COND_PROP___STRONG_IMP___bintree_split",
``!wpb rpb sfb e lt rt.
  (SMALLFOOT_AE_USED_VARS_SUBSET (SET_OF_BAG (BAG_UNION wpb rpb)) e)
  ==>
  SMALLFOOT_COND_PROP___STRONG_IMP
  (smallfoot_prop (wpb,rpb) (BAG_INSERT (smallfoot_ap_unequal e smallfoot_ae_null)
                            (BAG_INSERT (smallfoot_ap_bintree (lt,rt) e)
                             sfb))) 
  (COND_PROP___EXISTS n n'.
   smallfoot_prop (wpb,rpb) (BAG_INSERT (smallfoot_ap_points_to e (FEMPTY |+ (rt, smallfoot_ae_const n) |+ (lt, smallfoot_ae_const n')))
                            (BAG_INSERT (smallfoot_ap_unequal e smallfoot_ae_null)
                            (BAG_INSERT (smallfoot_ap_bintree (lt,rt) (smallfoot_ae_const n))
                            (BAG_INSERT (smallfoot_ap_bintree (lt,rt) (smallfoot_ae_const n'))
                             sfb)))))``,


SIMP_TAC std_ss [SMALLFOOT_COND_PROP___STRONG_IMP_def,
		 smallfoot_prop___REWRITE,
		 COND_RATOR, COND_RAND,
		 asl_bool_EVAL, IN_ABS,
		 smallfoot_prop___COND_INSERT,
		 COND_PROP___EXISTS_def,
		 SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___compare,
 		 SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___bintree,
		 SMALLFOOT_AE_USED_VARS_SUBSET___EVAL] THEN
REPEAT STRIP_TAC THEN

`!n n'.
SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS
        (SET_OF_BAG (BAG_UNION wpb rpb))
        (smallfoot_ap_points_to e  (FEMPTY |+ (rt, smallfoot_ae_const n) |+ (lt, smallfoot_ae_const n')))` by ALL_TAC THEN1 (
  REPEAT GEN_TAC THEN
  MATCH_MP_TAC SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___points_to THEN
  ASM_SIMP_TAC std_ss [FEVERY_FUPDATE, SMALLFOOT_AE_USED_VARS_SUBSET___EVAL,
		       DRESTRICT_FEMPTY, FEVERY_FEMPTY,
		       DRESTRICT_FUPDATE, IN_COMPL, IN_SING,
		       COND_RAND, COND_RATOR]
) THEN
ASM_REWRITE_TAC[] THEN

ONCE_REWRITE_TAC[EXTENSION] THEN
SIMP_TAC (std_ss++bool_eq_imp_ss) [IN_ABS,
   smallfoot_prop___PROP___REWRITE,
   smallfoot_ap_bigstar_REWRITE] THEN

Q.ABBREV_TAC `P = smallfoot_ap_star (smallfoot_ap_unequal e smallfoot_ae_null)
                  (smallfoot_ap_bintree (lt,rt) e)` THEN
`smallfoot_ap_star smallfoot_ap_stack_true
         (smallfoot_ap_star (smallfoot_ap_unequal e smallfoot_ae_null)
            (smallfoot_ap_star (smallfoot_ap_bintree (lt,rt) e)
               (smallfoot_ap_bigstar sfb))) =
smallfoot_ap_star P (smallfoot_ap_star smallfoot_ap_stack_true
                    (smallfoot_ap_bigstar sfb))` by ALL_TAC THEN1 (
   METIS_TAC[smallfoot_ap_star___PROPERTIES, 
	     COMM_DEF, ASSOC_DEF]
) THEN
ASM_REWRITE_TAC[] THEN (POP_ASSUM (K ALL_TAC)) THEN

MP_TAC (Q.SPECL [`e`, `lt`, `rt`] smallfoot_ap_star___bintree_unroll) THEN

`IS_SOME___SMALLFOOT_AE_USED_VARS e` by 
   FULL_SIMP_TAC std_ss [IS_SOME___SMALLFOOT_AE_USED_VARS_def,
	  	     SMALLFOOT_AE_USED_VARS_SUBSET_def] THEN

ASM_SIMP_TAC std_ss [smallfoot_ap_star_def,
                     GSYM asl_exists___asl_star_THM] THEN
Q.UNABBREV_TAC `P` THEN
DISCH_TAC THEN (POP_ASSUM (K ALL_TAC)) THEN


SIMP_TAC std_ss [GSYM smallfoot_ap_star_def,
                 asl_exists_def, IN_ABS,
		 smallfoot_ap_bigstar_list_def,
		 asl_bigstar_list_REWRITE,
		 GSYM smallfoot_ap_emp_def,
		 smallfoot_ap_star___PROPERTIES] THEN
`ASSOC smallfoot_ap_star` by REWRITE_TAC[smallfoot_ap_star___PROPERTIES] THEN
FULL_SIMP_TAC std_ss [ASSOC_SYM] THEN
SIMP_TAC std_ss [GSYM smallfoot_ap_bigstar_REWRITE] THEN
REPEAT STRIP_TAC THEN
METIS_TAC[bagTheory.BAG_INSERT_commutes]);







val SMALLFOOT_COND_PROP___IMP___bintree_split =
store_thm ("SMALLFOOT_COND_PROP___IMP___bintree_split",
``!wpb rpb sfb e lt rt.
  (SMALLFOOT_AE_USED_VARS_SUBSET (SET_OF_BAG (BAG_UNION wpb rpb)) e)
  ==>
  SMALLFOOT_COND_PROP___IMP
  (smallfoot_prop (wpb,rpb) (BAG_INSERT (smallfoot_ap_unequal e smallfoot_ae_null)
                            (BAG_INSERT (smallfoot_ap_bintree (lt,rt) e)
                             sfb))) 
  (COND_PROP___EXISTS n n'.
   smallfoot_prop (wpb,rpb) (BAG_INSERT (smallfoot_ap_points_to e (FEMPTY |+ (rt, smallfoot_ae_const n) |+ (lt, smallfoot_ae_const n')))
                            (BAG_INSERT (smallfoot_ap_unequal e smallfoot_ae_null)
                            (BAG_INSERT (smallfoot_ap_bintree (lt,rt) (smallfoot_ae_const n))
                            (BAG_INSERT (smallfoot_ap_bintree (lt,rt) (smallfoot_ae_const n'))
                             sfb)))))``,



REPEAT STRIP_TAC THEN
MATCH_MP_TAC SMALLFOOT_COND_PROP___STRONG_IMP_IMP THEN
ASM_SIMP_TAC std_ss [SMALLFOOT_COND_PROP___STRONG_IMP___bintree_split]);







val SMALLFOOT_IS_STRONG_STACK_PROPOSITION_def = Define 
`SMALLFOOT_IS_STRONG_STACK_PROPOSITION (P:smallfoot_a_proposition) =
 !s. s IN P ==> (SND s = FEMPTY)`


val SMALLFOOT_IS_STRONG_STACK_PROPOSITION___EVAL = store_thm ("SMALLFOOT_IS_STRONG_STACK_PROPOSITION___EVAL",

``SMALLFOOT_IS_STRONG_STACK_PROPOSITION (smallfoot_ap_equal e1 e2) /\
  SMALLFOOT_IS_STRONG_STACK_PROPOSITION (smallfoot_ap_unequal e1 e2) /\
  SMALLFOOT_IS_STRONG_STACK_PROPOSITION (smallfoot_ap_less e1 e2) /\
  SMALLFOOT_IS_STRONG_STACK_PROPOSITION (smallfoot_ap_lesseq e1 e2) /\
  SMALLFOOT_IS_STRONG_STACK_PROPOSITION (smallfoot_ap_greater e1 e2) /\
  SMALLFOOT_IS_STRONG_STACK_PROPOSITION (smallfoot_ap_greatereq e1 e2) /\
  SMALLFOOT_IS_STRONG_STACK_PROPOSITION (smallfoot_ap_stack_true) /\
  SMALLFOOT_IS_STRONG_STACK_PROPOSITION (smallfoot_ap_false) /\
  SMALLFOOT_IS_STRONG_STACK_PROPOSITION (smallfoot_ap_exp_is_defined e1) /\
  SMALLFOOT_IS_STRONG_STACK_PROPOSITION (smallfoot_ap_empty_heap_cond c)
``,

SIMP_TAC std_ss [SMALLFOOT_IS_STRONG_STACK_PROPOSITION_def,
		 smallfoot_ap_equal_def,
		 smallfoot_ap_binexpression_def,
		 smallfoot_a_stack_proposition_def,
		 IN_ABS,

		 smallfoot_ap_unequal_def,
		 smallfoot_ap_less_def,
		 smallfoot_ap_lesseq_def,
		 smallfoot_ap_greatereq_def,
		 smallfoot_ap_greater_def,
		 smallfoot_ap_stack_true_def,
		 smallfoot_ap_exp_is_defined_def,
		 smallfoot_ap_empty_heap_cond_def,
		 smallfoot_ap_false___NOT_IN]);









val SMALLFOOT_IS_STRONG_STACK_PROPOSITION___EQ_REWRITE = store_thm (
"SMALLFOOT_IS_STRONG_STACK_PROPOSITION___EQ_REWRITE",

``SMALLFOOT_IS_STRONG_STACK_PROPOSITION P =
 (!s. s IN P = (FST s, FEMPTY) IN P /\ (SND s = FEMPTY))``,

SIMP_TAC std_ss [SMALLFOOT_IS_STRONG_STACK_PROPOSITION_def,
		 PAIR_FORALL_THM] THEN
METIS_TAC[]);




val smallfoot_prop___PROP_UNION = store_thm ("smallfoot_prop___PROP_UNION",
``!wpb rpb sfb1 sfb2.
smallfoot_prop___COND (wpb,rpb) (BAG_UNION sfb1 sfb2) ==>

(smallfoot_prop___PROP (wpb,rpb) (BAG_UNION sfb1 sfb2) =
 (\s. ?h1 h2. 
              DISJOINT (FDOM h1) (FDOM h2) /\ (SND s = FUNION h1 h2) /\
              (FST s,h1) IN (smallfoot_prop___PROP (wpb,rpb) sfb1) /\
              (FST s,h2) IN (smallfoot_prop___PROP (wpb,rpb) sfb2)))``,

REPEAT STRIP_TAC THEN
ONCE_REWRITE_TAC[EXTENSION] THEN
SIMP_TAC std_ss [IN_ABS, smallfoot_prop___PROP___REWRITE] THEN
Q.ABBREV_TAC `P1 = smallfoot_ap_star smallfoot_ap_stack_true (smallfoot_ap_bigstar sfb1)` THEN
Q.ABBREV_TAC `P2 = smallfoot_ap_star smallfoot_ap_stack_true (smallfoot_ap_bigstar sfb2)` THEN
SIMP_TAC (std_ss++bool_eq_imp_ss) [] THEN
REPEAT STRIP_TAC THEN
`smallfoot_ap_star smallfoot_ap_stack_true
 (smallfoot_ap_bigstar (BAG_UNION sfb1 sfb2)) =
 smallfoot_ap_star P1 P2` by ALL_TAC THEN1 (

  ONCE_REWRITE_TAC[GSYM smallfoot_ap_star___ap_stack_true___IDEM] THEN
  `(COMM smallfoot_ap_star) /\ (ASSOC smallfoot_ap_star)` by REWRITE_TAC[smallfoot_ap_star___PROPERTIES] THEN
  SIMP_TAC std_ss [smallfoot_ap_bigstar___BAG_UNION] THEN 
  METIS_TAC[COMM_DEF, ASSOC_DEF]
) THEN
ASM_REWRITE_TAC[] THEN (POP_ASSUM (K ALL_TAC)) THEN

Tactical.REVERSE (`SMALLFOOT_AP_PERMISSION_UNIMPORTANT P1 /\
         SMALLFOOT_AP_PERMISSION_UNIMPORTANT P2` by ALL_TAC) THEN1 (
  ASM_SIMP_TAC std_ss [smallfoot_ap_star___PERMISSION_UNIMPORTANT, IN_ABS]
) THEN
FULL_SIMP_TAC std_ss [smallfoot_prop___COND_UNION] THEN
FULL_SIMP_TAC std_ss [smallfoot_prop___COND___EXPAND,
		      SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS_def]);









val smallfoot_ap_bag_implies_in_heap_or_null___SUB_BAG =
  store_thm ("smallfoot_ap_bag_implies_in_heap_or_null___SUB_BAG",
``  !sfb1 sfb2 e.
  (SUB_BAG sfb1 sfb2 /\
  smallfoot_ap_bag_implies_in_heap_or_null sfb1 e) ==>
  smallfoot_ap_bag_implies_in_heap_or_null sfb2 e``,

SIMP_TAC std_ss [smallfoot_ap_bag_implies_in_heap_or_null_def,
		 bagTheory.SUB_BAG_EXISTS, GSYM LEFT_EXISTS_AND_THM,
		 GSYM RIGHT_EXISTS_AND_THM, GSYM LEFT_FORALL_IMP_THM,
		 BAG_EVERY_def, bagTheory.BAG_IN_BAG_UNION] THEN
REPEAT STRIP_TAC THEN
FULL_SIMP_TAC std_ss [smallfoot_ap_bigstar___BAG_UNION,
		      smallfoot_ap_bigstar_REWRITE] THEN
Q.ABBREV_TAC `P1 = smallfoot_ap_star smallfoot_ap_stack_true
              (smallfoot_ap_bigstar sfb1)` THEN
Q.ABBREV_TAC `P2 = smallfoot_ap_star smallfoot_ap_stack_true
              (smallfoot_ap_bigstar b)` THEN

`smallfoot_ap_star smallfoot_ap_stack_true
        (smallfoot_ap_star (smallfoot_ap_bigstar sfb1)
           (smallfoot_ap_bigstar b)) =
 smallfoot_ap_star P1 P2` by ALL_TAC THEN1 (
  ONCE_REWRITE_TAC[GSYM smallfoot_ap_star___ap_stack_true___IDEM] THEN
  METIS_TAC[smallfoot_ap_star___PROPERTIES,
	    COMM_DEF, ASSOC_DEF]
) THEN
FULL_SIMP_TAC std_ss [] THEN POP_ASSUM (K ALL_TAC) THEN
`SMALLFOOT_AP_PERMISSION_UNIMPORTANT P1 /\
 SMALLFOOT_AP_PERMISSION_UNIMPORTANT P2` by ALL_TAC THEN1 (
   UNABBREV_ALL_TAC THEN
   CONJ_TAC THEN (
      REWRITE_TAC[GSYM smallfoot_ap_bigstar_REWRITE] THEN
      MATCH_MP_TAC SMALLFOOT_AP_PERMISSION_UNIMPORTANT___bigstar THEN
      ASM_SIMP_TAC std_ss [bagTheory.BAG_IN_BAG_INSERT,
			   DISJ_IMP_THM, FORALL_AND_THM,
			   bagTheory.BAG_INSERT_NOT_EMPTY,
			   SMALLFOOT_AP_PERMISSION_UNIMPORTANT___smallfoot_ap_stack_true]
   )
) THEN
FULL_SIMP_TAC std_ss [smallfoot_ap_star___PERMISSION_UNIMPORTANT,
		     GSYM LEFT_FORALL_IMP_THM, FDOM_FUNION,
		     IN_UNION, IN_ABS] THEN
RES_TAC THEN
FULL_SIMP_TAC std_ss [IN_INSERT, IN_UNION]);







val smallfoot_ap_bag_implies_in_heap_or_null___points_to = store_thm (
 "smallfoot_ap_bag_implies_in_heap_or_null___points_to",

``!e L sfb. smallfoot_ap_bag_implies_in_heap_or_null (BAG_INSERT (smallfoot_ap_points_to e L) sfb) e``,

SIMP_TAC std_ss [smallfoot_ap_bag_implies_in_heap_or_null_def,
		 smallfoot_ap_bigstar_REWRITE,
		 smallfoot_ap_star___swap_ap_stack_true,
		 BAG_EVERY_def, bagTheory.BAG_IN_BAG_INSERT,
		 DISJ_IMP_THM, FORALL_AND_THM] THEN
REPEAT GEN_TAC THEN STRIP_TAC THEN
Q.ABBREV_TAC `P = (smallfoot_ap_star smallfoot_ap_stack_true
           (smallfoot_ap_bigstar sfb))` THEN
`SMALLFOOT_AP_PERMISSION_UNIMPORTANT P` by ALL_TAC THEN1 (
   Q.UNABBREV_TAC `P` THEN
   SIMP_TAC std_ss [GSYM smallfoot_ap_bigstar_REWRITE] THEN
   MATCH_MP_TAC SMALLFOOT_AP_PERMISSION_UNIMPORTANT___bigstar THEN
   ASM_SIMP_TAC std_ss [bagTheory.BAG_IN_BAG_INSERT,
		        DISJ_IMP_THM, FORALL_AND_THM,
		        SMALLFOOT_AP_PERMISSION_UNIMPORTANT___smallfoot_ap_stack_true,
		        bagTheory.BAG_INSERT_NOT_EMPTY]
) THEN
ASM_SIMP_TAC std_ss [smallfoot_ap_star___PERMISSION_UNIMPORTANT,
		     GSYM LEFT_FORALL_IMP_THM,
		     smallfoot_ap_points_to_def, IN_ABS,
		     LET_THM, FDOM_FUNION, IN_UNION, IN_SING,
		     IN_INSERT] THEN
REPEAT STRIP_TAC THEN
FULL_SIMP_TAC std_ss [IS_SOME_EXISTS]);



val smallfoot_ap_bag_implies_in_heap_or_null___tree_seg_num = store_thm (
 "smallfoot_ap_bag_implies_in_heap_or_null___tree_seg_num",

``!e1 e2 n bal tagL sfb. 
    (IS_SOME___SMALLFOOT_AE_USED_VARS e1 /\
     IS_SOME___SMALLFOOT_AE_USED_VARS e2 /\
     ~(tagL = [])) ==>
             smallfoot_ap_bag_implies_in_heap_or_null (BAG_INSERT (smallfoot_ap_tree_seg_num n bal tagL e1 e2) 
                                              (BAG_INSERT (smallfoot_ap_unequal e1 e2) sfb)) e1``,

SIMP_TAC std_ss [smallfoot_ap_bag_implies_in_heap_or_null_def,
		 smallfoot_ap_bigstar_REWRITE,
		 smallfoot_ap_star___swap_ap_stack_true,
		 BAG_EVERY_def, bagTheory.BAG_IN_BAG_INSERT,
		 DISJ_IMP_THM, FORALL_AND_THM] THEN
REPEAT GEN_TAC THEN STRIP_TAC THEN STRIP_TAC THEN
Q.ABBREV_TAC `P = (smallfoot_ap_star smallfoot_ap_stack_true
           (smallfoot_ap_bigstar sfb))` THEN
`SMALLFOOT_AP_PERMISSION_UNIMPORTANT P` by ALL_TAC THEN1 (
   Q.UNABBREV_TAC `P` THEN
   SIMP_TAC std_ss [GSYM smallfoot_ap_bigstar_REWRITE] THEN
   MATCH_MP_TAC SMALLFOOT_AP_PERMISSION_UNIMPORTANT___bigstar THEN
   ASM_SIMP_TAC std_ss [bagTheory.BAG_IN_BAG_INSERT,
		        DISJ_IMP_THM, FORALL_AND_THM,
		        SMALLFOOT_AP_PERMISSION_UNIMPORTANT___smallfoot_ap_stack_true,
		        bagTheory.BAG_INSERT_NOT_EMPTY]
) THEN
ASM_SIMP_TAC std_ss [smallfoot_ap_star___PERMISSION_UNIMPORTANT,
		     SMALLFOOT_AP_PERMISSION_UNIMPORTANT___star,
		     IN_ABS] THEN
SIMP_TAC std_ss [asl_bool_EVAL, smallfoot_ap_equal_def,
		 smallfoot_ap_weak_unequal_def,
		 smallfoot_ap_binexpression_def,
		 smallfoot_a_stack_proposition_def, IN_ABS,
		 smallfoot_ap_unequal_def, FUNION_FEMPTY_1,
		 LET_THM, DISJOINT_EMPTY, FDOM_FEMPTY] THEN
REPEAT GEN_TAC THEN
Cases_on `e1 (FST s)` THEN ASM_SIMP_TAC std_ss [] THEN
Cases_on `e2 (FST s)` THEN ASM_SIMP_TAC std_ss [] THEN
Cases_on `x = x'` THEN ASM_SIMP_TAC std_ss [] THEN

ONCE_REWRITE_TAC[smallfoot_ap_tree_seg_num_REWRITE] THEN
ASM_SIMP_TAC list_ss [asl_bool_EVAL, smallfoot_ap_equal_def,
		      smallfoot_ap_weak_unequal_def,
		      smallfoot_ap_binexpression_def,
		      smallfoot_a_stack_proposition_def,
		      LET_THM, IN_ABS, GSYM LEFT_FORALL_IMP_THM,
		      COND_RATOR, COND_RAND] THEN
REPEAT GEN_TAC THEN STRIP_TAC THEN
`(SMALLFOOT_AP_PERMISSION_UNIMPORTANT (smallfoot_ap_points_to e1 (LISTS_TO_FMAP (tagL,eL)))) /\
 SMALLFOOT_AP_PERMISSION_UNIMPORTANT (smallfoot_ap_bigstar_list
              (MAP
                 (\startExp.
                    smallfoot_ap_tree_seg_num (PRE n) bal tagL startExp e2)
                 eL))` by ALL_TAC THEN1 (

   REPEAT STRIP_TAC THENL [
      MATCH_MP_TAC SMALLFOOT_AP_PERMISSION_UNIMPORTANT___points_to THEN
      ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC FEVERY_LISTS_TO_FMAP THEN
      ASM_SIMP_TAC list_ss [MEM_ZIP, GSYM LEFT_FORALL_IMP_THM] THEN
      REPEAT STRIP_TAC  THEN
      RES_TAC THEN
      FULL_SIMP_TAC std_ss [IS_SOME___SMALLFOOT_AE_USED_VARS___EVAL,
			    smallfoot_ae_is_const_def],

      MATCH_MP_TAC SMALLFOOT_AP_PERMISSION_UNIMPORTANT___bigstar_list THEN
      ASM_SIMP_TAC list_ss [MEM_MAP, GSYM LEFT_FORALL_IMP_THM,
			    MEM_EL] THEN
      REPEAT STRIP_TAC THENL [
         Cases_on `tagL` THEN
         FULL_SIMP_TAC list_ss [],

	 RES_TAC THEN
	 MATCH_MP_TAC SMALLFOOT_AP_PERMISSION_UNIMPORTANT___smallfoot_ap_tree_seg_num THEN
	 FULL_SIMP_TAC std_ss [smallfoot_ae_is_const_def,
			       IS_SOME___SMALLFOOT_AE_USED_VARS___EVAL]
      ]
   ]
) THEN
FULL_SIMP_TAC std_ss [smallfoot_ap_star___PERMISSION_UNIMPORTANT,
		     IN_ABS, GSYM RIGHT_EXISTS_AND_THM,
		     GSYM LEFT_FORALL_IMP_THM,
		     GSYM LEFT_EXISTS_AND_THM] THEN
Q.PAT_ASSUM `(FST s,h1') IN X` MP_TAC THEN
ASM_SIMP_TAC std_ss [smallfoot_ap_points_to_def, IN_ABS,
		 LET_THM, FDOM_FUNION, IN_UNION, IN_SING, IN_INSERT]);







val smallfoot_ap_bag_implies_in_heap_or_null___tree_seg = store_thm (
 "smallfoot_ap_bag_implies_in_heap_or_null___tree_seg",

``!e1 e2 bal tagL sfb. 
    (IS_SOME___SMALLFOOT_AE_USED_VARS e1 /\
     IS_SOME___SMALLFOOT_AE_USED_VARS e2 /\
     ~(tagL = [])) ==>
             smallfoot_ap_bag_implies_in_heap_or_null (BAG_INSERT (smallfoot_ap_tree_seg bal tagL e1 e2) 
                                              (BAG_INSERT (smallfoot_ap_unequal e1 e2) sfb)) e1``,


REPEAT STRIP_TAC THEN
`!n. smallfoot_ap_bag_implies_in_heap_or_null
              (BAG_INSERT (smallfoot_ap_tree_seg_num n bal tagL e1 e2)
                 (BAG_INSERT (smallfoot_ap_unequal e1 e2) sfb)) e1` by ALL_TAC THEN1 (
  ASM_SIMP_TAC std_ss [smallfoot_ap_bag_implies_in_heap_or_null___tree_seg_num]
) THEN
FULL_SIMP_TAC std_ss [smallfoot_ap_bag_implies_in_heap_or_null_def,
		      smallfoot_ap_tree_seg_def,
		      smallfoot_ap_bigstar_REWRITE,
		      smallfoot_ap_star_def,
		      GSYM asl_exists___asl_star_THM,
		      BAG_EVERY_THM] THEN
REPEAT STRIP_TAC THEN
`!n. SMALLFOOT_AP_PERMISSION_UNIMPORTANT
              (smallfoot_ap_tree_seg_num n bal tagL e1 e2)` by ALL_TAC THEN1 (
  GEN_TAC THEN
  MATCH_MP_TAC SMALLFOOT_AP_PERMISSION_UNIMPORTANT___smallfoot_ap_tree_seg_num THEN
  ASM_REWRITE_TAC[]
) THEN
FULL_SIMP_TAC std_ss [smallfoot_ap_implies_in_heap_def,
		      asl_exists_def, IN_DEF,
		      GSYM LEFT_FORALL_IMP_THM] THEN
METIS_TAC[]);





val smallfoot_ap_bag_implies_in_heap_or_null___data_list_seg = store_thm (
 "smallfoot_ap_bag_implies_in_heap_or_null___data_list_seg",

``!e1 data e2 tl sfb. 
    (IS_SOME___SMALLFOOT_AE_USED_VARS e1 /\
     IS_SOME___SMALLFOOT_AE_USED_VARS e2) ==>
             smallfoot_ap_bag_implies_in_heap_or_null (BAG_INSERT (smallfoot_ap_data_list_seg tl e1 data e2) 
                                              (BAG_INSERT (smallfoot_ap_unequal e1 e2) sfb)) e1``,

REPEAT STRIP_TAC THEN
SIMP_TAC std_ss [smallfoot_ap_bag_implies_in_heap_or_null_def,
		 smallfoot_ap_bigstar_REWRITE,
		 BAG_EVERY_THM] THEN

Q.ABBREV_TAC `P = smallfoot_ap_star smallfoot_ap_stack_true
                   (smallfoot_ap_bigstar sfb)` THEN
`smallfoot_ap_star smallfoot_ap_stack_true
        (smallfoot_ap_star (smallfoot_ap_data_list_seg tl e1 data e2)
           (smallfoot_ap_star (smallfoot_ap_unequal e1 e2)
              (smallfoot_ap_bigstar sfb))) =
 smallfoot_ap_star P (smallfoot_ap_star (smallfoot_ap_unequal e1 e2)
                      (smallfoot_ap_data_list_seg tl e1 data e2))` by ALL_TAC THEN1 (
   METIS_TAC[smallfoot_ap_star___PROPERTIES, ASSOC_DEF, COMM_DEF]
) THEN
ASM_REWRITE_TAC[] THEN POP_ASSUM (K ALL_TAC) THEN
ASM_SIMP_TAC std_ss [smallfoot_ap_star___data_list_seg_unroll] THEN
Tactical.REVERSE (Cases_on `FEVERY (\x. ~(SND x = [])) data`) THEN (
   ASM_SIMP_TAC std_ss [asl_bool_REWRITES] THEN
   ASM_SIMP_TAC std_ss [GSYM smallfoot_ap_false_def,
		        smallfoot_ap_false___smallfoot_ap_star_THM,
		        smallfoot_ap_false___NOT_IN,
                        GSYM asl_exists___smallfoot_ap_star_THM,
		        asl_bool_EVAL]
) THEN
STRIP_TAC THEN
`SMALLFOOT_AP_PERMISSION_UNIMPORTANT P /\
 !n. SMALLFOOT_AP_PERMISSION_UNIMPORTANT (smallfoot_ap_points_to e1
                    (FMAP_MAP (\dl. smallfoot_ae_const (HD dl)) data |+
                     (tl,smallfoot_ae_const n)))` by ALL_TAC THEN1 (
   Q.UNABBREV_TAC `P` THEN
   SIMP_TAC std_ss [GSYM smallfoot_ap_bigstar_REWRITE] THEN
   CONSEQ_REWRITE_TAC ([],[SMALLFOOT_AP_PERMISSION_UNIMPORTANT___bigstar,
		      SMALLFOOT_AP_PERMISSION_UNIMPORTANT___points_to,
		      FEVERY_STRENGTHEN_THM],[]) THEN
   FULL_SIMP_TAC std_ss [FEVERY_DEF, FMAP_MAP_THM,
      IS_SOME___SMALLFOOT_AE_USED_VARS___EVAL, bagTheory.BAG_INSERT_NOT_EMPTY,
      bagTheory.BAG_IN_BAG_INSERT, DISJ_IMP_THM, FORALL_AND_THM,
      SMALLFOOT_AP_PERMISSION_UNIMPORTANT___smallfoot_ap_stack_true,
      BAG_EVERY_def]
) THEN
ASM_SIMP_TAC std_ss [smallfoot_ap_star___PERMISSION_UNIMPORTANT,
		     SMALLFOOT_AP_PERMISSION_UNIMPORTANT___star,
     		     SMALLFOOT_AP_PERMISSION_UNIMPORTANT___data_list_seg,
		     IS_SOME___SMALLFOOT_AE_USED_VARS___EVAL] THEN
SIMP_TAC (std_ss++boolSimps.CONJ_ss) [IN_ABS, GSYM RIGHT_EXISTS_AND_THM,
		 smallfoot_ap_points_to_def, LET_THM,
                 IS_SOME_EXISTS, GSYM LEFT_EXISTS_AND_THM,
		 GSYM LEFT_FORALL_IMP_THM, FDOM_FUNION, IN_INSERT,
                 IN_UNION]);



val smallfoot_ap_bag_implies_in_heap_or_null___unequal_null =
store_thm ("smallfoot_ap_bag_implies_in_heap_or_null___unequal_null",

``!e sfb.
IS_SOME___SMALLFOOT_AE_USED_VARS e ==>
(smallfoot_ap_bag_implies_in_heap_or_null
    (BAG_INSERT (smallfoot_ap_unequal e smallfoot_ae_null) sfb) e =
smallfoot_ap_bag_implies_in_heap_or_null 
    (BAG_INSERT (smallfoot_ap_exp_is_defined e) sfb) e)``,

REPEAT STRIP_TAC THEN
ASM_SIMP_TAC std_ss [smallfoot_ap_bag_implies_in_heap_or_null_def,
		 BAG_EVERY_THM,
		     SMALLFOOT_AP_PERMISSION_UNIMPORTANT___compare,
		     IS_SOME___SMALLFOOT_AE_USED_VARS___EVAL,
		     smallfoot_ap_bigstar_REWRITE,
		     smallfoot_ap_star___swap_ap_stack_true] THEN
Cases_on `BAG_EVERY SMALLFOOT_AP_PERMISSION_UNIMPORTANT sfb` THEN ASM_REWRITE_TAC[] THEN
Q.ABBREV_TAC `P = (smallfoot_ap_star smallfoot_ap_stack_true 
            (smallfoot_ap_bigstar sfb))` THEN

`SMALLFOOT_AP_PERMISSION_UNIMPORTANT P` by ALL_TAC THEN1 (
   Q.UNABBREV_TAC `P` THEN
   REWRITE_TAC [GSYM smallfoot_ap_bigstar_REWRITE] THEN
   MATCH_MP_TAC SMALLFOOT_AP_PERMISSION_UNIMPORTANT___bigstar THEN
   FULL_SIMP_TAC std_ss [BAG_EVERY_def, bagTheory.BAG_INSERT_NOT_EMPTY,
			 bagTheory.BAG_IN_BAG_INSERT,
			 DISJ_IMP_THM, FORALL_AND_THM,
			 SMALLFOOT_AP_PERMISSION_UNIMPORTANT___smallfoot_ap_stack_true]
) THEN
ASM_SIMP_TAC std_ss [SMALLFOOT_AP_PERMISSION_UNIMPORTANT___compare,
		     SMALLFOOT_AP_PERMISSION_UNIMPORTANT___smallfoot_ap_exp_is_defined,
	             IS_SOME___SMALLFOOT_AE_USED_VARS___EVAL,
		     smallfoot_ap_star___PERMISSION_UNIMPORTANT] THEN
SIMP_TAC std_ss [IN_ABS, smallfoot_ap_unequal_def,
		 smallfoot_ap_binexpression_def,
		 smallfoot_a_stack_proposition_def,
		 FDOM_FEMPTY, DISJOINT_EMPTY, FUNION_FEMPTY_1,
		 LET_THM, smallfoot_ae_null_def,
		 smallfoot_ap_exp_is_defined_def,
		 smallfoot_ae_const_def] THEN
SIMP_TAC (std_ss++boolSimps.CONJ_ss) [IS_SOME_EXISTS,
    GSYM LEFT_EXISTS_AND_THM, GSYM RIGHT_EXISTS_AND_THM,
    GSYM LEFT_FORALL_IMP_THM, IN_INSERT] THEN
METIS_TAC[]);




val smallfoot_ap_bag_implies_in_heap_or_null___data_list = store_thm (
 "smallfoot_ap_bag_implies_in_heap_or_null___data_list",

``!e data tl sfb.  
     IS_SOME___SMALLFOOT_AE_USED_VARS e ==>
             (smallfoot_ap_bag_implies_in_heap_or_null (BAG_INSERT (smallfoot_ap_data_list tl e data) sfb) e)``,

REPEAT STRIP_TAC THEN
MP_TAC (Q.SPECL [`e`, `data`, `smallfoot_ae_null`, `tl`, `sfb`] smallfoot_ap_bag_implies_in_heap_or_null___data_list_seg) THEN
ASM_SIMP_TAC list_ss [IS_SOME___SMALLFOOT_AE_USED_VARS___EVAL] THEN
ONCE_REWRITE_TAC[bagTheory.BAG_INSERT_commutes] THEN
ASM_SIMP_TAC std_ss [smallfoot_ap_bag_implies_in_heap_or_null___unequal_null,
		     GSYM smallfoot_ap_data_list_def] THEN

ASM_SIMP_TAC std_ss [smallfoot_ap_bag_implies_in_heap_or_null_def,
         	     BAG_EVERY_THM,
		     SMALLFOOT_AP_PERMISSION_UNIMPORTANT___data_list,
		     SMALLFOOT_AP_PERMISSION_UNIMPORTANT___compare,
		     SMALLFOOT_AP_PERMISSION_UNIMPORTANT___smallfoot_ap_exp_is_defined,
		     IS_SOME___SMALLFOOT_AE_USED_VARS___EVAL,
		     smallfoot_ap_bigstar_REWRITE,
		     smallfoot_ap_star___swap_ap_stack_true] THEN

Q.ABBREV_TAC `P1 = (smallfoot_ap_star smallfoot_ap_stack_true
                  (smallfoot_ap_bigstar sfb))` THEN
Q.ABBREV_TAC `P =  smallfoot_ap_star (smallfoot_ap_data_list tl e data) P1` THEN

REPEAT STRIP_TAC THEN FULL_SIMP_TAC std_ss [] THEN
Q.PAT_ASSUM `!s. X s` MATCH_MP_TAC THEN
`SMALLFOOT_AP_PERMISSION_UNIMPORTANT P1` by ALL_TAC THEN1 (
   Q.UNABBREV_TAC `P1` THEN
   REWRITE_TAC [GSYM smallfoot_ap_bigstar_REWRITE] THEN
   MATCH_MP_TAC SMALLFOOT_AP_PERMISSION_UNIMPORTANT___bigstar THEN
   FULL_SIMP_TAC std_ss [bagTheory.BAG_INSERT_NOT_EMPTY,
			   bagTheory.BAG_IN_BAG_INSERT,
			   DISJ_IMP_THM, FORALL_AND_THM,
			    BAG_EVERY_def,
			    SMALLFOOT_AP_PERMISSION_UNIMPORTANT___smallfoot_ap_stack_true]
) THEN
`SMALLFOOT_AP_PERMISSION_UNIMPORTANT P` by ALL_TAC THEN1 (
   Q.UNABBREV_TAC `P` THEN
   MATCH_MP_TAC SMALLFOOT_AP_PERMISSION_UNIMPORTANT___star THEN
   ASM_SIMP_TAC std_ss [SMALLFOOT_AP_PERMISSION_UNIMPORTANT___data_list]
) THEN

ASM_SIMP_TAC std_ss [smallfoot_ap_star___PERMISSION_UNIMPORTANT,
		     SMALLFOOT_AP_PERMISSION_UNIMPORTANT___smallfoot_ap_exp_is_defined] THEN
ASM_SIMP_TAC std_ss [IN_ABS, smallfoot_ap_exp_is_defined_def,
		 FUNION_FEMPTY_1, DISJOINT_EMPTY, FDOM_FEMPTY] THEN
Q.PAT_ASSUM `s IN P` MP_TAC THEN
Q.UNABBREV_TAC `P` THEN
ASM_SIMP_TAC std_ss [smallfoot_ap_star___PERMISSION_UNIMPORTANT,
		     SMALLFOOT_AP_PERMISSION_UNIMPORTANT___data_list,
                     smallfoot_ap_data_list_def] THEN
ONCE_REWRITE_TAC[smallfoot_ap_data_list_seg_REWRITE] THEN
ASM_SIMP_TAC std_ss [IN_ABS, asl_bool_EVAL, smallfoot_ap_equal_def,
		     smallfoot_ap_weak_unequal_def,
		     smallfoot_ap_binexpression_def,
		     smallfoot_a_stack_proposition_def, LET_THM] THEN
REPEAT STRIP_TAC THEN
ASM_REWRITE_TAC[]);





val smallfoot_ap_bag_implies_in_heap_or_null___bintree = store_thm (
 "smallfoot_ap_bag_implies_in_heap_or_null___bintree",

``!e lt rt sfb.  
     IS_SOME___SMALLFOOT_AE_USED_VARS e ==>
             (smallfoot_ap_bag_implies_in_heap_or_null (BAG_INSERT (smallfoot_ap_bintree (lt,rt) e) sfb) e)``,

REPEAT STRIP_TAC THEN
MP_TAC (Q.SPECL [`e`, `smallfoot_ae_null`, `F`, `[lt;rt]`, `sfb`] smallfoot_ap_bag_implies_in_heap_or_null___tree_seg) THEN
ASM_SIMP_TAC list_ss [IS_SOME___SMALLFOOT_AE_USED_VARS___EVAL] THEN
ONCE_REWRITE_TAC[bagTheory.BAG_INSERT_commutes] THEN
ASM_SIMP_TAC std_ss [smallfoot_ap_bag_implies_in_heap_or_null___unequal_null,
		     smallfoot_ap_tree_seg_def,
		     GSYM smallfoot_ap_bintree_num_def,
		     GSYM smallfoot_ap_bintree_def] THEN

ASM_SIMP_TAC std_ss [smallfoot_ap_bag_implies_in_heap_or_null_def,
         	     BAG_EVERY_THM,
		     SMALLFOOT_AP_PERMISSION_UNIMPORTANT___bintree,
		     SMALLFOOT_AP_PERMISSION_UNIMPORTANT___compare,
		     SMALLFOOT_AP_PERMISSION_UNIMPORTANT___smallfoot_ap_exp_is_defined,
		     IS_SOME___SMALLFOOT_AE_USED_VARS___EVAL,
		     smallfoot_ap_bigstar_REWRITE,
		     smallfoot_ap_star___swap_ap_stack_true] THEN

Q.ABBREV_TAC `P1 = (smallfoot_ap_star smallfoot_ap_stack_true
                  (smallfoot_ap_bigstar sfb))` THEN
Q.ABBREV_TAC `P =  smallfoot_ap_star (smallfoot_ap_bintree (lt,rt) e) P1` THEN

REPEAT STRIP_TAC THEN FULL_SIMP_TAC std_ss [] THEN
Q.PAT_ASSUM `!s. X s` MATCH_MP_TAC THEN
`SMALLFOOT_AP_PERMISSION_UNIMPORTANT P1` by ALL_TAC THEN1 (
   Q.UNABBREV_TAC `P1` THEN
   REWRITE_TAC [GSYM smallfoot_ap_bigstar_REWRITE] THEN
   MATCH_MP_TAC SMALLFOOT_AP_PERMISSION_UNIMPORTANT___bigstar THEN
   FULL_SIMP_TAC std_ss [bagTheory.BAG_INSERT_NOT_EMPTY,
			   bagTheory.BAG_IN_BAG_INSERT,
			   DISJ_IMP_THM, FORALL_AND_THM,
			    BAG_EVERY_def,
			    SMALLFOOT_AP_PERMISSION_UNIMPORTANT___smallfoot_ap_stack_true]
) THEN
`SMALLFOOT_AP_PERMISSION_UNIMPORTANT P` by ALL_TAC THEN1 (
   Q.UNABBREV_TAC `P` THEN
   MATCH_MP_TAC SMALLFOOT_AP_PERMISSION_UNIMPORTANT___star THEN
   ASM_SIMP_TAC std_ss [SMALLFOOT_AP_PERMISSION_UNIMPORTANT___bintree]
) THEN

ASM_SIMP_TAC std_ss [smallfoot_ap_star___PERMISSION_UNIMPORTANT,
		     SMALLFOOT_AP_PERMISSION_UNIMPORTANT___smallfoot_ap_exp_is_defined] THEN
ASM_SIMP_TAC std_ss [IN_ABS, smallfoot_ap_exp_is_defined_def,
		 FUNION_FEMPTY_1, DISJOINT_EMPTY, FDOM_FEMPTY] THEN
Q.PAT_ASSUM `s IN P` MP_TAC THEN
Q.UNABBREV_TAC `P` THEN
ASM_SIMP_TAC std_ss [smallfoot_ap_star___PERMISSION_UNIMPORTANT,
		     SMALLFOOT_AP_PERMISSION_UNIMPORTANT___bintree] THEN
ONCE_REWRITE_TAC[smallfoot_ap_bintree_REWRITE] THEN
ASM_SIMP_TAC std_ss [IN_ABS, asl_bool_EVAL, smallfoot_ap_equal_def,
		     smallfoot_ap_weak_unequal_def,
		     smallfoot_ap_binexpression_def,
		     smallfoot_a_stack_proposition_def, LET_THM] THEN
REPEAT STRIP_TAC THEN
ASM_REWRITE_TAC[]);







val smallfoot_ap_bag_implies_in_heap_or_null___ae_null = store_thm (
 "smallfoot_ap_bag_implies_in_heap_or_null___ae_null",

``!sfb.  smallfoot_ap_bag_implies_in_heap_or_null sfb smallfoot_ae_null``,

SIMP_TAC std_ss [smallfoot_ap_bag_implies_in_heap_or_null_def,
		 smallfoot_ae_null_def,
		 smallfoot_ae_const_def, IN_INSERT]);








val smallfoot_ap_bag_implies_unequal_def = Define `
  smallfoot_ap_bag_implies_unequal sfb e1 e2 =
  (BAG_EVERY SMALLFOOT_AP_PERMISSION_UNIMPORTANT sfb ==>
  (!s. s IN (smallfoot_ap_bigstar (BAG_INSERT smallfoot_ap_stack_true sfb)) ==>
       s IN smallfoot_ap_weak_unequal e1 e2))`;




val smallfoot_prop___bag_implies___UNEQUAL_INTRO =
store_thm ("smallfoot_prop___bag_implies___UNEQUAL_INTRO",
``!e1 e2 wpb rpb sfb.

 (smallfoot_ap_bag_implies_unequal sfb e1 e2) ==>
 ((SMALLFOOT_AE_USED_VARS_SUBSET
         (SET_OF_BAG (BAG_UNION wpb rpb)) e1 /\
  SMALLFOOT_AE_USED_VARS_SUBSET
         (SET_OF_BAG (BAG_UNION wpb rpb)) e2) ==>

  (smallfoot_prop (wpb,rpb) sfb =
   smallfoot_prop (wpb,rpb) (BAG_INSERT (smallfoot_ap_unequal e1 e2) sfb)))``,


SIMP_TAC std_ss [smallfoot_prop___REWRITE,
		 smallfoot_prop___COND_INSERT,
		 SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___compare] THEN
REPEAT STRIP_TAC THEN
Cases_on `smallfoot_prop___COND (wpb,rpb) sfb` THEN ASM_REWRITE_TAC[] THEN

ASM_SIMP_TAC std_ss [smallfoot_prop___PROP_INSERT,
		     smallfoot_prop___COND_INSERT,
		     SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___compare] THEN
SIMP_TAC std_ss [smallfoot_ap_unequal_def, smallfoot_ap_binexpression_def,
		 smallfoot_a_stack_proposition_def, LET_THM,
		 IN_ABS, FUNION_FEMPTY_1, DISJOINT_EMPTY, FDOM_FEMPTY] THEN
ONCE_REWRITE_TAC[EXTENSION] THEN
SIMP_TAC (std_ss++bool_eq_imp_ss) [IN_ABS] THEN
GEN_TAC THEN STRIP_TAC THEN
Tactical.REVERSE (`x IN smallfoot_ap_weak_unequal e1 e2` by ALL_TAC) THEN1 (
   POP_ASSUM MP_TAC THEN
   SIMP_TAC std_ss [smallfoot_ap_weak_unequal_def,
		    smallfoot_ap_binexpression_def,
		    smallfoot_a_stack_proposition_def,
		    LET_THM, IN_ABS]
) THEN

Q.PAT_ASSUM `smallfoot_ap_bag_implies_unequal sfb e1 e2` MP_TAC THEN
FULL_SIMP_TAC std_ss [smallfoot_ap_bag_implies_unequal_def, smallfoot_prop___PROP___REWRITE,
		      IN_ABS, smallfoot_ap_bigstar_REWRITE, BAG_EVERY_def,
		      smallfoot_prop___COND___REWRITE,
		      SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS_def]);




val smallfoot_ap_bag_implies_unequal___points_to =
store_thm ("smallfoot_ap_bag_implies_unequal___points_to",
``!e1 e2 sfb L.
  smallfoot_ap_bag_implies_in_heap_or_null sfb e2 ==>
  smallfoot_ap_bag_implies_unequal (BAG_INSERT (smallfoot_ap_points_to e1 L) sfb) e1 e2``,

SIMP_TAC std_ss [smallfoot_ap_bag_implies_unequal_def,
		 BAG_EVERY_THM, smallfoot_ap_bigstar_REWRITE,
		 smallfoot_ap_star___swap_ap_stack_true] THEN
REPEAT GEN_TAC THEN STRIP_TAC THEN STRIP_TAC THEN
Q.ABBREV_TAC `P = smallfoot_ap_star smallfoot_ap_stack_true
                     (smallfoot_ap_bigstar sfb)` THEN
`SMALLFOOT_AP_PERMISSION_UNIMPORTANT P` by ALL_TAC THEN1 (
   Q.UNABBREV_TAC `P` THEN
   REWRITE_TAC[GSYM smallfoot_ap_bigstar_REWRITE] THEN
   MATCH_MP_TAC SMALLFOOT_AP_PERMISSION_UNIMPORTANT___bigstar THEN
   FULL_SIMP_TAC std_ss [bagTheory.BAG_IN_BAG_INSERT,
			 DISJ_IMP_THM, FORALL_AND_THM,
			 SMALLFOOT_AP_PERMISSION_UNIMPORTANT___smallfoot_ap_stack_true,
			 BAG_EVERY_def, bagTheory.BAG_INSERT_NOT_EMPTY]
) THEN
ASM_SIMP_TAC std_ss [smallfoot_ap_star___PERMISSION_UNIMPORTANT, IN_ABS] THEN
REPEAT STRIP_TAC THEN
FULL_SIMP_TAC std_ss [smallfoot_ap_bag_implies_in_heap_or_null_def,
		      smallfoot_ap_bigstar_REWRITE] THEN
RES_TAC THEN
FULL_SIMP_TAC std_ss [smallfoot_ap_points_to_def, IN_ABS,
		      smallfoot_ap_weak_unequal_def,
		      smallfoot_ap_binexpression_def,
		      smallfoot_a_stack_proposition_def,
		      LET_THM, DISJOINT_DEF, EXTENSION, NOT_IN_EMPTY,
		      IN_INTER, IN_SING] THEN
FULL_SIMP_TAC std_ss [IN_INSERT] THEN
METIS_TAC[]);





val smallfoot_ap_bag_implies_unequal___tree_seg_num =
store_thm ("smallfoot_ap_bag_implies_unequal___tree_seg_num",
``!e1 e2 e3 sfb n bal tagL.
  smallfoot_ap_bag_implies_in_heap_or_null (BAG_INSERT (smallfoot_ap_unequal e1 e2) sfb) e3 ==>
  (IS_SOME___SMALLFOOT_AE_USED_VARS e1 ==>
  smallfoot_ap_bag_implies_unequal (BAG_INSERT (smallfoot_ap_tree_seg_num n bal tagL e1 e2)
                                   (BAG_INSERT (smallfoot_ap_unequal e1 e2) sfb)) e1 e3)``,

SIMP_TAC std_ss [smallfoot_ap_bag_implies_unequal_def,
		 BAG_EVERY_THM, smallfoot_ap_bigstar_REWRITE,
		 smallfoot_ap_star___swap_ap_stack_true] THEN
REPEAT GEN_TAC THEN STRIP_TAC THEN STRIP_TAC THEN STRIP_TAC THEN
Q.ABBREV_TAC `P1 =  smallfoot_ap_star smallfoot_ap_stack_true
                (smallfoot_ap_bigstar sfb)` THEN
Q.ABBREV_TAC `P =  smallfoot_ap_star (smallfoot_ap_unequal e1 e2) P1` THEN
`SMALLFOOT_AP_PERMISSION_UNIMPORTANT P1` by ALL_TAC THEN1 (
   Q.UNABBREV_TAC `P1` THEN
   REWRITE_TAC[GSYM smallfoot_ap_bigstar_REWRITE] THEN
   MATCH_MP_TAC SMALLFOOT_AP_PERMISSION_UNIMPORTANT___bigstar THEN
   FULL_SIMP_TAC std_ss [bagTheory.BAG_IN_BAG_INSERT,
			 DISJ_IMP_THM, FORALL_AND_THM,
			 SMALLFOOT_AP_PERMISSION_UNIMPORTANT___smallfoot_ap_stack_true,
			 BAG_EVERY_def, bagTheory.BAG_INSERT_NOT_EMPTY]
) THEN
`SMALLFOOT_AP_PERMISSION_UNIMPORTANT P` by ALL_TAC THEN1 (
   Q.UNABBREV_TAC `P` THEN
   MATCH_MP_TAC SMALLFOOT_AP_PERMISSION_UNIMPORTANT___star THEN
   ASM_REWRITE_TAC[]
) THEN

ASM_SIMP_TAC std_ss [smallfoot_ap_star___PERMISSION_UNIMPORTANT, IN_ABS] THEN
REPEAT STRIP_TAC THEN
`s IN smallfoot_ap_weak_unequal e1 e2` by ALL_TAC THEN1 (
   Q.PAT_ASSUM `X IN P` MP_TAC THEN
   Q.UNABBREV_TAC `P` THEN
   ASM_SIMP_TAC std_ss [smallfoot_ap_star___PERMISSION_UNIMPORTANT,
		        IN_ABS, smallfoot_ap_weak_unequal_def,
		        smallfoot_ap_binexpression_def,
		        smallfoot_a_stack_proposition_def,
		        LET_THM, smallfoot_ap_unequal_def,
		        FUNION_FEMPTY_1]
) THEN
`?c. (e3 (FST s) = SOME c) /\ c IN 0 INSERT FDOM h2` by ALL_TAC THEN1 (
   Q.PAT_ASSUM `smallfoot_ap_bag_implies_in_heap_or_null X e3` MP_TAC THEN
   ASM_SIMP_TAC std_ss [smallfoot_ap_bag_implies_in_heap_or_null_def,
		        BAG_EVERY_THM, smallfoot_ap_bigstar_REWRITE,
		        smallfoot_ap_star___swap_ap_stack_true,
		        GSYM LEFT_EXISTS_IMP_THM] THEN
   Q.EXISTS_TAC `(FST s, h2)` THEN
   ASM_REWRITE_TAC[]
) THEN


Q.PAT_ASSUM `X IN smallfoot_ap_tree_seg_num n bal tagL e1 e2` MP_TAC THEN
ONCE_REWRITE_TAC[smallfoot_ap_tree_seg_num_REWRITE] THEN
FULL_SIMP_TAC std_ss [smallfoot_ap_equal_def,
		      smallfoot_ap_weak_unequal_def,
		      COND_RAND, COND_RATOR,
		      smallfoot_ap_binexpression_def,
		      smallfoot_a_stack_proposition_def,
		      LET_THM, IN_ABS, asl_bool_EVAL] THEN
SIMP_TAC std_ss [smallfoot_ap_star_def, asl_star_def,
		 smallfoot_ap_points_to_def, IN_ABS, LET_THM,
		 PAIR_EXISTS_THM] THEN
REPEAT STRIP_TAC THEN
`e1 (FST s) = SOME c` by ALL_TAC THEN1 (
   Cases_on `e1 (FST s)` THEN
   FULL_SIMP_TAC std_ss []
) THEN
`e1 x1 = SOME c` by ALL_TAC THEN1 (
   POP_ASSUM (ASSUME_TAC o GSYM) THEN
   ASM_REWRITE_TAC[] THEN
   Q.PAT_ASSUM `IS_SOME___SMALLFOOT_AE_USED_VARS e1` MP_TAC THEN
   SIMP_TAC std_ss [IS_SOME___SMALLFOOT_AE_USED_VARS___REWRITE,
		    SMALLFOOT_AE_USED_VARS_REL___REWRITE] THEN
   STRIP_TAC THEN
   POP_ASSUM MATCH_MP_TAC THEN
   FULL_SIMP_TAC std_ss [SOME___smallfoot_separation_combinator,
			 SOME___VAR_RES_STACK_COMBINE,
			 FMERGE_DEF,
			 VAR_RES_STACK_COMBINE___MERGE_FUNC_def,
			 COND_REWRITES,
			 VAR_RES_STACK_IS_SEPARATE_def, SUBSET_DEF]
) THEN
FULL_SIMP_TAC std_ss [IN_INSERT, SOME___smallfoot_separation_combinator] THEN
Q.PAT_ASSUM `DISJOINT X (FDOM h2)` MP_TAC THEN
ASM_SIMP_TAC std_ss [FDOM_FUNION, EXTENSION, DISJOINT_DEF,
		     IN_UNION, IN_INTER, NOT_IN_EMPTY, IN_SING] THEN
Q.EXISTS_TAC `c` THEN
ASM_SIMP_TAC std_ss []);





val smallfoot_ap_bag_implies_unequal___tree_seg =
store_thm ("smallfoot_ap_bag_implies_unequal___tree_seg",
``!e1 e2 e3 sfb bal tagL.
  smallfoot_ap_bag_implies_in_heap_or_null (BAG_INSERT (smallfoot_ap_unequal e1 e2) sfb) e3 ==>
  ((IS_SOME___SMALLFOOT_AE_USED_VARS e1 /\
   IS_SOME___SMALLFOOT_AE_USED_VARS e2) ==> 
  smallfoot_ap_bag_implies_unequal (BAG_INSERT (smallfoot_ap_tree_seg bal tagL e1 e2)
                                   (BAG_INSERT (smallfoot_ap_unequal e1 e2) sfb)) e1 e3)``,

REPEAT STRIP_TAC THEN
`!n. smallfoot_ap_bag_implies_unequal
              (BAG_INSERT (smallfoot_ap_tree_seg_num n bal tagL e1 e2)
                 (BAG_INSERT (smallfoot_ap_unequal e1 e2) sfb)) e1 e3` by
   PROVE_TAC[smallfoot_ap_bag_implies_unequal___tree_seg_num] THEN
POP_ASSUM MP_TAC THEN
ASM_SIMP_TAC std_ss [smallfoot_ap_bag_implies_unequal_def,
		      smallfoot_ap_bigstar_REWRITE, BAG_EVERY_THM,
		      SMALLFOOT_AP_PERMISSION_UNIMPORTANT___compare,
		      SMALLFOOT_AP_PERMISSION_UNIMPORTANT___smallfoot_ap_tree_seg_num,
		     SMALLFOOT_AP_PERMISSION_UNIMPORTANT___smallfoot_ap_tree_seg] THEN
SIMP_TAC std_ss [smallfoot_ap_tree_seg_def, GSYM asl_exists___smallfoot_ap_star_THM,
		 asl_bool_EVAL, IN_ABS]);






val smallfoot_ap_bag_implies_unequal___data_list_seg =
store_thm ("smallfoot_ap_bag_implies_unequal___data_list_seg",
``!e1 e2 e3 data sfb tl.
  smallfoot_ap_bag_implies_in_heap_or_null (BAG_INSERT (smallfoot_ap_unequal e1 e2) sfb) e3 ==>

  ((IS_SOME___SMALLFOOT_AE_USED_VARS e1 /\
   IS_SOME___SMALLFOOT_AE_USED_VARS e2) ==>
  smallfoot_ap_bag_implies_unequal (BAG_INSERT (smallfoot_ap_data_list_seg tl e1 data e2)
                                   (BAG_INSERT (smallfoot_ap_unequal e1 e2) sfb)) e1 e3)``,

REPEAT STRIP_TAC THEN
SIMP_TAC std_ss [smallfoot_ap_bag_implies_unequal_def,
		 smallfoot_ap_bigstar_REWRITE,
		 BAG_EVERY_THM] THEN

Q.ABBREV_TAC `P = smallfoot_ap_star smallfoot_ap_stack_true
                   (smallfoot_ap_bigstar sfb)` THEN
`smallfoot_ap_star smallfoot_ap_stack_true
        (smallfoot_ap_star (smallfoot_ap_data_list_seg tl e1 data e2)
           (smallfoot_ap_star (smallfoot_ap_unequal e1 e2)
              (smallfoot_ap_bigstar sfb))) =
 smallfoot_ap_star P (smallfoot_ap_star (smallfoot_ap_unequal e1 e2)
                      (smallfoot_ap_data_list_seg tl e1 data e2))` by ALL_TAC THEN1 (
   METIS_TAC[smallfoot_ap_star___PROPERTIES, ASSOC_DEF, COMM_DEF]
) THEN
ASM_REWRITE_TAC[] THEN POP_ASSUM (K ALL_TAC) THEN
ASM_SIMP_TAC std_ss [smallfoot_ap_star___data_list_seg_unroll] THEN
Tactical.REVERSE (Cases_on `FEVERY (\x. ~(SND x = [])) data`) THEN (
   ASM_SIMP_TAC std_ss [asl_bool_REWRITES] THEN
   ASM_SIMP_TAC std_ss [GSYM smallfoot_ap_false_def,
		        smallfoot_ap_false___smallfoot_ap_star_THM,
		        smallfoot_ap_false___NOT_IN,
                        GSYM asl_exists___smallfoot_ap_star_THM,
		        asl_bool_EVAL]
) THEN
STRIP_TAC THEN
`SMALLFOOT_AP_PERMISSION_UNIMPORTANT P /\
 !n. SMALLFOOT_AP_PERMISSION_UNIMPORTANT (smallfoot_ap_points_to e1
                    (FMAP_MAP (\dl. smallfoot_ae_const (HD dl)) data |+
                     (tl,smallfoot_ae_const n)))` by ALL_TAC THEN1 (
   Q.UNABBREV_TAC `P` THEN
   SIMP_TAC std_ss [GSYM smallfoot_ap_bigstar_REWRITE] THEN
   CONSEQ_REWRITE_TAC ([], [SMALLFOOT_AP_PERMISSION_UNIMPORTANT___bigstar,
		      SMALLFOOT_AP_PERMISSION_UNIMPORTANT___points_to,
		      FEVERY_STRENGTHEN_THM],[]) THEN
   FULL_SIMP_TAC std_ss [FEVERY_DEF, FMAP_MAP_THM,
      IS_SOME___SMALLFOOT_AE_USED_VARS___EVAL, bagTheory.BAG_INSERT_NOT_EMPTY,
      bagTheory.BAG_IN_BAG_INSERT, DISJ_IMP_THM, FORALL_AND_THM,
      SMALLFOOT_AP_PERMISSION_UNIMPORTANT___smallfoot_ap_stack_true,
      BAG_EVERY_def]
) THEN
Q.ABBREV_TAC `P2 = smallfoot_ap_bigstar
         (BAG_INSERT smallfoot_ap_stack_true
            (BAG_INSERT (smallfoot_ap_unequal e1 e2) sfb))` THEN
`!X. smallfoot_ap_star P (smallfoot_ap_star (smallfoot_ap_unequal e1 e2) X) =
 smallfoot_ap_star P2 X` by ALL_TAC THEN1 (
   Q.UNABBREV_TAC `P` THEN
   Q.UNABBREV_TAC `P2` THEN 
   SIMP_TAC std_ss [smallfoot_ap_bigstar_REWRITE] THEN
   METIS_TAC[smallfoot_ap_star___PROPERTIES, ASSOC_DEF, COMM_DEF]
) THEN
ASM_REWRITE_TAC[] THEN POP_ASSUM (K ALL_TAC) THEN
`SMALLFOOT_AP_PERMISSION_UNIMPORTANT P2` by ALL_TAC THEN1 (
   Q.UNABBREV_TAC `P2` THEN
   MATCH_MP_TAC SMALLFOOT_AP_PERMISSION_UNIMPORTANT___bigstar THEN
   ASM_SIMP_TAC std_ss [bagTheory.BAG_INSERT_NOT_EMPTY,
		        bagTheory.BAG_IN_BAG_INSERT, IN_INSERT,
		        DISJ_IMP_THM, FORALL_AND_THM,
		        SMALLFOOT_AP_PERMISSION_UNIMPORTANT___smallfoot_ap_stack_true] THEN
   FULL_SIMP_TAC std_ss [BAG_EVERY_def]
) THEN
ASM_SIMP_TAC std_ss [smallfoot_ap_star___PERMISSION_UNIMPORTANT,
		     SMALLFOOT_AP_PERMISSION_UNIMPORTANT___star,
     		     SMALLFOOT_AP_PERMISSION_UNIMPORTANT___data_list_seg,
		     IS_SOME___SMALLFOOT_AE_USED_VARS___EVAL] THEN
SIMP_TAC (std_ss++boolSimps.CONJ_ss) [IN_ABS, GSYM RIGHT_EXISTS_AND_THM,
		 smallfoot_ap_points_to_def, LET_THM,
                 IS_SOME_EXISTS, GSYM LEFT_EXISTS_AND_THM,
		 GSYM LEFT_FORALL_IMP_THM, FDOM_FUNION, IN_INSERT,
                 IN_UNION, smallfoot_ap_weak_unequal_def,
	         smallfoot_ap_binexpression_def,
                 smallfoot_a_stack_proposition_def] THEN
REPEAT STRIP_TAC THEN
Q.PAT_ASSUM `smallfoot_ap_bag_implies_in_heap_or_null_def X e3` MP_TAC THEN

ASM_SIMP_TAC std_ss [smallfoot_ap_bag_implies_in_heap_or_null_def,
  BAG_EVERY_THM, GSYM LEFT_EXISTS_IMP_THM] THEN
Q.EXISTS_TAC `(FST (s:smallfoot_state), h1)` THEN
ASM_SIMP_TAC std_ss [GSYM LEFT_FORALL_IMP_THM, IN_INSERT] THEN
FULL_SIMP_TAC std_ss [DISJOINT_DEF, EXTENSION, NOT_IN_EMPTY,
   IN_INTER, IN_UNION, IN_SING] THEN
METIS_TAC[]);




val smallfoot_ap_bag_implies_unequal___data_list =
store_thm ("smallfoot_ap_bag_implies_unequal___data_list",
``!e1 data e3 sfb tl.
  smallfoot_ap_bag_implies_in_heap_or_null (BAG_INSERT (smallfoot_ap_unequal e1 smallfoot_ae_null) sfb) e3 ==>

  (IS_SOME___SMALLFOOT_AE_USED_VARS e1 ==>
  smallfoot_ap_bag_implies_unequal (BAG_INSERT (smallfoot_ap_data_list tl e1 data)
                                   (BAG_INSERT (smallfoot_ap_unequal e1 smallfoot_ae_null) sfb)) e1 e3)``,

SIMP_TAC std_ss [smallfoot_ap_data_list_def,
		 smallfoot_ap_bag_implies_unequal___data_list_seg,
	         IS_SOME___SMALLFOOT_AE_USED_VARS___EVAL]);



val smallfoot_ap_bag_implies_unequal___bintree =
store_thm ("smallfoot_ap_bag_implies_unequal___bintree",
``!e1 e3 sfb lt rt.
  smallfoot_ap_bag_implies_in_heap_or_null (BAG_INSERT (smallfoot_ap_unequal e1 smallfoot_ae_null) sfb) e3 ==>
  (IS_SOME___SMALLFOOT_AE_USED_VARS e1 ==>
  smallfoot_ap_bag_implies_unequal (BAG_INSERT (smallfoot_ap_bintree (lt,rt) e1)
                                   (BAG_INSERT (smallfoot_ap_unequal e1 smallfoot_ae_null) sfb)) e1 e3)``,

SIMP_TAC std_ss [smallfoot_ap_bintree_def,
		 smallfoot_ap_bintree_num_def,
		 GSYM smallfoot_ap_tree_seg_def,
		 smallfoot_ap_bag_implies_unequal___tree_seg,
	         IS_SOME___SMALLFOOT_AE_USED_VARS___EVAL]);







(*the first argument is ignored by this definition. It's used as an indicator to 
  conversions. If strong_rest is true the conversions try to make the deduced frame as strong as possible.
  to this end equations and disequations are put into it. Otherwise,
  they are left out.*)

val SMALLFOOT_PROP_IMPLIES_def = Define `
SMALLFOOT_PROP_IMPLIES (strong_rest:bool) (wpb,rpb) wpb' sfb_context sfb_split sfb_imp sfb_restP =

~(sfb_restP = EMPTY) ==>
?sfb_rest. sfb_restP sfb_rest /\
((smallfoot_prop___COND (wpb,rpb) (BAG_UNION sfb_context (BAG_UNION sfb_split sfb_imp))) ==>

(!s. smallfoot_prop___PROP (wpb,rpb) (BAG_UNION sfb_split sfb_context) s ==>
(smallfoot_prop___COND (BAG_DIFF wpb wpb',BAG_DIFF rpb wpb') sfb_rest /\
smallfoot_prop___PROP (wpb,rpb) (BAG_UNION sfb_imp (BAG_UNION sfb_rest sfb_context)) s)))`




val SMALLFOOT_PROP_IMPLIES_EXPAND = store_thm ("SMALLFOOT_PROP_IMPLIES_EXPAND",
``
!strong_rest wpb rpb wpb' sfb_context sfb_split sfb_imp sfb_restP.

SMALLFOOT_PROP_IMPLIES strong_rest (wpb,rpb) wpb' sfb_context sfb_split sfb_imp sfb_restP =

~(sfb_restP = EMPTY) ==>
(?sfb_rest. sfb_restP sfb_rest /\ 
(smallfoot_prop___COND (wpb,rpb) (BAG_UNION sfb_context (BAG_UNION sfb_split sfb_imp)) ==>

(!s. smallfoot_prop___PROP (wpb,rpb) (BAG_UNION sfb_split sfb_context) s ==>

smallfoot_prop___COND (BAG_DIFF wpb wpb',BAG_DIFF rpb wpb') sfb_rest /\
 smallfoot_prop___COND (wpb,rpb) sfb_rest /\
smallfoot_prop___PROP (wpb,rpb) (BAG_UNION sfb_imp (BAG_UNION sfb_rest sfb_context)) s)))``,


SIMP_TAC (std_ss++bool_eq_imp_ss) [SMALLFOOT_PROP_IMPLIES_def] THEN
REPEAT STRIP_TAC THEN
HO_MATCH_MP_TAC (prove (``(!s. (X s = Y s)) ==> ((?s. X s) = (?s. Y s))``,
		     METIS_TAC[])) THEN
SIMP_TAC (std_ss++bool_eq_imp_ss) [] THEN
REPEAT STRIP_TAC THEN
HO_MATCH_MP_TAC (prove (``(!s. (X s = Y s)) ==> ((!s. X s) = (!s. Y s))``,
		     METIS_TAC[])) THEN
FULL_SIMP_TAC (std_ss++bool_eq_imp_ss) [smallfoot_prop___COND___REWRITE] THEN
REPEAT STRIP_TAC THEN
MATCH_MP_TAC SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___SUBSET THEN
Q.EXISTS_TAC `(SET_OF_BAG
                  (BAG_UNION (BAG_DIFF wpb wpb') (BAG_DIFF rpb wpb')))` THEN
ASM_SIMP_TAC std_ss [SUBSET_DEF, bagTheory.BAG_IN_BAG_UNION,
		     bagTheory.IN_SET_OF_BAG, DISJ_IMP_THM,
		     BAG_IN___BAG_DIFF___ALL_DISTINCT]);







val SMALLFOOT_COND_HOARE_TRIPLE___SOLVE = store_thm ("SMALLFOOT_COND_HOARE_TRIPLE___SOLVE",
``!wpb rpb sfb wpb' rpb' sfb'.

  ((SET_OF_BAG wpb' SUBSET SET_OF_BAG wpb) /\
   (SET_OF_BAG rpb' SUBSET SET_OF_BAG (BAG_UNION wpb rpb))) ==>

((SMALLFOOT_PROP_IMPLIES F (wpb,rpb) EMPTY_BAG EMPTY_BAG sfb sfb' 
  (BAG_EVERY SMALLFOOT_IS_STRONG_STACK_PROPOSITION))
 ==>


  SMALLFOOT_COND_HOARE_TRIPLE 
    (smallfoot_prop (wpb,rpb) sfb)
    (smallfoot_prog_block [])
    (smallfoot_prop (wpb',rpb') sfb'))``,

SIMP_TAC std_ss [SMALLFOOT_COND_HOARE_TRIPLE_def,
		 smallfoot_prop___REWRITE,
                 smallfoot_prog_block_def,
		 fasl_prog_block_def,
		 SMALLFOOT_HOARE_TRIPLE_def,
		 FASL_PROGRAM_HOARE_TRIPLE_def,
		 HOARE_TRIPLE_def, IN_ABS,
		 FASL_PROGRAM_SEM___skip,
		 fasla_skip_def,
		 fasl_order_THM,
		 BAG_EVERY_def,
		 SUBSET_DEF, IN_SING,
		 bagTheory.IN_SET_OF_BAG,
		 VAR_RES_STACK___IS_EQUAL_UPTO_VALUES_def,
		 smallfoot_prop___PROP___REWRITE] THEN
REPEAT STRIP_TAC THEN1 (
   Cases_on `BAG_IN v rpb` THEN1 ASM_SIMP_TAC std_ss [] THEN
   `BAG_IN v wpb` by ALL_TAC THEN1 (
      RES_TAC THEN
      FULL_SIMP_TAC std_ss [bagTheory.BAG_IN_BAG_UNION] THEN
      FULL_SIMP_TAC std_ss []
   ) THEN
   RES_TAC THEN
   FULL_SIMP_TAC std_ss [var_res_sl___has_write_permission_def,
			 var_res_sl___has_read_permission_def]
) THEN

Q.PAT_ASSUM `SMALLFOOT_PROP_IMPLIES F X Y Z sfb sfb' D` MP_TAC THEN
SIMP_TAC std_ss [SMALLFOOT_PROP_IMPLIES_def, bagTheory.BAG_UNION_EMPTY,
		 bagTheory.BAG_DIFF_EMPTY] THEN
`~(BAG_EVERY SMALLFOOT_IS_STRONG_STACK_PROPOSITION = {})` by ALL_TAC THEN1 (
  ONCE_REWRITE_TAC[FUN_EQ_THM] THEN
  SIMP_TAC std_ss [EMPTY_DEF] THEN
  Q.EXISTS_TAC `EMPTY_BAG` THEN
  REWRITE_TAC[BAG_EVERY_THM]
) THEN 

`smallfoot_prop___COND (wpb,rpb) sfb'` by ALL_TAC THEN1 (
   FULL_SIMP_TAC std_ss [smallfoot_prop___COND___REWRITE] THEN
   REPEAT STRIP_TAC THEN
   MATCH_MP_TAC SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___SUBSET THEN
   Q.EXISTS_TAC `SET_OF_BAG (BAG_UNION wpb' rpb')` THEN
   ASM_SIMP_TAC std_ss [] THEN
   FULL_SIMP_TAC std_ss [SUBSET_DEF, bagTheory.BAG_IN_BAG_UNION,
			 bagTheory.IN_SET_OF_BAG, DISJ_IMP_THM]
) THEN
ASM_SIMP_TAC (std_ss++boolSimps.CONJ_ss) [smallfoot_prop___COND_UNION, GSYM LEFT_EXISTS_IMP_THM,
		     smallfoot_prop___PROP_UNION] THEN
REPEAT STRIP_TAC THEN
Q.PAT_ASSUM `!s. X s` (MP_TAC o Q.SPEC `x`) THEN
ASM_SIMP_TAC std_ss [smallfoot_prop___PROP___REWRITE, IN_ABS] THEN
REPEAT STRIP_TAC THEN
Tactical.REVERSE (`h2 = FEMPTY` by ALL_TAC) THEN1 (
   Cases_on `x` THEN
   FULL_SIMP_TAC std_ss [FUNION_FEMPTY_2]
) THEN


Q.PAT_ASSUM `(FST x, h2) IN X` MP_TAC THEN
Q.PAT_ASSUM `BAG_EVERY P sfb_rest` MP_TAC THEN
`FINITE_BAG sfb_rest` by FULL_SIMP_TAC std_ss [smallfoot_prop___COND___REWRITE] THEN
Q.PAT_ASSUM `smallfoot_prop___COND X sfb_rest` MP_TAC THEN
POP_ASSUM MP_TAC THEN
Q.SPEC_TAC (`sfb_rest`, `sfb`) THEN
REPEAT (POP_ASSUM (K ALL_TAC)) THEN
HO_MATCH_MP_TAC bagTheory.FINITE_BAG_INDUCT THEN


SIMP_TAC std_ss [bagTheory.NOT_IN_EMPTY_BAG,
		 BAG_EVERY_def,
		 smallfoot_ap_bigstar_REWRITE,
		 smallfoot_ap_star___swap_ap_stack_true,
		 smallfoot_ap_star___PROPERTIES,
		 bagTheory.BAG_IN_BAG_INSERT,
		 DISJ_IMP_THM, FORALL_AND_THM] THEN
CONJ_TAC THEN1 SIMP_TAC std_ss [smallfoot_ap_stack_true_def, IN_ABS] THEN

REPEAT STRIP_TAC THEN
Q.ABBREV_TAC `P = (smallfoot_ap_bigstar (BAG_INSERT smallfoot_ap_stack_true sfb))` THEN
FULL_SIMP_TAC std_ss [GSYM smallfoot_ap_bigstar_REWRITE,
		      smallfoot_prop___COND_INSERT] THEN

`SMALLFOOT_AP_PERMISSION_UNIMPORTANT e` 
   by FULL_SIMP_TAC std_ss [SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS_def] THEN

`SMALLFOOT_AP_PERMISSION_UNIMPORTANT P` by ALL_TAC THEN1 (
  Q.UNABBREV_TAC `P` THEN
  FULL_SIMP_TAC std_ss [smallfoot_prop___COND___EXPAND,
                        SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS_def,
			smallfoot_ap_bigstar_REWRITE]
) THEN
FULL_SIMP_TAC std_ss [smallfoot_ap_star___PERMISSION_UNIMPORTANT,
		      IN_ABS, SMALLFOOT_IS_STRONG_STACK_PROPOSITION_def] THEN
RES_TAC THEN
FULL_SIMP_TAC std_ss [FUNION_FEMPTY_1, FUNION_FEMPTY_2]);





val smallfoot_ae_is_list_cond_defined___STRONG_EXISTS =
store_thm ("smallfoot_ae_is_list_cond_defined___STRONG_EXISTS",
``
smallfoot_ae_is_list_cond_defined (COND_PROP___STRONG_EXISTS (\x. P x)) L =
(COND_PROP___STRONG_EXISTS (\x. smallfoot_ae_is_list_cond_defined (P x) L))``,

SIMP_TAC std_ss [COND_PROP___STRONG_EXISTS_def,
		 smallfoot_ae_is_list_cond_defined_def,
		 EXISTS_OR_THM, asl_exists_def, IN_ABS, LEFT_EXISTS_AND_THM]);


val SMALLFOOT_COND_PROP___STRONG_EQUIV___smallfoot_ae_is_list_cond_defined =
store_thm ("SMALLFOOT_COND_PROP___STRONG_EQUIV___smallfoot_ae_is_list_cond_defined",
``!P P' L.
  SMALLFOOT_COND_PROP___STRONG_EQUIV P P' ==>
  SMALLFOOT_COND_PROP___STRONG_EQUIV 
     (smallfoot_ae_is_list_cond_defined P  L)
     (smallfoot_ae_is_list_cond_defined P' L)``,

SIMP_TAC std_ss [SMALLFOOT_COND_PROP___STRONG_EQUIV_REWRITE,
		 smallfoot_ae_is_list_cond_defined_def]);





(*
val SMALLFOOT_COND_CHOICE_IS_INDEPENDEND_FROM_SUBSTATE___smallfoot_ae_is_list_cond =
store_thm ("SMALLFOOT_COND_CHOICE_IS_INDEPENDEND_FROM_SUBSTATE___smallfoot_ae_is_list_cond",
``
SMALLFOOT_COND_CHOICE_IS_INDEPENDEND_FROM_SUBSTATE (\x y. P x y) ==>
SMALLFOOT_COND_CHOICE_IS_INDEPENDEND_FROM_SUBSTATE (\x y. (smallfoot_ae_is_list_cond_defined (P x y) L))``,

SIMP_TAC std_ss [SMALLFOOT_COND_CHOICE_IS_INDEPENDEND_FROM_SUBSTATE_def,
		 smallfoot_ae_is_list_cond_defined_def,
		 SMALLFOOT_CHOICE_IS_INDEPENDEND_FROM_SUBSTATE_def,
		 EXISTS_OR_THM, asl_exists_def, IN_ABS, LEFT_EXISTS_AND_THM] THEN
METIS_TAC[]);
*)



val SMALLFOOT_COND_AP_PERMISSION_UNIMPORTANT_def = Define `
SMALLFOOT_COND_AP_PERMISSION_UNIMPORTANT P =
(FST P) ==> SMALLFOOT_AP_PERMISSION_UNIMPORTANT (SND P)`


(*

val SMALLFOOT_COND_INFERENCE___smallfoot_cond_best_local_action___ae_defined_elim = store_thm ("SMALLFOOT_COND_INFERENCE___smallfoot_cond_best_local_action___ae_defined_elim",
``!wpb rpb sfb pre post prog expL.

  (EVERY (SMALLFOOT_AE_USED_VARS_SUBSET (SET_OF_BAG (BAG_UNION wpb rpb))) expL /\
   SMALLFOOT_COND_AP_PERMISSION_UNIMPORTANT pre /\
   SMALLFOOT_COND_AP_PERMISSION_UNIMPORTANT post) ==>

((SMALLFOOT_COND_HOARE_TRIPLE 
    (smallfoot_prop (wpb,rpb) sfb)
    (fasl_prog_seq 
        (smallfoot_cond_best_local_action pre post)
        prog)
    Q)

 ==>

 (SMALLFOOT_COND_HOARE_TRIPLE 
    (smallfoot_prop (wpb,rpb) sfb)
    (fasl_prog_seq 
        (smallfoot_cond_best_local_action 
            (smallfoot_ae_is_list_cond_defined pre expL)
            post)
        prog)
    Q))``,


REPEAT GEN_TAC THEN
`?Q_ap Q_cond. Q = (Q_cond, Q_ap)` by (Cases_on `Q` THEN SIMP_TAC std_ss []) THEN
ASM_SIMP_TAC std_ss [SMALLFOOT_COND_HOARE_TRIPLE_def,
		 smallfoot_prop___REWRITE, smallfoot_cond_best_local_action_def,
                 smallfoot_ae_is_list_cond_defined_def,
		 SUBSET_DEF, bagTheory.IN_SET_OF_BAG] THEN
SIMP_TAC std_ss [SMALLFOOT_HOARE_TRIPLE_def,
                 FASL_PROGRAM_HOARE_TRIPLE_def,
		 FASL_PROGRAM_SEM___prog_seq,
		 HOARE_TRIPLE_def, IN_ABS,
		 fasl_order_THM] THEN
Cases_on `~FST pre \/ ~FST post` THEN (
   FULL_SIMP_TAC std_ss []
) THEN
Q.ABBREV_TAC `prog_sem = 
                FASL_PROGRAM_SEM (smallfoot_env,K smallfoot_ap_true) FEMPTY prog` THEN
REPEAT STRIP_TAC THEN
FULL_SIMP_TAC std_ss [] THEN
Q.PAT_ASSUM `!x. X x` (MP_TAC o Q.SPEC `x`) THEN
ASM_REWRITE_TAC[] THEN
Q.ABBREV_TAC `Q' = (\s.
          s IN Q_ap /\
          VAR_RES_STACK___IS_EQUAL_UPTO_VALUES (FST x) (FST s))` THEN
SIMP_TAC std_ss [SOME___fasla_seq, GSYM LEFT_EXISTS_AND_THM,
		 GSYM RIGHT_EXISTS_AND_THM,
		 GSYM LEFT_FORALL_IMP_THM] THEN
Q.ABBREV_TAC `Q'' = \s1. (!e. e IN s1 ==> IS_SOME (prog_sem e)) /\
      BIGUNION (IMAGE THE (IMAGE prog_sem s1)) SUBSET Q'` THEN
`!s1. (!e. e IN s1 ==> IS_SOME (prog_sem e)) /\
      BIGUNION (IMAGE THE (IMAGE prog_sem s1)) SUBSET Q' = Q'' s1` by ALL_TAC THEN1 (
   Q.UNABBREV_TAC `Q''` THEN SIMP_TAC std_ss []
) THEN
ASM_SIMP_TAC std_ss [GSYM CONJ_ASSOC] THEN POP_ASSUM (K ALL_TAC) THEN



SIMP_TAC std_ss [smallfoot_prog_best_local_action_def,
		 IN_ABS, fasl_prog_quant_best_local_action_def,
		 FASL_PROGRAM_SEM___prim_command,
		 FASL_ATOMIC_ACTION_SEM_def, EVAL_fasl_prim_command_THM,
		 SMALLFOOT_SEPARATION_COMBINATOR___EXTRACT,
		 quant_best_local_action_THM,
		 IS_SEPARATION_COMBINATOR___smallfoot_separation_combinator] THEN
Q.ABBREV_TAC `post' =  (\x:smallfoot_state s.
            s IN SND post /\
            VAR_RES_STACK___IS_EQUAL_UPTO_VALUES (FST x) (FST s))` THEN

SIMP_TAC std_ss [SOME___quant_best_local_action, IN_ABS] THEN

`EVERY (\e. IS_SOME (e (FST x))) expL` by ALL_TAC THEN1 (
      Q.PAT_ASSUM `EVERY X expL` MP_TAC THEN
      MATCH_MP_TAC MONO_EVERY THEN
      SIMP_TAC std_ss [SMALLFOOT_AE_USED_VARS_SUBSET___REWRITE,
		       SMALLFOOT_AE_USED_VARS_REL___REWRITE,
		       GSYM LEFT_FORALL_IMP_THM] THEN
      Tactical.REVERSE (`SET_OF_BAG (BAG_UNION wpb rpb) SUBSET FDOM (FST x)` by ALL_TAC) THEN1 (
         FULL_SIMP_TAC std_ss [SUBSET_DEF]
      ) THEN
      Q.PAT_ASSUM `x IN Y` MP_TAC THEN
      SIMP_TAC std_ss [smallfoot_prop___PROP___REWRITE,
		       IN_ABS, SUBSET_DEF, bagTheory.IN_SET_OF_BAG,
		       bagTheory.BAG_IN_BAG_UNION, DISJ_IMP_THM,
		       FORALL_AND_THM, var_res_sl___has_read_permission_def,
		       var_res_sl___has_write_permission_def]
) THEN
`SMALLFOOT_AP_PERMISSION_UNIMPORTANT (SND pre) /\ 
 SMALLFOOT_AP_PERMISSION_UNIMPORTANT (SND post)` by 
   METIS_TAC[SMALLFOOT_COND_AP_PERMISSION_UNIMPORTANT_def] THEN

REPEAT STRIP_TAC THENL [
   `SMALLFOOT_IS_SUBSTATE x' x` by METIS_TAC[SMALLFOOT_IS_SUBSTATE_INTRO] THEN
   Q.EXISTS_TAC (`(FST x, SND x')`) THEN
   Q.EXISTS_TAC (`(FEMPTY, SND s0)`) THEN
   FULL_SIMP_TAC std_ss [SOME___smallfoot_separation_combinator,
		        VAR_RES_STACK_COMBINE_REWRITE] THEN
   MATCH_MP_TAC SMALLFOOT_AP_PERMISSION_UNIMPORTANT___SUBSTATE THEN
   ASM_SIMP_TAC std_ss [],



   POP_ASSUM MP_TAC THEN
   `!s1 s2. s1 SUBSET s2 ==> (Q'' s2 ==> Q'' s1)` by ALL_TAC THEN1 (
      Q.UNABBREV_TAC `Q''` THEN
      SIMP_TAC std_ss [SUBSET_DEF, IN_BIGUNION, IN_IMAGE,
		       GSYM RIGHT_EXISTS_AND_THM, GSYM LEFT_FORALL_IMP_THM] THEN
      METIS_TAC[]
   ) THEN
   POP_ASSUM MATCH_MP_TAC THEN
   SIMP_TAC std_ss [SUBSET_DEF, IN_ABS] THEN
   REPEAT STRIP_TAC THEN
   Q.PAT_ASSUM `!x''' s0. X x''' s0` 
      (MP_TAC o Q.SPECL [`(FST (x:smallfoot_state), SND (x''':smallfoot_state))`, 
                          `(FEMPTY, SND (s0':smallfoot_state))`]) THEN
   `SMALLFOOT_IS_SUBSTATE x''' x` by METIS_TAC[SMALLFOOT_IS_SUBSTATE_INTRO] THEN
   FULL_SIMP_TAC std_ss [SOME___smallfoot_separation_combinator,
		        VAR_RES_STACK_COMBINE_REWRITE] THEN


   `(FST x,SND x''') IN SND pre` by ALL_TAC THEN1 (
      MATCH_MP_TAC SMALLFOOT_AP_PERMISSION_UNIMPORTANT___SUBSTATE THEN
      ASM_SIMP_TAC std_ss []
   ) THEN
   ASM_REWRITE_TAC[] THEN

   Q.UNABBREV_TAC `post'` THEN
   SIMP_TAC std_ss [asl_star_def, IN_ABS, IN_SING,
		    SOME___smallfoot_separation_combinator,
		    VAR_RES_STACK_COMBINE_REWRITE] THEN
   REPEAT STRIP_TAC THEN
   Q.PAT_ASSUM `p IN X` MP_TAC THEN
   Q.UNABBREV_TAC `post'` THEN
   ASM_SIMP_TAC std_ss [IN_ABS] THEN

   Q.ABBREV_TAC `p_st = (FUN_FMAP (\v. (FST ((FST x'') ' v),
                                 if (v IN FDOM (FST (x''':smallfoot_state))) then
				    SND ((FST (x'':smallfoot_state)) ' v) else var_res_write_permission)
                           )

                           (FDOM (FST x'') DIFF (\v. (v IN FDOM (FST s0')) /\
                            ((SND ((FST (s0':smallfoot_state)) ' v) = var_res_write_permission))
                           )))` THEN
   REPEAT STRIP_TAC THEN
   Q.EXISTS_TAC `(p_st, SND (p:smallfoot_state))` THEN
   ASM_SIMP_TAC std_ss [] THEN
   REPEAT STRIP_TAC THENL [
      Q.PAT_ASSUM `X = SOME (FST x)` MP_TAC THEN
      Q.PAT_ASSUM `VAR_RES_STACK___IS_EQUAL_UPTO_VALUES X Y` MP_TAC THEN
      ASM_SIMP_TAC std_ss [SOME___VAR_RES_STACK_COMBINE,
			   VAR_RES_STACK___IS_EQUAL_UPTO_VALUES_def,
			   GSYM fmap_EQ_THM] THEN
      ASM_SIMP_TAC (std_ss++boolSimps.CONJ_ss) [FMERGE_DEF,
			   VAR_RES_STACK_IS_SEPARATE_def, IN_UNION,
		           VAR_RES_STACK_COMBINE___MERGE_FUNC_def] THEN
      Q.ABBREV_TAC `FDOMS = (FDOM (FST x'') DIFF
                 (\v.
                    v IN FDOM (FST s0') /\
                    (SND (FST s0' ' v) = var_res_write_permission)))` THEN
      `FINITE FDOMS` by (Q.UNABBREV_TAC `FDOMS` THEN ASM_SIMP_TAC std_ss [FINITE_DIFF, FDOM_FINITE]) THEN
      Q.UNABBREV_TAC `p_st` THEN
      ASM_SIMP_TAC std_ss [FUN_FMAP_DEF] THEN
      `(FDOM (FST x'') = FDOMS UNION FDOM (FST s0'))` by ALL_TAC THEN1 (
          Q.UNABBREV_TAC `FDOMS` YTHJE
      )

   ASM_SIMP_TAC std_ss [] THEN
   Q.PAT_ASSUM `p IN X` MP_TAC THEN
   Q.PAT_ASSUM `X = SOME (FST x)` MP_TAC THEN
   Q.UNABBREV_TAC `post'` THEN
   ASM_SIMP_TAC std_ss [IN_ABS, VAR_RES_STACK___IS_EQUAL_UPTO_VALUES_def,
		    FUN_FMAP_DEF, FDOM_FINITE, FINITE_DIFF,
		    IN_DIFF, SOME___VAR_RES_STACK_COMBINE,
			 FMERGE_DEF, IN_UNION, 
			 VAR_RES_STACK_IS_SEPARATE_def] THEN
   STRIP_TAC THEN STRIP_TAC THEN
   REPEAT CONJ_TAC THENL [
      GEN_TAC THEN STRIP_TAC THEN
      Q.ABBREV_TAC `FDOMS = FDOM (FST x'') DIFF (\v.
                      v IN FDOM (FST s0') /\
                      (SND (FST s0' ' v) = var_res_write_permission))` THEN
      `(x'''' IN FDOMS) /\ FINITE FDOMS` by ALL_TAC THEN1 (
         Q.UNABBREV_TAC `FDOMS` THEN
         ASM_SIMP_TAC std_ss [IN_DIFF, IN_ABS, FDOM_FINITE, FINITE_DIFF]
      ) THEN
      ASM_SIMP_TAC std_ss [FUN_FMAP_DEF] THEN
      METIS_TAC[]
      
   FUN_FMAP_DEF
   


		     
   REPEAT STRIP_TAC THENL [
      Q.PAT_ASSUM `VAR_RES_STACK_COMBINE
   VAR_RES_STACK___IS_EQUAL_UPTO_VALUES_def

find "UPDATE_PERM"
   FULL_SIMP_TAC std_ss [SOME___smallfoot_separation_combinator,
			 VAR_RES_STACK_COMBINE_REWRITE,
   ASM_SIMP_TAC std_ss []
   METIS_TAC[]
find "VAR_RES_STACK_COMBINE"

match [] ``FST smallfoot_env``


Q.ABBREV_TAC `

		 IN_ABS, FASL_PROGRAM_TRACES_IN_THM,
		    fasl_prog_diverge_def, fasl_prog_prim_command_def,
		    FASL_PROGRAM_TRACES_def, IN_INSERT, IN_BIGUNION,
		    IN_SING, IN_IMAGE, GSYM RIGHT_EXISTS_AND_THM,
		    FASL_PROTO_TRACES_EVAL_IN_THM,
		    GSYM fasl_aa_diverge_def,
		    GSYM LEFT_FORALL_IMP_THM] THEN
   SIMP_TAC list_ss [FASL_TRACE_SEM_diverge, EMPTY_SUBSET]


Cases_on `~FST pre \/ ~FST post` THEN1 (
   ASM_REWRITE_TAC[] THEN
   SIMP_TAC std_ss [SMALLFOOT_HOARE_TRIPLE_def,
		    FASL_PROGRAM_HOARE_TRIPLE_REWRITE,
		    IN_ABS, FASL_PROGRAM_TRACES_IN_THM,
		    fasl_prog_diverge_def, fasl_prog_prim_command_def,
		    FASL_PROGRAM_TRACES_def, IN_INSERT, IN_BIGUNION,
		    IN_SING, IN_IMAGE, GSYM RIGHT_EXISTS_AND_THM,
		    FASL_PROTO_TRACES_EVAL_IN_THM,
		    GSYM fasl_aa_diverge_def,
		    GSYM LEFT_FORALL_IMP_THM] THEN
   SIMP_TAC list_ss [FASL_TRACE_SEM_diverge, EMPTY_SUBSET]
) THEN
FULL_SIMP_TAC std_ss [] THEN

`smallfoot_prop___COND (wpb,rpb) (BAG_UNION sfb' sfb'')` by ALL_TAC THEN1 (
   FULL_SIMP_TAC std_ss [smallfoot_prop___COND___REWRITE, bagTheory.FINITE_BAG_UNION] THEN
   REPEAT STRIP_TAC THEN
   MATCH_MP_TAC SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___SUBSET THEN
   Q.EXISTS_TAC `SET_OF_BAG (BAG_UNION wpb' rpb')` THEN
   FULL_SIMP_TAC std_ss [SUBSET_DEF, bagTheory.BAG_IN_BAG_UNION,
        	        bagTheory.IN_SET_OF_BAG, DISJ_IMP_THM]
) THEN

FULL_SIMP_TAC std_ss [SMALLFOOT_PROP_IMPLIES_EXPAND, bagTheory.BAG_UNION_EMPTY] THEN
FULL_SIMP_TAC std_ss [smallfoot_prop___COND_UNION] THEN
`~((\sfb'''.
               smallfoot_prop___COND (wpb,rpb) sfb''' ==>
               SMALLFOOT_HOARE_TRIPLE (K smallfoot_ap_true) FEMPTY
                 (smallfoot_prop___PROP (wpb,rpb) (BAG_UNION sfb'' sfb'''))
                 prog Q_ap) =
            {})` by ALL_TAC THEN1 (
   SIMP_TAC std_ss [EXTENSION, NOT_IN_EMPTY, IN_ABS] THEN
   Q.EXISTS_TAC `{| smallfoot_ap_false|}` THEN
   SIMP_TAC std_ss [SMALLFOOT_HOARE_TRIPLE_def,
		    FASL_PROGRAM_HOARE_TRIPLE_REWRITE,
		    IN_ABS, smallfoot_prop___PROP___REWRITE,
		    smallfoot_ap_bigstar___BAG_UNION,
		    smallfoot_ap_bigstar_REWRITE,
		    smallfoot_ap_star___PROPERTIES] THEN
   SIMP_TAC std_ss [smallfoot_ap_star_def, asl_star_def,
		    IN_ABS, smallfoot_ap_false___NOT_IN]
) THEN
FULL_SIMP_TAC std_ss [] THEN
POP_ASSUM (K ALL_TAC) THEN

Tactical.REVERSE (Cases_on `smallfoot_prop___COND (wpb,rpb) sfb'''`) THEN1 (
   Tactical.REVERSE (`!x. ~(x IN smallfoot_prop___PROP (wpb,rpb) sfb)` by ALL_TAC) THEN1 (
      ASM_SIMP_TAC std_ss [SMALLFOOT_HOARE_TRIPLE_def,
		    FASL_PROGRAM_HOARE_TRIPLE_REWRITE, IN_ABS]
   ) THEN
   FULL_SIMP_TAC std_ss [IN_DEF]
) THEN

MATCH_MP_TAC SMALLFOOT_INFERENCE_prog_seq THEN
Q.EXISTS_TAC `smallfoot_prop___PROP (wpb,rpb) (BAG_UNION sfb'' sfb''')` THEN

FULL_SIMP_TAC std_ss [smallfoot_prop___COND_UNION] THEN
SIMP_TAC list_ss [SMALLFOOT_HOARE_TRIPLE_def,
		 smallfoot_prog_best_local_action_def,
		 IN_ABS, FASL_PROGRAM_HOARE_TRIPLE_REWRITE,
		 fasl_prog_quant_best_local_action_def,
		 FASL_PROGRAM_TRACES_def, IN_BIGUNION, IN_IMAGE,
		 IN_SING, GSYM RIGHT_EXISTS_AND_THM,
		 fasl_prog_prim_command_def,
		 FASL_PROTO_TRACES_EVAL_IN_THM,
		 FASL_TRACE_SEM_def, fasla_big_seq_def,
		 fasla_seq_skip, SUBSET_DEF,
		 FASL_ATOMIC_ACTION_SEM_def,
		 EVAL_fasl_prim_command_THM,
		 SMALLFOOT_SEPARATION_COMBINATOR___EXTRACT,
		 quant_best_local_action_THM,
		 IS_SEPARATION_COMBINATOR___smallfoot_separation_combinator] THEN
SIMP_TAC std_ss [quant_best_local_action_def, INF_fasl_action_order_def,
		 INF_fasl_order_def, COND_NONE_SOME_REWRITES,
		 IN_IMAGE, GSYM RIGHT_EXISTS_AND_THM, IN_ABS,
		 GSYM LEFT_EXISTS_AND_THM, IN_BIGINTER, IN_INTER,
		 GSYM LEFT_FORALL_IMP_THM, IS_SOME_EXISTS] THEN
SIMP_TAC std_ss [SOME___best_local_action, NONE___best_local_action,
		 IN_ABS, GSYM LEFT_FORALL_IMP_THM,
		 GSYM LEFT_EXISTS_AND_THM] THEN
REPEAT STRIP_TAC THEN
FULL_SIMP_TAC std_ss [SMALLFOOT_PROP_IMPLIES_def,
        	      bagTheory.BAG_UNION_EMPTY] THEN
FULL_SIMP_TAC std_ss [smallfoot_prop___COND_UNION,
			 smallfoot_prop___PROP_UNION] THEN
`smallfoot_prop___PROP (wpb,rpb) sfb x` by FULL_SIMP_TAC std_ss [IN_DEF] THEN
RES_TAC THEN
Q.EXISTS_TAC `(VAR_RES_STACK_SPLIT1 (SET_OF_BAG wpb') (FST x), h1)` THEN
Q.EXISTS_TAC `(VAR_RES_STACK_SPLIT2 (SET_OF_BAG wpb') (FST x), h2)` THEN
MATCH_MP_TAC (prove (``(A /\ (A ==> B)) ==> (A /\ B)``, SIMP_TAC std_ss [])) THEN
CONJ_TAC THEN1 (
   REPEAT STRIP_TAC THENL [
      FULL_SIMP_TAC std_ss [smallfoot_prop___PROP___REWRITE,
			    IN_ABS, bagTheory.BAG_IN_BAG_UNION,
			    VAR_RES_STACK_SPLIT12___read_writes,
			    bagTheory.IN_SET_OF_BAG] THEN
      REPEAT STRIP_TAC THEN1 (
         `BAG_IN v wpb \/ BAG_IN v rpb` by ASM_SIMP_TAC std_ss [] THEN
         FULL_SIMP_TAC std_ss [var_res_sl___has_read_permission_def,
	          	       var_res_sl___has_write_permission_def]
      ) THEN
      Q.ABBREV_TAC `P = smallfoot_ap_star smallfoot_ap_stack_true (smallfoot_ap_bigstar sfb')` THEN
      `SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS
           (SET_OF_BAG (BAG_UNION wpb' rpb')) P` by FULL_SIMP_TAC std_ss [smallfoot_prop___COND___EXPAND] THEN
      POP_ASSUM (MATCH_MP_TAC o REWRITE_RULE [SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___ALTERNATIVE_DEF_2]) THEN
      Q.EXISTS_TAC `(FST x,h1)` THEN
      ASM_SIMP_TAC std_ss [VAR_RES_STACK_SPLIT12___REWRITES,
			   SUBSET_DEF, IN_INTER],

      Q.PAT_ASSUM `EVERY XX expL` MP_TAC THEN
      SIMP_TAC std_ss [EVERY_MEM, GSYM IS_SOME_EXISTS] THEN
      HO_MATCH_MP_TAC (prove (``(!e. Y e ==> Z e) ==> ((!e. X e ==> Y e) ==> (!e. X e ==> Z e))``, METIS_TAC[])) THEN
      SIMP_TAC std_ss [SMALLFOOT_AE_USED_VARS_SUBSET___REWRITE,
		       SMALLFOOT_AE_USED_VARS_REL_def,
		       GSYM LEFT_FORALL_IMP_THM,
		       VAR_RES_STACK_SPLIT12___REWRITES] THEN
      REPEAT STRIP_TAC THEN
      Tactical.REVERSE (`SET_OF_BAG (BAG_UNION wpb rpb) SUBSET FDOM (FST x)` by ALL_TAC) THEN1 (
         METIS_TAC [SUBSET_TRANS]
      ) THEN
      FULL_SIMP_TAC std_ss [SUBSET_DEF,
			    smallfoot_prop___PROP___REWRITE,
			    IN_ABS, var_res_sl___has_write_permission_def,
			    var_res_sl___has_read_permission_def,
			    bagTheory.IN_SET_OF_BAG, bagTheory.BAG_IN_BAG_UNION,
			    DISJ_IMP_THM],		       


      ASM_SIMP_TAC std_ss [SOME___smallfoot_separation_combinator,			   
			   DISJOINT_SYM, FUNION___COMM,
			   FMERGE_FEMPTY] THEN
      METIS_TAC [VAR_RES_STACK_COMBINE___IS_SEPARATION_COMBINATOR,
		 IS_SEPARATION_COMBINATOR_def,
		 COMM_DEF,
	         VAR_RES_STACK_COMBINE___VAR_RES_STACK_SPLIT12]
   ]
) THEN
STRIP_TAC THEN GEN_TAC THEN
SIMP_TAC std_ss [GSYM LEFT_EXISTS_IMP_THM, IN_ABS]  THEN
Q.EXISTS_TAC `(VAR_RES_STACK_SPLIT1 (SET_OF_BAG wpb') (FST x), h1)` THEN
Q.EXISTS_TAC `(VAR_RES_STACK_SPLIT2 (SET_OF_BAG wpb') (FST x), h2)` THEN
ASM_SIMP_TAC std_ss [GSYM LEFT_EXISTS_IMP_THM] THEN
Q.EXISTS_TAC `(VAR_RES_STACK_SPLIT2 (SET_OF_BAG wpb') (FST x), h2)` THEN


ASM_SIMP_TAC std_ss [asl_star_def, IN_ABS, IN_SING, PAIR_EXISTS_THM,
		     SOME___smallfoot_separation_combinator,
		     SOME___VAR_RES_STACK_COMBINE,
		     GSYM LEFT_EXISTS_AND_THM] THEN
REPEAT STRIP_TAC THEN
Q.EXISTS_TAC `x2` THEN
Q.EXISTS_TAC `h2` THEN
ASM_REWRITE_TAC[] THEN

FULL_SIMP_TAC std_ss [smallfoot_prop___PROP___REWRITE, IN_ABS,
		      var_res_sl___has_read_permission_def,
		      var_res_sl___has_write_permission_def,
		      VAR_RES_STACK_SPLIT12___REWRITES,
		      bagTheory.IN_SET_OF_BAG,
		      FMERGE_DEF, IN_UNION, IN_DIFF,
		      VAR_RES_STACK_COMBINE___MERGE_FUNC_def,
		      COND_REWRITES] THEN
SIMP_TAC (std_ss++boolSimps.CONJ_ss) [] THEN
`!v. (v IN FDOM x1 \/ ~BAG_IN v wpb')` by METIS_TAC[] THEN
`!v. BAG_IN v wpb ==> v IN FDOM x1` by ALL_TAC THEN1 (
   REPEAT STRIP_TAC THEN
   CCONTR_TAC THEN
   `~BAG_IN v wpb'` by PROVE_TAC[] THEN
   FULL_SIMP_TAC std_ss [VAR_RES_STACK___IS_EQUAL_UPTO_VALUES_def,
			    VAR_RES_STACK_SPLIT12___REWRITES,
			    bagTheory.IN_SET_OF_BAG] THEN
   Q.PAT_ASSUM `!x'. x' IN FDOM (FST x) /\ ~(x' IN FDOM x1) ==> X x'`
      (MP_TAC o Q.SPEC `v`) THEN
   ASM_SIMP_TAC std_ss [var_res_permission_THM2]
) THEN
ASM_SIMP_TAC std_ss [COND_RATOR, COND_RAND] THEN
REPEAT STRIP_TAC THENL [
   Q.ABBREV_TAC `P = smallfoot_ap_star smallfoot_ap_stack_true (smallfoot_ap_bigstar sfb'')` THEN
   `SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS
        (SET_OF_BAG (BAG_UNION wpb' rpb')) P` by FULL_SIMP_TAC std_ss [smallfoot_prop___COND___EXPAND] THEN
   POP_ASSUM (MATCH_MP_TAC o REWRITE_RULE [SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___ALTERNATIVE_DEF_2]) THEN
   Q.EXISTS_TAC `(x1,x2)` THEN
   ASM_SIMP_TAC std_ss [FMERGE_DEF, bagTheory.IN_SET_OF_BAG,
		        VAR_RES_STACK_SPLIT12___REWRITES,
		        bagTheory.BAG_IN_BAG_UNION, IN_DIFF,
		        COND_REWRITES, SUBSET_DEF, IN_INTER, IN_UNION],



   FULL_SIMP_TAC std_ss [VAR_RES_STACK___IS_EQUAL_UPTO_VALUES_def,
			    VAR_RES_STACK_SPLIT12___REWRITES,
			    bagTheory.IN_SET_OF_BAG] THEN
   Cases_on `BAG_IN v wpb'` THEN ASM_SIMP_TAC std_ss [] THEN
   `SND (x1 ' v) = var_res_permission_split (SND (FST x ' v))` by METIS_TAC[] THEN
   ASM_SIMP_TAC std_ss [var_res_permission_THM2],



   Q.ABBREV_TAC `P = smallfoot_ap_star smallfoot_ap_stack_true (smallfoot_ap_bigstar sfb''')` THEN
   `SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS
        (SET_OF_BAG (BAG_UNION (BAG_DIFF wpb wpb') (BAG_DIFF rpb wpb'))) P` by FULL_SIMP_TAC std_ss [smallfoot_prop___COND___EXPAND] THEN
   POP_ASSUM (MATCH_MP_TAC o REWRITE_RULE [SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___ALTERNATIVE_DEF_2]) THEN
   Q.EXISTS_TAC `(FST x,h2)` THEN
   `BAG_ALL_DISTINCT wpb /\ BAG_ALL_DISTINCT rpb` by 
       FULL_SIMP_TAC std_ss [smallfoot_prop___COND___EXPAND] THEN
   ASM_SIMP_TAC std_ss [FMERGE_DEF, bagTheory.IN_SET_OF_BAG,
		        VAR_RES_STACK_SPLIT12___REWRITES,
		        bagTheory.BAG_IN_BAG_UNION, IN_DIFF,
		        COND_REWRITES, SUBSET_DEF, IN_INTER, IN_UNION,
		        BAG_IN___BAG_DIFF___ALL_DISTINCT,
		        LEFT_AND_OVER_OR, DISJ_IMP_THM, FORALL_AND_THM] THEN
   Q.PAT_ASSUM `VAR_RES_STACK_IS_SEPARATE X Y` MP_TAC THEN
   ASM_SIMP_TAC std_ss [VAR_RES_STACK_IS_SEPARATE_def,
		    VAR_RES_STACK_SPLIT12___REWRITES,
		    bagTheory.IN_SET_OF_BAG,
		    IN_DIFF, FMERGE_DEF,
		        IN_UNION, IN_DIFF, bagTheory.IN_SET_OF_BAG] THEN
   ASM_SIMP_TAC (std_ss++boolSimps.CONJ_ss) [COND_REWRITES],



   Q.PAT_ASSUM `VAR_RES_STACK___IS_EQUAL_UPTO_VALUES X x1` MP_TAC THEN
   ASM_SIMP_TAC std_ss [VAR_RES_STACK___IS_EQUAL_UPTO_VALUES_def,
			    VAR_RES_STACK_SPLIT12___REWRITES,
			    bagTheory.IN_SET_OF_BAG, FMERGE_DEF,
		        var_res_permission_THM2, IN_UNION,
		        IN_DIFF] THEN
   ASM_SIMP_TAC (std_ss++boolSimps.CONJ_ss) [COND_REWRITES,
					    var_res_permission_THM2] THEN
   REPEAT STRIP_TAC THEN
   Tactical.REVERSE (Cases_on `(x'' IN FDOM x1)`) THEN1 (
      METIS_TAC[]
   ) THEN
   Cases_on `BAG_IN x'' wpb'` THEN (
      ASM_SIMP_TAC std_ss []
   ) THEN
   `SND (x1 ' x'') = var_res_permission_split (SND (FST x ' x''))` by METIS_TAC[] THEN
   ASM_SIMP_TAC std_ss [var_res_permission_THM2]
]);



*)




val SMALLFOOT_COND_INFERENCE___smallfoot_cond_best_local_action = store_thm ("SMALLFOOT_COND_INFERENCE___smallfoot_cond_best_local_action",
``!wpb rpb sfb wpb' rpb' sfb' sfb'' prog expL.

  (((SET_OF_BAG wpb') SUBSET (SET_OF_BAG wpb)) /\
   ((SET_OF_BAG rpb') SUBSET (SET_OF_BAG (BAG_UNION wpb rpb))) /\
   EVERY (SMALLFOOT_AE_USED_VARS_SUBSET (SET_OF_BAG (BAG_UNION wpb rpb))) expL) ==>

( (
  SMALLFOOT_PROP_IMPLIES T (wpb,rpb) wpb' EMPTY_BAG sfb sfb' 
  (\sfb'''. SMALLFOOT_COND_HOARE_TRIPLE 
    (smallfoot_prop (wpb,rpb) (BAG_UNION sfb'' sfb''')) prog Q))

 ==>


  SMALLFOOT_COND_HOARE_TRIPLE 
    (smallfoot_prop (wpb,rpb) sfb)
    (fasl_prog_seq 
        (smallfoot_cond_best_local_action 
            (smallfoot_ae_is_list_cond_defined 
               (smallfoot_prop (wpb',rpb') sfb')
               expL)
            (smallfoot_prop (wpb',rpb') sfb''))
        prog)
    Q)``,


REPEAT GEN_TAC THEN
`?Q_ap Q_cond. Q = (Q_cond, Q_ap)` by (Cases_on `Q` THEN SIMP_TAC std_ss []) THEN
ASM_SIMP_TAC std_ss [SMALLFOOT_COND_HOARE_TRIPLE_def,
		 smallfoot_prop___REWRITE, smallfoot_cond_best_local_action_def,
                 smallfoot_ae_is_list_cond_defined_def,
		 SUBSET_DEF, bagTheory.IN_SET_OF_BAG] THEN
REPEAT STRIP_TAC THEN
Cases_on `~smallfoot_prop___COND (wpb',rpb') sfb' \/
          ~smallfoot_prop___COND (wpb',rpb') sfb''` THEN1 (
   ASM_REWRITE_TAC[] THEN
   SIMP_TAC std_ss [SMALLFOOT_HOARE_TRIPLE_def,
		    FASL_PROGRAM_HOARE_TRIPLE_REWRITE,
		    IN_ABS, FASL_PROGRAM_TRACES_IN_THM,
		    fasl_prog_diverge_def, fasl_prog_prim_command_def,
		    FASL_PROGRAM_TRACES_def, IN_INSERT, IN_BIGUNION,
		    IN_SING, IN_IMAGE, GSYM RIGHT_EXISTS_AND_THM,
		    FASL_PROTO_TRACES_EVAL_IN_THM,
		    GSYM fasl_aa_diverge_def,
		    GSYM LEFT_FORALL_IMP_THM] THEN
   SIMP_TAC list_ss [FASL_TRACE_SEM_diverge, EMPTY_SUBSET]
) THEN
FULL_SIMP_TAC std_ss [] THEN

`smallfoot_prop___COND (wpb,rpb) (BAG_UNION sfb' sfb'')` by ALL_TAC THEN1 (
   FULL_SIMP_TAC std_ss [smallfoot_prop___COND___REWRITE, bagTheory.FINITE_BAG_UNION] THEN
   REPEAT STRIP_TAC THEN
   MATCH_MP_TAC SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___SUBSET THEN
   Q.EXISTS_TAC `SET_OF_BAG (BAG_UNION wpb' rpb')` THEN
   FULL_SIMP_TAC std_ss [SUBSET_DEF, bagTheory.BAG_IN_BAG_UNION,
        	        bagTheory.IN_SET_OF_BAG, DISJ_IMP_THM]
) THEN

FULL_SIMP_TAC std_ss [SMALLFOOT_PROP_IMPLIES_EXPAND, bagTheory.BAG_UNION_EMPTY] THEN
FULL_SIMP_TAC std_ss [smallfoot_prop___COND_UNION] THEN
`~((\sfb'''.
               smallfoot_prop___COND (wpb,rpb) sfb''' ==>
               SMALLFOOT_HOARE_TRIPLE (K smallfoot_ap_true) FEMPTY
                 (smallfoot_prop___PROP (wpb,rpb) (BAG_UNION sfb'' sfb'''))
                 prog Q_ap) =
            {})` by ALL_TAC THEN1 (
   SIMP_TAC std_ss [EXTENSION, NOT_IN_EMPTY, IN_ABS] THEN
   Q.EXISTS_TAC `{| smallfoot_ap_false|}` THEN
   SIMP_TAC std_ss [SMALLFOOT_HOARE_TRIPLE_def,
		    FASL_PROGRAM_HOARE_TRIPLE_REWRITE,
		    IN_ABS, smallfoot_prop___PROP___REWRITE,
		    smallfoot_ap_bigstar___BAG_UNION,
		    smallfoot_ap_bigstar_REWRITE,
		    smallfoot_ap_star___PROPERTIES] THEN
   SIMP_TAC std_ss [smallfoot_ap_star_def, asl_star_def,
		    IN_ABS, smallfoot_ap_false___NOT_IN]
) THEN
FULL_SIMP_TAC std_ss [] THEN
POP_ASSUM (K ALL_TAC) THEN

Tactical.REVERSE (Cases_on `smallfoot_prop___COND (wpb,rpb) sfb'''`) THEN1 (
   Tactical.REVERSE (`!x. ~(x IN smallfoot_prop___PROP (wpb,rpb) sfb)` by ALL_TAC) THEN1 (
      ASM_SIMP_TAC std_ss [SMALLFOOT_HOARE_TRIPLE_def,
		    FASL_PROGRAM_HOARE_TRIPLE_REWRITE, IN_ABS]
   ) THEN
   FULL_SIMP_TAC std_ss [IN_DEF]
) THEN

MATCH_MP_TAC SMALLFOOT_INFERENCE_prog_seq THEN
Q.EXISTS_TAC `smallfoot_prop___PROP (wpb,rpb) (BAG_UNION sfb'' sfb''')` THEN

FULL_SIMP_TAC std_ss [smallfoot_prop___COND_UNION] THEN
SIMP_TAC list_ss [SMALLFOOT_HOARE_TRIPLE_def,
		 smallfoot_prog_best_local_action_def,
		 IN_ABS, FASL_PROGRAM_HOARE_TRIPLE_REWRITE,
		 fasl_prog_quant_best_local_action_def,
		 FASL_PROGRAM_TRACES_def, IN_BIGUNION, IN_IMAGE,
		 IN_SING, GSYM RIGHT_EXISTS_AND_THM,
		 fasl_prog_prim_command_def,
		 FASL_PROTO_TRACES_EVAL_IN_THM,
		 FASL_TRACE_SEM_def, fasla_big_seq_def,
		 fasla_seq_skip, SUBSET_DEF,
		 FASL_ATOMIC_ACTION_SEM_def,
		 EVAL_fasl_prim_command_THM,
		 SMALLFOOT_SEPARATION_COMBINATOR___EXTRACT,
		 quant_best_local_action_THM,
		 IS_SEPARATION_COMBINATOR___smallfoot_separation_combinator] THEN
SIMP_TAC std_ss [quant_best_local_action_def, INF_fasl_action_order_def,
		 INF_fasl_order_def, COND_NONE_SOME_REWRITES,
		 IN_IMAGE, GSYM RIGHT_EXISTS_AND_THM, IN_ABS,
		 GSYM LEFT_EXISTS_AND_THM, IN_BIGINTER, IN_INTER,
		 GSYM LEFT_FORALL_IMP_THM, IS_SOME_EXISTS] THEN
SIMP_TAC std_ss [SOME___best_local_action, NONE___best_local_action,
		 IN_ABS, GSYM LEFT_FORALL_IMP_THM,
		 GSYM LEFT_EXISTS_AND_THM] THEN
REPEAT STRIP_TAC THEN
FULL_SIMP_TAC std_ss [SMALLFOOT_PROP_IMPLIES_def,
        	      bagTheory.BAG_UNION_EMPTY] THEN
FULL_SIMP_TAC std_ss [smallfoot_prop___COND_UNION,
			 smallfoot_prop___PROP_UNION] THEN
`smallfoot_prop___PROP (wpb,rpb) sfb x` by FULL_SIMP_TAC std_ss [IN_DEF] THEN
RES_TAC THEN
Q.EXISTS_TAC `(VAR_RES_STACK_SPLIT1 (SET_OF_BAG wpb') (FST x), h1)` THEN
Q.EXISTS_TAC `(VAR_RES_STACK_SPLIT2 (SET_OF_BAG wpb') (FST x), h2)` THEN
MATCH_MP_TAC (prove (``(A /\ (A ==> B)) ==> (A /\ B)``, SIMP_TAC std_ss [])) THEN
CONJ_TAC THEN1 (
   REPEAT STRIP_TAC THENL [
      FULL_SIMP_TAC std_ss [smallfoot_prop___PROP___REWRITE,
			    IN_ABS, bagTheory.BAG_IN_BAG_UNION,
			    VAR_RES_STACK_SPLIT12___read_writes,
			    bagTheory.IN_SET_OF_BAG] THEN
      REPEAT STRIP_TAC THEN1 (
         `BAG_IN v wpb \/ BAG_IN v rpb` by ASM_SIMP_TAC std_ss [] THEN
         FULL_SIMP_TAC std_ss [var_res_sl___has_read_permission_def,
	          	       var_res_sl___has_write_permission_def]
      ) THEN
      Q.ABBREV_TAC `P = smallfoot_ap_star smallfoot_ap_stack_true (smallfoot_ap_bigstar sfb')` THEN
      `SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS
           (SET_OF_BAG (BAG_UNION wpb' rpb')) P` by FULL_SIMP_TAC std_ss [smallfoot_prop___COND___EXPAND] THEN
      POP_ASSUM (MATCH_MP_TAC o REWRITE_RULE [SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___ALTERNATIVE_DEF_2]) THEN
      Q.EXISTS_TAC `(FST x,h1)` THEN
      ASM_SIMP_TAC std_ss [VAR_RES_STACK_SPLIT12___REWRITES,
			   SUBSET_DEF, IN_INTER],

      Q.PAT_ASSUM `EVERY XX expL` MP_TAC THEN
      SIMP_TAC std_ss [EVERY_MEM, GSYM IS_SOME_EXISTS] THEN
      HO_MATCH_MP_TAC (prove (``(!e. Y e ==> Z e) ==> ((!e. X e ==> Y e) ==> (!e. X e ==> Z e))``, METIS_TAC[])) THEN
      SIMP_TAC std_ss [SMALLFOOT_AE_USED_VARS_SUBSET___REWRITE,
		       SMALLFOOT_AE_USED_VARS_REL_def,
		       GSYM LEFT_FORALL_IMP_THM,
		       VAR_RES_STACK_SPLIT12___REWRITES] THEN
      REPEAT STRIP_TAC THEN
      Tactical.REVERSE (`SET_OF_BAG (BAG_UNION wpb rpb) SUBSET FDOM (FST x)` by ALL_TAC) THEN1 (
         METIS_TAC [SUBSET_TRANS]
      ) THEN
      FULL_SIMP_TAC std_ss [SUBSET_DEF,
			    smallfoot_prop___PROP___REWRITE,
			    IN_ABS, var_res_sl___has_write_permission_def,
			    var_res_sl___has_read_permission_def,
			    bagTheory.IN_SET_OF_BAG, bagTheory.BAG_IN_BAG_UNION,
			    DISJ_IMP_THM],		       


      ASM_SIMP_TAC std_ss [SOME___smallfoot_separation_combinator,			   
			   DISJOINT_SYM, FUNION___COMM,
			   FMERGE_FEMPTY] THEN
      METIS_TAC [VAR_RES_STACK_COMBINE___IS_SEPARATION_COMBINATOR,
		 IS_SEPARATION_COMBINATOR_def,
		 COMM_DEF,
	         VAR_RES_STACK_COMBINE___VAR_RES_STACK_SPLIT12]
   ]
) THEN
STRIP_TAC THEN GEN_TAC THEN
SIMP_TAC std_ss [GSYM LEFT_EXISTS_IMP_THM, IN_ABS]  THEN
Q.EXISTS_TAC `(VAR_RES_STACK_SPLIT1 (SET_OF_BAG wpb') (FST x), h1)` THEN
Q.EXISTS_TAC `(VAR_RES_STACK_SPLIT2 (SET_OF_BAG wpb') (FST x), h2)` THEN
ASM_SIMP_TAC std_ss [GSYM LEFT_EXISTS_IMP_THM] THEN
Q.EXISTS_TAC `(VAR_RES_STACK_SPLIT2 (SET_OF_BAG wpb') (FST x), h2)` THEN


ASM_SIMP_TAC std_ss [asl_star_def, IN_ABS, IN_SING, PAIR_EXISTS_THM,
		     SOME___smallfoot_separation_combinator,
		     SOME___VAR_RES_STACK_COMBINE,
		     GSYM LEFT_EXISTS_AND_THM] THEN
REPEAT STRIP_TAC THEN
Q.EXISTS_TAC `x2` THEN
Q.EXISTS_TAC `h2` THEN
ASM_REWRITE_TAC[] THEN

FULL_SIMP_TAC std_ss [smallfoot_prop___PROP___REWRITE, IN_ABS,
		      var_res_sl___has_read_permission_def,
		      var_res_sl___has_write_permission_def,
		      VAR_RES_STACK_SPLIT12___REWRITES,
		      bagTheory.IN_SET_OF_BAG,
		      FMERGE_DEF, IN_UNION, IN_DIFF,
		      VAR_RES_STACK_COMBINE___MERGE_FUNC_def,
		      COND_REWRITES] THEN
SIMP_TAC (std_ss++boolSimps.CONJ_ss) [] THEN
`!v. (v IN FDOM x1 \/ ~BAG_IN v wpb')` by METIS_TAC[] THEN
`!v. BAG_IN v wpb ==> v IN FDOM x1` by ALL_TAC THEN1 (
   REPEAT STRIP_TAC THEN
   CCONTR_TAC THEN
   `~BAG_IN v wpb'` by PROVE_TAC[] THEN
   FULL_SIMP_TAC std_ss [VAR_RES_STACK___IS_EQUAL_UPTO_VALUES_def,
			    VAR_RES_STACK_SPLIT12___REWRITES,
			    bagTheory.IN_SET_OF_BAG] THEN
   Q.PAT_ASSUM `!x'. x' IN FDOM (FST x) /\ ~(x' IN FDOM x1) ==> X x'`
      (MP_TAC o Q.SPEC `v`) THEN
   ASM_SIMP_TAC std_ss [var_res_permission_THM2]
) THEN
ASM_SIMP_TAC std_ss [COND_RATOR, COND_RAND] THEN
REPEAT STRIP_TAC THENL [
   Q.ABBREV_TAC `P = smallfoot_ap_star smallfoot_ap_stack_true (smallfoot_ap_bigstar sfb'')` THEN
   `SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS
        (SET_OF_BAG (BAG_UNION wpb' rpb')) P` by FULL_SIMP_TAC std_ss [smallfoot_prop___COND___EXPAND] THEN
   POP_ASSUM (MATCH_MP_TAC o REWRITE_RULE [SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___ALTERNATIVE_DEF_2]) THEN
   Q.EXISTS_TAC `(x1,x2)` THEN
   ASM_SIMP_TAC std_ss [FMERGE_DEF, bagTheory.IN_SET_OF_BAG,
		        VAR_RES_STACK_SPLIT12___REWRITES,
		        bagTheory.BAG_IN_BAG_UNION, IN_DIFF,
		        COND_REWRITES, SUBSET_DEF, IN_INTER, IN_UNION],



   FULL_SIMP_TAC std_ss [VAR_RES_STACK___IS_EQUAL_UPTO_VALUES_def,
			    VAR_RES_STACK_SPLIT12___REWRITES,
			    bagTheory.IN_SET_OF_BAG] THEN
   Cases_on `BAG_IN v wpb'` THEN ASM_SIMP_TAC std_ss [] THEN
   `SND (x1 ' v) = var_res_permission_split (SND (FST x ' v))` by METIS_TAC[] THEN
   ASM_SIMP_TAC std_ss [var_res_permission_THM2],



   Q.ABBREV_TAC `P = smallfoot_ap_star smallfoot_ap_stack_true (smallfoot_ap_bigstar sfb''')` THEN
   `SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS
        (SET_OF_BAG (BAG_UNION (BAG_DIFF wpb wpb') (BAG_DIFF rpb wpb'))) P` by FULL_SIMP_TAC std_ss [smallfoot_prop___COND___EXPAND] THEN
   POP_ASSUM (MATCH_MP_TAC o REWRITE_RULE [SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___ALTERNATIVE_DEF_2]) THEN
   Q.EXISTS_TAC `(FST x,h2)` THEN
   `BAG_ALL_DISTINCT wpb /\ BAG_ALL_DISTINCT rpb` by 
       FULL_SIMP_TAC std_ss [smallfoot_prop___COND___EXPAND] THEN
   ASM_SIMP_TAC std_ss [FMERGE_DEF, bagTheory.IN_SET_OF_BAG,
		        VAR_RES_STACK_SPLIT12___REWRITES,
		        bagTheory.BAG_IN_BAG_UNION, IN_DIFF,
		        COND_REWRITES, SUBSET_DEF, IN_INTER, IN_UNION,
		        BAG_IN___BAG_DIFF___ALL_DISTINCT,
		        LEFT_AND_OVER_OR, DISJ_IMP_THM, FORALL_AND_THM] THEN
   Q.PAT_ASSUM `VAR_RES_STACK_IS_SEPARATE X Y` MP_TAC THEN
   ASM_SIMP_TAC std_ss [VAR_RES_STACK_IS_SEPARATE_def,
		    VAR_RES_STACK_SPLIT12___REWRITES,
		    bagTheory.IN_SET_OF_BAG,
		    IN_DIFF, FMERGE_DEF,
		        IN_UNION, IN_DIFF, bagTheory.IN_SET_OF_BAG] THEN
   ASM_SIMP_TAC (std_ss++boolSimps.CONJ_ss) [COND_REWRITES],



   Q.PAT_ASSUM `VAR_RES_STACK___IS_EQUAL_UPTO_VALUES X x1` MP_TAC THEN
   ASM_SIMP_TAC std_ss [VAR_RES_STACK___IS_EQUAL_UPTO_VALUES_def,
			    VAR_RES_STACK_SPLIT12___REWRITES,
			    bagTheory.IN_SET_OF_BAG, FMERGE_DEF,
		        var_res_permission_THM2, IN_UNION,
		        IN_DIFF] THEN
   ASM_SIMP_TAC (std_ss++boolSimps.CONJ_ss) [COND_REWRITES,
					    var_res_permission_THM2] THEN
   REPEAT STRIP_TAC THEN
   Tactical.REVERSE (Cases_on `(x'' IN FDOM x1)`) THEN1 (
      METIS_TAC[]
   ) THEN
   Cases_on `BAG_IN x'' wpb'` THEN (
      ASM_SIMP_TAC std_ss []
   ) THEN
   `SND (x1 ' x'') = var_res_permission_split (SND (FST x ' x''))` by METIS_TAC[] THEN
   ASM_SIMP_TAC std_ss [var_res_permission_THM2]
]);



val smallfoot_bag_exists_def = Define `

smallfoot_bag_exists exS sfb =

if (!sf x.  BAG_IN sf (sfb x) ==>
           SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS
             exS sf) /\ 
   (!x. FINITE_BAG (sfb x)) then
   {|asl_exists x. (smallfoot_ap_bigstar (BAG_INSERT smallfoot_ap_stack_true (sfb x)))|}
else
   {|smallfoot_ap_emp|}`;





val smallfoot_prop___COND___bag_exists___IMP = store_thm (
"smallfoot_prop___COND___bag_exists___IMP",

``!exS wpb rpb sfb.
  (exS SUBSET SET_OF_BAG (BAG_UNION wpb rpb) /\
  (smallfoot_prop___COND (wpb,rpb)
          (smallfoot_bag_exists exS sfb))) ==>
  (!x. smallfoot_prop___COND (wpb,rpb) (sfb x))``,


SIMP_TAC std_ss [smallfoot_bag_exists_def,
		 smallfoot_prop___COND___REWRITE,
		 FORALL_AND_THM] THEN
REPEAT GEN_TAC THEN
Tactical.REVERSE (
Cases_on `(!sf x.
            BAG_IN sf (sfb x) ==>
            SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS exS sf) /\
         !x. FINITE_BAG (sfb x)`) THEN1 (
   ASM_REWRITE_TAC[] THEN
   SIMP_TAC std_ss [bagTheory.BAG_IN_BAG_INSERT,
		    bagTheory.NOT_IN_EMPTY_BAG,
		    SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___smallfoot_ap_emp]
) THEN
ASM_REWRITE_TAC[] THEN
METIS_TAC[SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___SUBSET]);





val smallfoot_prop___PROP___bag_exists = store_thm (
"smallfoot_prop___PROP___bag_exists",

``!exS wpb rpb sfb s.
  (exS SUBSET SET_OF_BAG (BAG_UNION wpb rpb) /\
  (smallfoot_prop___COND (wpb,rpb)
          (smallfoot_bag_exists exS sfb))) ==>


  (smallfoot_prop___PROP (wpb,rpb) (smallfoot_bag_exists exS sfb) =
  (asl_exists x. smallfoot_prop___PROP (wpb,rpb) (sfb x)))``,


SIMP_TAC std_ss [smallfoot_bag_exists_def,
		 smallfoot_prop___PROP___REWRITE,
		 FORALL_AND_THM, IN_ABS] THEN
REPEAT GEN_TAC THEN
Tactical.REVERSE (
Cases_on `(!sf x.
            BAG_IN sf (sfb x) ==>
            SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS exS sf) /\
         !x. FINITE_BAG (sfb x)`) THEN1 (
   ASM_REWRITE_TAC[] THEN
   SIMP_TAC std_ss [bagTheory.BAG_IN_BAG_INSERT,
		    bagTheory.NOT_IN_EMPTY_BAG,
		    smallfoot_prop___COND___REWRITE,
		    SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___smallfoot_ap_emp]
) THEN
ASM_REWRITE_TAC[] THEN
SIMP_TAC std_ss [smallfoot_ap_bigstar_REWRITE, EXTENSION,
		 GSYM asl_exists___smallfoot_ap_star_THM,
		 smallfoot_ap_star___PROPERTIES,
		 smallfoot_ap_star___ap_stack_true___IDEM2] THEN
SIMP_TAC std_ss [asl_exists_def, IN_ABS, GSYM RIGHT_EXISTS_AND_THM,
		 GSYM LEFT_FORALL_IMP_THM]);




val SMALLFOOT_PROP___STRONG_EXISTS___REWRITE = store_thm (
"SMALLFOOT_PROP___STRONG_EXISTS___REWRITE",

``SMALLFOOT_COND_PROP___STRONG_EQUIV
  (COND_PROP___STRONG_EXISTS (\x. smallfoot_prop (wpb,rpb) (sfb x))) 
  (smallfoot_prop (wpb, rpb) (smallfoot_bag_exists (SET_OF_BAG (BAG_UNION wpb rpb)) sfb))``,


SIMP_TAC std_ss [SMALLFOOT_COND_PROP___STRONG_EQUIV_REWRITE,
		 COND_PROP___STRONG_EXISTS_def,
		 smallfoot_prop___REWRITE,
		 smallfoot_bag_exists_def, FORALL_AND_THM] THEN
Tactical.REVERSE (Cases_on `(!sf x.
             BAG_IN sf (sfb x) ==>
             SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS
               (SET_OF_BAG (BAG_UNION wpb rpb)) sf) /\
          !x. FINITE_BAG (sfb x)`) THEN1 (
   ASM_REWRITE_TAC[] THEN  
   SIMP_TAC std_ss [smallfoot_prop___COND___REWRITE,
		    bagTheory.IN_SET_OF_BAG,
		    bagTheory.BAG_IN_BAG_INSERT,
		    bagTheory.NOT_IN_EMPTY_BAG,
		    SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___smallfoot_ap_emp] THEN
   METIS_TAC[]
) THEN
ASM_REWRITE_TAC[] THEN
FULL_SIMP_TAC std_ss [smallfoot_prop___COND___REWRITE,
		    bagTheory.BAG_IN_BAG_INSERT,
		    bagTheory.NOT_IN_EMPTY_BAG,
		    bagTheory.FINITE_BAG_THM,
		 smallfoot_prop___PROP___REWRITE] THEN

Cases_on `BAG_ALL_DISTINCT rpb` THEN ASM_REWRITE_TAC[] THEN
Cases_on `BAG_ALL_DISTINCT wpb` THEN ASM_REWRITE_TAC[] THEN
Cases_on `(!v. BAG_IN v rpb ==> ~BAG_IN v wpb)` THEN ASM_REWRITE_TAC[] THEN
SIMP_TAC (std_ss++boolSimps.CONJ_ss) [] THEN
CONJ_TAC THENL [
   CONSEQ_HO_REWRITE_TAC ([],[SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___asl_exists_direct,
			  SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___bigstar],[]) THEN
   ASM_SIMP_TAC std_ss [bagTheory.BAG_INSERT_NOT_EMPTY,
		        bagTheory.BAG_IN_BAG_INSERT, DISJ_IMP_THM,
		        FORALL_AND_THM, SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___smallfoot_ap_stack_true] THEN
   ASM_REWRITE_TAC[],

   ONCE_REWRITE_TAC[EXTENSION] THEN
   SIMP_TAC std_ss [
		 IN_ABS, smallfoot_ap_bigstar_REWRITE,
		 smallfoot_ap_star___PROPERTIES,
		 GSYM asl_exists___smallfoot_ap_star_THM] THEN
   SIMP_TAC std_ss [asl_exists_def, IN_ABS, LEFT_EXISTS_AND_THM,
		 RIGHT_EXISTS_AND_THM,
		 smallfoot_ap_star___ap_stack_true___IDEM2]
]);



val SMALLFOOT_PROP___STRONG_EXISTS___REWRITE_TRANS = store_thm (
"SMALLFOOT_PROP___STRONG_EXISTS___REWRITE_TRANS",

``(!x. SMALLFOOT_COND_PROP___STRONG_EQUIV (P x) (smallfoot_prop (wpb,rpb) (sfb x))) ==>

SMALLFOOT_COND_PROP___STRONG_EQUIV
  (COND_PROP___STRONG_EXISTS P) 
  (smallfoot_prop (wpb, rpb) (smallfoot_bag_exists (SET_OF_BAG (BAG_UNION wpb rpb)) sfb))``,

REPEAT STRIP_TAC THEN
`SMALLFOOT_COND_PROP___STRONG_EQUIV 
   (COND_PROP___STRONG_EXISTS (\x. (smallfoot_prop (wpb,rpb) (sfb x))))
   (smallfoot_prop (wpb,rpb)
         (smallfoot_bag_exists (SET_OF_BAG (BAG_UNION wpb rpb)) sfb))` by 
   REWRITE_TAC[SMALLFOOT_PROP___STRONG_EXISTS___REWRITE] THEN
FULL_SIMP_TAC std_ss [SMALLFOOT_COND_PROP___STRONG_EQUIV_REWRITE,
		      COND_PROP___STRONG_EXISTS_def,
		      smallfoot_prop___REWRITE] THEN
STRIP_TAC THEN
FULL_SIMP_TAC std_ss []);




val smallfoot_bag_exists___BAG_UNION_SWAP___left =
store_thm ("smallfoot_bag_exists___BAG_UNION_SWAP___left",
``!wpb rpb exS sfb1 sfb2.

exS SUBSET (SET_OF_BAG (BAG_UNION wpb rpb)) ==>
SMALLFOOT_COND_PROP___STRONG_IMP
(smallfoot_prop (wpb,rpb) (BAG_UNION (smallfoot_bag_exists exS (\x. sfb1 x)) sfb2))
(smallfoot_prop (wpb,rpb) (smallfoot_bag_exists (SET_OF_BAG (BAG_UNION wpb rpb)) (\x. BAG_UNION (sfb1 x) sfb2)))``,

REPEAT STRIP_TAC THEN
SIMP_TAC std_ss [SMALLFOOT_COND_PROP___STRONG_IMP_def,
		 smallfoot_prop___REWRITE,
		 smallfoot_prop___COND_UNION,
		 smallfoot_prop___PROP_UNION] THEN
SIMP_TAC (std_ss++boolSimps.CONJ_ss) [IN_ABS] THEN
MATCH_MP_TAC (prove (``(A /\ (A==> B)) ==> (A /\ B)``, SIMP_TAC std_ss [])) THEN
Tactical.REVERSE CONJ_TAC THENL [
   REPEAT STRIP_TAC THEN
   FULL_SIMP_TAC std_ss [smallfoot_prop___PROP___bag_exists,
			 SUBSET_REFL] THEN
   ONCE_REWRITE_TAC[EXTENSION] THEN
   SIMP_TAC std_ss [IN_ABS, asl_exists_def,
		    GSYM RIGHT_EXISTS_AND_THM,
		    GSYM LEFT_EXISTS_AND_THM] THEN
   `!x'. smallfoot_prop___COND (wpb,rpb) (sfb1 x')` by
      METIS_TAC[smallfoot_prop___COND___bag_exists___IMP] THEN
   METIS_TAC [smallfoot_prop___PROP_UNION,
              smallfoot_prop___COND_UNION, IN_ABS],


   ASM_SIMP_TAC std_ss [smallfoot_prop___COND___REWRITE,
			 smallfoot_bag_exists_def,
		         bagTheory.BAG_IN_BAG_UNION,
		         bagTheory.FINITE_BAG_UNION] THEN
   SIMP_TAC std_ss [COND_RAND, COND_RATOR,
		       bagTheory.FINITE_BAG_THM,
		    bagTheory.BAG_IN_BAG_INSERT,
		    bagTheory.NOT_IN_EMPTY_BAG,
		    DISJ_IMP_THM, FORALL_AND_THM] THEN
   SIMP_TAC std_ss [COND_EXPAND_OR,
		    DISJ_IMP_THM, FORALL_AND_THM,
		    SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___smallfoot_ap_emp] THEN

   STRIP_TAC THEN
   MATCH_MP_TAC (prove (``(A /\ (A ==> C) /\ (A ==> B)) ==> ((A ==> B) /\ C)``,
			  PROVE_TAC[])) THEN
   CONJ_TAC THEN1 METIS_TAC[SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___SUBSET] THEN
   CONJ_TAC THEN1 PROVE_TAC[] THEN
   STRIP_TAC THEN
   Q.PAT_ASSUM `((!sf x. P sf x) /\ X) ==> Q` MP_TAC THEN
   `!sf x. BAG_IN sf (sfb1 x) ==>
       SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS exS sf` by PROVE_TAC[] THEN
   ASM_REWRITE_TAC[] THEN

   Tactical.REVERSE (`(asl_exists x.
    smallfoot_ap_bigstar
      (BAG_INSERT smallfoot_ap_stack_true (BAG_UNION (sfb1 x) sfb2))) =
     smallfoot_ap_star (asl_exists x.
     smallfoot_ap_bigstar
       (BAG_INSERT smallfoot_ap_stack_true (sfb1 x))) (smallfoot_ap_bigstar
       (BAG_INSERT smallfoot_ap_stack_true sfb2))` by ALL_TAC) THEN1 (

      REPEAT STRIP_TAC THEN
      ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___star_MP THEN
      ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___bigstar THEN
      ASM_SIMP_TAC std_ss [bagTheory.BAG_IN_BAG_INSERT,
		       bagTheory.BAG_INSERT_NOT_EMPTY,
		       DISJ_IMP_THM, FORALL_AND_THM,
			   SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___smallfoot_ap_stack_true]
   ) THEN
   SIMP_TAC std_ss [smallfoot_ap_bigstar_REWRITE,
		    smallfoot_ap_bigstar___BAG_UNION,
		    GSYM smallfoot_ap_star___swap_ap_stack_true,
		    GSYM asl_exists___smallfoot_ap_star_THM,
		    REWRITE_RULE [ASSOC_DEF] smallfoot_ap_star___PROPERTIES,
		    smallfoot_ap_star___ap_stack_true___IDEM]
]);




val smallfoot_bag_exists___BAG_UNION_SWAP___right =
store_thm ("smallfoot_bag_exists___BAG_UNION_SWAP___right",
``!wpb rpb exS sfb1 sfb2.

exS SUBSET (SET_OF_BAG (BAG_UNION wpb rpb)) ==>
SMALLFOOT_COND_PROP___STRONG_IMP
(smallfoot_prop (wpb,rpb) (BAG_UNION sfb1 (smallfoot_bag_exists exS (\x. sfb2 x))))
(smallfoot_prop (wpb,rpb) (smallfoot_bag_exists (SET_OF_BAG (BAG_UNION wpb rpb)) (\x. BAG_UNION sfb1 (sfb2 x))))``,

REPEAT STRIP_TAC THEN
ONCE_REWRITE_TAC[bagTheory.COMM_BAG_UNION] THEN
METIS_TAC[smallfoot_bag_exists___BAG_UNION_SWAP___left,
	  bagTheory.COMM_BAG_UNION]);


val smallfoot_bag_exists___BAG_UNION_REWRITE___left =
store_thm ("smallfoot_bag_exists___BAG_UNION_REWRITE___left",
``!wpb rpb exS sfb1 sfb2.

exS SUBSET (SET_OF_BAG (BAG_UNION wpb rpb)) ==>
SMALLFOOT_COND_PROP___STRONG_IMP
(smallfoot_prop (wpb,rpb) (BAG_UNION (smallfoot_bag_exists exS (\x. sfb1 x)) sfb2))
(COND_PROP___STRONG_EXISTS (\x. smallfoot_prop (wpb,rpb) (BAG_UNION (sfb1 x) sfb2)))``,

METIS_TAC[smallfoot_bag_exists___BAG_UNION_SWAP___left,
	  SMALLFOOT_COND_PROP___STRONG_EQUIV_def,
	  SMALLFOOT_COND_PROP___STRONG_IMP___TRANS,
          SMALLFOOT_PROP___STRONG_EXISTS___REWRITE]);




val smallfoot_bag_exists___BAG_UNION_REWRITE___right =
store_thm ("smallfoot_bag_exists___BAG_UNION_REWRITE___right",
``!wpb rpb exS sfb1 sfb2.

exS SUBSET (SET_OF_BAG (BAG_UNION wpb rpb)) ==>
SMALLFOOT_COND_PROP___STRONG_IMP
(smallfoot_prop (wpb,rpb) (BAG_UNION sfb1 (smallfoot_bag_exists exS (\x. sfb2 x))))
(COND_PROP___STRONG_EXISTS (\x. smallfoot_prop (wpb,rpb) (BAG_UNION sfb1 (sfb2 x))))``,

REPEAT STRIP_TAC THEN
ONCE_REWRITE_TAC[bagTheory.COMM_BAG_UNION] THEN
METIS_TAC[smallfoot_bag_exists___BAG_UNION_REWRITE___left,
          bagTheory.COMM_BAG_UNION]);






val SMALLFOOT_PROP_IMPLIES___sfb_split___bag_exists_ELIM =
store_thm ("SMALLFOOT_PROP_IMPLIES___sfb_split___bag_exists_ELIM",
``!sr wpb rpb wpb' sfb_context sfb sfb' sfb_restP exS.

(exS SUBSET SET_OF_BAG (BAG_UNION wpb rpb)) ==>

((?x.
SMALLFOOT_PROP_IMPLIES sr (wpb,rpb) wpb' sfb_context sfb (sfb' x)
  sfb_restP) ==>
SMALLFOOT_PROP_IMPLIES sr (wpb,rpb) wpb' sfb_context sfb (smallfoot_bag_exists exS (\x. sfb' x))
  sfb_restP)``,


SIMP_TAC std_ss [SMALLFOOT_PROP_IMPLIES_def,
		 RIGHT_EXISTS_IMP_THM] THEN
REPEAT STRIP_TAC THEN
FULL_SIMP_TAC std_ss [smallfoot_prop___COND_UNION] THEN
Q.EXISTS_TAC `sfb_rest` THEN
ASM_REWRITE_TAC[] THEN
STRIP_TAC THEN
`smallfoot_prop___COND (wpb,rpb) (sfb' x)` 
   by METIS_TAC[smallfoot_prop___COND___bag_exists___IMP] THEN
FULL_SIMP_TAC std_ss [] THEN
GEN_TAC THEN STRIP_TAC THEN
Q.PAT_ASSUM `!s. X s` (MP_TAC o Q.SPEC `s`) THEN
ASM_SIMP_TAC std_ss [] THEN
REPEAT STRIP_TAC THEN

`smallfoot_prop___COND (wpb,rpb) sfb_rest` by ALL_TAC THEN1 (
   FULL_SIMP_TAC std_ss [smallfoot_prop___COND___REWRITE] THEN
   REPEAT STRIP_TAC THEN
   MATCH_MP_TAC SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___SUBSET THEN
   Q.EXISTS_TAC `SET_OF_BAG (BAG_UNION (BAG_DIFF wpb wpb') (BAG_DIFF rpb wpb'))` THEN
   ASM_SIMP_TAC std_ss [SUBSET_DEF,  bagTheory.IN_SET_OF_BAG, DISJ_IMP_THM,
		        bagTheory.BAG_IN_BAG_UNION, BAG_IN___BAG_DIFF___ALL_DISTINCT]
) THEN
Q.PAT_ASSUM `smallfoot_prop___PROP X Y s` MP_TAC THEN
ASM_SIMP_TAC std_ss [smallfoot_prop___PROP_UNION,
		     smallfoot_prop___COND_UNION, IN_ABS,
		     GSYM RIGHT_EXISTS_AND_THM] THEN
STRIP_TAC THEN
Q.EXISTS_TAC `h1` THEN
Q.EXISTS_TAC `h1'` THEN
Q.EXISTS_TAC `h2'` THEN
ASM_SIMP_TAC std_ss [smallfoot_prop___PROP___bag_exists,
		     asl_bool_EVAL] THEN
Q.EXISTS_TAC `x` THEN
ASM_SIMP_TAC std_ss []);



val SMALLFOOT_PROP_IMPLIES___sfb_restP___bag_exists =
store_thm ("SMALLFOOT_PROP_IMPLIES___sfb_restP___bag_exists",
``!wpb rpb sfb_ex sfb prog Q exS.

(exS SUBSET SET_OF_BAG (BAG_UNION wpb rpb)) ==>

((!x. SMALLFOOT_COND_HOARE_TRIPLE 
    (smallfoot_prop (wpb,rpb) (BAG_UNION (sfb_ex x) sfb2)) prog Q) ==>
 (SMALLFOOT_COND_HOARE_TRIPLE 
    (smallfoot_prop (wpb,rpb) (BAG_UNION (smallfoot_bag_exists exS (\x. sfb_ex x)) sfb2)) prog Q))
``,


REPEAT GEN_TAC THEN
`?Q_cond Q_pred. Q = (Q_cond, Q_pred)` by (Cases_on `Q` THEN SIMP_TAC std_ss []) THEN
ASM_SIMP_TAC std_ss [SMALLFOOT_COND_HOARE_TRIPLE_def,
		 smallfoot_prop___REWRITE, IN_ABS,
		 smallfoot_prop___COND_UNION,
		     SMALLFOOT_HOARE_TRIPLE_def,
		     FASL_PROGRAM_HOARE_TRIPLE_REWRITE] THEN
REPEAT STRIP_TAC THEN
`!x. smallfoot_prop___COND (wpb,rpb) ((\x. sfb_ex x) x)` by
   METIS_TAC[smallfoot_prop___COND___bag_exists___IMP] THEN
Q.PAT_ASSUM `x IN smallfoot_prop___PROP X Y` MP_TAC THEN
FULL_SIMP_TAC std_ss [smallfoot_prop___PROP_UNION,
		      smallfoot_prop___COND_UNION, IN_ABS,
		      GSYM LEFT_EXISTS_AND_THM,
		      GSYM LEFT_FORALL_IMP_THM,
		      smallfoot_prop___PROP___bag_exists,
		      asl_bool_EVAL] THEN
REPEAT STRIP_TAC THEN
Q.PAT_ASSUM `!x x' t'. XXX x x' t'` HO_MATCH_MP_TAC THEN
METIS_TAC[]);



val SMALLFOOT_PROP_IMPLIES___sfb_restP___STRENGTHEN = store_thm (
"SMALLFOOT_PROP_IMPLIES___sfb_restP___STRENGTHEN",

``!sr wpb rpb wpb' sfb_context sfb_split sfb_imp sfb_restP sfb_restP'.

((?x. sfb_restP' x) /\
(!x. sfb_restP' x ==> sfb_restP x)) ==>

(
SMALLFOOT_PROP_IMPLIES sr (wpb,rpb) wpb' sfb_context sfb_split sfb_imp
  sfb_restP' ==>
SMALLFOOT_PROP_IMPLIES sr (wpb,rpb) wpb' sfb_context sfb_split sfb_imp
  sfb_restP)``,


SIMP_TAC std_ss [SMALLFOOT_PROP_IMPLIES_def,
		 GSYM MEMBER_NOT_EMPTY, IN_DEF] THEN
REPEAT STRIP_TAC THEN
METIS_TAC[]);


val SMALLFOOT_COND_HOARE_TRIPLE___precond_BAG_UNION_false =
store_thm ("SMALLFOOT_COND_HOARE_TRIPLE___precond_BAG_UNION_false",
``!wpb rpb prog Q.
  (SMALLFOOT_COND_HOARE_TRIPLE (smallfoot_prop (wpb,rpb)
			       (BAG_UNION sfb {|smallfoot_ap_false|}))
     prog Q)``,

Cases_on `Q` THEN
SIMP_TAC std_ss [SMALLFOOT_COND_HOARE_TRIPLE_REWRITE,
		 smallfoot_prop___REWRITE,
		 SMALLFOOT_HOARE_TRIPLE_def,
		 smallfoot_prop___PROP_UNION] THEN
SIMP_TAC std_ss [smallfoot_prop___PROP___REWRITE,
		 smallfoot_ap_bigstar_REWRITE,
		 smallfoot_ap_false___smallfoot_ap_star_THM,
		 smallfoot_ap_false___NOT_IN, IN_ABS] THEN
SIMP_TAC std_ss [FASL_PROGRAM_HOARE_TRIPLE_REWRITE, IN_ABS]);





val IS_SOME___fasla_assume = store_thm ("IS_SOME___fasla_assume",
``
IS_SOME (fasla_assume f P s) =
(s IN P \/ s IN ASL_INTUITIONISTIC_NEGATION f P)``,

SIMP_TAC std_ss [fasla_assume_def] THEN
Cases_on `s IN P` THEN ASM_SIMP_TAC std_ss [] THEN
SIMP_TAC std_ss [COND_RAND, COND_RATOR]);







val SMALLFOOT_COND_INFERENCE___prog_aquire_resource = store_thm ("SMALLFOOT_COND_INFERENCE___prog_aquire_resource",
``!wpb rpb sfb wpb' sfb' c prog Q.


(SMALLFOOT_PP_USED_VARS c SUBSET SET_OF_BAG (BAG_UNION (BAG_UNION wpb' wpb) rpb)) ==>


((
  SMALLFOOT_COND_HOARE_TRIPLE 
    (smallfoot_prop (BAG_UNION wpb' wpb,rpb) 
        (BAG_INSERT (SMALLFOOT_P_PROPOSITION_EVAL c) (BAG_UNION sfb' sfb)))
    prog Q)

 ==>


  SMALLFOOT_COND_HOARE_TRIPLE 
    (smallfoot_prop (wpb,rpb) sfb)
    (fasl_prog_seq 
        (smallfoot_prog_aquire_resource c wpb' sfb')
        prog)
    Q)``,


REPEAT GEN_TAC THEN STRIP_TAC THEN
ASM_SIMP_TAC std_ss [smallfoot_prop_def,
                     GSYM smallfoot_prop_internal___PROG_PROP_TO_BAG] THEN
REPEAT STRIP_TAC THEN
`?Q_ap Q_cond. Q = (Q_cond, Q_ap)` by (Cases_on `Q` THEN SIMP_TAC std_ss []) THEN
FULL_SIMP_TAC std_ss [SMALLFOOT_COND_HOARE_TRIPLE_def, smallfoot_prop___REWRITE,
		      smallfoot_prop_internal_def,
		      GSYM smallfoot_prop___COND_def,
		      smallfoot_prop___COND_UNION,
		      smallfoot_prog_aquire_resource_def,
		      smallfoot_prog_aquire_resource_internal_def] THEN
REPEAT STRIP_TAC THEN

Tactical.REVERSE (Cases_on `smallfoot_prop___COND (wpb',{| |}) sfb'`) THEN1 (
   ASM_SIMP_TAC std_ss [SMALLFOOT_HOARE_TRIPLE_def, IN_ABS,
		        FASL_PROGRAM_HOARE_TRIPLE_REWRITE,
		        FASL_PROGRAM_TRACES_IN_THM, IN_INSERT,
		        IN_ABS, fasl_prog_diverge_def,
		        GSYM fasl_aa_diverge_def,
		        GSYM RIGHT_EXISTS_AND_THM,
		        GSYM LEFT_FORALL_IMP_THM] THEN
   SIMP_TAC list_ss [FASL_TRACE_SEM_diverge, EMPTY_SUBSET]
) THEN
ASM_SIMP_TAC std_ss [SMALLFOOT_HOARE_TRIPLE_def, IN_ABS,
		     FASL_PROGRAM_HOARE_TRIPLE_def,
		     HOARE_TRIPLE_def, fasl_order_THM,
		     FASL_PROGRAM_SEM___prog_seq,
		     FASL_PROGRAM_SEM___prim_command,
		     FASL_ATOMIC_ACTION_SEM_def,
                     EVAL_fasl_prim_command_THM,
		     fasl_prog_best_local_action_def] THEN

ASSUME_TAC FASL_IS_LOCAL_EVAL_ENV___smallfoot_env THEN
FULL_SIMP_TAC std_ss [smallfoot_env_def, FASL_IS_LOCAL_EVAL_ENV_THM,
		      best_local_action_IS_LOCAL,
		      GSYM fasla_materialisation_def,
		      smallfoot_ap_emp_def] THEN
ASM_SIMP_TAC std_ss [GSYM smallfoot_ap_emp_def, GSYM smallfoot_env_def,
		 SOME___fasla_seq, IS_SOME___fasla_assume,
		 fasla_materialisation_THM,
		 GSYM smallfoot_prop___PROP_def] THEN
GEN_TAC THEN STRIP_TAC THEN
Q.ABBREV_TAC `P' = asl_star smallfoot_separation_combinator
           (smallfoot_ap_fix_varset (SET_OF_BAG wpb')
                 (smallfoot_prop___PROP (wpb',{| |}) sfb')) {x}` THEN
Cases_on `P' = EMPTY` THEN1 (
   ASM_SIMP_TAC std_ss [IMAGE_EMPTY, BIGUNION_EMPTY, NOT_IN_EMPTY,
			EMPTY_SUBSET]
) THEN
`!s. s IN P' ==> VAR_RES_STACK___IS_EQUAL_UPTO_VALUES (FST x) (FST s)` by ALL_TAC THEN1 (
   Q.UNABBREV_TAC `P'` THEN   
   SIMP_TAC std_ss [VAR_RES_STACK___IS_EQUAL_UPTO_VALUES_def,
		    asl_star_def, IN_ABS, IN_SING,
		    SOME___smallfoot_separation_combinator,
		    SOME___VAR_RES_STACK_COMBINE,
		    GSYM LEFT_FORALL_IMP_THM,
		    smallfoot_ap_fix_varset_def] THEN
   SIMP_TAC (std_ss++boolSimps.CONJ_ss) [PAIR_FORALL_THM, FMERGE_DEF, IN_UNION,
					 bagTheory.IN_SET_OF_BAG] THEN
   SIMP_TAC std_ss [COND_REWRITES, smallfoot_prop___PROP___REWRITE,
		    bagTheory.NOT_IN_EMPTY_BAG, IN_ABS,
		    VAR_RES_STACK_IS_SEPARATE_def,
		    var_res_sl___has_write_permission_def] THEN
   REPEAT STRIP_TAC THEN
   Q.PAT_ASSUM `!x'. x' IN FDOM x1' /\ x' IN Y ==> X x'` (MP_TAC o Q.SPEC `x'`) THEN
   Q.PAT_ASSUM `!v. BAG_IN v wpb' ==> X v` (MP_TAC o Q.SPEC `x'`) THEN
   ASM_SIMP_TAC std_ss [var_res_permission_THM2]
) THEN

Q.ABBREV_TAC `P'' = BIGUNION
         (IMAGE THE
            (IMAGE
               (fasla_assume smallfoot_separation_combinator
                  (EVAL_fasl_predicate smallfoot_separation_combinator
                     SMALLFOOT_PT_PROPOSITION_pred_map c)) P'))` THEN


MATCH_MP_TAC (prove (``(A /\ (A ==> B)) ==> (A /\ B)``, METIS_TAC[])) THEN
CONJ_TAC THEN1 (
   REPEAT STRIP_TAC THEN
   MP_TAC (Q.SPECL [`c`, `e`] smallfoot_predicate_IS_DECIDED_IN_STATE) THEN
   ASM_SIMP_TAC std_ss [fasl_predicate_IS_DECIDED_IN_STATE_def,
		        XEVAL_fasl_predicate_def,
		        EVAL_fasl_predicate_def, smallfoot_env_def] THEN
   MATCH_MP_TAC (prove (``A ==> ((A ==> B) ==> B)``, SIMP_TAC std_ss [])) THEN
   Tactical.REVERSE (`SET_OF_BAG (BAG_UNION (BAG_UNION wpb' wpb) rpb) SUBSET FDOM (FST e)` by ALL_TAC) THEN1 (
      PROVE_TAC[SUBSET_TRANS]
   ) THEN
   Q.PAT_ASSUM `e IN P'` MP_TAC THEN
   Q.UNABBREV_TAC `P'` THEN
   SIMP_TAC std_ss [asl_star_def, IN_ABS, IN_SING,
		    GSYM LEFT_FORALL_IMP_THM,
		    SOME___smallfoot_separation_combinator,
		    SOME___VAR_RES_STACK_COMBINE, FMERGE_DEF,
		    smallfoot_ap_fix_varset_def, SUBSET_DEF,
		    bagTheory.IN_SET_OF_BAG, bagTheory.BAG_IN_BAG_UNION,
		    IN_UNION] THEN
   GEN_TAC THEN STRIP_TAC THEN GEN_TAC THEN
   Cases_on `BAG_IN x' wpb'` THEN ASM_REWRITE_TAC[] THEN
   Q.PAT_ASSUM `x IN X` MP_TAC THEN
   SIMP_TAC std_ss [smallfoot_prop___PROP___REWRITE,
		    IN_ABS, 
		    SUBSET_DEF, bagTheory.BAG_IN_BAG_UNION,
		    bagTheory.IN_SET_OF_BAG,
		    DISJ_IMP_THM, FORALL_AND_THM,
		    var_res_sl___has_write_permission_def,
		    var_res_sl___has_read_permission_def]
) THEN
STRIP_TAC THEN

`!s. s IN P'' ==> VAR_RES_STACK___IS_EQUAL_UPTO_VALUES (FST x) (FST s)` by ALL_TAC THEN1 (
   Q.UNABBREV_TAC `P''` THEN
   SIMP_TAC std_ss [IN_BIGUNION, IN_IMAGE, GSYM RIGHT_EXISTS_AND_THM,
		    fasla_assume_def, GSYM LEFT_FORALL_IMP_THM] THEN
   REPEAT GEN_TAC THEN
   Cases_on `x' IN P'` THEN ASM_REWRITE_TAC[] THEN
   Q.PAT_ASSUM `!e. e IN P' ==> X e` (MP_TAC o Q.SPEC `x'`) THEN
   ASM_REWRITE_TAC[] THEN
   Cases_on `x' IN
    EVAL_fasl_predicate smallfoot_separation_combinator
      SMALLFOOT_PT_PROPOSITION_pred_map c` THENL [
      ASM_SIMP_TAC std_ss [IN_SING],
      ASM_SIMP_TAC std_ss [NOT_IN_EMPTY]
   ]
) THEN


`smallfoot_prop___COND (BAG_UNION wpb' wpb,rpb) sfb' /\
 smallfoot_prop___COND (BAG_UNION wpb' wpb,rpb) sfb` by ALL_TAC THEN1 (
   Tactical.REVERSE (
      `BAG_DISJOINT wpb' wpb /\ (!v. BAG_IN v rpb ==> ~BAG_IN v wpb')` by ALL_TAC) THEN1 (
   
      FULL_SIMP_TAC std_ss [smallfoot_prop___COND___REWRITE,
	      		 BAG_ALL_DISTINCT_THM, 
			 bagTheory.NOT_IN_EMPTY_BAG,
                         BAG_ALL_DISTINCT___BAG_UNION,
		         bagTheory.BAG_IN_BAG_UNION,
			 bagTheory.BAG_UNION_EMPTY] THEN
      REPEAT STRIP_TAC THENL [
         MATCH_MP_TAC SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___SUBSET THEN
	 Q.EXISTS_TAC `SET_OF_BAG wpb'` THEN
         ASM_SIMP_TAC std_ss [SUBSET_DEF, bagTheory.BAG_IN_BAG_UNION,
			      bagTheory.IN_SET_OF_BAG],


         MATCH_MP_TAC SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___SUBSET THEN
	 Q.EXISTS_TAC `SET_OF_BAG (BAG_UNION wpb rpb)` THEN
         ASM_SIMP_TAC std_ss [SUBSET_DEF, bagTheory.BAG_IN_BAG_UNION,
			      bagTheory.IN_SET_OF_BAG, DISJ_IMP_THM]
     ]
   ) THEN

   Q.PAT_ASSUM `~(P' = EMPTY)` MP_TAC THEN
   Q.PAT_ASSUM `x IN X` MP_TAC THEN
   Q.UNABBREV_TAC `P'` THEN
   SIMP_TAC std_ss [GSYM MEMBER_NOT_EMPTY,
		    asl_star_def, IN_ABS, IN_SING,
		    smallfoot_prop___PROP___REWRITE,
		    GSYM smallfoot_prop___PROP_def,
		    bagTheory.NOT_IN_EMPTY_BAG,
		    SOME___smallfoot_separation_combinator,
		    SOME___VAR_RES_STACK_COMBINE,
		    smallfoot_ap_fix_varset_def] THEN
   SIMP_TAC std_ss [PAIR_EXISTS_THM,
		    var_res_sl___has_read_permission_def,
		    var_res_sl___has_write_permission_def,
		    bagTheory.BAG_DISJOINT,
		    DISJOINT_DEF, EXTENSION, NOT_IN_EMPTY,
		    IN_INTER, bagTheory.IN_SET_OF_BAG] THEN
   REPEAT STRIP_TAC THENL [
     CCONTR_TAC THEN
     Q.PAT_ASSUM `VAR_RES_STACK_IS_SEPARATE x1' (FST x)` MP_TAC THEN
     FULL_SIMP_TAC std_ss [VAR_RES_STACK_IS_SEPARATE_def] THEN
     Q.EXISTS_TAC `x'` THEN
     ASM_SIMP_TAC std_ss [var_res_permission_THM2],


     Q.PAT_ASSUM `VAR_RES_STACK_IS_SEPARATE x1' (FST x)` MP_TAC THEN
     FULL_SIMP_TAC std_ss [VAR_RES_STACK_IS_SEPARATE_def] THEN
     Q.EXISTS_TAC `v` THEN
     ASM_SIMP_TAC std_ss [var_res_permission_THM2]
   ]
) THEN
FULL_SIMP_TAC std_ss [GSYM smallfoot_ap_emp_def] THEN
Q.ABBREV_TAC `P''' =  (smallfoot_prop_internal___PROP (BAG_UNION wpb' wpb,rpb) ({},{}) 
               [c] (BAG_UNION sfb' sfb) smallfoot_ap_emp)` THEN
Tactical.REVERSE (`!s. s IN P'' ==> s IN P'''` by ALL_TAC) THEN1 (
   Q.PAT_ASSUM `SMALLFOOT_HOARE_TRIPLE X1 X2 X3 prog Y` MP_TAC THEN
   SIMP_TAC std_ss [SMALLFOOT_HOARE_TRIPLE_def, FASL_PROGRAM_HOARE_TRIPLE_def,
		    HOARE_TRIPLE_def, IN_ABS, fasl_order_THM,
		    SUBSET_DEF, IN_BIGUNION] THEN
   SIMP_TAC std_ss [IN_IMAGE, GSYM RIGHT_EXISTS_AND_THM,
		    GSYM LEFT_FORALL_IMP_THM] THEN
   REPEAT STRIP_TAC THEN (
     RES_TAC THEN
     RES_TAC THEN
     FULL_SIMP_TAC std_ss []
   ) THEN
   `VAR_RES_STACK___IS_EQUAL_UPTO_VALUES (FST x'') (FST x')` by METIS_TAC[] THEN
   METIS_TAC[VAR_RES_STACK___IS_EQUAL_UPTO_VALUES___TRANS]
) THEN

Q.UNABBREV_TAC `P''` THEN
SIMP_TAC std_ss [IN_BIGUNION, 
		 IN_IMAGE, GSYM RIGHT_EXISTS_AND_THM, IN_ABS,
		 bagTheory.NOT_IN_EMPTY_BAG, fasla_assume_def,
                 GSYM LEFT_FORALL_IMP_THM] THEN
REPEAT GEN_TAC THEN
Tactical.REVERSE (Cases_on `x' IN
         EVAL_fasl_predicate smallfoot_separation_combinator
           SMALLFOOT_PT_PROPOSITION_pred_map c`) THEN1 (
   Cases_on `x' IN P'` THEN ASM_REWRITE_TAC[] THEN
   RES_TAC THEN
   ASM_SIMP_TAC std_ss [NOT_IN_EMPTY]
) THEN
ASM_SIMP_TAC std_ss [IN_SING] THEN
Q.UNABBREV_TAC `P'''` THEN
Q.UNABBREV_TAC `P'` THEN
Q.PAT_ASSUM `x IN X` MP_TAC THEN

ASM_SIMP_TAC list_ss [smallfoot_prop_internal___PROP_def,
		 NOT_IN_EMPTY, IN_ABS,
		 smallfoot_prop___PROP___REWRITE,
		 bagTheory.NOT_IN_EMPTY_BAG,
		 XEVAL_fasl_predicate_def,
		 smallfoot_env_def,
		 bagTheory.BAG_IN_BAG_UNION,
		 DISJ_IMP_THM, FORALL_AND_THM,
		 asl_star_def, smallfoot_ap_fix_varset_def,
		 IN_SING] THEN
REPEAT STRIP_TAC THENL [
   RES_TAC THEN
   FULL_SIMP_TAC std_ss [SOME___smallfoot_separation_combinator,
			 SOME___VAR_RES_STACK_COMBINE,
                         var_res_sl___has_write_permission_def,
			 FMERGE_DEF, IN_UNION, bagTheory.IN_SET_OF_BAG,
                         COND_REWRITES] THEN
   Tactical.REVERSE (`~(v IN FDOM (FST x))` by ALL_TAC) THEN1 (
      ASM_REWRITE_TAC[]
   ) THEN
   CCONTR_TAC THEN
   Q.PAT_ASSUM `VAR_RES_STACK_IS_SEPARATE X Y` MP_TAC THEN
   FULL_SIMP_TAC std_ss [VAR_RES_STACK_IS_SEPARATE_def] THEN
   Q.EXISTS_TAC `v` THEN
   ASM_SIMP_TAC std_ss [var_res_permission_THM2, bagTheory.IN_SET_OF_BAG],


   RES_TAC THEN
   FULL_SIMP_TAC std_ss [SOME___smallfoot_separation_combinator,
			 SOME___VAR_RES_STACK_COMBINE,
                         var_res_sl___has_write_permission_def,
			 FMERGE_DEF, IN_UNION, bagTheory.IN_SET_OF_BAG,
                         COND_REWRITES] THEN
   Tactical.REVERSE (`~(BAG_IN v wpb')` by ALL_TAC) THEN1 (
      ASM_REWRITE_TAC[]
   ) THEN
   CCONTR_TAC THEN
   Q.PAT_ASSUM `VAR_RES_STACK_IS_SEPARATE X Y` MP_TAC THEN
   FULL_SIMP_TAC std_ss [VAR_RES_STACK_IS_SEPARATE_def] THEN
   Q.EXISTS_TAC `v` THEN
   ASM_SIMP_TAC std_ss [var_res_permission_THM2, bagTheory.IN_SET_OF_BAG],


   RES_TAC THEN
   FULL_SIMP_TAC std_ss [SOME___smallfoot_separation_combinator,
			 SOME___VAR_RES_STACK_COMBINE,
                         var_res_sl___has_read_permission_def,
			 FMERGE_DEF, IN_UNION, bagTheory.IN_SET_OF_BAG,
                         COND_REWRITES],


   `smallfoot_ap_bigstar
      (BAG_INSERT smallfoot_ap_stack_true
         (BAG_INSERT smallfoot_ap_emp (BAG_UNION sfb' sfb))) =
    smallfoot_ap_star
      (smallfoot_ap_bigstar
         (BAG_INSERT smallfoot_ap_stack_true sfb'))
      (smallfoot_ap_bigstar
         (BAG_INSERT smallfoot_ap_stack_true sfb))` by ALL_TAC THEN1 (
      REPEAT (POP_ASSUM (K ALL_TAC)) THEN
      SIMP_TAC std_ss [smallfoot_ap_bigstar_REWRITE,
		       smallfoot_ap_star___PROPERTIES,
		       smallfoot_ap_bigstar___BAG_UNION] THEN
      METIS_TAC[smallfoot_ap_star___PROPERTIES, COMM_DEF, ASSOC_DEF,
	        smallfoot_ap_star___ap_stack_true___IDEM]
   ) THEN
   ASM_SIMP_TAC std_ss [smallfoot_ap_star_def, asl_star_def, IN_ABS] THEN

   Q.EXISTS_TAC `p` THEN
   Q.EXISTS_TAC `x` THEN
   ASM_SIMP_TAC std_ss [smallfoot_ap_bigstar_REWRITE]
]);


   










val SMALLFOOT_COND_INFERENCE___prog_release_resource = store_thm ("SMALLFOOT_COND_INFERENCE___prog_release_resource",
``!wpb rpb sfb wpb' sfb' prog Q.

 ((SET_OF_BAG wpb') SUBSET (SET_OF_BAG wpb)) ==>


( (
  SMALLFOOT_PROP_IMPLIES T (wpb,rpb) wpb' EMPTY_BAG sfb sfb' 
  (\sfb''. SMALLFOOT_COND_HOARE_TRIPLE 
    (smallfoot_prop (BAG_DIFF wpb wpb',rpb) sfb'') prog Q))

 ==>


  SMALLFOOT_COND_HOARE_TRIPLE 
    (smallfoot_prop (wpb,rpb) sfb)
    (fasl_prog_seq 
        (smallfoot_prog_release_resource wpb' sfb')
        prog)
    Q)``,



REPEAT GEN_TAC THEN
`?Q_ap Q_cond. Q = (Q_cond, Q_ap)` by (Cases_on `Q` THEN SIMP_TAC std_ss []) THEN
ASM_SIMP_TAC std_ss [SMALLFOOT_COND_HOARE_TRIPLE_def,
		 smallfoot_prop___REWRITE, smallfoot_prog_release_resource_def,
                  smallfoot_prog_release_resource_internal_def,
		 SUBSET_DEF, bagTheory.IN_SET_OF_BAG] THEN
REPEAT STRIP_TAC THEN
Cases_on `~smallfoot_prop___COND (wpb',EMPTY_BAG) sfb'` THEN1 (
   ASM_REWRITE_TAC[] THEN
   SIMP_TAC std_ss [SMALLFOOT_HOARE_TRIPLE_def,
		    smallfoot_prog_release_resource_internal_def,
		    FASL_PROGRAM_HOARE_TRIPLE_REWRITE,
		    IN_ABS, FASL_PROGRAM_TRACES_IN_THM,
		    fasl_prog_diverge_def, fasl_prog_prim_command_def,
		    FASL_PROGRAM_TRACES_def, IN_INSERT, IN_BIGUNION,
		    IN_SING, IN_IMAGE, GSYM RIGHT_EXISTS_AND_THM,
		    FASL_PROTO_TRACES_EVAL_IN_THM,
		    GSYM fasl_aa_diverge_def,
		    GSYM LEFT_FORALL_IMP_THM] THEN
   SIMP_TAC list_ss [FASL_TRACE_SEM_diverge, EMPTY_SUBSET]
) THEN
FULL_SIMP_TAC std_ss [] THEN

`smallfoot_prop___COND (wpb,rpb) sfb'` by ALL_TAC THEN1 (
   FULL_SIMP_TAC std_ss [smallfoot_prop___COND___REWRITE, bagTheory.FINITE_BAG_UNION] THEN
   REPEAT STRIP_TAC THEN
   MATCH_MP_TAC SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___SUBSET THEN
   Q.EXISTS_TAC `SET_OF_BAG wpb'` THEN
   FULL_SIMP_TAC std_ss [SUBSET_DEF, bagTheory.BAG_IN_BAG_UNION,
        	        bagTheory.IN_SET_OF_BAG, DISJ_IMP_THM, bagTheory.BAG_UNION_EMPTY]
) THEN

FULL_SIMP_TAC std_ss [SMALLFOOT_PROP_IMPLIES_EXPAND, bagTheory.BAG_UNION_EMPTY] THEN
FULL_SIMP_TAC std_ss [smallfoot_prop___COND_UNION] THEN
`~((\sfb''.
               smallfoot_prop___COND (BAG_DIFF wpb wpb',rpb) sfb'' ==>
               SMALLFOOT_HOARE_TRIPLE (K smallfoot_ap_true) FEMPTY
                 (smallfoot_prop___PROP (BAG_DIFF wpb wpb',rpb) sfb'')
                 prog Q_ap) =
            {})` by ALL_TAC THEN1 (
   SIMP_TAC std_ss [EXTENSION, NOT_IN_EMPTY, IN_ABS] THEN
   Q.EXISTS_TAC `{| smallfoot_ap_false|}` THEN
   SIMP_TAC std_ss [SMALLFOOT_HOARE_TRIPLE_def,
		    FASL_PROGRAM_HOARE_TRIPLE_REWRITE,
		    IN_ABS, smallfoot_prop___PROP___REWRITE,
		    smallfoot_ap_bigstar___BAG_UNION,
		    smallfoot_ap_bigstar_REWRITE,
		    smallfoot_ap_star___PROPERTIES] THEN
   SIMP_TAC std_ss [smallfoot_ap_star_def, asl_star_def,
		    IN_ABS, smallfoot_ap_false___NOT_IN]
) THEN
FULL_SIMP_TAC std_ss [] THEN
POP_ASSUM (K ALL_TAC) THEN


Tactical.REVERSE (Cases_on `smallfoot_prop___COND (wpb,rpb) sfb'' /\
	                     smallfoot_prop___COND (BAG_DIFF wpb wpb',BAG_DIFF rpb wpb')  sfb''`) THEN1 (
   Tactical.REVERSE (`!x. ~(x IN smallfoot_prop___PROP (wpb,rpb) sfb)` by ALL_TAC) THEN1 (
      ASM_SIMP_TAC std_ss [SMALLFOOT_HOARE_TRIPLE_def,
		    FASL_PROGRAM_HOARE_TRIPLE_REWRITE, IN_ABS]
   ) THEN
   FULL_SIMP_TAC std_ss [] THEN
   FULL_SIMP_TAC std_ss [IN_DEF]
) THEN
FULL_SIMP_TAC std_ss [] THEN

`smallfoot_prop___COND (BAG_DIFF wpb wpb',rpb) sfb''` by ALL_TAC THEN1 (
   FULL_SIMP_TAC std_ss [smallfoot_prop___COND___REWRITE, bagTheory.FINITE_BAG_UNION,
			 BAG_IN___BAG_DIFF___ALL_DISTINCT] THEN
   REPEAT STRIP_TAC THEN
   MATCH_MP_TAC SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___SUBSET THEN
   Q.EXISTS_TAC `SET_OF_BAG (BAG_UNION (BAG_DIFF wpb wpb') (BAG_DIFF rpb wpb'))` THEN
   FULL_SIMP_TAC std_ss [SUBSET_DEF, bagTheory.BAG_IN_BAG_UNION,
        	        bagTheory.IN_SET_OF_BAG, DISJ_IMP_THM, bagTheory.BAG_UNION_EMPTY,
			BAG_IN___BAG_DIFF___ALL_DISTINCT]
) THEN
FULL_SIMP_TAC std_ss [] THEN

MATCH_MP_TAC SMALLFOOT_INFERENCE_prog_seq THEN
Q.EXISTS_TAC `smallfoot_prop___PROP (BAG_DIFF wpb wpb',rpb) sfb''` THEN

FULL_SIMP_TAC std_ss [smallfoot_prop___COND_UNION] THEN
SIMP_TAC list_ss [SMALLFOOT_HOARE_TRIPLE_def,
		 fasl_prog_best_local_action_def,
		 IN_ABS, FASL_PROGRAM_HOARE_TRIPLE_def,
		 FASL_PROGRAM_SEM___prim_command,
		 FASL_ATOMIC_ACTION_SEM_def,
                 EVAL_fasl_prim_command_THM,
		 SMALLFOOT_SEPARATION_COMBINATOR___EXTRACT,
		 best_local_action_IS_LOCAL,
		 IS_SEPARATION_COMBINATOR___smallfoot_separation_combinator] THEN
SIMP_TAC std_ss [HOARE_TRIPLE_def, IN_ABS, fasl_order_THM,
		 SOME___best_local_action, SUBSET_DEF, IN_ABS,
		 GSYM smallfoot_ap_star_def, smallfoot_ap_star___PROPERTIES,
		 IN_SING, smallfoot_ap_fix_varset_def] THEN
GEN_TAC THEN STRIP_TAC THEN

`?s0 s1.
    (SOME x = smallfoot_separation_combinator (SOME s0) (SOME s1)) /\
    (FDOM (FST s1) = SET_OF_BAG wpb') /\
    s0 IN smallfoot_prop___PROP (BAG_DIFF wpb wpb',rpb) sfb'' /\
    s1 IN smallfoot_prop___PROP (wpb',{| |}) sfb'` by ALL_TAC THEN1 (

   `x IN smallfoot_prop___PROP (wpb,rpb) (BAG_UNION sfb' sfb'')` by METIS_TAC[IN_DEF] THEN
   POP_ASSUM MP_TAC THEN
   ASM_SIMP_TAC std_ss [smallfoot_prop___PROP_UNION, IN_ABS,
		        smallfoot_prop___COND_UNION, SOME___smallfoot_separation_combinator,
		        PAIR_EXISTS_THM] THEN
   STRIP_TAC THEN
   `?xst xh. x = (xst,xh)` by (Cases_on `x` THEN SIMP_TAC std_ss []) THEN
   Q.EXISTS_TAC `DRESTRICT xst (COMPL (SET_OF_BAG wpb'))` THEN
   Q.EXISTS_TAC `h2` THEN
   Q.EXISTS_TAC `DRESTRICT xst (SET_OF_BAG wpb')` THEN
   Q.EXISTS_TAC `h1` THEN

   FULL_SIMP_TAC std_ss [FDOM_DRESTRICT, DISJOINT_SYM,
			 FUNION___COMM] THEN
   REPEAT STRIP_TAC THENL [
      SIMP_TAC (std_ss++boolSimps.CONJ_ss) [SOME___VAR_RES_STACK_COMBINE,
		       VAR_RES_STACK_IS_SEPARATE_def,
		       DRESTRICT_DEF, IN_INTER, IN_COMPL] THEN
      ONCE_REWRITE_TAC[GSYM fmap_EQ_THM] THEN
      SIMP_TAC std_ss [EXTENSION, FMERGE_DEF, DRESTRICT_DEF,
		       IN_UNION, IN_INTER, IN_COMPL] THEN
      METIS_TAC[],


      ONCE_REWRITE_TAC[EXTENSION] THEN
      SIMP_TAC (std_ss++bool_eq_imp_ss) [IN_INTER,
					 bagTheory.IN_SET_OF_BAG] THEN
      FULL_SIMP_TAC std_ss [smallfoot_prop___PROP___REWRITE,
			    IN_ABS, var_res_sl___has_write_permission_def],


      `BAG_ALL_DISTINCT wpb /\ BAG_ALL_DISTINCT wpb' /\
       BAG_ALL_DISTINCT rpb /\
       (!v. BAG_IN v rpb ==> ~BAG_IN v wpb)` by
         FULL_SIMP_TAC std_ss [smallfoot_prop___COND___REWRITE] THEN
      FULL_SIMP_TAC std_ss [smallfoot_prop___PROP___REWRITE, IN_ABS,
			    bagTheory.NOT_IN_EMPTY_BAG,
			    var_res_sl___has_write_permission_def,
			    var_res_sl___has_read_permission_def,
			    DRESTRICT_DEF, IN_INTER,
			    bagTheory.IN_SET_OF_BAG, IN_COMPL,
			    BAG_IN___BAG_DIFF___ALL_DISTINCT] THEN
      CONJ_TAC THEN1 METIS_TAC[] THEN
      `SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS
           (SET_OF_BAG (BAG_UNION (BAG_DIFF wpb wpb') (BAG_DIFF rpb wpb')))
           (smallfoot_ap_star smallfoot_ap_stack_true
              (smallfoot_ap_bigstar sfb''))` by FULL_SIMP_TAC std_ss [smallfoot_prop___COND___EXPAND] THEN
      POP_ASSUM (MATCH_MP_TAC o (REWRITE_RULE [SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___ALTERNATIVE_DEF_2])) THEN
      Q.EXISTS_TAC `(xst,h2)` THEN
      ASM_SIMP_TAC std_ss [bagTheory.BAG_UNION_EMPTY,
			   DRESTRICT_DEF, IN_INTER, SUBSET_DEF,
			   bagTheory.IN_SET_OF_BAG,
			   IN_COMPL, bagTheory.BAG_IN_BAG_UNION,
			   BAG_IN___BAG_DIFF___ALL_DISTINCT,
			   COND_REWRITES] THEN
      METIS_TAC[],



      FULL_SIMP_TAC std_ss [smallfoot_prop___PROP___REWRITE, IN_ABS,
			    bagTheory.NOT_IN_EMPTY_BAG,
			    var_res_sl___has_write_permission_def,
			    DRESTRICT_DEF, IN_INTER,
			    bagTheory.IN_SET_OF_BAG] THEN
      `SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS
           (SET_OF_BAG (BAG_UNION wpb' EMPTY_BAG))
           (smallfoot_ap_star smallfoot_ap_stack_true
              (smallfoot_ap_bigstar sfb'))` by FULL_SIMP_TAC std_ss [smallfoot_prop___COND___EXPAND] THEN
      POP_ASSUM (MATCH_MP_TAC o (REWRITE_RULE [SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___ALTERNATIVE_DEF_2])) THEN
      Q.EXISTS_TAC `(xst,h1)` THEN
      ASM_SIMP_TAC std_ss [bagTheory.BAG_UNION_EMPTY,
			   DRESTRICT_DEF, IN_INTER, SUBSET_DEF]
  ]
) THEN

CONJ_TAC THEN1 (
   Q.EXISTS_TAC `s0` THEN
   Q.EXISTS_TAC `s1` THEN
   ASM_REWRITE_TAC[]
) THEN
GEN_TAC THEN STRIP_TAC THEN
`x' = s0` by METIS_TAC[] THEN
ASM_SIMP_TAC std_ss [] THEN


`!v. BAG_IN v wpb' ==> var_res_sl___has_write_permission v (FST s1)` by ALL_TAC THEN1 (
   FULL_SIMP_TAC std_ss [smallfoot_prop___PROP___REWRITE,
			IN_ABS]
) THEN
FULL_SIMP_TAC std_ss [VAR_RES_STACK___IS_EQUAL_UPTO_VALUES_def,
		      SOME___smallfoot_separation_combinator,
		      SOME___VAR_RES_STACK_COMBINE,
		      FMERGE_DEF, IN_UNION, IN_ABS,
		      bagTheory.IN_SET_OF_BAG,
		      var_res_sl___has_write_permission_def] THEN
ASM_SIMP_TAC (std_ss++boolSimps.CONJ_ss) [COND_REWRITES] THEN
REPEAT STRIP_TAC THEN
Tactical.REVERSE (`~(VAR_RES_STACK_IS_SEPARATE (FST s0) (FST s1))` by ALL_TAC) THEN

SIMP_TAC std_ss [VAR_RES_STACK_IS_SEPARATE_def, 
		     bagTheory.IN_SET_OF_BAG] THEN
Q.EXISTS_TAC `x''` THEN
ASM_SIMP_TAC std_ss [var_res_permission_THM2]);











val SMALLFOOT_PROP_IMPLIES___FRAME = store_thm ("SMALLFOOT_PROP_IMPLIES___FRAME",
``!wpb rpb wpb' sfb_context sfb_split sfb_imp sfb_restP sr sf.
SMALLFOOT_PROP_IMPLIES sr (wpb,rpb) wpb' sfb_context (BAG_INSERT sf sfb_split) (BAG_INSERT sf sfb_imp) sfb_restP =
SMALLFOOT_PROP_IMPLIES sr (wpb,rpb) wpb' (BAG_INSERT sf sfb_context) sfb_split sfb_imp sfb_restP
``,

SIMP_TAC (std_ss++bool_eq_imp_ss)
                [SMALLFOOT_PROP_IMPLIES_def,
		 smallfoot_prop___COND_UNION,
		 smallfoot_prop___COND_INSERT,
		 bagTheory.BAG_UNION_INSERT] THEN
REPEAT STRIP_TAC THEN
HO_MATCH_MP_TAC (
   prove (``(!x. (P x = Q x)) ==> ((?x. P x) = (?x. Q x))``, METIS_TAC[])) THEN
SIMP_TAC (std_ss++bool_eq_imp_ss) []);




val SMALLFOOT_PROP_IS_EQUIV_FALSE_def =
    Define `SMALLFOOT_PROP_IS_EQUIV_FALSE (wpb,rpb) sfb =
            SMALLFOOT_COND_PROP___EQUIV (smallfoot_prop (wpb,rpb) sfb) cond_prop_false`


val SMALLFOOT_PROP_IS_EQUIV_FALSE___REWRITE =
store_thm ("SMALLFOOT_PROP_IS_EQUIV_FALSE___REWRITE",
``!wpb rpb sfb.
  SMALLFOOT_PROP_IS_EQUIV_FALSE (wpb,rpb) sfb =
  (smallfoot_prop___COND (wpb,rpb) sfb ==>
   !x. ~(x IN smallfoot_prop___PROP (wpb,rpb) sfb))``,


SIMP_TAC (std_ss++bool_eq_imp_ss) [SMALLFOOT_PROP_IS_EQUIV_FALSE_def,
                 SMALLFOOT_COND_PROP___EQUIV_REWRITE,
		  smallfoot_prop___REWRITE,
		  cond_prop_false_def]);


val SMALLFOOT_PROP_IS_EQUIV_FALSE___PROP_IMPLIES_DEF =
store_thm ("SMALLFOOT_PROP_IS_EQUIV_FALSE___PROP_IMPLIES_DEF",
``SMALLFOOT_PROP_IS_EQUIV_FALSE (wpb,rpb) sfb =
  SMALLFOOT_PROP_IMPLIES F (wpb,rpb) EMPTY_BAG EMPTY_BAG sfb {| smallfoot_ap_false |} (K T)``,

SIMP_TAC std_ss [SMALLFOOT_PROP_IS_EQUIV_FALSE_def,
		 SMALLFOOT_PROP_IMPLIES_def,
		 bagTheory.BAG_UNION_EMPTY,
		 bagTheory.BAG_UNION_INSERT,
		 smallfoot_prop___COND_INSERT,
		 smallfoot_prop___PROP___smallfoot_ap_false,
		 SMALLFOOT_COND_PROP___EQUIV_REWRITE,
		 cond_prop_false_def,
		 smallfoot_prop___REWRITE] THEN
Cases_on `smallfoot_prop___COND (wpb,rpb) sfb` THEN ASM_REWRITE_TAC[] THEN
`~(K T = {}:(smallfoot_a_proposition -> num) -> bool)` by ALL_TAC THEN1 (
   SIMP_TAC std_ss [EXTENSION, NOT_IN_EMPTY] THEN
   Q.EXISTS_TAC `ARB` THEN
   SIMP_TAC std_ss [IN_DEF]
) THEN
ASM_SIMP_TAC std_ss [smallfoot_ap_false_def, asl_false_def,
		     EMPTY_DEF, IN_ABS,
		     SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___ALTERNATIVE_DEF_2] THEN
METIS_TAC[IN_DEF]);


val SMALLFOOT_PROP_IS_EQUIV_FALSE___PROP_IMPLIES_DEF2 =
store_thm ("SMALLFOOT_PROP_IS_EQUIV_FALSE___PROP_IMPLIES_DEF2",
``SMALLFOOT_PROP_IS_EQUIV_FALSE (wpb,rpb) sfb =
  SMALLFOOT_PROP_IMPLIES F (wpb,rpb) EMPTY_BAG sfb EMPTY_BAG {| smallfoot_ap_false |} (K T)``,

SIMP_TAC std_ss [SMALLFOOT_PROP_IS_EQUIV_FALSE___PROP_IMPLIES_DEF,
		 SMALLFOOT_PROP_IMPLIES_def,
		 bagTheory.BAG_UNION_EMPTY,
		 bagTheory.BAG_UNION_INSERT,
		 smallfoot_prop___PROP___smallfoot_ap_false]);






val SMALLFOOT_PROP_IS_EQUIV_FALSE___PROP_IMPLIES_IMP = 
store_thm ("SMALLFOOT_PROP_IS_EQUIV_FALSE___PROP_IMPLIES_IMP",
``!wpb rpb wpb' sfb_context sfb_split sfb_imp sfb_restP sr.

SMALLFOOT_PROP_IS_EQUIV_FALSE (wpb,rpb) (BAG_UNION sfb_context sfb_split)
 ==>

(SMALLFOOT_PROP_IMPLIES sr (wpb,rpb) wpb' sfb_context 
   sfb_split sfb_imp sfb_restP)
``,

SIMP_TAC std_ss [SMALLFOOT_PROP_IS_EQUIV_FALSE___REWRITE,
		 SMALLFOOT_PROP_IMPLIES_def] THEN
REPEAT STRIP_TAC THEN
`?sfb_rest. sfb_restP sfb_rest` by ALL_TAC THEN1 (
      Q.PAT_ASSUM `~(sfb_restP = EMPTY)` MP_TAC THEN
      SIMP_TAC std_ss [EXTENSION, NOT_IN_EMPTY, IN_DEF]
) THEN
Q.EXISTS_TAC `sfb_rest` THEN
FULL_SIMP_TAC std_ss [smallfoot_prop___COND_UNION,
		     smallfoot_prop___COND_INSERT] THEN
STRIP_TAC THEN
FULL_SIMP_TAC std_ss [IN_DEF, bagTheory.BAG_UNION_INSERT] THEN
METIS_TAC[bagTheory.COMM_BAG_UNION]);






val SMALLFOOT_PROP_IS_EQUIV_FALSE___INTRO =
store_thm ("SMALLFOOT_PROP_IS_EQUIV_FALSE___INTRO",
``!st wpb rpb wpb' sfb_context sfb_split.
    SMALLFOOT_PROP_IMPLIES st (wpb,rpb) wpb' sfb_context sfb_split {|smallfoot_ap_false|} (K T) =
    SMALLFOOT_PROP_IS_EQUIV_FALSE (wpb,rpb) (BAG_UNION sfb_context sfb_split)``,

REPEAT GEN_TAC THEN
SIMP_TAC std_ss [SMALLFOOT_PROP_IS_EQUIV_FALSE___PROP_IMPLIES_DEF,
		 SMALLFOOT_PROP_IMPLIES_def,
		 bagTheory.BAG_UNION_INSERT,
		 bagTheory.BAG_UNION_EMPTY,
		 smallfoot_prop___PROP___smallfoot_ap_false] THEN
SIMP_TAC std_ss [smallfoot_ap_false_def, asl_false_def, EMPTY_DEF] THEN
METIS_TAC[bagTheory.COMM_BAG_UNION]);







val SMALLFOOT_PROP_IMPLIES___SOLVE = store_thm ("SMALLFOOT_PROP_IMPLIES___SOLVE",
``!wpb rpb wpb' sfb_context sfb_split sfb_rest sr.

(smallfoot_prop___WEAK_COND wpb rpb ==>
 BAG_EVERY (SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS
           ((SET_OF_BAG wpb UNION SET_OF_BAG rpb) DIFF (SET_OF_BAG wpb'))) sfb_split) ==>
((sfb_restP sfb_split) \/ (SMALLFOOT_PROP_IS_EQUIV_FALSE (wpb,rpb) (BAG_UNION sfb_context sfb_split)) ==>
SMALLFOOT_PROP_IMPLIES sr (wpb,rpb) wpb' sfb_context sfb_split EMPTY_BAG sfb_restP)
``,


SIMP_TAC (std_ss++bool_eq_imp_ss)
                [SMALLFOOT_PROP_IMPLIES_def,
		 bagTheory.BAG_UNION_EMPTY,
		 bagTheory.FINITE_BAG_UNION,
		 BAG_IN___BAG_DIFF___ALL_DISTINCT,
	         BAG_ALL_DISTINCT___DIFF,
		 BAG_EVERY_def,
		 bagTheory.FINITE_EMPTY_BAG,
		 bagTheory.NOT_IN_EMPTY_BAG,
		 smallfoot_prop___WEAK_COND_def,
                 smallfoot_prop___COND___REWRITE,
		 SMALLFOOT_PROP_IS_EQUIV_FALSE___REWRITE] THEN
REPEAT STRIP_TAC THENL [
   Q.EXISTS_TAC `sfb_split` THEN
   ASM_SIMP_TAC std_ss [] THEN
   REPEAT STRIP_TAC THEN
   Tactical.REVERSE (`(SET_OF_BAG (BAG_UNION (BAG_DIFF wpb wpb') (BAG_DIFF rpb wpb'))) =
		   (SET_OF_BAG wpb UNION SET_OF_BAG rpb DIFF SET_OF_BAG wpb')` by ALL_TAC) THEN1 (
     ASM_SIMP_TAC std_ss []
   ) THEN
   ONCE_REWRITE_TAC[EXTENSION] THEN
   FULL_SIMP_TAC std_ss [BAG_IN___BAG_DIFF___ALL_DISTINCT,
		 IN_UNION, IN_DIFF,
		 bagTheory.IN_SET_OF_BAG,
		 bagTheory.BAG_IN_BAG_UNION] THEN
   SIMP_TAC (std_ss++bool_eq_imp_ss) [],




   `?sfb_rest. sfb_restP sfb_rest` by ALL_TAC THEN1 (
      Q.PAT_ASSUM `~(sfb_restP = EMPTY)` MP_TAC THEN
      SIMP_TAC std_ss [EXTENSION, NOT_IN_EMPTY, IN_DEF]
   ) THEN
   Q.EXISTS_TAC `sfb_rest` THEN
   `BAG_UNION sfb_split sfb_context =
    BAG_UNION sfb_context sfb_split` by METIS_TAC[bagTheory.COMM_BAG_UNION] THEN
   ASM_SIMP_TAC std_ss [] THEN
   STRIP_TAC THEN
   FULL_SIMP_TAC std_ss [IN_DEF]
]);
  





val SMALLFOOT_PROP_IMPLIES___STRONG_STACK_PROPOSITION_INTRO = store_thm ("SMALLFOOT_PROP_IMPLIES___STRONG_STACK_PROPOSITION_INTRO",
``!sf wpb rpb wpb' sfb_context sfb_split sfb_imp sfb_restP sr.
SMALLFOOT_IS_STRONG_STACK_PROPOSITION sf ==>

((SMALLFOOT_PROP_IMPLIES sr (wpb,rpb) wpb' sfb_context 
   (BAG_INSERT sf sfb_split)
   sfb_imp sfb_restP) =

(SMALLFOOT_PROP_IMPLIES sr (wpb,rpb) wpb' sfb_context
   (BAG_INSERT sf sfb_split)
   (BAG_INSERT sf sfb_imp)
   sfb_restP))``,

SIMP_TAC (std_ss++bool_eq_imp_ss)
                [SMALLFOOT_PROP_IMPLIES_EXPAND,
		 bagTheory.BAG_UNION_INSERT] THEN
REPEAT STRIP_TAC THEN
HO_MATCH_MP_TAC (prove (``(!x. (P x = Q x)) ==>
		          ((?x. P x) = (?x. Q x))``,
			SIMP_TAC std_ss [])) THEN
SIMP_TAC (std_ss++bool_eq_imp_ss) [smallfoot_prop___COND_INSERT,
		 smallfoot_prop___COND_UNION] THEN
REPEAT STRIP_TAC THEN
HO_MATCH_MP_TAC (prove (``(!x. Y x = Z x) ==> ((!x. Y x) = (!x. Z x))``, METIS_TAC[])) THEN
SIMP_TAC (std_ss++bool_eq_imp_ss) [] THEN
REPEAT STRIP_TAC THEN
Q.PAT_ASSUM `smallfoot_prop___PROP (wpb,rpb) X s` MP_TAC THEN
FULL_SIMP_TAC std_ss [smallfoot_prop___PROP_INSERT,
		      smallfoot_prop___COND_INSERT,
		      smallfoot_prop___COND_UNION] THEN
Q.PAT_ASSUM `SMALLFOOT_IS_STRONG_STACK_PROPOSITION sf` (fn thm =>
   ONCE_REWRITE_TAC[REWRITE_RULE [SMALLFOOT_IS_STRONG_STACK_PROPOSITION___EQ_REWRITE] thm]) THEN
SIMP_TAC std_ss [DISJOINT_EMPTY, FDOM_FEMPTY, FUNION_FEMPTY_1,
		 IN_DEF]);




val SMALLFOOT_PROP_IMPLIES___STRONG_STACK_PROPOSITION___TO_CONTEXT = store_thm ("SMALLFOOT_PROP_IMPLIES___STRONG_STACK_PROPOSITION___TO_CONTEXT",
``!wpb rpb wpb' sfb_context sfb_split sfb_imp sfb_restP sr sf.


SMALLFOOT_IS_STRONG_STACK_PROPOSITION sf ==>

((SMALLFOOT_PROP_IMPLIES sr (wpb,rpb) wpb' sfb_context 
   (BAG_INSERT sf sfb_split)
   sfb_imp sfb_restP) =

(SMALLFOOT_PROP_IMPLIES sr (wpb,rpb) wpb'
   (BAG_INSERT sf sfb_context)
   sfb_split sfb_imp
   sfb_restP))``,

REPEAT STRIP_TAC THEN
MP_TAC (Q.SPEC `sf`  SMALLFOOT_PROP_IMPLIES___STRONG_STACK_PROPOSITION_INTRO) THEN
ASM_REWRITE_TAC[] THEN
STRIP_TAC THEN
ONCE_ASM_REWRITE_TAC[] THEN
REWRITE_TAC [SMALLFOOT_PROP_IMPLIES___FRAME]);




val SMALLFOOT_PROP_IMPLIES___STRONG_STACK_PROPOSITION___CONTEXT_FRAME = store_thm ("SMALLFOOT_PROP_IMPLIES___STRONG_STACK_PROPOSITION___CONTEXT_FRAME",
``!wpb rpb wpb' sfb_context sfb_split sfb_imp sfb_restP sr sf.


SMALLFOOT_IS_STRONG_STACK_PROPOSITION sf ==>

((SMALLFOOT_PROP_IMPLIES sr (wpb,rpb) wpb' (BAG_INSERT sf sfb_context)
   sfb_split
   (BAG_INSERT sf sfb_imp) sfb_restP) =

(SMALLFOOT_PROP_IMPLIES sr (wpb,rpb) wpb'
   (BAG_INSERT sf sfb_context)
   sfb_split sfb_imp
   sfb_restP))``,


PROVE_TAC[SMALLFOOT_PROP_IMPLIES___STRONG_STACK_PROPOSITION___TO_CONTEXT,
	  SMALLFOOT_PROP_IMPLIES___FRAME]);






val SMALLFOOT_PROP_IMPLIES___COND_PROP_IMP___split =
store_thm ("SMALLFOOT_PROP_IMPLIES___COND_PROP_IMP___split",
``!wpb rpb wpb' sfb_context  sfb_split  sfb_imp 
                sfb_split' sfb_restP sr.

(SMALLFOOT_COND_PROP___IMP (smallfoot_prop (wpb,rpb) sfb_split)
                           (smallfoot_prop (wpb,rpb) sfb_split')) ==>

((SMALLFOOT_PROP_IMPLIES sr (wpb,rpb) wpb' 
   sfb_context sfb_split' sfb_imp sfb_restP) ==>
(SMALLFOOT_PROP_IMPLIES sr (wpb,rpb) wpb' 
   sfb_context sfb_split sfb_imp sfb_restP))
``,


REPEAT STRIP_TAC THEN
FULL_SIMP_TAC (std_ss++boolSimps.CONJ_ss)
   [SMALLFOOT_PROP_IMPLIES_def, 
    smallfoot_prop___COND_UNION,
    smallfoot_prop___PROP_UNION,
    IN_ABS, GSYM RIGHT_EXISTS_AND_THM,
    GSYM LEFT_FORALL_IMP_THM] THEN
REPEAT STRIP_TAC THEN
FULL_SIMP_TAC std_ss [] THEN
Q.EXISTS_TAC `sfb_rest` THEN
ASM_REWRITE_TAC[] THEN
STRIP_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
`?sst sh. s = (sst,sh)` by (Cases_on `s` THEN SIMP_TAC std_ss []) THEN
FULL_SIMP_TAC (std_ss++boolSimps.CONJ_ss) [SMALLFOOT_COND_PROP___IMP_def,
		      smallfoot_prop___REWRITE] THEN

`smallfoot_prop___COND (wpb,rpb) sfb_split' /\
 (sst,h1) IN smallfoot_prop___PROP (wpb,rpb) sfb_split'` by ALL_TAC THEN1 (
   RES_TAC THEN
   ASM_REWRITE_TAC[]
) THEN
FULL_SIMP_TAC std_ss [] THEN
Q.PAT_ASSUM `!s h1 h2. X s h1 h2` (MP_TAC o Q.SPECL [`s`, `h1`, `h2`]) THEN
ASM_SIMP_TAC std_ss []);







val SMALLFOOT_PROP_IMPLIES___equal_const = store_thm ("SMALLFOOT_PROP_IMPLIES___equal_const",
``!v c wpb rpb wpb' sfb_context sfb_split sfb_imp sfb_restP sr.

(v IN (SET_OF_BAG (BAG_UNION wpb rpb))) ==>

((SMALLFOOT_PROP_IMPLIES sr (wpb,rpb) wpb' 
   (BAG_INSERT
      (smallfoot_ap_equal (smallfoot_ae_var v) (smallfoot_ae_const c))
      sfb_context)
   sfb_split
   (BAG_IMAGE (smallfoot_ap_var_update v c) sfb_imp)
   sfb_restP) ==>

(SMALLFOOT_PROP_IMPLIES sr (wpb,rpb) wpb' sfb_context 
   (BAG_INSERT
      (smallfoot_ap_equal (smallfoot_ae_var v) (smallfoot_ae_const c))
      sfb_split)
   sfb_imp sfb_restP))
``,


SIMP_TAC std_ss [SMALLFOOT_PROP_IMPLIES_EXPAND, bagTheory.BAG_UNION_INSERT] THEN
SIMP_TAC std_ss [smallfoot_prop___COND_INSERT, smallfoot_prop___COND_UNION] THEN
SIMP_TAC (std_ss++bool_eq_imp_ss) [] THEN
REPEAT STRIP_TAC THEN
FULL_SIMP_TAC std_ss [] THEN
Q.EXISTS_TAC `sfb_rest` THEN
ASM_REWRITE_TAC[] THEN
STRIP_TAC THEN GEN_TAC THEN STRIP_TAC THEN
FULL_SIMP_TAC std_ss [] THEN

`smallfoot_prop___COND (wpb,rpb)
            (BAG_IMAGE (smallfoot_ap_var_update v c) sfb_imp)` by ALL_TAC THEN1 (
   FULL_SIMP_TAC std_ss [smallfoot_prop___COND___REWRITE,
			 bagTheory.BAG_IMAGE_FINITE,
			 bagTheory.BAG_IN_FINITE_BAG_IMAGE,
			 GSYM LEFT_FORALL_IMP_THM] THEN
   REPEAT STRIP_TAC THEN
   MATCH_MP_TAC SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___smallfoot_ap_var_update THEN
   ASM_SIMP_TAC std_ss []
) THEN
FULL_SIMP_TAC std_ss [] THEN
Q.PAT_ASSUM `!s. X s` (MP_TAC o Q.SPEC `s`) THEN
ASM_SIMP_TAC std_ss [] THEN STRIP_TAC THEN
Q.PAT_ASSUM `smallfoot_prop___PROP (wpb,rpb) XX s` MP_TAC THEN
ASM_SIMP_TAC std_ss [smallfoot_prop___COND_UNION,
		     smallfoot_prop___COND_INSERT,
		     smallfoot_prop___PROP_UNION,
		     smallfoot_prop___PROP_INSERT,
		     IN_ABS,
		     smallfoot_ap_equal_def,
		     smallfoot_ap_binexpression_def,
		     smallfoot_a_stack_proposition_def,
		     LET_THM, smallfoot_ae_const_def,
		     FDOM_FEMPTY, DISJOINT_EMPTY,
		     FUNION_FEMPTY_1, smallfoot_ae_var_def,
		     GSYM RIGHT_EXISTS_AND_THM,
		     COND_NONE_SOME_REWRITES] THEN
SIMP_TAC (std_ss++boolSimps.CONJ_ss) [] THEN
STRIP_TAC THEN
FULL_SIMP_TAC std_ss [] THEN
Q.EXISTS_TAC `h1'` THEN
Q.EXISTS_TAC `h1''` THEN
Q.EXISTS_TAC `h2'` THEN
ASM_SIMP_TAC std_ss [] THEN

Q.PAT_ASSUM `(FST s,h1') IN X` MP_TAC THEN
`FINITE_BAG sfb_imp /\ !sf. BAG_IN sf sfb_imp ==> SMALLFOOT_AP_PERMISSION_UNIMPORTANT sf` by ALL_TAC THEN1 (
   FULL_SIMP_TAC std_ss [
      smallfoot_prop___COND___REWRITE,
      SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS_def]
) THEN
ASM_SIMP_TAC std_ss [smallfoot_prop___PROP___REWRITE, 
 IN_ABS, smallfoot_ap_var_update___smallfoot_ap_bigstar___ap_true,
 smallfoot_ap_var_update_def] THEN

Q.ABBREV_TAC `P = smallfoot_ap_star smallfoot_ap_stack_true (smallfoot_ap_bigstar sfb_imp)` THEN
REPEAT STRIP_TAC THEN
`SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS
             (SET_OF_BAG (BAG_UNION wpb rpb)) P` by
   FULL_SIMP_TAC std_ss [smallfoot_prop___COND___EXPAND] THEN
POP_ASSUM (MATCH_MP_TAC o REWRITE_RULE[SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___ALTERNATIVE_DEF_2]) THEN

Q.EXISTS_TAC `SMALLFOOT_STATE_UPDATE_VAR v c var_res_write_permission
             (FST s,h1')` THEN

ASM_REWRITE_TAC[] THEN
ASM_SIMP_TAC std_ss [SMALLFOOT_STATE_UPDATE_VAR_def,
		 SMALLFOOT_STACK_UPDATE_VAR_def, FDOM_FUPDATE,
		    SUBSET_DEF, IN_INTER, IN_INSERT,
		    RIGHT_AND_OVER_OR, DISJ_IMP_THM,
		    FORALL_AND_THM, FAPPLY_FUPDATE_THM,
		    COND_REWRITES]
);




val SMALLFOOT_PROP_IMPLIES___WEAK_COND_REWRITE = store_thm ("SMALLFOOT_PROP_IMPLIES___WEAK_COND_REWRITE",
``!wpb rpb wpb' sfb_context sfb_split sfb_imp sfb_restP sr.

(smallfoot_prop___WEAK_COND wpb rpb ==>
 (sfb_context = sfb_context') /\
 (sfb_split = sfb_split') /\
 (sfb_imp = sfb_imp')) ==>

((SMALLFOOT_PROP_IMPLIES sr (wpb,rpb) wpb' 
   sfb_context sfb_split sfb_imp sfb_restP) =
 (SMALLFOOT_PROP_IMPLIES sr (wpb,rpb) wpb' 
   sfb_context' sfb_split' sfb_imp' sfb_restP))
``,

REPEAT STRIP_TAC THEN
Cases_on `smallfoot_prop___WEAK_COND wpb rpb` THEN1 (
   FULL_SIMP_TAC std_ss []
) THEN
`!sfb. ~(smallfoot_prop___COND (wpb,rpb) sfb)` by
  PROVE_TAC[smallfoot_prop___WEAK_COND_IMP] THEN
ASM_SIMP_TAC std_ss [SMALLFOOT_PROP_IMPLIES_def]);





val SMALLFOOT_PROP_IMPLIES___COND_PROP_STRONG_IMP___imp =
store_thm ("SMALLFOOT_PROP_IMPLIES___COND_PROP_STRONG_IMP___imp",
``!wpb rpb wpb' sfb_context  sfb_split sfb_imp 
                sfb_imp' sfb_restP sr.

(SMALLFOOT_COND_PROP___STRONG_IMP (smallfoot_prop (wpb,rpb) sfb_imp)
                           (smallfoot_prop (wpb,rpb) sfb_imp')) ==>

((SMALLFOOT_PROP_IMPLIES sr (wpb,rpb) wpb' 
   sfb_context sfb_split sfb_imp' sfb_restP) ==>
(SMALLFOOT_PROP_IMPLIES sr (wpb,rpb) wpb' 
   sfb_context sfb_split sfb_imp sfb_restP))
``,


REPEAT STRIP_TAC THEN
FULL_SIMP_TAC (std_ss++boolSimps.CONJ_ss)
   [SMALLFOOT_PROP_IMPLIES_EXPAND, 
    smallfoot_prop___COND_UNION,
    smallfoot_prop___PROP_UNION,
    IN_ABS, GSYM RIGHT_EXISTS_AND_THM,
    GSYM LEFT_FORALL_IMP_THM,
    SMALLFOOT_COND_PROP___EQUIV_REWRITE,
    smallfoot_prop___REWRITE] THEN
STRIP_TAC THEN FULL_SIMP_TAC std_ss [] THEN
Q.EXISTS_TAC `sfb_rest`  THEN
ASM_REWRITE_TAC[] THEN
STRIP_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
`?sst sh. s = (sst,sh)` by (Cases_on `s` THEN SIMP_TAC std_ss []) THEN
FULL_SIMP_TAC (std_ss++boolSimps.CONJ_ss) [SMALLFOOT_COND_PROP___STRONG_IMP_def,
		      smallfoot_prop___REWRITE] THEN
Q.PAT_ASSUM `smallfoot_prop___COND (wpb,rpb) sfb_imp'` ASSUME_TAC THEN
Q.PAT_ASSUM `X = smallfoot_prop___PROP (wpb,rpb) sfb_imp'` ASSUME_TAC THEN
FULL_SIMP_TAC std_ss [] THEN
Q.PAT_ASSUM `!s h1 h2. X s h1 h2` (MP_TAC o Q.SPECL [`s`, `h1`, `h2`]) THEN
ASM_SIMP_TAC std_ss []);





val SMALLFOOT_PROP_IMPLIES___COND_PROP_STRONG_EQUIV___imp =
store_thm ("SMALLFOOT_PROP_IMPLIES___COND_PROP_STRONG_EQUIV___imp",
``!wpb rpb wpb' sfb_context  sfb_split  sfb_imp 
                sfb_imp' sfb_restP sr.

(SMALLFOOT_COND_PROP___STRONG_EQUIV (smallfoot_prop (wpb,rpb) sfb_imp)
                           (smallfoot_prop (wpb,rpb) sfb_imp')) ==>

((SMALLFOOT_PROP_IMPLIES sr (wpb,rpb) wpb' 
   sfb_context sfb_split sfb_imp' sfb_restP) =
(SMALLFOOT_PROP_IMPLIES sr (wpb,rpb) wpb' 
   sfb_context sfb_split sfb_imp sfb_restP))
``,

REPEAT STRIP_TAC THEN 
METIS_TAC[SMALLFOOT_COND_PROP___STRONG_EQUIV_def,
	  SMALLFOOT_PROP_IMPLIES___COND_PROP_STRONG_IMP___imp]);







val SMALLFOOT_PROP_IMPLIES___stack_true =
store_thm ("SMALLFOOT_PROP_IMPLIES___stack_true",
``!wpb rpb wpb' sfb_context  sfb_split  sfb_imp sfb_rest sr.

((SMALLFOOT_PROP_IMPLIES sr (wpb,rpb) wpb' 
   sfb_context sfb_split (BAG_INSERT smallfoot_ap_stack_true sfb_imp) sfb_restP) =
(SMALLFOOT_PROP_IMPLIES sr (wpb,rpb) wpb' 
   sfb_context sfb_split sfb_imp sfb_restP))
``,

REPEAT STRIP_TAC THEN 
MATCH_MP_TAC SMALLFOOT_PROP_IMPLIES___COND_PROP_STRONG_EQUIV___imp THEN
ONCE_REWRITE_TAC[SMALLFOOT_COND_PROP___STRONG_EQUIV___SYM] THEN
REWRITE_TAC [SMALLFOOT_COND_PROP___STRONG_EQUIV___smallfoot_ap_stack_true]);



val SMALLFOOT_PROP_IMPLIES___empty_heap_cond =
store_thm ("SMALLFOOT_PROP_IMPLIES___empty_heap_cond",
``!wpb rpb wpb' sfb_context  sfb_split  sfb_imp sfb_rest c sr.

((SMALLFOOT_PROP_IMPLIES sr (wpb,rpb) wpb' 
   (BAG_INSERT (smallfoot_ap_empty_heap_cond c) sfb_context) sfb_split sfb_imp sfb_restP) =
(c ==>
(SMALLFOOT_PROP_IMPLIES sr (wpb,rpb) wpb' 
   sfb_context sfb_split sfb_imp sfb_restP)))
``,

REPEAT STRIP_TAC THEN 
SIMP_TAC std_ss [SMALLFOOT_PROP_IMPLIES_EXPAND,
		 smallfoot_prop___COND_INSERT,
		 bagTheory.BAG_UNION_INSERT,
		 SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___smallfoot_ap_empty_heap_cond] THEN
Tactical.REVERSE (Cases_on `c`) THENL [
   SIMP_TAC std_ss [smallfoot_prop___PROP___REWRITE,
		    smallfoot_ap_bigstar_REWRITE,
		    smallfoot_ap_star_def,
		    asl_star_def, IN_ABS,
		    smallfoot_ap_empty_heap_cond_def] THEN
   SIMP_TAC std_ss [EXTENSION, NOT_IN_EMPTY, IN_DEF],


   Cases_on `~(sfb_restP = {})` THEN ASM_REWRITE_TAC[] THEN
   HO_MATCH_MP_TAC (prove (``(!s. (X s = Y s)) ==> ((?s. X s) = (?s. Y s))``,
		     METIS_TAC[])) THEN
   SIMP_TAC (std_ss++bool_eq_imp_ss) [] THEN
   REPEAT STRIP_TAC THEN
   FULL_SIMP_TAC (std_ss++boolSimps.CONJ_ss)
                        [smallfoot_prop___PROP_INSERT,
			 smallfoot_prop___COND_INSERT,
			 smallfoot_prop___COND_UNION,
			 SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___smallfoot_ap_empty_heap_cond] THEN
   SIMP_TAC std_ss [smallfoot_ap_empty_heap_cond_def,
		    IN_ABS, FUNION_FEMPTY_1, DISJOINT_EMPTY,
		    FDOM_FEMPTY] THEN
   SIMP_TAC std_ss [IN_DEF]
]);




val smallfoot_ap_equal_BAG_def = Define `
smallfoot_ap_equal_BAG L L' =
BAG_OF_SET (\x. ?t. (x = smallfoot_ap_equal (L ' t) (L' ' t)) /\ t IN FDOM L /\ t IN FDOM L')`;

    





val SMALLFOOT_PROP_IMPLIES___points_to___points_to___SUBMAP = store_thm ("SMALLFOOT_PROP_IMPLIES___points_to___points_to___SUBMAP",
``!L L' e wpb rpb wpb' sfb_context sfb_split sfb_imp sfb_restP sr.

FEVERY (\(t,a). (t IN FDOM L) /\ (a = L ' t)) L' ==>

((SMALLFOOT_PROP_IMPLIES sr (wpb,rpb) wpb'
   (BAG_INSERT (smallfoot_ap_points_to e L) sfb_context)
   sfb_split sfb_imp
   sfb_restP) ==>

(SMALLFOOT_PROP_IMPLIES sr (wpb,rpb) wpb' sfb_context 
   (BAG_INSERT (smallfoot_ap_points_to e L) sfb_split)
   (BAG_INSERT (smallfoot_ap_points_to e L') sfb_imp) sfb_restP))

``,

SIMP_TAC (std_ss++bool_eq_imp_ss) [SMALLFOOT_PROP_IMPLIES_EXPAND,
		 smallfoot_prop___COND_UNION,
    		 smallfoot_prop___COND_INSERT,
		 bagTheory.BAG_UNION_INSERT] THEN
REPEAT STRIP_TAC THEN
FULL_SIMP_TAC std_ss [] THEN
Q.EXISTS_TAC `sfb_rest` THEN
ASM_REWRITE_TAC[] THEN
STRIP_TAC THEN GEN_TAC THEN STRIP_TAC THEN
FULL_SIMP_TAC std_ss [] THEN
Q.PAT_ASSUM `!s. X s` (MP_TAC o Q.SPEC `s`) THEN
ASM_SIMP_TAC std_ss [] THEN

REPEAT STRIP_TAC THEN
Q.PAT_ASSUM `smallfoot_prop___PROP (wpb, rpb) X s` MP_TAC THEN
ASM_SIMP_TAC std_ss [
   smallfoot_prop___COND_INSERT,
   smallfoot_prop___COND_UNION,
   smallfoot_prop___PROP_INSERT,
   IN_ABS, GSYM RIGHT_EXISTS_AND_THM] THEN
REPEAT STRIP_TAC THEN
Q.EXISTS_TAC `h1` THEN
Q.EXISTS_TAC `h2` THEN
ASM_SIMP_TAC std_ss [] THEN

Q.PAT_ASSUM `(FST s, h1) IN X` MP_TAC THEN
Q.PAT_ASSUM `FEVERY XX L'` MP_TAC THEN

SIMP_TAC (std_ss++boolSimps.CONJ_ss) [smallfoot_ap_points_to_def,
		 IN_ABS, LET_THM, IS_SOME_EXISTS,
		 GSYM LEFT_EXISTS_AND_THM, GSYM RIGHT_EXISTS_AND_THM,
		 GSYM LEFT_FORALL_IMP_THM,
		 FEVERY_DEF] THEN
METIS_TAC[]);






val SMALLFOOT_PROP_IMPLIES___points_to___points_to = store_thm ("SMALLFOOT_PROP_IMPLIES___points_to___points_to",
``!L L' e wpb rpb wpb' sfb_context sfb_split sfb_imp sfb_restP sr.

(((FEVERY (\(t,a). (t IN FDOM L) /\ (a = L ' t)) L' /\
(SMALLFOOT_PROP_IMPLIES sr (wpb,rpb) wpb'
   (BAG_INSERT (smallfoot_ap_points_to e L) sfb_context)
   sfb_split sfb_imp
   sfb_restP)) \/

SMALLFOOT_PROP_IS_EQUIV_FALSE (wpb,rpb) (BAG_UNION sfb_context
   (BAG_INSERT (smallfoot_ap_points_to e L) sfb_split)))
 ==>

(SMALLFOOT_PROP_IMPLIES sr (wpb,rpb) wpb' sfb_context 
   (BAG_INSERT (smallfoot_ap_points_to e L) sfb_split)
   (BAG_INSERT (smallfoot_ap_points_to e L') sfb_imp) sfb_restP))

``,

SIMP_TAC std_ss [DISJ_IMP_THM, SMALLFOOT_PROP_IMPLIES___points_to___points_to___SUBMAP,
		 SMALLFOOT_PROP_IS_EQUIV_FALSE___PROP_IMPLIES_IMP]);







val smallfoot_ap_tree_seg_num___REWRITE_START_EXP = 
store_thm ("smallfoot_ap_tree_seg_num___REWRITE_START_EXP",
``
!n bal tagL startExp endExp startExp' s.
((startExp (FST s) = (startExp' (FST s))) /\
(IS_SOME___SMALLFOOT_AE_USED_VARS startExp) /\
(IS_SOME___SMALLFOOT_AE_USED_VARS startExp') /\
(IS_SOME___SMALLFOOT_AE_USED_VARS endExp) /\
~(tagL = [])) ==>

(s IN (smallfoot_ap_tree_seg_num n bal tagL startExp endExp) =
 s IN (smallfoot_ap_tree_seg_num n bal tagL startExp' endExp))``,
	   

Induct_on `n` THEN (
   SIMP_TAC std_ss [smallfoot_ap_tree_seg_num_def,
		    asl_rec_pred_num_def,
		    smallfoot_ap_equal_def,
		    smallfoot_ap_weak_unequal_def,
		    smallfoot_ap_binexpression_def,
		    smallfoot_a_stack_proposition_def,
		    IN_ABS, asl_bool_EVAL, LET_THM]
) THEN
SIMP_TAC (std_ss++bool_eq_imp_ss) [] THEN
REPEAT GEN_TAC THEN STRIP_TAC THEN

Cases_on `startExp' (FST s)` THEN ASM_SIMP_TAC std_ss [] THEN
Cases_on `endExp (FST s)` THEN ASM_SIMP_TAC std_ss [] THEN
Cases_on `x = x'` THEN ASM_SIMP_TAC std_ss [] THEN


SIMP_TAC std_ss [smallfoot_ap_tree_seg_num_GSYM_REWRITE,
		 MAP_MAP_o, combinTheory.o_DEF] THEN

SIMP_TAC list_ss [asl_choose_pred_args_def,
		 asl_bool_EVAL, IN_ABS] THEN
HO_MATCH_MP_TAC (prove (``(!el. (X el = Y el)) ==>
		          ((?el. X el) = (?el. Y el))``,
			METIS_TAC[])) THEN
SIMP_TAC (std_ss++bool_eq_imp_ss) [asl_bigstar_list_REWRITE] THEN
REPEAT STRIP_TAC THEN
Q.ABBREV_TAC `P = (asl_bigstar_list smallfoot_separation_combinator
            (MAP
               (\startExp.
                  smallfoot_ap_tree_seg_num n bal tagL startExp endExp)
               eL))` THEN

`!e. IS_SOME___SMALLFOOT_AE_USED_VARS e ==>
 SMALLFOOT_AP_PERMISSION_UNIMPORTANT 
   (smallfoot_ap_points_to e (LISTS_TO_FMAP (tagL,eL)))` by ALL_TAC THEN1 (
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC SMALLFOOT_AP_PERMISSION_UNIMPORTANT___points_to THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC FEVERY_LISTS_TO_FMAP THEN
  FULL_SIMP_TAC list_ss [EVERY_MEM, MEM_ZIP,
			 GSYM LEFT_FORALL_IMP_THM,
			 EL_MAP, smallfoot_ae_is_const_def] THEN
  REPEAT STRIP_TAC THEN
  `?n. EL n' eL = smallfoot_ae_const n` by METIS_TAC[] THEN
  ASM_REWRITE_TAC[IS_SOME___SMALLFOOT_AE_USED_VARS___EVAL]
) THEN

`SMALLFOOT_AP_PERMISSION_UNIMPORTANT P` by ALL_TAC THEN1 (
  Q.UNABBREV_TAC `P` THEN
  Q.PAT_ASSUM `LENGTH eL = X` (ASSUME_TAC o GSYM) THEN 
  FULL_SIMP_TAC list_ss [EVERY_MEM, MEM_ZIP,
			 GSYM LEFT_FORALL_IMP_THM,
			 EL_MAP, smallfoot_ae_is_const_def] THEN
  Q.PAT_ASSUM `!n. n < LENGTH eL ==> X n` MP_TAC THEN
  `~(eL = [])` by ALL_TAC THEN1 (
     Cases_on `eL` THEN (
        FULL_SIMP_TAC list_ss [LENGTH_NIL]
     )
  ) THEN
  POP_ASSUM MP_TAC THEN
  Q.SPEC_TAC (`eL`, `L`) THEN
  Induct_on `L` THEN1 (
     REWRITE_TAC[]
  ) THEN
  Cases_on `L` THENL [
     SIMP_TAC list_ss [asl_bigstar_list_REWRITE,
		       GSYM smallfoot_ap_emp_def,
		       GSYM smallfoot_ap_star_def,
		       smallfoot_ap_star___PROPERTIES] THEN
     `!n:num. ((n < 1) = (n = 0))` by ALL_TAC THEN1 (
	 SIMP_TAC arith_ss []
     ) THEN
     ASM_SIMP_TAC list_ss [GSYM LEFT_FORALL_IMP_THM] THEN
     GEN_TAC THEN
     MATCH_MP_TAC SMALLFOOT_AP_PERMISSION_UNIMPORTANT___smallfoot_ap_tree_seg_num THEN
     ASM_SIMP_TAC std_ss [IS_SOME___SMALLFOOT_AE_USED_VARS___EVAL],


     FULL_SIMP_TAC list_ss [asl_bigstar_list_REWRITE,
		       GSYM smallfoot_ap_star_def] THEN
     REPEAT STRIP_TAC THEN
     MATCH_MP_TAC SMALLFOOT_AP_PERMISSION_UNIMPORTANT___star THEN
     CONJ_TAC THENL [
        MATCH_MP_TAC SMALLFOOT_AP_PERMISSION_UNIMPORTANT___smallfoot_ap_tree_seg_num THEN
        Q.PAT_ASSUM `!n. X n` (MP_TAC o Q.SPEC `0`) THEN
        ASM_SIMP_TAC list_ss [IS_SOME___SMALLFOOT_AE_USED_VARS___EVAL,
			      GSYM LEFT_FORALL_IMP_THM],


	Q.PAT_ASSUM `X ==> Y` MATCH_MP_TAC THEN
        REPEAT STRIP_TAC THEN
        Q.PAT_ASSUM `!n. X n` (MP_TAC o Q.SPEC `SUC n'`) THEN
        ASM_SIMP_TAC list_ss []
     ]
  ]
) THEN


ASM_SIMP_TAC std_ss [GSYM smallfoot_ap_star_def,
		     smallfoot_ap_star___PERMISSION_UNIMPORTANT,
		     IN_ABS] THEN
HO_MATCH_MP_TAC (prove (``(!p q. (X p q = Y p q)) ==>
		          ((?p q. X p q) = (?p q. Y p q))``,
			METIS_TAC[])) THEN

SIMP_TAC (std_ss++bool_eq_imp_ss) [] THEN
REPEAT STRIP_TAC THEN
ASM_SIMP_TAC std_ss [smallfoot_ap_points_to_def,
		 IN_ABS, LET_THM]);



val smallfoot_ap_data_list_seg_num___REWRITE_START_EXP = 
store_thm ("smallfoot_ap_data_list_seg_num___REWRITE_START_EXP",
``
!n tl data startExp endExp startExp' s.
((startExp (FST s) = (startExp' (FST s))) /\
(IS_SOME___SMALLFOOT_AE_USED_VARS startExp) /\
(IS_SOME___SMALLFOOT_AE_USED_VARS startExp') /\
(IS_SOME___SMALLFOOT_AE_USED_VARS endExp)) ==>

(s IN (smallfoot_ap_data_list_seg_num n tl startExp data endExp) =
 s IN (smallfoot_ap_data_list_seg_num n tl startExp' data endExp))``,
	   

Induct_on `n` THEN (
   SIMP_TAC std_ss [smallfoot_ap_data_list_seg_num_def,
		    asl_bool_EVAL,
		    smallfoot_ap_equal_def,
		    smallfoot_ap_weak_unequal_def,
		    smallfoot_ap_binexpression_def,
		    smallfoot_a_stack_proposition_def,
		    IN_ABS, LET_THM]
) THEN


SIMP_TAC (std_ss++bool_eq_imp_ss) [] THEN
REPEAT GEN_TAC THEN STRIP_TAC THEN

Cases_on `startExp' (FST s)` THEN ASM_SIMP_TAC std_ss [] THEN
Cases_on `endExp (FST s)` THEN ASM_SIMP_TAC std_ss [] THEN
STRIP_TAC THEN
CONSEQ_CONV_TAC (K EXISTS_EQ___CONSEQ_CONV) THEN
GEN_TAC THEN

`SMALLFOOT_AP_PERMISSION_UNIMPORTANT 
      (smallfoot_ap_points_to startExp
         (FMAP_MAP (\dl. smallfoot_ae_const (HD dl)) data |+
          (tl,smallfoot_ae_const n'))) /\
 SMALLFOOT_AP_PERMISSION_UNIMPORTANT 
      (smallfoot_ap_points_to startExp'
         (FMAP_MAP (\dl. smallfoot_ae_const (HD dl)) data |+
          (tl,smallfoot_ae_const n'))) /\
 SMALLFOOT_AP_PERMISSION_UNIMPORTANT
      (smallfoot_ap_data_list_seg_num n tl (smallfoot_ae_const n')
         (FMAP_MAP TL data) endExp)` by ALL_TAC THEN1 (

   CONSEQ_REWRITE_TAC ([],[SMALLFOOT_AP_PERMISSION_UNIMPORTANT___points_to,
		      SMALLFOOT_AP_PERMISSION_UNIMPORTANT___data_list_seg_num,
		      FEVERY_STRENGTHEN_THM],[]) THEN
   ASM_SIMP_TAC std_ss [FEVERY_DEF, FMAP_MAP_THM, FDOM_FUPDATE,
		        IS_SOME___SMALLFOOT_AE_USED_VARS___EVAL]
) THEN
ASM_SIMP_TAC std_ss [smallfoot_ap_star___PERMISSION_UNIMPORTANT, IN_ABS] THEN

DEPTH_CONSEQ_CONV_TAC (K EXISTS_EQ___CONSEQ_CONV) THEN
ASM_SIMP_TAC (std_ss++bool_eq_imp_ss) [smallfoot_ap_points_to_def,
				   IN_ABS, LET_THM]);











val SMALLFOOT_PROP_IMPLIES___points_to___data_list_seg = store_thm ("SMALLFOOT_PROP_IMPLIES___points_to___data_list_seg",
``!e3 e1 e2 tl data L wpb rpb wpb' sfb_context sfb_split sfb_imp sfb_restP sr.

((tl IN FDOM L) /\ (L ' tl = e3) /\ (FDOM data SUBSET FDOM L) /\
SMALLFOOT_AE_USED_VARS_SUBSET (SET_OF_BAG (BAG_UNION wpb rpb))
              e1 /\
SMALLFOOT_AE_USED_VARS_SUBSET (SET_OF_BAG (BAG_UNION wpb rpb))
              e2 /\
(FEVERY (\x.
   (SMALLFOOT_AE_USED_VARS_SUBSET (SET_OF_BAG (BAG_UNION wpb rpb))
              (SND x))) L))
  ==>


((SMALLFOOT_PROP_IMPLIES sr (wpb,rpb) wpb'
   (BAG_INSERT (smallfoot_ap_points_to e1 L) (BAG_INSERT (smallfoot_ap_unequal e1 e2) sfb_context))
   sfb_split 
   (BAG_UNION (BAG_OF_FMAP (\t tL. smallfoot_ap_equal (L ' t) (smallfoot_ae_const (HD tL))) data) 
   (BAG_INSERT (smallfoot_ap_empty_heap_cond (FEVERY (\x. ~(SND x = [])) data)) (
    BAG_INSERT (smallfoot_ap_data_list_seg tl e3 (FMAP_MAP TL data) e2) sfb_imp)))
   sfb_restP) ==>

(SMALLFOOT_PROP_IMPLIES sr (wpb,rpb) wpb' 
   (BAG_INSERT (smallfoot_ap_unequal e1 e2) sfb_context)
   (BAG_INSERT (smallfoot_ap_points_to e1 L) sfb_split)
   (BAG_INSERT (smallfoot_ap_data_list_seg tl e1 data e2) sfb_imp) sfb_restP))

``,

SIMP_TAC (std_ss++bool_eq_imp_ss) [SMALLFOOT_PROP_IMPLIES_EXPAND,
		 smallfoot_prop___COND_UNION,
    		 smallfoot_prop___COND_INSERT,
		 bagTheory.BAG_UNION_INSERT] THEN
REPEAT STRIP_TAC THEN
FULL_SIMP_TAC std_ss [] THEN
Q.EXISTS_TAC `sfb_rest` THEN
ASM_REWRITE_TAC[] THEN
STRIP_TAC THEN GEN_TAC THEN STRIP_TAC THEN
`!data. SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS
            (SET_OF_BAG (BAG_UNION wpb rpb))
            (smallfoot_ap_data_list_seg tl (L ' tl) data e2)` by ALL_TAC THEN1 (
   GEN_TAC THEN
   MATCH_MP_TAC SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___data_list_seg THEN
   FULL_SIMP_TAC std_ss [FEVERY_DEF]
) THEN
`!data. FDOM data SUBSET FDOM L ==>
smallfoot_prop___COND (wpb,rpb)
            (BAG_OF_FMAP
               (\t tL.
                  smallfoot_ap_equal (L ' t) (smallfoot_ae_const (HD tL)))
               data)` by ALL_TAC THEN1 (
   FULL_SIMP_TAC std_ss [smallfoot_prop___COND___REWRITE,
			 FINITE___BAG_OF_FMAP,
			 BAG_IN___BAG_OF_FMAP, FEVERY_DEF,
			 GSYM LEFT_FORALL_IMP_THM] THEN
   CONSEQ_REWRITE_TAC ([],[SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___compare],[]) THEN
   ASM_SIMP_TAC std_ss [SMALLFOOT_AE_USED_VARS_SUBSET___EVAL, SUBSET_DEF]
) THEN
Q.PAT_ASSUM `FDOM data SUBSET FDOM L` ASSUME_TAC  THEN
FULL_SIMP_TAC std_ss [SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___smallfoot_ap_empty_heap_cond] THEN
Q.PAT_ASSUM `!s. smallfoot_prop___PROP (wpb,rpb) X s ==> Y s` (MP_TAC o Q.SPEC `s`) THEN
ASM_SIMP_TAC std_ss [] THEN
STRIP_TAC THEN
Q.ABBREV_TAC `sfbX = BAG_UNION sfb_imp (BAG_UNION sfb_rest sfb_context)` THEN
`smallfoot_prop___COND (wpb,rpb) sfbX` by ALL_TAC THEN1 (
   Q.UNABBREV_TAC `sfbX` THEN
   ASM_SIMP_TAC std_ss [smallfoot_prop___COND_UNION,
		        smallfoot_prop___COND_INSERT]
) THEN
ONCE_REWRITE_TAC[bagTheory.BAG_INSERT_commutes] THEN

MP_TAC (Q.SPECL [`wpb`, `rpb`, `sfbX`, `e1`, `data`, `e2`, `tl`] SMALLFOOT_COND_PROP___STRONG_IMP___data_list_seg_split) THEN
ASM_SIMP_TAC (std_ss++boolSimps.CONJ_ss)
                    [SMALLFOOT_COND_PROP___STRONG_IMP_def,
		     smallfoot_prop___REWRITE,
		     smallfoot_prop___COND_INSERT,
		     COND_PROP___EXISTS_def, IN_ABS] THEN

`(!n. (SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS
         (SET_OF_BAG (BAG_UNION wpb rpb))
   (smallfoot_ap_points_to e1 ((FMAP_MAP (\dl. smallfoot_ae_const (HD dl)) data |+ (tl,smallfoot_ae_const n)))))) /\

(!data n.
 SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS
         (SET_OF_BAG (BAG_UNION wpb rpb))
   (smallfoot_ap_data_list_seg tl (smallfoot_ae_const n) data e2))` by ALL_TAC THEN1 (

   CONSEQ_REWRITE_TAC([],[SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___data_list_seg,
		      SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___points_to,
		      FEVERY_STRENGTHEN_THM],[]) THEN
   ASM_SIMP_TAC std_ss [SMALLFOOT_AE_USED_VARS_SUBSET___EVAL, FEVERY_DEF,
		        FMAP_MAP_THM]
) THEN
ASM_SIMP_TAC std_ss [SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___smallfoot_ap_empty_heap_cond] THEN
DISCH_TAC THEN (POP_ASSUM (K ALL_TAC)) THEN

Q.EXISTS_TAC `THE ((L ' tl) (FST s))` THEN
Q.PAT_ASSUM `smallfoot_prop___PROP (wpb,rpb) Y s` MP_TAC THEN
ASM_SIMP_TAC std_ss [GSYM bagTheory.ASSOC_BAG_UNION] THEN

ASM_SIMP_TAC std_ss [smallfoot_prop___PROP_INSERT,
		     smallfoot_prop___PROP_UNION,
		     smallfoot_prop___COND_INSERT,
		     smallfoot_prop___COND_UNION,
		     SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___smallfoot_ap_empty_heap_cond,
		     IN_ABS, GSYM RIGHT_EXISTS_AND_THM,
		     GSYM LEFT_FORALL_IMP_THM,
		     GSYM RIGHT_EXISTS_IMP_THM] THEN


`!st h data. FDOM data SUBSET FDOM L ==> (
 (st,h) IN smallfoot_prop___PROP (wpb,rpb)
          (BAG_OF_FMAP
             (\t tL.
                smallfoot_ap_equal (L ' t) (smallfoot_ae_const (HD tL)))
             data) =
 (st,h) IN asl_and smallfoot_ap_stack_true (smallfoot_prop___PROP (wpb,rpb)
          (BAG_OF_FMAP
             (\t tL.
                smallfoot_ap_equal (L ' t) (smallfoot_ae_const (HD tL)))
             data)))` by ALL_TAC THEN1 (
   GEN_TAC THEN GEN_TAC THEN
   SIMP_TAC std_ss [asl_bool_EVAL, smallfoot_ap_stack_true_def, IN_ABS] THEN
   Cases_on `h = FEMPTY` THEN ASM_REWRITE_TAC[] THEN
   HO_MATCH_MP_TAC fmap_INDUCT THEN
   FULL_SIMP_TAC std_ss [BAG_OF_FMAP_THM, IN_ABS,
		    smallfoot_prop___PROP_EMPTY,
		    FEVERY_DEF,
		    smallfoot_prop___PROP_INSERT,
		    DOMSUB_NOT_IN_DOM, FDOM_FUPDATE, INSERT_SUBSET] THEN
   ASM_SIMP_TAC std_ss [smallfoot_prop___PROP_INSERT,
		smallfoot_prop___COND_INSERT,
		SMALLFOOT_AE_USED_VARS_SUBSET___EVAL, IN_ABS,
		SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___compare] THEN
   SIMP_TAC std_ss [smallfoot_ap_equal_def, IN_ABS, LET_THM,
		    smallfoot_ap_binexpression_def, FUNION_FEMPTY_1,
		    smallfoot_a_stack_proposition_def]
) THEN

`!st h. 
 (st,h) IN smallfoot_ap_unequal e1 e2 =
 (st,h) IN asl_and smallfoot_ap_stack_true (smallfoot_ap_unequal e1 e2)` by ALL_TAC THEN1 (
   SIMP_TAC (std_ss++bool_eq_imp_ss)
                   [smallfoot_ap_unequal_def,
		    smallfoot_ap_binexpression_def,
		    smallfoot_a_stack_proposition_def,
		    asl_bool_EVAL, IN_ABS, smallfoot_ap_stack_true_def, LET_THM]
) THEN
ASM_SIMP_TAC std_ss [] THEN
NTAC 5 (POP_ASSUM (K ALL_TAC)) THEN


SIMP_TAC std_ss 
   [asl_bool_EVAL, IN_ABS,
    smallfoot_ap_stack_true_def,
    smallfoot_ap_empty_heap_cond_def,
    RIGHT_EXISTS_IMP_THM,
    FUNION_FEMPTY_1, FUNION_FEMPTY_2,
    FDOM_FEMPTY, DISJOINT_EMPTY] THEN

REPEAT GEN_TAC THEN
SIMP_TAC std_ss [GSYM RIGHT_EXISTS_IMP_THM] THEN

Q.EXISTS_TAC `h1''` THEN
Q.EXISTS_TAC `h1'` THEN
Q.EXISTS_TAC `h2'` THEN
SIMP_TAC std_ss [FDOM_FUNION, DISJOINT_UNION_BOTH] THEN
REPEAT STRIP_TAC THENL [
   METIS_TAC[DISJOINT_SYM],
   METIS_TAC[DISJOINT_SYM],
   METIS_TAC[FUNION___ASSOC, FUNION___COMM],
   ALL_TAC,
   METIS_TAC[DISJOINT_SYM],
   ALL_TAC
] THENL [

   Q.PAT_ASSUM `(FST s, h1'') IN X` MP_TAC THEN
   Q.PAT_ASSUM `(FST s, FEMPTY) IN smallfoot_prop___PROP (wpb,rpb) X` MP_TAC THEN
   Q.PAT_ASSUM `tl IN FDOM L` MP_TAC THEN
   Q.PAT_ASSUM `FEVERY X L` MP_TAC THEN
   Q.PAT_ASSUM `FDOM data SUBSET FDOM L` MP_TAC THEN
   Q.PAT_ASSUM `!data. FDOM data SUBSET FDOM L ==> X data` MP_TAC THEN
   REPEAT (POP_ASSUM (K ALL_TAC)) THEN


   SIMP_TAC std_ss [smallfoot_ap_points_to_def, IN_ABS, LET_THM,
		    FEVERY_DEF, FMAP_MAP_THM, FDOM_FUPDATE,
		    IN_INSERT, FEVERY_DEF] THEN
   REPEAT DISCH_TAC THEN GEN_TAC THEN
   Cases_on `x = tl` THEN (
      ASM_SIMP_TAC std_ss [FAPPLY_FUPDATE_THM, smallfoot_ae_const_def]
   ) THEN
   FULL_SIMP_TAC std_ss [FMAP_MAP_THM] THEN
   STRIP_TAC THEN
   `x IN FDOM L` by METIS_TAC[SUBSET_DEF] THEN
   FULL_SIMP_TAC std_ss [] THEN

   Q.ABBREV_TAC `xL = data ' x` THEN
   `?data'. (data = data' |+ (x, xL)) /\ FDOM (data' \\ x) SUBSET FDOM L` by ALL_TAC THEN1 (
      Q.EXISTS_TAC `data` THEN     
      FULL_SIMP_TAC std_ss [GSYM fmap_EQ_THM, FDOM_FUPDATE,
		       FAPPLY_FUPDATE_THM, EXTENSION, IN_INSERT,
		       FDOM_DOMSUB, SUBSET_DEF, IN_DELETE] THEN
      METIS_TAC[]
   ) THEN

   Q.PAT_ASSUM `(FST s, FEMPTY) IN X` MP_TAC THEN
   ASM_SIMP_TAC std_ss [BAG_OF_FMAP_THM, smallfoot_prop___PROP_INSERT,
		        smallfoot_prop___COND_INSERT,
		        SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___compare,
		        SMALLFOOT_AE_USED_VARS_SUBSET___EVAL] THEN
   SIMP_TAC std_ss [IN_ABS, FUNION_EQ_FEMPTY, FDOM_FEMPTY, DISJOINT_EMPTY,
		    smallfoot_ap_equal_def, smallfoot_ap_binexpression_def,
		    smallfoot_a_stack_proposition_def, LET_THM,
		    smallfoot_ae_const_def] THEN
   METIS_TAC[],


   Q.PAT_ASSUM `(FST s, h1') IN X` MP_TAC THEN
   SIMP_TAC std_ss [smallfoot_ap_data_list_seg_def, asl_exists_def, IN_ABS] THEN
   HO_MATCH_MP_TAC (prove (``(!x. P x = Q x) ==> ((?x. P x) ==> (?x. Q x))``, METIS_TAC[])) THEN
   GEN_TAC THEN
   MATCH_MP_TAC smallfoot_ap_data_list_seg_num___REWRITE_START_EXP THEN

   FULL_SIMP_TAC std_ss [IS_SOME___SMALLFOOT_AE_USED_VARS___EVAL,
			 SMALLFOOT_AE_USED_VARS_SUBSET_def, FEVERY_DEF,
			 GSYM IS_SOME___SMALLFOOT_AE_USED_VARS_def] THEN
   Cases_on `L ' tl (FST s)` THEN (
      SIMP_TAC std_ss [smallfoot_ae_const_def]
   ) THEN
   Q.PAT_ASSUM `(FST s, h1'') IN X` MP_TAC THEN
   SIMP_TAC std_ss [smallfoot_ap_points_to_def, IN_ABS, LET_THM, FEVERY_DEF] THEN
   METIS_TAC[]
]);







val SMALLFOOT_PROP_IMPLIES___points_to___data_list = store_thm ("SMALLFOOT_PROP_IMPLIES___points_to___data_list",
``!e2 e1 tl data L wpb rpb wpb' sfb_context sfb_split sfb_imp sfb_restP sr.

((tl IN FDOM L) /\ (L ' tl = e2) /\ (FDOM data SUBSET FDOM L) /\
SMALLFOOT_AE_USED_VARS_SUBSET (SET_OF_BAG (BAG_UNION wpb rpb))
              e1 /\
(FEVERY (\x. (SMALLFOOT_AE_USED_VARS_SUBSET (SET_OF_BAG (BAG_UNION wpb rpb))
              (SND x))) L))
  ==>


((SMALLFOOT_PROP_IMPLIES sr (wpb,rpb) wpb'
   (BAG_INSERT (smallfoot_ap_points_to e1 L) (BAG_INSERT (smallfoot_ap_unequal e1 smallfoot_ae_null) sfb_context))
   sfb_split 
   (BAG_UNION (BAG_OF_FMAP (\t tL. smallfoot_ap_equal (L ' t) (smallfoot_ae_const (HD tL))) data) 
   (BAG_INSERT (smallfoot_ap_empty_heap_cond (FEVERY (\x. ~(SND x = [])) data)) (
    BAG_INSERT (smallfoot_ap_data_list tl e2 (FMAP_MAP TL data)) sfb_imp)))
   sfb_restP) ==>

(SMALLFOOT_PROP_IMPLIES sr (wpb,rpb) wpb' 
   (BAG_INSERT (smallfoot_ap_unequal e1 smallfoot_ae_null) sfb_context)
   (BAG_INSERT (smallfoot_ap_points_to e1 L) sfb_split)
   (BAG_INSERT (smallfoot_ap_data_list tl e1 data) sfb_imp) sfb_restP))

``,

REPEAT GEN_TAC THEN STRIP_TAC THEN
REWRITE_TAC [smallfoot_ap_data_list_def] THEN
MATCH_MP_TAC SMALLFOOT_PROP_IMPLIES___points_to___data_list_seg THEN
ASM_REWRITE_TAC[SMALLFOOT_AE_USED_VARS_SUBSET___EVAL]);





val SMALLFOOT_PROP_IMPLIES___points_to___bintree = store_thm ("SMALLFOOT_PROP_IMPLIES___points_to___bintree",
``!el er e lt rt L L' wpb rpb wpb' sfb_context sfb_split sfb_imp sfb_restP sr .

((lt IN FDOM L) /\ (L ' lt = el) /\
 (rt IN FDOM L) /\ (L ' rt = er) /\
SMALLFOOT_AE_USED_VARS_SUBSET (SET_OF_BAG (BAG_UNION wpb rpb))
              e /\
SMALLFOOT_AE_USED_VARS_SUBSET (SET_OF_BAG (BAG_UNION wpb rpb))
              el /\
SMALLFOOT_AE_USED_VARS_SUBSET (SET_OF_BAG (BAG_UNION wpb rpb))
              er)

  ==>


((SMALLFOOT_PROP_IMPLIES sr (wpb,rpb) wpb'
   (BAG_INSERT (smallfoot_ap_points_to e L) (BAG_INSERT (smallfoot_ap_unequal e smallfoot_ae_null) sfb_context))
   sfb_split 
   (BAG_INSERT (smallfoot_ap_bintree (lt,rt) el) 
   (BAG_INSERT (smallfoot_ap_bintree (lt,rt) er) sfb_imp))
   sfb_restP) ==>

(SMALLFOOT_PROP_IMPLIES sr (wpb,rpb) wpb' 
   (BAG_INSERT (smallfoot_ap_unequal e smallfoot_ae_null) sfb_context)
   (BAG_INSERT (smallfoot_ap_points_to e L) sfb_split)
   (BAG_INSERT (smallfoot_ap_bintree (lt,rt) e) sfb_imp) sfb_restP))

``,

SIMP_TAC (std_ss++bool_eq_imp_ss) [SMALLFOOT_PROP_IMPLIES_EXPAND,
		 smallfoot_prop___COND_UNION,
    		 smallfoot_prop___COND_INSERT,
		 bagTheory.BAG_UNION_INSERT] THEN
REPEAT STRIP_TAC THEN
FULL_SIMP_TAC std_ss [] THEN
Q.EXISTS_TAC `sfb_rest` THEN
ASM_REWRITE_TAC[] THEN
STRIP_TAC THEN GEN_TAC THEN STRIP_TAC THEN
`SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS
            (SET_OF_BAG (BAG_UNION wpb rpb))
            (smallfoot_ap_bintree (lt,rt) (L ' lt)) /\
 SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS
            (SET_OF_BAG (BAG_UNION wpb rpb))
            (smallfoot_ap_bintree (lt,rt) (L ' rt))` by ALL_TAC THEN1 (
   CONJ_TAC THEN
   MATCH_MP_TAC SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___bintree THEN
   ASM_REWRITE_TAC[]
) THEN
FULL_SIMP_TAC std_ss [] THEN
Q.PAT_ASSUM `!s. X s` (MP_TAC o Q.SPEC `s`) THEN
ASM_SIMP_TAC std_ss [] THEN
STRIP_TAC THEN
Q.ABBREV_TAC `sfbX = BAG_UNION sfb_imp (BAG_UNION sfb_rest sfb_context)` THEN
`smallfoot_prop___COND (wpb,rpb) sfbX` by ALL_TAC THEN1 (
   Q.UNABBREV_TAC `sfbX` THEN
   ASM_SIMP_TAC std_ss [smallfoot_prop___COND_UNION,
		        smallfoot_prop___COND_INSERT]
) THEN
ONCE_REWRITE_TAC[bagTheory.BAG_INSERT_commutes] THEN

MP_TAC (Q.SPECL [`wpb`, `rpb`, `sfbX`, `e`, `lt`, `rt`] SMALLFOOT_COND_PROP___STRONG_IMP___bintree_split) THEN
ASM_SIMP_TAC (std_ss++boolSimps.CONJ_ss)
                    [SMALLFOOT_COND_PROP___STRONG_IMP_def,
		     smallfoot_prop___REWRITE,
		     smallfoot_prop___COND_INSERT,
		     COND_PROP___EXISTS_def, IN_ABS] THEN

`!n n'. (SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS
         (SET_OF_BAG (BAG_UNION wpb rpb))
   (smallfoot_ap_points_to e (FEMPTY |+ (rt,smallfoot_ae_const n) |+ (lt,smallfoot_ae_const n'))) /\

 SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS
         (SET_OF_BAG (BAG_UNION wpb rpb))
   (smallfoot_ap_bintree (lt,rt) (smallfoot_ae_const n)))` by ALL_TAC THEN1 (

   REPEAT STRIP_TAC THENL [
      MATCH_MP_TAC SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___points_to THEN
      ASM_SIMP_TAC std_ss [FEVERY_DEF, FDOM_FEMPTY, FDOM_FUPDATE,
			   IN_INSERT, NOT_IN_EMPTY, DISJ_IMP_THM,
			   FORALL_AND_THM,
			   FAPPLY_FUPDATE_THM] THEN
      SIMP_TAC std_ss[COND_RAND, COND_RATOR,
		      SMALLFOOT_AE_USED_VARS_SUBSET___EVAL],

      MATCH_MP_TAC SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___bintree THEN
      ASM_SIMP_TAC std_ss [SMALLFOOT_AE_USED_VARS_SUBSET___EVAL]
   ]
) THEN
ASM_SIMP_TAC std_ss [] THEN

DISCH_TAC THEN (POP_ASSUM (K ALL_TAC)) THEN

Q.EXISTS_TAC `THE ((L ' rt) (FST s))` THEN
Q.EXISTS_TAC `THE ((L ' lt) (FST s))` THEN
Q.PAT_ASSUM `smallfoot_prop___PROP (wpb,rpb) Y s` MP_TAC THEN

ASM_SIMP_TAC std_ss [smallfoot_prop___PROP_INSERT,
		     smallfoot_prop___COND_INSERT,
		     IN_ABS, GSYM RIGHT_EXISTS_AND_THM,
		     GSYM LEFT_FORALL_IMP_THM,
		     GSYM RIGHT_EXISTS_IMP_THM] THEN
REPEAT GEN_TAC THEN
Q.EXISTS_TAC `h1''` THEN
Q.EXISTS_TAC `h1'''` THEN
Q.EXISTS_TAC `h1'` THEN
Q.EXISTS_TAC `h1` THEN
Q.EXISTS_TAC `h2'` THEN

SIMP_TAC std_ss [FDOM_FUNION, DISJOINT_UNION_BOTH,
		 DISJOINT_SYM, 
		 LET_THM, IN_ABS, FEVERY_DEF,
		 FDOM_FUPDATE, IN_INSERT, FDOM_FEMPTY,
		 NOT_IN_EMPTY, FAPPLY_FUPDATE_THM,
		 GSYM RIGHT_FORALL_AND_THM,
      		 GSYM LEFT_FORALL_AND_THM,
		 GSYM LEFT_EXISTS_IMP_THM,
		 IS_SOME_EXISTS,
		 SOME___smallfoot_ae_const,
		 GSYM LEFT_EXISTS_AND_THM,
		 GSYM RIGHT_EXISTS_AND_THM,
		 GSYM RIGHT_EXISTS_IMP_THM,
		 GSYM LEFT_FORALL_IMP_THM
		] THEN
ASM_SIMP_TAC (std_ss++boolSimps.CONJ_ss) [] THEN
STRIP_TAC THEN
`?Lrt_c Llt_c. 
         ((L ' lt (FST s)) = SOME Llt_c) /\
         ((L ' rt (FST s)) = SOME Lrt_c)` by ALL_TAC THEN1 (
  Q.PAT_ASSUM `(FST s, h1'') IN X` MP_TAC THEN
  ASM_SIMP_TAC std_ss [smallfoot_ap_points_to_def,
		   IN_ABS, LET_THM, FEVERY_DEF,
		   LEFT_EXISTS_AND_THM, 
		   RIGHT_EXISTS_AND_THM, GSYM IS_SOME_EXISTS]
) THEN
REPEAT STRIP_TAC THENL [
   METIS_TAC[FUNION___COMM, FUNION___ASSOC],

   Q.PAT_ASSUM `(FST s, h1'') IN X` MP_TAC THEN
   ASM_SIMP_TAC std_ss [smallfoot_ap_points_to_def,
		        IN_ABS, LET_THM,
		        FEVERY_DEF, FDOM_FUPDATE,
		        FDOM_FEMPTY, NOT_IN_EMPTY,
		        IN_INSERT,
		        FAPPLY_FUPDATE_THM] THEN
   STRIP_TAC THEN GEN_TAC THEN
   Cases_on `x = lt` THENL [
      Q.PAT_ASSUM `!x. X x` (MP_TAC o Q.SPEC `lt`) THEN
      ASM_SIMP_TAC std_ss [smallfoot_ae_const_def],

      Q.PAT_ASSUM `!x. X x` (MP_TAC o Q.SPEC `rt`) THEN
      ASM_SIMP_TAC std_ss [smallfoot_ae_const_def]
   ],


   Q.PAT_ASSUM `(FST s, h1') IN X` MP_TAC THEN
   SIMP_TAC std_ss [smallfoot_ap_bintree_def,
		    smallfoot_ap_bintree_num_def,
       	            asl_exists_def, IN_ABS] THEN
   HO_MATCH_MP_TAC (prove (``(!x. (P x = Q x)) ==>
		          ((?x. P x) ==> (?x. Q x))``,
			SIMP_TAC std_ss [])) THEN
   GEN_TAC THEN
   HO_MATCH_MP_TAC smallfoot_ap_tree_seg_num___REWRITE_START_EXP THEN
   ASM_SIMP_TAC list_ss [IS_SOME___SMALLFOOT_AE_USED_VARS___EVAL] THEN
   FULL_SIMP_TAC std_ss [smallfoot_ae_const_def,
		      IS_SOME___SMALLFOOT_AE_USED_VARS_def,
		      SMALLFOOT_AE_USED_VARS_SUBSET_def],


   Q.PAT_ASSUM `(FST s, h1) IN X` MP_TAC THEN
   SIMP_TAC std_ss [smallfoot_ap_bintree_def,
		    smallfoot_ap_bintree_num_def,
       	            asl_exists_def, IN_ABS] THEN
   HO_MATCH_MP_TAC (prove (``(!x. (P x = Q x)) ==>
		          ((?x. P x) ==> (?x. Q x))``,
			SIMP_TAC std_ss [])) THEN
   GEN_TAC THEN
   HO_MATCH_MP_TAC smallfoot_ap_tree_seg_num___REWRITE_START_EXP THEN
   ASM_SIMP_TAC list_ss [IS_SOME___SMALLFOOT_AE_USED_VARS___EVAL] THEN
   FULL_SIMP_TAC std_ss [smallfoot_ae_const_def,
		      IS_SOME___SMALLFOOT_AE_USED_VARS_def,
		      SMALLFOOT_AE_USED_VARS_SUBSET_def]
]);
   











val asl_and___asl_star_THM = store_thm ("asl_and___asl_star_THM",
``!s. s IN asl_star f (asl_and P1 P2) Q ==>
  s IN (asl_star f P1 Q) /\ s IN (asl_star f P2 Q)``,

SIMP_TAC std_ss [asl_star_def, asl_and_def,
		 IN_ABS] THEN
METIS_TAC[]);


val asl_and___weak_unequal___PERMISSION_UNIMPORTANT =
store_thm ("asl_and___weak_unequal___PERMISSION_UNIMPORTANT",
``!e1 e2 P.
  (SMALLFOOT_AP_PERMISSION_UNIMPORTANT P /\
  SMALLFOOT_AP_PERMISSION_UNIMPORTANT (smallfoot_ap_unequal e1 e2)) ==>
  (asl_and (smallfoot_ap_weak_unequal e1 e2) P =
   smallfoot_ap_star (smallfoot_ap_unequal e1 e2) P)``,

ONCE_REWRITE_TAC [EXTENSION] THEN
SIMP_TAC std_ss [smallfoot_ap_weak_unequal_def,
		 smallfoot_ap_star___PERMISSION_UNIMPORTANT,
		 smallfoot_ap_unequal_def,
		 smallfoot_ap_binexpression_def,
		 smallfoot_a_stack_proposition_def,
		 asl_bool_EVAL, IN_ABS, LET_THM,
		 FUNION_FEMPTY_1, DISJOINT_EMPTY,
		 FDOM_FEMPTY] THEN
METIS_TAC[]);



val smallfoot_ap_data_list_seg_num_REWRITE___PERMISSION_UNIMPORTANT =
store_thm ("smallfoot_ap_data_list_seg_num_REWRITE___PERMISSION_UNIMPORTANT",

``
(!tl startExp data endExp.
          smallfoot_ap_data_list_seg_num 0 tl startExp data endExp =
          asl_and (K (FEVERY (\x. SND x = []) data)) (smallfoot_ap_equal endExp startExp)) /\
(!n tl startExp data endExp.
        (IS_SOME___SMALLFOOT_AE_USED_VARS startExp /\
         IS_SOME___SMALLFOOT_AE_USED_VARS endExp) ==>

        (smallfoot_ap_data_list_seg_num (SUC n) tl startExp data endExp =
         asl_exists n'.
	 (asl_and (K (FEVERY (\x. ~(SND x = [])) data))
         (smallfoot_ap_star (smallfoot_ap_unequal startExp endExp)
             (smallfoot_ap_star
               (smallfoot_ap_points_to startExp
                  ((FMAP_MAP (\dL. smallfoot_ae_const (HD (dL))) data) |+ (tl,smallfoot_ae_const n')))
               (smallfoot_ap_data_list_seg_num n tl (smallfoot_ae_const n')
		 (FMAP_MAP TL data) endExp))))))``,

SIMP_TAC (std_ss++bool_eq_imp_ss)
   [smallfoot_ap_data_list_seg_num_def, EXTENSION,
    asl_bool_EVAL, IN_ABS, GSYM RIGHT_EXISTS_AND_THM] THEN
REPEAT STRIP_TAC THEN
CONSEQ_CONV_TAC (K EXISTS_EQ___CONSEQ_CONV) THEN
GEN_TAC THEN
Q.ABBREV_TAC `P = smallfoot_ap_star
         (smallfoot_ap_points_to startExp
            (FMAP_MAP (\dl. smallfoot_ae_const (HD dl)) data |+
             (tl,smallfoot_ae_const n')))
         (smallfoot_ap_data_list_seg_num n tl (smallfoot_ae_const n')
            (FMAP_MAP TL data) endExp)` THEN
`SMALLFOOT_AP_PERMISSION_UNIMPORTANT (smallfoot_ap_unequal startExp endExp)` by ALL_TAC THEN1 (
   ASM_SIMP_TAC std_ss [SMALLFOOT_AP_PERMISSION_UNIMPORTANT___compare]
) THEN
`SMALLFOOT_AP_PERMISSION_UNIMPORTANT P` by ALL_TAC THEN1 (
   Q.UNABBREV_TAC `P` THEN
   CONSEQ_REWRITE_TAC([],[SMALLFOOT_AP_PERMISSION_UNIMPORTANT___star,
		      SMALLFOOT_AP_PERMISSION_UNIMPORTANT___data_list_seg_num,
		      SMALLFOOT_AP_PERMISSION_UNIMPORTANT___points_to,
		      FEVERY_STRENGTHEN_THM],[]) THEN
   ASM_SIMP_TAC std_ss [FEVERY_DEF, FMAP_MAP_THM, IS_SOME___SMALLFOOT_AE_USED_VARS___EVAL]
) THEN

ASM_SIMP_TAC std_ss [GSYM asl_and___weak_unequal___PERMISSION_UNIMPORTANT, asl_bool_EVAL] THEN
METIS_TAC[smallfoot_ap_weak_unequal___COMM]);






val smallfoot_ap_star___data_list_seg___append___data_list_seg =
store_thm ("smallfoot_ap_star___data_list_seg___append___data_list_seg",
``
!e1 e2 e3 data1 data2 data3 tl s.
(IS_SOME___SMALLFOOT_AE_USED_VARS e1 /\
 IS_SOME___SMALLFOOT_AE_USED_VARS e2 /\
 IS_SOME___SMALLFOOT_AE_USED_VARS e3 /\
 ((e3 (FST s) = SOME 0) \/ ~(THE (e3 (FST s)) IN FDOM (SND s))) /\
  (!t. t IN FDOM data3 ==> (t IN FDOM data1 /\ t IN FDOM data2 /\
			    ((data3 ' t) = (data1 ' t)++(data2 ' t)))) /\
 s IN (smallfoot_ap_star (smallfoot_ap_data_list_seg tl e1 data1 e2) (smallfoot_ap_data_list_seg tl e2 data2 e3))) ==>
 s IN smallfoot_ap_data_list_seg tl e1 data3 e3``,



SIMP_TAC std_ss [smallfoot_ap_data_list_seg_def,
		 smallfoot_ap_star_def,
		 GSYM asl_exists___asl_star_THM] THEN
SIMP_TAC std_ss [asl_exists_def, IN_ABS,
		 GSYM smallfoot_ap_star_def,
		 GSYM LEFT_FORALL_IMP_THM,
		 GSYM RIGHT_FORALL_IMP_THM,
		 GSYM RIGHT_EXISTS_AND_THM] THEN
Induct_on `x` THENL [
   REPEAT GEN_TAC THEN
   SIMP_TAC std_ss [smallfoot_ap_data_list_seg_num_REWRITE___PERMISSION_UNIMPORTANT] THEN
   Cases_on `FEVERY (\x. SND x = []) data1` THEN (
      ASM_SIMP_TAC std_ss [asl_bool_REWRITES] THEN
      SIMP_TAC std_ss [GSYM smallfoot_ap_false_def, smallfoot_ap_false___smallfoot_ap_star_THM,
		       smallfoot_ap_false___NOT_IN]
   ) THEN
   FULL_SIMP_TAC (list_ss++boolSimps.CONJ_ss) [FEVERY_DEF] THEN
   ASM_SIMP_TAC (std_ss++boolSimps.CONJ_ss) [
		    smallfoot_ap_star___PERMISSION_UNIMPORTANT,
		    SMALLFOOT_AP_PERMISSION_UNIMPORTANT___compare, IN_ABS,
		    SMALLFOOT_AP_PERMISSION_UNIMPORTANT___data_list_seg_num,
    		    SMALLFOOT_AP_PERMISSION_UNIMPORTANT___star] THEN
   SIMP_TAC std_ss [smallfoot_ap_equal_def, IN_ABS,
		    smallfoot_ap_unequal_def,
		    smallfoot_ap_binexpression_def,
		    smallfoot_a_stack_proposition_def,
		    LET_THM, FUNION_FEMPTY_1, IS_SOME_EXISTS,
		    GSYM RIGHT_EXISTS_AND_THM, GSYM LEFT_EXISTS_AND_THM,
		    FDOM_FEMPTY, DISJOINT_EMPTY,
		    GSYM LEFT_FORALL_IMP_THM] THEN
   SIMP_TAC (std_ss++boolSimps.CONJ_ss) [] THEN
   REPEAT GEN_TAC THEN
   Q.ABBREV_TAC `e3_cond = ((e3 (FST s) = SOME 0) \/ ~(THE (e3 (FST s)) IN FDOM (SND s)))` THEN
   REPEAT STRIP_TAC THEN
   Q.EXISTS_TAC `x'` THEN
   `s IN smallfoot_ap_data_list_seg_num x' tl e2 data3 e3` by ALL_TAC THEN1 (
      MATCH_MP_TAC smallfoot_ap_data_list_seg_num___ELIM_DATA THEN
      Q.EXISTS_TAC `data2` THEN
      ASM_SIMP_TAC std_ss []
   ) THEN
   POP_ASSUM MP_TAC THEN
   MATCH_MP_TAC (prove (``(A = B) ==> (A ==> B)``, SIMP_TAC std_ss [])) THEN
   MATCH_MP_TAC smallfoot_ap_data_list_seg_num___REWRITE_START_EXP THEN
   ASM_SIMP_TAC std_ss [],




   REPEAT GEN_TAC THEN 
   Q.ABBREV_TAC `e3_cond = ((e3 (FST s) = SOME 0) \/ ~(THE (e3 (FST s)) IN FDOM (SND s)))` THEN
   STRIP_TAC THEN
   Q.PAT_ASSUM `s IN X` MP_TAC THEN
   ASM_SIMP_TAC std_ss [smallfoot_ap_data_list_seg_num_REWRITE___PERMISSION_UNIMPORTANT] THEN
   Tactical.REVERSE (Cases_on `FEVERY (\x. ~(SND x = [])) data1`) THEN1 (
      ASM_SIMP_TAC std_ss [asl_bool_REWRITES] THEN
      SIMP_TAC std_ss [GSYM smallfoot_ap_false_def, smallfoot_ap_false___smallfoot_ap_star_THM,
		       smallfoot_ap_false___NOT_IN,
		       asl_exists_def, asl_bool_REWRITES]
   ) THEN
   ASM_SIMP_TAC std_ss [asl_bool_REWRITES, GSYM asl_exists___smallfoot_ap_star_THM,
		    asl_bool_EVAL, GSYM LEFT_FORALL_IMP_THM,
		    GSYM RIGHT_EXISTS_AND_THM] THEN
   GEN_TAC THEN
   `ASSOC smallfoot_ap_star` by REWRITE_TAC[smallfoot_ap_star___PROPERTIES] THEN
   FULL_SIMP_TAC std_ss [ASSOC_SYM] THEN
   Q.ABBREV_TAC `P = (smallfoot_ap_star
            (smallfoot_ap_data_list_seg_num x tl (smallfoot_ae_const n')
               (FMAP_MAP TL data1) e2)
            (smallfoot_ap_data_list_seg_num x' tl e2 data2 e3))` THEN

   `SMALLFOOT_AP_PERMISSION_UNIMPORTANT (smallfoot_ap_unequal e1 e2) /\
    (!data. SMALLFOOT_AP_PERMISSION_UNIMPORTANT (smallfoot_ap_points_to e1 ((FMAP_MAP (\dL. smallfoot_ae_const (HD dL)) data |+ (tl,smallfoot_ae_const n'))))) /\
    SMALLFOOT_AP_PERMISSION_UNIMPORTANT P /\
    (!x data. SMALLFOOT_AP_PERMISSION_UNIMPORTANT (smallfoot_ap_data_list_seg_num x tl (smallfoot_ae_const n') data e3))` by ALL_TAC THEN1 (
      Q.UNABBREV_TAC `P` THEN
      CONSEQ_REWRITE_TAC([],[SMALLFOOT_AP_PERMISSION_UNIMPORTANT___compare,
			 SMALLFOOT_AP_PERMISSION_UNIMPORTANT___points_to,
			 SMALLFOOT_AP_PERMISSION_UNIMPORTANT___data_list_seg_num,
			 SMALLFOOT_AP_PERMISSION_UNIMPORTANT___star,
			 FEVERY_STRENGTHEN_THM],[]) THEN
      ASM_SIMP_TAC std_ss [FEVERY_DEF, FMAP_MAP_THM, IS_SOME___SMALLFOOT_AE_USED_VARS___EVAL]
   ) THEN
   STRIP_TAC THEN
   `?x. s IN
    smallfoot_ap_star (smallfoot_ap_unequal e1 e2)
      (smallfoot_ap_star
         (smallfoot_ap_points_to e1 ((FMAP_MAP (\dL. smallfoot_ae_const (HD dL)) data1) |+ (tl,smallfoot_ae_const n')))
         (smallfoot_ap_data_list_seg_num x tl (smallfoot_ae_const n') (FMAP_MAP TL data3) e3))` by ALL_TAC THEN1 (
      Q.PAT_ASSUM `s IN X` MP_TAC THEN
      ASM_SIMP_TAC std_ss [smallfoot_ap_star___PERMISSION_UNIMPORTANT,
			   SMALLFOOT_AP_PERMISSION_UNIMPORTANT___star,
			   IN_ABS, GSYM RIGHT_EXISTS_AND_THM] THEN
      REPEAT STRIP_TAC THEN
      Q.PAT_ASSUM `!e1 e2 e3 data1 data2 data3 tl s x'. X e1 e2 e3 data1 data2 data3 tl s x'` 
         (MP_TAC o Q.SPECL [`(smallfoot_ae_const n')`, `e2`, `e3`, `FMAP_MAP TL data1`, `data2`, `FMAP_MAP TL data3`, `tl`, `(FST (s:smallfoot_state), h2')`, `x'`]) THEN
      Q.PAT_ASSUM `Abbrev (X \/ Y)` MP_TAC THEN
      ASM_SIMP_TAC std_ss [IS_SOME___SMALLFOOT_AE_USED_VARS___EVAL,
			   FDOM_FUNION, IN_UNION, FMAP_MAP_THM,
			   markerTheory.Abbrev_def] THEN
      MATCH_MP_TAC (prove (``(B2 /\ (A ==> B1) /\ (C ==> D)) ==> (A ==> (((B1 /\ B2) ==> C) ==> D))``,
			    METIS_TAC[])) THEN
      REPEAT CONJ_TAC THENL [
         REPEAT STRIP_TAC THEN
         Cases_on `data1 ' t` THEN1 (
	    FULL_SIMP_TAC std_ss [FEVERY_DEF] THEN
	    METIS_TAC[]
         ) THEN
         ASM_SIMP_TAC list_ss [],

         
         SIMP_TAC std_ss [DISJ_IMP_THM],


         REPEAT STRIP_TAC THEN
         Q.EXISTS_TAC `x''` THEN
         Q.EXISTS_TAC `h1` THEN
         Q.EXISTS_TAC `h1'` THEN
         Q.EXISTS_TAC `h2'` THEN
         FULL_SIMP_TAC std_ss [FDOM_FUNION]
     ]
   ) THEN

   Q.EXISTS_TAC `SUC x''` THEN
   ASM_SIMP_TAC std_ss [smallfoot_ap_data_list_seg_num_REWRITE___PERMISSION_UNIMPORTANT,
		        asl_exists_def, IN_ABS] THEN
   Q.EXISTS_TAC `n'` THEN
   Q.PAT_ASSUM `s IN X` MP_TAC THEN

   `FEVERY (\x. ~(SND x = [])) data3` by ALL_TAC THEN1 (
      FULL_SIMP_TAC list_ss [FEVERY_DEF]
   ) THEN
   ASM_SIMP_TAC list_ss [smallfoot_ap_star___PERMISSION_UNIMPORTANT,
			 SMALLFOOT_AP_PERMISSION_UNIMPORTANT___star,
			 IN_ABS, asl_bool_REWRITES,
			 SMALLFOOT_AP_PERMISSION_UNIMPORTANT___compare] THEN 
   SIMP_TAC std_ss [GSYM RIGHT_EXISTS_AND_THM,
		    smallfoot_ap_unequal_def,
		    smallfoot_ap_binexpression_def,
		    smallfoot_a_stack_proposition_def,
		    IN_ABS, FDOM_FEMPTY, DISJOINT_EMPTY,
		    FUNION_FEMPTY_1, LET_THM,
		    IS_SOME_EXISTS, GSYM RIGHT_EXISTS_AND_THM,
		    GSYM LEFT_EXISTS_AND_THM] THEN
   SIMP_TAC (std_ss++boolSimps.CONJ_ss) [] THEN  
   REPEAT STRIP_TAC THEN
   Q.EXISTS_TAC `h1'` THEN
   Q.EXISTS_TAC `h2'` THEN
   ASM_SIMP_TAC std_ss [] THEN


   Cases_on `e3 (FST s)` THEN1 (
      Q.PAT_ASSUM `(FST s, h2') IN X` MP_TAC THEN
      ONCE_REWRITE_TAC[smallfoot_ap_data_list_seg_num_REWRITE] THEN
      ASM_SIMP_TAC std_ss [COND_RAND, COND_RATOR,
		       smallfoot_ap_equal_def,
		       smallfoot_ap_weak_unequal_def,
		       smallfoot_ap_binexpression_def,
		       smallfoot_a_stack_proposition_def,
		       LET_THM, IN_ABS, asl_bool_EVAL]
   ) THEN
   FULL_SIMP_TAC std_ss [] THEN
   Q.PAT_ASSUM `(FST s, h1') IN X` MP_TAC THEN
   ASM_SIMP_TAC std_ss [smallfoot_ap_points_to_def,
		        IN_ABS, LET_THM, IN_SING,
		        FEVERY_DEF, FMAP_MAP_THM,
		        FAPPLY_FUPDATE_THM, FDOM_FUPDATE,
		        IN_INSERT, DISJ_IMP_THM, FORALL_AND_THM,
		        smallfoot_ae_const_def] THEN
   STRIP_TAC THEN CONJ_TAC THENL [
      FULL_SIMP_TAC std_ss [markerTheory.Abbrev_def,
			    FDOM_FUNION, IN_UNION,
			    IN_SING],


      GEN_TAC THEN STRIP_TAC THEN
      `x'''' IN FDOM data1 /\ x'''' IN FDOM data2 /\
       (data3 ' x'''' = data1 ' x'''' ++ data2 ' x'''')` by ASM_SIMP_TAC std_ss [] THEN
      Q.PAT_ASSUM `!x. X x` (MP_TAC o Q.SPEC `x''''`) THEN
      Cases_on `x'''' = tl` THEN (
         ASM_SIMP_TAC std_ss []
      ) THEN
      Tactical.REVERSE (Cases_on `data1 ' x''''`) THEN1 (
         ASM_SIMP_TAC list_ss []
      ) THEN
      FULL_SIMP_TAC std_ss [FEVERY_DEF] THEN
      METIS_TAC[]
  ]      
]);




val SMALLFOOT_DATA_LIST___DATA_LENGTH_PRED_def = Define `
SMALLFOOT_DATA_LIST___DATA_LENGTH_PRED data n =
((FDOM data = EMPTY) \/ (?t. t IN FDOM data /\ (n = LENGTH (data ' t))))`



val SMALLFOOT_DATA_LIST___DATA_LENGTH_PRED_THM = store_thm (
"SMALLFOOT_DATA_LIST___DATA_LENGTH_PRED_THM",

``(!n. SMALLFOOT_DATA_LIST___DATA_LENGTH_PRED FEMPTY n) /\
  (!data k v. SMALLFOOT_DATA_LIST___DATA_LENGTH_PRED (data |+ (k, v)) (LENGTH v))``,

SIMP_TAC std_ss [SMALLFOOT_DATA_LIST___DATA_LENGTH_PRED_def,
		 FDOM_FEMPTY, FDOM_FUPDATE, IN_INSERT, FAPPLY_FUPDATE_THM] THEN
METIS_TAC[]);





val SMALLFOOT_PROP_IMPLIES___data_list_seg___REMOVE_START = store_thm ("SMALLFOOT_PROP_IMPLIES___data_list_seg___REMOVE_START",
``!dl data1 data2 wpb rpb wpb' sfb_context sfb_split sfb_imp sfb_restP sr e1 e2 e3 tl.

smallfoot_ap_bag_implies_in_heap_or_null
   (BAG_UNION sfb_imp sfb_context) e3 ==>

((
SMALLFOOT_AE_USED_VARS_SUBSET (SET_OF_BAG (BAG_UNION wpb rpb))
              e1 /\
SMALLFOOT_AE_USED_VARS_SUBSET (SET_OF_BAG (BAG_UNION wpb rpb))
              e2 /\
SMALLFOOT_AE_USED_VARS_SUBSET (SET_OF_BAG (BAG_UNION wpb rpb))
              e3 /\
 (FDOM data2 SUBSET FDOM data1) /\
 SMALLFOOT_DATA_LIST___DATA_LENGTH_PRED data1 dl
)
  ==>


((SMALLFOOT_PROP_IMPLIES sr (wpb,rpb) wpb'
   (BAG_INSERT (smallfoot_ap_data_list_seg tl e1 data1 e2) sfb_context)
   sfb_split 
   (BAG_INSERT (smallfoot_ap_empty_heap_cond 
        (FEVERY (\x. ?l2. (SND x = (data1 ' (FST x) ++ l2))) data2))
   (BAG_INSERT (smallfoot_ap_data_list_seg tl e2 (FMAP_MAP (DROP dl) data2) e3) sfb_imp))
   sfb_restP) ==>

(SMALLFOOT_PROP_IMPLIES sr (wpb,rpb) wpb' 
   sfb_context
   (BAG_INSERT (smallfoot_ap_data_list_seg tl e1 data1 e2) sfb_split)
   (BAG_INSERT (smallfoot_ap_data_list_seg tl e1 data2 e3) sfb_imp) sfb_restP)))

``,

SIMP_TAC (std_ss++bool_eq_imp_ss) [SMALLFOOT_PROP_IMPLIES_EXPAND,
		 smallfoot_prop___COND_UNION,
    		 smallfoot_prop___COND_INSERT,
		 bagTheory.BAG_UNION_INSERT] THEN
REPEAT STRIP_TAC THEN
FULL_SIMP_TAC std_ss [] THEN
Q.EXISTS_TAC `sfb_rest` THEN
ASM_REWRITE_TAC[] THEN
STRIP_TAC THEN GEN_TAC THEN STRIP_TAC THEN
`!data. SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS
            (SET_OF_BAG (BAG_UNION wpb rpb))
            (smallfoot_ap_data_list_seg tl e2 data e3)` by ALL_TAC THEN1 (
   CONSEQ_REWRITE_TAC ([],[SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___data_list_seg],[]) THEN
   ASM_REWRITE_TAC[]
) THEN
FULL_SIMP_TAC std_ss [SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___smallfoot_ap_empty_heap_cond] THEN
Q.PAT_ASSUM `!s:smallfoot_state. X s` (MP_TAC o Q.SPEC `s`) THEN
ASM_SIMP_TAC std_ss [] THEN
STRIP_TAC THEN
Q.ABBREV_TAC `sfbX = BAG_UNION sfb_imp (BAG_UNION sfb_rest sfb_context)` THEN
`smallfoot_prop___COND (wpb,rpb) sfbX` by ALL_TAC THEN1 (
   Q.UNABBREV_TAC `sfbX` THEN
   ASM_SIMP_TAC std_ss [smallfoot_prop___COND_UNION,
		        smallfoot_prop___COND_INSERT]
) THEN
Q.PAT_ASSUM `smallfoot_prop___PROP Y X s` MP_TAC THEN

ASM_SIMP_TAC std_ss [smallfoot_prop___PROP___REWRITE,
		     smallfoot_ap_bigstar_REWRITE,
		     smallfoot_ap_star___swap_ap_stack_true] THEN

Q.ABBREV_TAC `P = smallfoot_ap_star (smallfoot_ap_data_list_seg tl e1 data1 e2)
                                    (smallfoot_ap_data_list_seg tl e2 (FMAP_MAP (DROP dl) data2) e3)` THEN
Q.ABBREV_TAC `Q = (smallfoot_ap_star smallfoot_ap_stack_true
            (smallfoot_ap_bigstar sfbX))` THEN

`smallfoot_ap_star (smallfoot_ap_data_list_seg tl e2 (FMAP_MAP (DROP dl) data2) e3)
      (smallfoot_ap_star (smallfoot_ap_data_list_seg tl e1 data1 e2) Q) =
 smallfoot_ap_star P Q` by (METIS_TAC[smallfoot_ap_star___PROPERTIES,
				     COMM_DEF, ASSOC_DEF]) THEN
ASM_REWRITE_TAC[] THEN POP_ASSUM (K ALL_TAC) THEN

`SMALLFOOT_AP_PERMISSION_UNIMPORTANT P /\
 SMALLFOOT_AP_PERMISSION_UNIMPORTANT Q /\ 
 SMALLFOOT_AP_PERMISSION_UNIMPORTANT (smallfoot_ap_data_list_seg tl e1 data2 e3)` by ALL_TAC THEN1 (
  
   FULL_SIMP_TAC std_ss [smallfoot_prop___COND___EXPAND,
			 SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS_def] THEN
   Q.UNABBREV_TAC `P` THEN
   MATCH_MP_TAC SMALLFOOT_AP_PERMISSION_UNIMPORTANT___star THEN
   ASM_REWRITE_TAC[]
) THEN

ASM_SIMP_TAC std_ss [smallfoot_ap_star___PERMISSION_UNIMPORTANT,
		     SMALLFOOT_AP_PERMISSION_UNIMPORTANT___star,
		     SMALLFOOT_AP_PERMISSION_UNIMPORTANT___smallfoot_ap_empty_heap_cond,
		     IN_ABS, smallfoot_ap_empty_heap_cond_def, IN_ABS,
                     FDOM_FEMPTY, FUNION_FEMPTY_1, DISJOINT_EMPTY] THEN
REPEAT STRIP_TAC THEN
Q.EXISTS_TAC `h1` THEN
Q.EXISTS_TAC `h2'` THEN
ASM_SIMP_TAC std_ss [] THEN

MATCH_MP_TAC smallfoot_ap_star___data_list_seg___append___data_list_seg THEN
Q.EXISTS_TAC `e2` THEN
Q.EXISTS_TAC `data1` THEN
Q.EXISTS_TAC `FMAP_MAP (DROP dl) data2` THEN
ASM_SIMP_TAC std_ss [CONJ_ASSOC] THEN
CONJ_TAC THENL [
   CONJ_TAC THEN1 (
      FULL_SIMP_TAC std_ss [IS_SOME___SMALLFOOT_AE_USED_VARS_def,
			    SMALLFOOT_AE_USED_VARS_SUBSET_def]
   ),
   ALL_TAC
] THENL [

   `smallfoot_ap_bag_implies_in_heap_or_null sfbX e3` by ALL_TAC THEN1 (
      MATCH_MP_TAC smallfoot_ap_bag_implies_in_heap_or_null___SUB_BAG THEN
      Q.EXISTS_TAC `BAG_UNION sfb_imp sfb_context` THEN
      Q.UNABBREV_TAC `sfbX` THEN
      ASM_SIMP_TAC std_ss [bagTheory.SUB_BAG_UNION_eliminate,
		        bagTheory.SUB_BAG_UNION,
		        bagTheory.SUB_BAG_REFL]
   ) THEN
   POP_ASSUM MP_TAC THEN

   ASM_SIMP_TAC std_ss [smallfoot_ap_bag_implies_in_heap_or_null_def,
		     smallfoot_ap_bigstar_REWRITE] THEN
   FULL_SIMP_TAC std_ss [BAG_EVERY_def,
		      smallfoot_prop___COND___REWRITE,
		      SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS_def, 
                     GSYM LEFT_EXISTS_IMP_THM] THEN
   Q.EXISTS_TAC `(FST (s:smallfoot_state), h2')` THEN
   ASM_SIMP_TAC std_ss [GSYM LEFT_FORALL_IMP_THM, 
		     IN_INSERT, 
		     LEFT_AND_OVER_OR, DISJ_IMP_THM] THEN
   REPEAT STRIP_TAC THEN
   FULL_SIMP_TAC std_ss [DISJOINT_DEF, EXTENSION, IN_INTER,
		      NOT_IN_EMPTY] THEN
   METIS_TAC[],



   GEN_TAC THEN STRIP_TAC THEN
   FULL_SIMP_TAC std_ss [SUBSET_DEF, FUN_FMAP_DEF, FDOM_FINITE,
			 FEVERY_DEF] THEN
   `?l2. data2 ' t = data1 ' t ++ l2` by METIS_TAC[] THEN
   ASM_SIMP_TAC list_ss [FMAP_MAP_THM] THEN
   Tactical.REVERSE (`dl = LENGTH (data1 ' t)` by ALL_TAC) THEN1 (
      ASM_SIMP_TAC list_ss [BUTFIRSTN_LENGTH_APPEND]
   ) THEN
   `?t2. t2 IN FDOM data1 /\ (dl = LENGTH (data1 ' t2))` by ALL_TAC THEN1 (
      FULL_SIMP_TAC std_ss [SMALLFOOT_DATA_LIST___DATA_LENGTH_PRED_def, EXTENSION, NOT_IN_EMPTY] THEN
      METIS_TAC[]       
   ) THEN
   ASM_REWRITE_TAC[] THEN
   Cases_on `?n. FEVERY (\x. LENGTH (SND x) = n) data1` THEN1 (
      FULL_SIMP_TAC std_ss [FEVERY_DEF]
   ) THEN
   `P = smallfoot_ap_false` by ALL_TAC THEN1 (
      Q.UNABBREV_TAC `P` THEN
      IMP_RES_TAC smallfoot_ap_data_list_seg___DATA_LENGTH THEN
      ASM_SIMP_TAC std_ss [smallfoot_ap_false___smallfoot_ap_star_THM]
   ) THEN
   FULL_SIMP_TAC std_ss [smallfoot_ap_false___NOT_IN]
]);









val SMALLFOOT_PROP_IMPLIES___data_list___REMOVE_START = store_thm ("SMALLFOOT_PROP_IMPLIES___data_list___REMOVE_START",
``!dl data1 data2 wpb rpb wpb' sfb_context sfb_split sfb_imp sfb_rest sr e1 e2 tl.

(
SMALLFOOT_AE_USED_VARS_SUBSET (SET_OF_BAG (BAG_UNION wpb rpb))
              e1 /\
SMALLFOOT_AE_USED_VARS_SUBSET (SET_OF_BAG (BAG_UNION wpb rpb))
              e2 /\
(FDOM data2 SUBSET FDOM data1) /\
 SMALLFOOT_DATA_LIST___DATA_LENGTH_PRED data1 dl)
  ==>


((SMALLFOOT_PROP_IMPLIES sr (wpb,rpb) wpb'
   (BAG_INSERT (smallfoot_ap_data_list_seg tl e1 data1 e2) sfb_context)
   sfb_split 
   (BAG_INSERT (smallfoot_ap_empty_heap_cond 
        (FEVERY (\x. ?l2. (SND x = (data1 ' (FST x) ++ l2))) data2))
   (BAG_INSERT (smallfoot_ap_data_list tl e2 (FMAP_MAP (DROP dl) data2)) sfb_imp))
   sfb_rest) ==>

(SMALLFOOT_PROP_IMPLIES sr (wpb,rpb) wpb' 
   sfb_context
   (BAG_INSERT (smallfoot_ap_data_list_seg tl e1 data1 e2) sfb_split)
   (BAG_INSERT (smallfoot_ap_data_list tl e1 data2) sfb_imp) sfb_rest))

``,


ASM_REWRITE_TAC[smallfoot_ap_data_list_def] THEN
REPEAT STRIP_TAC THEN
MATCH_MP_TAC (SIMP_RULE std_ss [AND_IMP_INTRO] SMALLFOOT_PROP_IMPLIES___data_list_seg___REMOVE_START) THEN
Q.EXISTS_TAC `dl` THEN
ASM_SIMP_TAC std_ss [SMALLFOOT_AE_USED_VARS_SUBSET___EVAL,
		     smallfoot_ap_bag_implies_in_heap_or_null___ae_null]);









val smallfoot_ap_unequal_cond___UNEQ_REWRITE___const =
store_thm ("smallfoot_ap_unequal_cond___UNEQ_REWRITE___const",
``!c1 c2 P. ~(c1 = c2) ==>
          (smallfoot_ap_unequal_cond (smallfoot_ae_const c1)
		                               (smallfoot_ae_const c2) P =
           smallfoot_ap_equal_cond smallfoot_ae_null
	                             smallfoot_ae_null P)``,

SIMP_TAC std_ss [smallfoot_ap_unequal_cond_def,
		 smallfoot_ap_equal_cond_def,
		 smallfoot_ap_binexpression_cond_def,
		 smallfoot_ae_null_def, smallfoot_ae_const_def,
		 smallfoot_ap_binexpression_def, LET_THM, IN_ABS]);




val smallfoot_ap_equal_cond___UNEQ_REWRITE___const =
store_thm ("smallfoot_ap_equal_cond___UNEQ_REWRITE___const",
``!c1 c2 P. ~(c1 = c2) ==>
          (smallfoot_ap_equal_cond (smallfoot_ae_const c1)
		                   (smallfoot_ae_const c2) P =
           smallfoot_ap_unequal_cond smallfoot_ae_null
	                             smallfoot_ae_null P)``,

SIMP_TAC std_ss [smallfoot_ap_unequal_cond_def,
		 smallfoot_ap_equal_cond_def,
		 smallfoot_ap_binexpression_cond_def,
		 smallfoot_ae_null_def, smallfoot_ae_const_def,
		 smallfoot_ap_binexpression_def, LET_THM, IN_ABS]);





val SMALLFOOT_COND_PROP___EQ___EQUAL_UNEQUAL_COND =
store_thm ("SMALLFOOT_COND_PROP___EQ___EQUAL_UNEQUAL_COND",
``!wpb rpb sfb sf e1 e2.
  (SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS
          (SET_OF_BAG (BAG_UNION wpb rpb)) sf /\
   SMALLFOOT_AE_USED_VARS_SUBSET (SET_OF_BAG (BAG_UNION wpb rpb)) e1 /\
   SMALLFOOT_AE_USED_VARS_SUBSET (SET_OF_BAG (BAG_UNION wpb rpb)) e2) ==>

  (
  ((smallfoot_prop (wpb,rpb) (BAG_INSERT (smallfoot_ap_equal e1 e2)
                             (BAG_INSERT (smallfoot_ap_equal_cond e1 e2 sf)
                             sfb))) =
   smallfoot_prop (wpb,rpb) (BAG_INSERT (smallfoot_ap_equal e1 e2)
                            (BAG_INSERT sf sfb))) /\
  ((smallfoot_prop (wpb,rpb) (BAG_INSERT (smallfoot_ap_unequal e1 e2)
                             (BAG_INSERT (smallfoot_ap_unequal_cond e1 e2 sf)
                             sfb))) =
   smallfoot_prop (wpb,rpb) (BAG_INSERT (smallfoot_ap_unequal e1 e2)
                            (BAG_INSERT sf sfb))) /\

  ((smallfoot_prop (wpb,rpb) (BAG_INSERT (smallfoot_ap_unequal e1 e2)
                             (BAG_INSERT (smallfoot_ap_equal_cond e1 e2 sf)
                             sfb))) =
   smallfoot_prop (wpb,rpb) (BAG_INSERT (smallfoot_ap_unequal e1 e2)
                            sfb)) /\

  ((smallfoot_prop (wpb,rpb) (BAG_INSERT (smallfoot_ap_equal e1 e2)
                             (BAG_INSERT (smallfoot_ap_unequal_cond e1 e2 sf)
                             sfb))) =
   smallfoot_prop (wpb,rpb) (BAG_INSERT (smallfoot_ap_equal e1 e2)
                            sfb)) /\


  ((smallfoot_prop (wpb,rpb) (BAG_INSERT (smallfoot_ap_equal_cond e1 e1 sf)
                             sfb)) =
   smallfoot_prop (wpb,rpb) (BAG_INSERT sf sfb)) /\

  ((smallfoot_prop (wpb,rpb) (BAG_INSERT (smallfoot_ap_unequal_cond e1 e1 sf)
                             sfb)) =
   smallfoot_prop (wpb,rpb) sfb)
)``,


SIMP_TAC std_ss [smallfoot_prop___REWRITE,
		 smallfoot_prop___COND_INSERT] THEN
REPEAT GEN_TAC THEN STRIP_TAC THEN
ASM_SIMP_TAC std_ss [SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___smallfoot_ap_equal_cond,
                     SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___smallfoot_ap_unequal_cond,
		     SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___compare] THEN
Cases_on `smallfoot_prop___COND (wpb,rpb) sfb` THEN ASM_REWRITE_TAC[] THEN

ASM_SIMP_TAC std_ss [smallfoot_prop___PROP_INSERT, smallfoot_prop___COND_INSERT,
                     SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___smallfoot_ap_equal_cond,
                     SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___smallfoot_ap_unequal_cond,
		     SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___compare] THEN
ONCE_REWRITE_TAC[EXTENSION] THEN
SIMP_TAC std_ss [smallfoot_ap_equal_def, IN_ABS, GSYM RIGHT_EXISTS_AND_THM,
		 smallfoot_ap_binexpression_def, smallfoot_ap_unequal_def,
		 smallfoot_a_stack_proposition_def,
		 FUNION_FEMPTY_1, FDOM_FEMPTY, DISJOINT_EMPTY,
		 LET_THM, smallfoot_ap_equal_cond_def,
                 smallfoot_ap_unequal_cond_def,
		 smallfoot_ap_binexpression_cond_def,
		 asl_cond_def, GSYM FORALL_AND_THM] THEN
`SMALLFOOT_AP_PERMISSION_UNIMPORTANT sf` by FULL_SIMP_TAC std_ss [SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS_def] THEN
GEN_TAC THEN

Cases_on `!h2. ~((FST x,h2) IN smallfoot_prop___PROP (wpb,rpb) sfb)` THEN1 (
   Cases_on `x` THEN
   FULL_SIMP_TAC std_ss []
) THEN
FULL_SIMP_TAC std_ss [] THEN
`IS_SOME (e1 (FST x)) /\
 IS_SOME (e2 (FST x))` by ALL_TAC THEN1 (
   FULL_SIMP_TAC std_ss [SMALLFOOT_AE_USED_VARS_SUBSET___REWRITE,
		      SMALLFOOT_AE_USED_VARS_REL___REWRITE, SUBSET_DEF,
		      smallfoot_prop___PROP___REWRITE,
		      IN_ABS, var_res_sl___has_read_permission_def,
		      var_res_sl___has_write_permission_def,
		      bagTheory.BAG_IN_BAG_UNION,
		      bagTheory.IN_SET_OF_BAG, GSYM IS_SOME_EXISTS] THEN
   METIS_TAC[]
) THEN

FULL_SIMP_TAC std_ss [IS_SOME_EXISTS] THEN
ASM_SIMP_TAC (std_ss++boolSimps.CONJ_ss) [smallfoot_ap_star___ap_stack_true___PERMISSION_UNIMPORTANT] THEN
SIMP_TAC std_ss [smallfoot_ap_stack_true_def, IN_ABS,
	         FUNION_FEMPTY_1, FDOM_FEMPTY,
	         DISJOINT_EMPTY]);


val SMALLFOOT_COND_PROP___EQ___EQUAL_UNEQUAL_COND_LIST = 
CONJUNCTS (
SIMP_RULE std_ss [IMP_CONJ_THM, prove (``(!e1 e2. (P1 /\ P2 e1 /\ P2 e2) ==> (Q e1)) =
         (!e. (P1 /\ P2 e) ==> Q e)``, METIS_TAC[]),
		  FORALL_AND_THM] SMALLFOOT_COND_PROP___EQ___EQUAL_UNEQUAL_COND)



val SMALLFOOT_COND_PROP___EQ___EQUAL_UNEQUAL_COND___EQ_EQ =
save_thm ("SMALLFOOT_COND_PROP___EQ___EQUAL_UNEQUAL_COND___EQ_EQ",
el 1 SMALLFOOT_COND_PROP___EQ___EQUAL_UNEQUAL_COND_LIST);

val SMALLFOOT_COND_PROP___EQ___EQUAL_UNEQUAL_COND___UNEQ_UNEQ =
save_thm ("SMALLFOOT_COND_PROP___EQ___EQUAL_UNEQUAL_COND___UNEQ_UNEQ",
el 2 SMALLFOOT_COND_PROP___EQ___EQUAL_UNEQUAL_COND_LIST);

val SMALLFOOT_COND_PROP___EQ___EQUAL_UNEQUAL_COND___UNEQ_EQ =
save_thm ("SMALLFOOT_COND_PROP___EQ___EQUAL_UNEQUAL_COND___UNEQ_EQ",
el 3 SMALLFOOT_COND_PROP___EQ___EQUAL_UNEQUAL_COND_LIST);

val SMALLFOOT_COND_PROP___EQ___EQUAL_UNEQUAL_COND___EQ_UNEQ =
save_thm ("SMALLFOOT_COND_PROP___EQ___EQUAL_UNEQUAL_COND___EQ_UNEQ",
el 4 SMALLFOOT_COND_PROP___EQ___EQUAL_UNEQUAL_COND_LIST);


val SMALLFOOT_COND_PROP___EQ___EQUAL_UNEQUAL_COND___IDEM_EQ =
save_thm ("SMALLFOOT_COND_PROP___EQ___EQUAL_UNEQUAL_COND___IDEM_EQ",
el 5 SMALLFOOT_COND_PROP___EQ___EQUAL_UNEQUAL_COND_LIST);

val SMALLFOOT_COND_PROP___EQ___EQUAL_UNEQUAL_COND___IDEM_UNEQ =
save_thm ("SMALLFOOT_COND_PROP___EQ___EQUAL_UNEQUAL_COND___IDEM_UNEQ",
el 6 SMALLFOOT_COND_PROP___EQ___EQUAL_UNEQUAL_COND_LIST);




















val SMALLFOOT_PROP_IMPLIES___EQ___EQUAL_UNEQUAL_COND =
store_thm ("SMALLFOOT_PROP_IMPLIES___EQ___EQUAL_UNEQUAL_COND",
``!strong_rest wpb rpb wpb' sfb_context sfb_split sfb_imp sfb_restP sf e1 e2.
  (SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS
          (SET_OF_BAG (BAG_UNION wpb rpb)) sf /\
   SMALLFOOT_AE_USED_VARS_SUBSET (SET_OF_BAG (BAG_UNION wpb rpb)) e1 /\
   SMALLFOOT_AE_USED_VARS_SUBSET (SET_OF_BAG (BAG_UNION wpb rpb)) e2) ==>

  (
  ((SMALLFOOT_PROP_IMPLIES strong_rest (wpb,rpb) wpb'
         (BAG_INSERT (smallfoot_ap_equal e1 e2) sfb_context)
	 sfb_split
         (BAG_INSERT (smallfoot_ap_equal_cond e1 e2 sf) sfb_imp)
         sfb_restP) =
   (SMALLFOOT_PROP_IMPLIES strong_rest (wpb,rpb) wpb'
         (BAG_INSERT (smallfoot_ap_equal e1 e2) sfb_context)
	 sfb_split
         (BAG_INSERT sf sfb_imp)
         sfb_restP)) /\

  ((SMALLFOOT_PROP_IMPLIES strong_rest (wpb,rpb) wpb'
         (BAG_INSERT (smallfoot_ap_unequal e1 e2) sfb_context)
	 sfb_split
         (BAG_INSERT (smallfoot_ap_unequal_cond e1 e2 sf) sfb_imp)
         sfb_restP) =
   (SMALLFOOT_PROP_IMPLIES strong_rest (wpb,rpb) wpb'
         (BAG_INSERT (smallfoot_ap_unequal e1 e2) sfb_context)
	 sfb_split
         (BAG_INSERT sf sfb_imp)
         sfb_restP)) /\

  ((SMALLFOOT_PROP_IMPLIES strong_rest (wpb,rpb) wpb'
         (BAG_INSERT (smallfoot_ap_unequal e1 e2) sfb_context)
	 sfb_split
         (BAG_INSERT (smallfoot_ap_equal_cond e1 e2 sf) sfb_imp)
         sfb_restP) =
   (SMALLFOOT_PROP_IMPLIES strong_rest (wpb,rpb) wpb'
         (BAG_INSERT (smallfoot_ap_unequal e1 e2) sfb_context)
	 sfb_split
         sfb_imp
         sfb_restP)) /\

  ((SMALLFOOT_PROP_IMPLIES strong_rest (wpb,rpb) wpb'
         (BAG_INSERT (smallfoot_ap_equal e1 e2) sfb_context)
	 sfb_split
         (BAG_INSERT (smallfoot_ap_unequal_cond e1 e2 sf) sfb_imp)
         sfb_restP) =
   (SMALLFOOT_PROP_IMPLIES strong_rest (wpb,rpb) wpb'
         (BAG_INSERT (smallfoot_ap_equal e1 e2) sfb_context)
	 sfb_split
         sfb_imp
         sfb_restP)) /\


  ((SMALLFOOT_PROP_IMPLIES strong_rest (wpb,rpb) wpb'
         sfb_context
	 sfb_split
         (BAG_INSERT (smallfoot_ap_equal_cond e1 e1 sf) sfb_imp)
         sfb_restP) =
   (SMALLFOOT_PROP_IMPLIES strong_rest (wpb,rpb) wpb'
         sfb_context
	 sfb_split
         (BAG_INSERT sf sfb_imp)
         sfb_restP)) /\


  ((SMALLFOOT_PROP_IMPLIES strong_rest (wpb,rpb) wpb'
         sfb_context
	 sfb_split
         (BAG_INSERT (smallfoot_ap_unequal_cond e1 e1 sf) sfb_imp)
         sfb_restP) =
   (SMALLFOOT_PROP_IMPLIES strong_rest (wpb,rpb) wpb'
         sfb_context
	 sfb_split
         sfb_imp
         sfb_restP)))``,



SIMP_TAC std_ss [SMALLFOOT_PROP_IMPLIES_EXPAND,
		 bagTheory.BAG_UNION_INSERT,
		 smallfoot_prop___COND_INSERT,
		 smallfoot_prop___COND_UNION] THEN
REPEAT GEN_TAC THEN STRIP_TAC THEN
Cases_on `sfb_restP = EMPTY` THEN ASM_REWRITE_TAC[] THEN
DEPTH_CONSEQ_CONV_TAC (K EXISTS_EQ___CONSEQ_CONV) THEN
SIMP_TAC std_ss [GSYM FORALL_AND_THM] THEN 
GEN_TAC THEN
ASM_SIMP_TAC std_ss [SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___smallfoot_ap_equal_cond,
                     SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___smallfoot_ap_unequal_cond,
		     SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___compare] THEN
Cases_on `sfb_restP sfb_rest` THEN ASM_REWRITE_TAC[] THEN
Cases_on `smallfoot_prop___COND (wpb,rpb) sfb_context` THEN ASM_REWRITE_TAC[] THEN
Cases_on `smallfoot_prop___COND (wpb,rpb) sfb_split` THEN ASM_REWRITE_TAC[] THEN
Cases_on `smallfoot_prop___COND (wpb,rpb) sfb_imp` THEN ASM_REWRITE_TAC[] THEN
Cases_on `smallfoot_prop___COND (wpb,rpb) sfb_rest` THEN ASM_REWRITE_TAC[] THEN
Cases_on `smallfoot_prop___COND (BAG_DIFF wpb wpb',BAG_DIFF rpb wpb')
         sfb_rest` THEN ASM_REWRITE_TAC[] THEN

ASM_SIMP_TAC std_ss [smallfoot_prop___PROP_INSERT, smallfoot_prop___COND_INSERT,
		     smallfoot_prop___COND_UNION,
                     SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___smallfoot_ap_equal_cond,
                     SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___smallfoot_ap_unequal_cond,
		     SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___compare] THEN
SIMP_TAC std_ss [smallfoot_ap_equal_def, IN_ABS, GSYM RIGHT_EXISTS_AND_THM,
		 smallfoot_ap_binexpression_def, smallfoot_ap_unequal_def,
		 smallfoot_a_stack_proposition_def,
		 FUNION_FEMPTY_1, FDOM_FEMPTY, DISJOINT_EMPTY,
		 LET_THM, smallfoot_ap_equal_cond_def,
                 smallfoot_ap_unequal_cond_def,
		 smallfoot_ap_binexpression_cond_def,
		 asl_cond_def, GSYM FORALL_AND_THM] THEN
`SMALLFOOT_AP_PERMISSION_UNIMPORTANT sf` by FULL_SIMP_TAC std_ss [SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS_def] THEN
DEPTH_CONSEQ_CONV_TAC (K FORALL_EQ___CONSEQ_CONV) THEN
SIMP_TAC (std_ss++bool_eq_imp_ss) [GSYM FORALL_AND_THM] THEN
GEN_TAC THEN

Tactical.REVERSE (Cases_on `s IN
     smallfoot_prop___PROP (wpb,rpb) (BAG_UNION sfb_split sfb_context)`) THEN1 (
   FULL_SIMP_TAC std_ss [IN_DEF]
) THEN
`smallfoot_prop___PROP (wpb,rpb) (BAG_UNION sfb_split sfb_context) s` by
  FULL_SIMP_TAC std_ss [IN_DEF] THEN
ASM_SIMP_TAC std_ss [smallfoot_ap_star___ap_stack_true___PERMISSION_UNIMPORTANT] THEN
`IS_SOME (e1 (FST s)) /\
 IS_SOME (e2 (FST s))` by ALL_TAC THEN1 (
   FULL_SIMP_TAC std_ss [SMALLFOOT_AE_USED_VARS_SUBSET___REWRITE,
		      SMALLFOOT_AE_USED_VARS_REL___REWRITE, SUBSET_DEF,
		      smallfoot_prop___PROP___REWRITE,
		      IN_ABS, var_res_sl___has_read_permission_def,
		      var_res_sl___has_write_permission_def,
		      bagTheory.BAG_IN_BAG_UNION,
		      bagTheory.IN_SET_OF_BAG, GSYM IS_SOME_EXISTS] THEN
   METIS_TAC[]
) THEN

FULL_SIMP_TAC std_ss [IS_SOME_EXISTS] THEN
SIMP_TAC std_ss [smallfoot_ap_stack_true_def, IN_ABS,
	         FUNION_FEMPTY_1, FDOM_FEMPTY,
	         DISJOINT_EMPTY, IN_DEF]);









val SMALLFOOT_PROP_IMPLIES___EQ___EQUAL_UNEQUAL_COND_LIST = 
CONJUNCTS (
SIMP_RULE std_ss [IMP_CONJ_THM, prove (``(!e1 e2. (P1 /\ P2 e1 /\ P2 e2) ==> (Q e1)) =
         (!e. (P1 /\ P2 e) ==> Q e)``, METIS_TAC[]),
		  FORALL_AND_THM] SMALLFOOT_PROP_IMPLIES___EQ___EQUAL_UNEQUAL_COND)



val SMALLFOOT_PROP_IMPLIES___EQ___EQUAL_UNEQUAL_COND___EQ_EQ =
save_thm ("SMALLFOOT_PROP_IMPLIES___EQ___EQUAL_UNEQUAL_COND___EQ_EQ",
el 1 SMALLFOOT_PROP_IMPLIES___EQ___EQUAL_UNEQUAL_COND_LIST);

val SMALLFOOT_PROP_IMPLIES___EQ___EQUAL_UNEQUAL_COND___UNEQ_UNEQ =
save_thm ("SMALLFOOT_PROP_IMPLIES___EQ___EQUAL_UNEQUAL_COND___UNEQ_UNEQ",
el 2 SMALLFOOT_PROP_IMPLIES___EQ___EQUAL_UNEQUAL_COND_LIST);

val SMALLFOOT_PROP_IMPLIES___EQ___EQUAL_UNEQUAL_COND___UNEQ_EQ =
save_thm ("SMALLFOOT_PROP_IMPLIES___EQ___EQUAL_UNEQUAL_COND___UNEQ_EQ",
el 3 SMALLFOOT_PROP_IMPLIES___EQ___EQUAL_UNEQUAL_COND_LIST);

val SMALLFOOT_PROP_IMPLIES___EQ___EQUAL_UNEQUAL_COND___EQ_UNEQ =
save_thm ("SMALLFOOT_PROP_IMPLIES___EQ___EQUAL_UNEQUAL_COND___EQ_UNEQ",
el 4 SMALLFOOT_PROP_IMPLIES___EQ___EQUAL_UNEQUAL_COND_LIST);


val SMALLFOOT_PROP_IMPLIES___EQ___EQUAL_UNEQUAL_COND___IDEM_EQ =
save_thm ("SMALLFOOT_PROP_IMPLIES___EQ___EQUAL_UNEQUAL_COND___IDEM_EQ",
el 5 SMALLFOOT_PROP_IMPLIES___EQ___EQUAL_UNEQUAL_COND_LIST);

val SMALLFOOT_PROP_IMPLIES___EQ___EQUAL_UNEQUAL_COND___IDEM_UNEQ =
save_thm ("SMALLFOOT_PROP_IMPLIES___EQ___EQUAL_UNEQUAL_COND___IDEM_UNEQ",
el 6 SMALLFOOT_PROP_IMPLIES___EQ___EQUAL_UNEQUAL_COND_LIST);












val SMALLFOOT_PROP_IMPLIES___EQ___SPLIT_EQUAL_UNEQUAL_COND =
store_thm ("SMALLFOOT_PROP_IMPLIES___EQ___SPLIT_EQUAL_UNEQUAL_COND",
``!strong_rest wpb rpb wpb' sfb_context sfb_split sfb_imp sfb_restP sf e1 e2.
  (SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS
          (SET_OF_BAG (BAG_UNION wpb rpb)) sf /\
   SMALLFOOT_AE_USED_VARS_SUBSET (SET_OF_BAG (BAG_UNION wpb rpb)) e1 /\
   SMALLFOOT_AE_USED_VARS_SUBSET (SET_OF_BAG (BAG_UNION wpb rpb)) e2) ==>

  (
  ((SMALLFOOT_PROP_IMPLIES strong_rest (wpb,rpb) wpb'
         (BAG_INSERT (smallfoot_ap_equal e1 e2) sfb_context)
         (BAG_INSERT (smallfoot_ap_equal_cond e1 e2 sf) sfb_split)
         sfb_imp
         sfb_restP) =
   (SMALLFOOT_PROP_IMPLIES strong_rest (wpb,rpb) wpb'
         (BAG_INSERT (smallfoot_ap_equal e1 e2) sfb_context)
         (BAG_INSERT sf sfb_split)
	 sfb_imp
         sfb_restP)) /\

  ((SMALLFOOT_PROP_IMPLIES strong_rest (wpb,rpb) wpb'
         (BAG_INSERT (smallfoot_ap_unequal e1 e2) sfb_context)
         (BAG_INSERT (smallfoot_ap_unequal_cond e1 e2 sf) sfb_split)
	 sfb_imp
         sfb_restP) =
   (SMALLFOOT_PROP_IMPLIES strong_rest (wpb,rpb) wpb'
         (BAG_INSERT (smallfoot_ap_unequal e1 e2) sfb_context)
         (BAG_INSERT sf sfb_split)
	 sfb_imp
         sfb_restP)) /\

  ((SMALLFOOT_PROP_IMPLIES strong_rest (wpb,rpb) wpb'
         (BAG_INSERT (smallfoot_ap_unequal e1 e2) sfb_context)
         (BAG_INSERT (smallfoot_ap_equal_cond e1 e2 sf) sfb_split)
	 sfb_imp
         sfb_restP) =
   (SMALLFOOT_PROP_IMPLIES strong_rest (wpb,rpb) wpb'
         (BAG_INSERT (smallfoot_ap_unequal e1 e2) sfb_context)
         sfb_split
	 sfb_imp
         sfb_restP)) /\

  ((SMALLFOOT_PROP_IMPLIES strong_rest (wpb,rpb) wpb'
         (BAG_INSERT (smallfoot_ap_equal e1 e2) sfb_context)
         (BAG_INSERT (smallfoot_ap_unequal_cond e1 e2 sf) sfb_split)
	 sfb_imp
         sfb_restP) =
   (SMALLFOOT_PROP_IMPLIES strong_rest (wpb,rpb) wpb'
         (BAG_INSERT (smallfoot_ap_equal e1 e2) sfb_context)
         sfb_split
	 sfb_imp
         sfb_restP)) /\


  ((SMALLFOOT_PROP_IMPLIES strong_rest (wpb,rpb) wpb'
         sfb_context
         (BAG_INSERT (smallfoot_ap_equal_cond e1 e1 sf) sfb_split)
	 sfb_imp
         sfb_restP) =
   (SMALLFOOT_PROP_IMPLIES strong_rest (wpb,rpb) wpb'
         sfb_context
         (BAG_INSERT sf sfb_split)
	 sfb_imp
         sfb_restP)) /\


  ((SMALLFOOT_PROP_IMPLIES strong_rest (wpb,rpb) wpb'
         sfb_context
         (BAG_INSERT (smallfoot_ap_unequal_cond e1 e1 sf) sfb_split)
	 sfb_imp
         sfb_restP) =
   (SMALLFOOT_PROP_IMPLIES strong_rest (wpb,rpb) wpb'
         sfb_context
         sfb_split
	 sfb_imp
         sfb_restP)))``,



SIMP_TAC std_ss [SMALLFOOT_PROP_IMPLIES_EXPAND,
		 bagTheory.BAG_UNION_INSERT,
		 smallfoot_prop___COND_INSERT,
		 smallfoot_prop___COND_UNION] THEN
REPEAT GEN_TAC THEN STRIP_TAC THEN
Cases_on `sfb_restP = EMPTY` THEN ASM_REWRITE_TAC[] THEN
DEPTH_CONSEQ_CONV_TAC (K EXISTS_EQ___CONSEQ_CONV) THEN
SIMP_TAC std_ss [GSYM FORALL_AND_THM] THEN 
GEN_TAC THEN
ASM_SIMP_TAC std_ss [SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___smallfoot_ap_equal_cond,
                     SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___smallfoot_ap_unequal_cond,
		     SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___compare] THEN
Cases_on `sfb_restP sfb_rest` THEN ASM_REWRITE_TAC[] THEN
Cases_on `smallfoot_prop___COND (wpb,rpb) sfb_context` THEN ASM_REWRITE_TAC[] THEN
Cases_on `smallfoot_prop___COND (wpb,rpb) sfb_split` THEN ASM_REWRITE_TAC[] THEN
Cases_on `smallfoot_prop___COND (wpb,rpb) sfb_imp` THEN ASM_REWRITE_TAC[] THEN
DEPTH_CONSEQ_CONV_TAC (K (HO_PART_MATCH (snd o dest_imp)
		       (prove (``(P1 = P2) ==>
                                 ((!s. (P1 s ==> Q s)) = (!s. (P2 s ==> Q s)))``,
		              METIS_TAC[])))) THEN
CONV_TAC (DEPTH_CONV ETA_CONV) THEN

MP_TAC (Q.SPECL [`wpb`, `rpb`, `BAG_UNION sfb_split sfb_context`, `sf`, `e1`, `e2`] 
(SIMP_RULE (std_ss++boolSimps.CONJ_ss) 
   [smallfoot_prop___REWRITE, COND_EQ_REWRITE] SMALLFOOT_COND_PROP___EQ___EQUAL_UNEQUAL_COND)) THEN
ASM_SIMP_TAC std_ss [smallfoot_prop___COND_UNION, smallfoot_prop___COND_INSERT,
		     SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___compare,
		     SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___smallfoot_ap_unequal_cond,
		     SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___smallfoot_ap_equal_cond] THEN
METIS_TAC[bagTheory.BAG_INSERT_commutes]);







val SMALLFOOT_PROP_IMPLIES___EQ___SPLIT_EQUAL_UNEQUAL_COND_LIST = 
CONJUNCTS (
SIMP_RULE std_ss [IMP_CONJ_THM, prove (``(!e1 e2. (P1 /\ P2 e1 /\ P2 e2) ==> (Q e1)) =
         (!e. (P1 /\ P2 e) ==> Q e)``, METIS_TAC[]),
		  FORALL_AND_THM] SMALLFOOT_PROP_IMPLIES___EQ___SPLIT_EQUAL_UNEQUAL_COND)



val SMALLFOOT_PROP_IMPLIES___EQ___SPLIT_EQUAL_UNEQUAL_COND___EQ_EQ =
save_thm ("SMALLFOOT_PROP_IMPLIES___EQ___SPLIT_EQUAL_UNEQUAL_COND___EQ_EQ",
el 1 SMALLFOOT_PROP_IMPLIES___EQ___SPLIT_EQUAL_UNEQUAL_COND_LIST);

val SMALLFOOT_PROP_IMPLIES___EQ___SPLIT_EQUAL_UNEQUAL_COND___UNEQ_UNEQ =
save_thm ("SMALLFOOT_PROP_IMPLIES___EQ___SPLIT_EQUAL_UNEQUAL_COND___UNEQ_UNEQ",
el 2 SMALLFOOT_PROP_IMPLIES___EQ___SPLIT_EQUAL_UNEQUAL_COND_LIST);

val SMALLFOOT_PROP_IMPLIES___EQ___SPLIT_EQUAL_UNEQUAL_COND___UNEQ_EQ =
save_thm ("SMALLFOOT_PROP_IMPLIES___EQ___SPLIT_EQUAL_UNEQUAL_COND___UNEQ_EQ",
el 3 SMALLFOOT_PROP_IMPLIES___EQ___SPLIT_EQUAL_UNEQUAL_COND_LIST);

val SMALLFOOT_PROP_IMPLIES___EQ___SPLIT_EQUAL_UNEQUAL_COND___EQ_UNEQ =
save_thm ("SMALLFOOT_PROP_IMPLIES___EQ___SPLIT_EQUAL_UNEQUAL_COND___EQ_UNEQ",
el 4 SMALLFOOT_PROP_IMPLIES___EQ___SPLIT_EQUAL_UNEQUAL_COND_LIST);


val SMALLFOOT_PROP_IMPLIES___EQ___SPLIT_EQUAL_UNEQUAL_COND___IDEM_EQ =
save_thm ("SMALLFOOT_PROP_IMPLIES___EQ___SPLIT_EQUAL_UNEQUAL_COND___IDEM_EQ",
el 5 SMALLFOOT_PROP_IMPLIES___EQ___SPLIT_EQUAL_UNEQUAL_COND_LIST);

val SMALLFOOT_PROP_IMPLIES___EQ___SPLIT_EQUAL_UNEQUAL_COND___IDEM_UNEQ =
save_thm ("SMALLFOOT_PROP_IMPLIES___EQ___SPLIT_EQUAL_UNEQUAL_COND___IDEM_UNEQ",
el 6 SMALLFOOT_PROP_IMPLIES___EQ___SPLIT_EQUAL_UNEQUAL_COND_LIST);









val SMALLFOOT_PROP_IMPLIES___EQ_CASE_SPLIT =
store_thm ("SMALLFOOT_PROP_IMPLIES___EQ_CASE_SPLIT",

``!n1 n2 strong_rest wpb rpb wpb' sfb_context sfb_split sfb_imp sfb_restP.


  SMALLFOOT_PROP_IMPLIES strong_rest (wpb,rpb) wpb' sfb_context
           sfb_split sfb_imp sfb_restP =
  (((n1 = n2) ==>
    (SMALLFOOT_PROP_IMPLIES strong_rest (wpb,rpb) wpb' 
           sfb_context
           sfb_split sfb_imp sfb_restP)) /\
   (~(n1 = n2) ==>
   (SMALLFOOT_PROP_IMPLIES strong_rest (wpb,rpb) wpb' 
           (BAG_INSERT (smallfoot_ap_unequal (smallfoot_ae_const n1) 
					     (smallfoot_ae_const n2)) 
                       sfb_context)
           sfb_split sfb_imp sfb_restP)))``,



REPEAT STRIP_TAC THEN
Cases_on `n1 = n2` THEN1 (
   FULL_SIMP_TAC std_ss []
) THEN
ASM_SIMP_TAC (std_ss++boolSimps.CONJ_ss) [SMALLFOOT_PROP_IMPLIES_EXPAND,
		      bagTheory.BAG_UNION_INSERT,
		      smallfoot_prop___PROP_INSERT,
		      smallfoot_prop___COND_INSERT,
      		      smallfoot_prop___COND_UNION] THEN
ASM_SIMP_TAC std_ss [SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___compare,
		      SMALLFOOT_AE_USED_VARS_SUBSET___EVAL,
		      smallfoot_ap_unequal_def,
		      smallfoot_a_stack_proposition_def,
		      smallfoot_ap_binexpression_def,
		      LET_THM, IN_ABS, smallfoot_ae_const_def,
		      FUNION_FEMPTY_1, DISJOINT_EMPTY, FDOM_FEMPTY,
		      IN_DEF]);




val SMALLFOOT_PROP_IMPLIES___smallfoot_ap_false___context =
store_thm ("SMALLFOOT_PROP_IMPLIES___smallfoot_ap_false___context",

``!strong_rest wpb rpb wpb' sfb_context sfb_split sfb_imp sfb_restP.

  SMALLFOOT_PROP_IMPLIES strong_rest (wpb,rpb) wpb' 
           (BAG_INSERT smallfoot_ap_false sfb_context)
           sfb_split sfb_imp sfb_restP``,

SIMP_TAC (std_ss++boolSimps.CONJ_ss)
                [SMALLFOOT_PROP_IMPLIES_EXPAND,
		 bagTheory.BAG_UNION_INSERT,
		 smallfoot_prop___COND_UNION,
		 smallfoot_prop___COND_INSERT,
		 smallfoot_prop___PROP_INSERT] THEN
SIMP_TAC std_ss [smallfoot_ap_false___NOT_IN] THEN
SIMP_TAC std_ss [EXTENSION, NOT_IN_EMPTY, IN_DEF]);




val SMALLFOOT_PROP_IMPLIES___smallfoot_ap_false___split =
store_thm ("SMALLFOOT_PROP_IMPLIES___smallfoot_ap_false___split",

``!strong_rest wpb rpb wpb' sfb_context sfb_split sfb_imp sfb_restP.

  SMALLFOOT_PROP_IMPLIES strong_rest (wpb,rpb) wpb' sfb_context 
           (BAG_INSERT smallfoot_ap_false sfb_split)
           sfb_imp sfb_restP``,

SIMP_TAC (std_ss++boolSimps.CONJ_ss)
                [SMALLFOOT_PROP_IMPLIES_EXPAND,
		 bagTheory.BAG_UNION_INSERT,
		 smallfoot_prop___COND_UNION,
		 smallfoot_prop___COND_INSERT,
		 smallfoot_prop___PROP_INSERT] THEN
SIMP_TAC std_ss [smallfoot_ap_false___NOT_IN] THEN
SIMP_TAC std_ss [EXTENSION, NOT_IN_EMPTY, IN_DEF]);




val SMALLFOOT_PROP_IMPLIES___context_unequal_const___helper =
prove(
``!c1 c2 wpb rpb wpb' sfb_context sfb_split sfb_imp sfb_rest sr.

((SMALLFOOT_PROP_IMPLIES sr (wpb,rpb) wpb' 
   (BAG_INSERT (smallfoot_ap_unequal (smallfoot_ae_const c1) (smallfoot_ae_const c2)) sfb_context) 
   sfb_split sfb_imp sfb_restP) =
(~(c1 = c2) ==>
(SMALLFOOT_PROP_IMPLIES sr (wpb,rpb) wpb' 
   (BAG_INSERT (smallfoot_ap_unequal (smallfoot_ae_const c1) (smallfoot_ae_const c2)) sfb_context)
   sfb_split sfb_imp sfb_restP)))
``,

REPEAT STRIP_TAC THEN
Cases_on `c1 = c2` THEN (
   ASM_REWRITE_TAC []
) THEN
SIMP_TAC std_ss [smallfoot_ap_unequal___EQ_REWRITES,
		 SMALLFOOT_PROP_IMPLIES___smallfoot_ap_false___context]);



val SMALLFOOT_PROP_IMPLIES___context_unequal_const =
store_thm("SMALLFOOT_PROP_IMPLIES___context_unequal_const",
``(!c1 c2 wpb rpb wpb' sfb_context sfb_split sfb_imp sfb_rest sr.

((SMALLFOOT_PROP_IMPLIES sr (wpb,rpb) wpb' 
   (BAG_INSERT (smallfoot_ap_unequal (smallfoot_ae_const c1) (smallfoot_ae_const c2)) sfb_context) 
   sfb_split sfb_imp sfb_restP) =
(~(c1 = c2) ==>
(SMALLFOOT_PROP_IMPLIES sr (wpb,rpb) wpb' 
   (BAG_INSERT (smallfoot_ap_unequal (smallfoot_ae_const c1) (smallfoot_ae_const c2)) sfb_context)
   sfb_split sfb_imp sfb_restP)))) /\

(!c wpb rpb wpb' sfb_context sfb_split sfb_imp sfb_rest sr.

((SMALLFOOT_PROP_IMPLIES sr (wpb,rpb) wpb' 
   (BAG_INSERT (smallfoot_ap_unequal (smallfoot_ae_const c) smallfoot_ae_null) sfb_context) 
   sfb_split sfb_imp sfb_restP) =
(~(c = 0) ==>
(SMALLFOOT_PROP_IMPLIES sr (wpb,rpb) wpb' 
   (BAG_INSERT (smallfoot_ap_unequal (smallfoot_ae_const c) smallfoot_ae_null) sfb_context)
   sfb_split sfb_imp sfb_restP)))) /\

(!c wpb rpb wpb' sfb_context sfb_split sfb_imp sfb_rest sr.

((SMALLFOOT_PROP_IMPLIES sr (wpb,rpb) wpb' 
   (BAG_INSERT (smallfoot_ap_unequal smallfoot_ae_null (smallfoot_ae_const c)) sfb_context) 
   sfb_split sfb_imp sfb_restP) =
(~(c = 0) ==>
(SMALLFOOT_PROP_IMPLIES sr (wpb,rpb) wpb' 
   (BAG_INSERT (smallfoot_ap_unequal smallfoot_ae_null (smallfoot_ae_const c)) sfb_context)
   sfb_split sfb_imp sfb_restP))))
``,

REWRITE_TAC[smallfoot_ae_null_def] THEN
ONCE_REWRITE_TAC[SMALLFOOT_PROP_IMPLIES___context_unequal_const___helper] THEN
SIMP_TAC std_ss [] THEN
PROVE_TAC[]);




val SMALLFOOT_PROP_IMPLIES___bag_implies___UNEQUAL_INTRO =
store_thm ("SMALLFOOT_PROP_IMPLIES___bag_implies___UNEQUAL_INTRO",

``!e1 e2 strong_rest wpb rpb wpb' sfb_context sfb_split sfb_imp sfb_restP.

  smallfoot_ap_bag_implies_unequal (BAG_UNION sfb_split sfb_context) e1 e2 ==>

  ((SMALLFOOT_AE_USED_VARS_SUBSET (SET_OF_BAG (BAG_UNION wpb rpb)) e1 /\
  SMALLFOOT_AE_USED_VARS_SUBSET (SET_OF_BAG (BAG_UNION wpb rpb)) e2) ==>

  (SMALLFOOT_PROP_IMPLIES strong_rest (wpb,rpb) wpb' sfb_context
           sfb_split sfb_imp sfb_restP =
  SMALLFOOT_PROP_IMPLIES strong_rest (wpb,rpb) wpb' 
           (BAG_INSERT (smallfoot_ap_unequal e1 e2) sfb_context)
           sfb_split sfb_imp sfb_restP))``,


SIMP_TAC (std_ss++bool_eq_imp_ss) [SMALLFOOT_PROP_IMPLIES_EXPAND] THEN
REPEAT STRIP_TAC THEN
HO_MATCH_MP_TAC (prove (``(!s. (X s = Y s)) ==> ((?s. X s) = (?s. Y s))``,
		     METIS_TAC[])) THEN
SIMP_TAC (std_ss++bool_eq_imp_ss) [smallfoot_prop___COND_UNION,
				   smallfoot_prop___COND_INSERT,
				   bagTheory.BAG_UNION_INSERT] THEN
REPEAT STRIP_TAC THEN
ASM_SIMP_TAC std_ss [SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___compare] THEN
HO_MATCH_MP_TAC (prove (``(!s. (X s = Y s)) ==> ((!s. X s) = (!s. Y s))``,
		     METIS_TAC[])) THEN
`SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS (SET_OF_BAG (BAG_UNION wpb rpb)) (smallfoot_ap_unequal e1 e2)` by ALL_TAC THEN1 (   
   ASM_SIMP_TAC std_ss [SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___compare]
) THEN
ASM_SIMP_TAC (std_ss++boolSimps.CONJ_ss) [smallfoot_prop___PROP_INSERT,
		     smallfoot_prop___COND_INSERT,
		     smallfoot_prop___COND_UNION] THEN
GEN_TAC THEN
Tactical.REVERSE (`smallfoot_prop___PROP (wpb,rpb) (BAG_UNION sfb_split sfb_context) s ==>
                  s IN smallfoot_ap_weak_unequal e1 e2` by ALL_TAC) THEN1 (
   
   POP_ASSUM MP_TAC THEN
   SIMP_TAC std_ss [smallfoot_ap_unequal_def,
                    smallfoot_ap_weak_unequal_def,
		    smallfoot_ap_binexpression_def,
		    smallfoot_a_stack_proposition_def,
		    LET_THM, IN_ABS, DISJOINT_EMPTY, FDOM_FEMPTY,
		    FUNION_FEMPTY_1, IN_DEF] THEN
   METIS_TAC[] 
) THEN
FULL_SIMP_TAC std_ss [smallfoot_ap_bag_implies_unequal_def,
		      BAG_EVERY_def, bagTheory.BAG_IN_BAG_UNION,
		      smallfoot_prop___COND___REWRITE,
		      smallfoot_prop___PROP___REWRITE,
		      DISJ_IMP_THM, FORALL_AND_THM,
		      SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS_def,
		      smallfoot_ap_bigstar_REWRITE]);

 

val smallfoot_ap_var_update___REWRITES = 
save_thm ("smallfoot_ap_var_update___REWRITES",

LIST_CONJ [smallfoot_ap_var_update___BOOL,
	   smallfoot_ap_var_update___smallfoot_bintree,
	   smallfoot_ap_var_update___data_list_seg,
	   smallfoot_ap_var_update___data_list,
	   smallfoot_ap_var_update___compare,
           smallfoot_ap_var_update___smallfoot_ap_equal_cond,
           smallfoot_ap_var_update___smallfoot_ap_unequal_cond,
	   smallfoot_ap_var_update___smallfoot_ap_points_to,
	   smallfoot_ap_var_update___smallfoot_ap_exp_is_defined,
           smallfoot_ap_var_update___smallfoot_ap_cond_equal]);

















val SMALLFOOT_PROP_IMPLIES___JUST_COND___GUESS = store_thm (
"SMALLFOOT_PROP_IMPLIES___JUST_COND___GUESS",
``((c /\
SMALLFOOT_PROP_IMPLIES strong_rest (wpb,rpb) wpb' sfb_context
       sfb_split {||} sfb_restP) ==>

SMALLFOOT_PROP_IMPLIES strong_rest (wpb,rpb) wpb' sfb_context
       sfb_split {|smallfoot_ap_empty_heap_cond c|} sfb_restP) /\

((SMALLFOOT_PROP_IMPLIES strong_rest (wpb,rpb) wpb' sfb_context
       sfb_split (BAG_INSERT (smallfoot_ap_empty_heap_cond c1) 
                  (BAG_INSERT (smallfoot_ap_empty_heap_cond c2) sfb_imp)) 
       sfb_restP) =
SMALLFOOT_PROP_IMPLIES strong_rest (wpb,rpb) wpb' sfb_context
       sfb_split (BAG_INSERT (smallfoot_ap_empty_heap_cond (c1 /\ c2)) 
                  sfb_imp) sfb_restP)``,

SIMP_TAC std_ss[SMALLFOOT_PROP_IMPLIES___stack_true,
	        GSYM smallfoot_ap_stack_true_REWRITE] THEN
SIMP_TAC std_ss [SMALLFOOT_PROP_IMPLIES_def,
		 bagTheory.BAG_UNION_INSERT,
		 smallfoot_prop___COND_INSERT,
  		SMALLFOOT_AP_PERMISSION_UNIMPORTANT___USED_VARS___smallfoot_ap_empty_heap_cond,
		 smallfoot_prop___PROP___REWRITE,
		 smallfoot_ap_bigstar_REWRITE] THEN

Cases_on `c1` THEN Cases_on `c2` THEN (
   SIMP_TAC std_ss [GSYM smallfoot_ap_stack_true_REWRITE,
		    GSYM smallfoot_ap_empty_heap_cond___false,
		    smallfoot_ap_false___smallfoot_ap_star_THM,
		    smallfoot_ap_star___ap_stack_true___IDEM2]
));



val SMALLFOOT_PROP_IS_EQUIV_FALSE___ELIM = 
store_thm ("SMALLFOOT_PROP_IS_EQUIV_FALSE___ELIM",
``F ==> SMALLFOOT_PROP_IS_EQUIV_FALSE (wpb,rpb) sfb``,
SIMP_TAC std_ss[]);


val _ = export_theory();
