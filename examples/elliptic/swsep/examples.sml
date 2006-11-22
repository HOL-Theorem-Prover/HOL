

(*
quietdec := true;
loadPath := 
            (concat Globals.HOLDIR "/examples/dev/sw") :: 
            (concat Globals.HOLDIR "/examples/elliptic/arm") :: 
            (concat Globals.HOLDIR "/examples/elliptic/spec") :: 
            (concat Globals.HOLDIR "/examples/elliptic/sep") :: 
            (concat Globals.HOLDIR "/examples/elliptic/swsep") :: 
            !loadPath;

map load ["swsepLib", "elliptic_exampleTheory"];
show_assums := true;
*)

open swsepLib;
open ellipticTheory
open elliptic_exampleTheory;
open mechReasoning;

(*
quietdec := false;
*)

fun sep_compile def prove_equiv =
	let 
		val comp = pp_compile def prove_equiv;
		val _ = print "Translating specification to separation logic\n";
		val spec = spec_sep comp
	in 
		spec
	end



val ex1_field_neg_eval = REWRITE_RULE [ex1_prime_def,
	example1_prime_def] ex1_field_neg_def
val ex1_field_neg_spec = sep_compile ex1_field_neg_eval true


val ex1_field_add_eval = REWRITE_RULE [ex1_prime_def,
	example1_prime_def] ex1_field_add_def
val ex1_field_add_spec = sep_compile ex1_field_add_eval true;


val ex1_field_sub_eval = REWRITE_RULE [ex1_field_neg_eval,ex1_field_add_eval] ex1_field_sub_def
val ex1_field_sub_spec___pre = sep_compile ex1_field_sub_eval false;


val ex1_field_sub_spec = PROVE_HYP (
	prove (hd (hyp ex1_field_sub_spec___pre),

REWRITE_TAC[FUN_EQ_THM] THEN
Cases_on `x` THEN
SIMP_TAC std_ss [ex1_field_sub_eval] THEN
Cases_on `r = 0w` THEN (
	ASM_SIMP_TAC std_ss [WORD_ADD_0, LET_THM] THEN
	WORDS_TAC
))) ex1_field_sub_spec___pre




val WORD_LO___MEASURE = store_thm ("WORD_LO___MEASURE",
  ``word_lo = measure w2n``,
  SIMP_TAC std_ss [FUN_EQ_THM, prim_recTheory.measure_def,
    relationTheory.inv_image_def, WORD_LO] );

val fact_def = Hol_defn "fact" 
   `fact (x:word32,a:word32) = if x=0w then a else fact(x-1w, x*a)`;

val (fact_def, fact_ind) =
Defn.tprove (fact_def,
  TotalDefn.WF_REL_TAC `inv_image $<+ (\(v1:word32,v2:word32). v1)` THENL [
    SIMP_TAC std_ss [WORD_LO___MEASURE, prim_recTheory.WF_measure],
    SIMP_TAC std_ss [WORD_LO, WORD_PRED_THM]
  ]);

val fact_spec___pre =  sep_compile fact_def false;

val fact_spec = 
	PROVE_HYP 
		(prove (hd (hyp fact_spec___pre),
			SIMP_TAC std_ss [FUN_EQ_THM, FORALL_PROD] THEN
			HO_MATCH_MP_TAC fact_ind THEN
			REPEAT STRIP_TAC THEN
			ONCE_REWRITE_TAC [fact_def, WHILE] THEN
			RW_TAC std_ss [] THEN
			Q.PAT_ASSUM `~(x = 0w) ==> P x` MP_TAC THEN
			WORDS_TAC THEN
			ASM_SIMP_TAC std_ss []))
		fact_spec___pre


(*
IR.inline_funcs := ["f1"]
*)

val def1 = Define `f1 (x:word32) = x + 1w`;
val def2 = Define `f2 (x:word32) = x + f1(x) + 1w`;
val def3 = Define `f3 (x:word32) = f2(x) + 1w`;
val def4 = Define `f4 (x:word32, y:word32) = fact(x, 2w) + 1w`;
val def5 = Define `f5 (x:word32) = if (x = 0w) then (f1 x + 1w) else x`;

val comp1 = pp_compile def1 false
val comp2 = pp_compile def2 false
val comp3 = pp_compile def3 false
val comp4 = pp_compile def4 false
val comp5 = pp_compile def5 false
