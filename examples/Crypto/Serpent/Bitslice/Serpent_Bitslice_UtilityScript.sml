open HolKernel Parse boolLib bossLib listTheory rich_listTheory bitsTheory
     markerTheory metisLib pairTheory arithmeticTheory  word32Theory
     word128Theory word256Theory word32Lib word128Lib word256Lib metisLib;

val _ = new_theory "Serpent_Bitslice_Utility";



(*conversion between different words,
EL 0 is the MS in all split result,
the bit ordering is perserved
*)

val word128to32l_def =Define 
`word128to32l (w128:word128) = 
 [word32$n2w (w2n (w128 >>> 96)); word32$n2w (w2n ((w128 <<32) >>> 96));
  word32$n2w (w2n ((w128<<64) >>> 96)); word32$n2w (w2n ((w128<<96) >>> 96))]`;


val word256to128l = Define
`word256to128l (w256:word256) = 
 [word128$n2w (w2n (w256 >>> 128)); word128$n2w  (w2n ((w256 <<128) >>> 128))]`;

val word256to32l_def = Define
`word256to32l (w256:word256) = FLAT ( MAP word128to32l (word256to128l w256))`;


val word256to32lLength = Q.store_thm (
"word256to32lLength",
`!w. 
	LENGTH (word256to32l w) =8`,

EVAL_TAC THEN METIS_TAC []);

(*housemade FIRSTN and BUTLASTN for easy evaluation*)
val (myFIRSTN_def,myFIRSTN_termi) =Defn.tstore_defn(
 Defn.Hol_defn "myFIRSTN"
`myFIRSTN n l = if n=0 
                   then []
		   else if l=[] 
                    	   then []
			   else (HD l)::(myFIRSTN (n-1) (TL l))`,

WF_REL_TAC `measure (LENGTH o SND)` THEN
RW_TAC list_ss [] THEN
Cases_on `l` THENL [
	FULL_SIMP_TAC list_ss [],
	RW_TAC list_ss []]);

val myBUTLASTN_def = Define
`myBUTLASTN n l 
 = let len=LENGTH l 
   in
   if len>=n 
      then myFIRSTN (LENGTH l-n) l
      else []`;

val LENGTH_myFIRSTN=Q.store_thm(
"LENGTH_myFIRSTN",
`!n l. 
	n <= LENGTH l 
	==> 
	(LENGTH (myFIRSTN n l) = n)`,

Induct_on `n` THENL [
	RW_TAC list_ss [] THEN
	`myFIRSTN 0 l=[]` by METIS_TAC  [myFIRSTN_def] THEN
	RW_TAC list_ss [],
	RW_TAC list_ss [] THEN
	Cases_on `l` THENL [
		FULL_SIMP_TAC list_ss [],
		`~(SUC n=0)` by RW_TAC arith_ss [] THEN
		`~((h::t) =[])` by RW_TAC list_ss [] THEN
		`myFIRSTN (SUC n) (h::t)= (HD (h::t))::(myFIRSTN (SUC n-1) (TL (h::t)))` by  METIS_TAC  [myFIRSTN_def] THEN
		FULL_SIMP_TAC list_ss []]]);
	



val LENGTH_myBUTLASTN=Q.store_thm(
"LENGTH_myBUTLASTN",
`!n l. 
	n <= LENGTH l 
	==> 
	(LENGTH (myBUTLASTN n l) = LENGTH l - n)`,

RW_TAC arith_ss [myBUTLASTN_def,LENGTH_myFIRSTN,LET_THM]);	
	   
	

(*explicitly instantiate a list give its length*)      
val LENGTH_GREATER_EQ_CONS=Q.store_thm(
"LENGTH_GREATER_EQ_CONS",
`!l n. 
	(LENGTH l >=SUC n) 
	==>
	?x l'. (LENGTH l' >= n) /\ (l = x::l')`,

Induct_on `l` THEN
RW_TAC list_ss []);
	  		

val listInstGreaterEq8=Q.store_thm(
"listInstGreaterEq8",
`!l. 
	(LENGTH l>=8) 
	==> 
	?v_1 v_2 v_3 v_4 v_5 v_6 v_7 v_8 t. 
		l = (v_1::v_2::v_3::v_4::v_5::v_6::v_7::v_8::t)`,
	     
REWRITE_TAC [DECIDE ``8 = SUC (SUC (SUC (SUC (SUC (SUC (SUC (SUC 0)))))))``] THEN
METIS_TAC  [LENGTH_GREATER_EQ_CONS, LENGTH_NIL]);	


val listInstEq33 =Q.store_thm(
"listInstEq33",
`!l.
	(LENGTH l = 33) 
	==>
        ?v_0 v_1 v_2 v_3 v_4 v_5 v_6 v_7 v_8 v_9 v_10 v_11 v_12 v_13 v_14
           v_15 v_16 v_17 v_18 v_19 v_20 v_21 v_22 v_23 v_24 v_25 v_26 v_27
           v_28 v_29 v_30 v_31 v_32.
        	l = [v_0; v_1; v_2; v_3; v_4; v_5; v_6; v_7; v_8; v_9; v_10; v_11;
                     v_12; v_13; v_14; v_15; v_16; v_17; v_18; v_19; v_20; v_21; 
		     v_22; v_23; v_24; v_25; v_26; v_27; v_28; v_29; v_30; v_31;
		     v_32]`,

	      
	       
REWRITE_TAC [LENGTH_CONS, LENGTH_NIL, 
             DECIDE `` 33 = SUC (SUC (SUC (SUC (SUC (SUC (SUC (SUC (SUC 
	                   (SUC (SUC (SUC (SUC (SUC (SUC (SUC (SUC (SUC
			   (SUC (SUC (SUC (SUC (SUC (SUC (SUC (SUC (SUC
			   (SUC (SUC (SUC (SUC (SUC (SUC  
			    0)))))))))))))))))))))))))))))))) ``] THEN
METIS_TAC []); 

(*trivial properties of bit operations on word*)
val rot_wl_lem= Q.store_thm(
"rot_wl_lem",
`!a:word32. 
	a #>>word32$WL =a`,
	
METIS_TAC [MULT_CLAUSES,word32Theory.ROR_CYCLE]);	

val WORD_EOR_REDUCTION = Q.store_thm(
"WORD_EOR_REDUCTION",
`!(a:word32) b. 
	a #b # a # b =0w`,
	
METIS_TAC [word32Theory.WORD_EOR_COMM,word32Theory.WORD_EOR_ASSOC,
           word32Theory.WORD_EOR_ID,word32Theory.WORD_EOR_INV]);

val WORD_EOR_ID2 =Q.store_thm(
"WORD_EOR_ID2",
`!(a:word32) b c. 
	c#a #b # a # b =c`,

METIS_TAC [word32Theory.WORD_EOR_COMM,word32Theory.WORD_EOR_ASSOC,
           word32Theory.WORD_EOR_ID,word32Theory.WORD_EOR_INV]);

val ror_32_lem=Q.store_thm (
"ror_32_lem",
`!(a:word32). 
	a #>>32 =a`,

`32=word32$WL` by RW_TAC std_ss [word32Theory.WL_def,word32Theory.HB_def] THEN
METIS_TAC [MULT_CLAUSES,word32Theory.ROR_CYCLE]);


val _ = export_theory();
