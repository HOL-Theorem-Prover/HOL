open HolKernel Parse boolLib bossLib listTheory rich_listTheory bitsTheory
     markerTheory metisLib pairTheory arithmeticTheory 
     word128Theory Serpent_Reference_UtilityTheory word128Lib;

val _ = new_theory "Serpent_Reference_Permutation";

(*initial/inverse final permutation table*)			
val IPTable_def=Define
`IPTable=
 [  0; 32; 64; 96;  1; 33; 65; 97;  2; 34; 66; 98;  3; 35; 67; 99;
    4; 36; 68;100;  5; 37; 69;101;  6; 38; 70;102;  7; 39; 71;103;
    8; 40; 72;104;  9; 41; 73;105; 10; 42; 74;106; 11; 43; 75;107;
   12; 44; 76;108; 13; 45; 77;109; 14; 46; 78;110; 15; 47; 79;111;
   16; 48; 80;112; 17; 49; 81;113; 18; 50; 82;114; 19; 51; 83;115;
   20; 52; 84;116; 21; 53; 85;117; 22; 54; 86;118; 23; 55; 87;119;
   24; 56; 88;120; 25; 57; 89;121; 26; 58; 90;122; 27; 59; 91;123;
   28; 60; 92;124; 29; 61; 93;125; 30; 62; 94;126; 31; 63; 95;127]`;

(*final/inverse initial permutation table*)
val FPTable_def=Define
`FPTable= 
 [  0;  4;  8; 12; 16; 20; 24; 28; 32; 36; 40; 44; 48; 52; 56; 60;
   64; 68; 72; 76; 80; 84; 88; 92; 96;100;104;108;112;116;120;124;
    1;  5;  9; 13; 17; 21; 25; 29; 33; 37; 41; 45; 49; 53; 57; 61;
   65; 69; 73; 77; 81; 85; 89; 93; 97;101;105;109;113;117;121;125;
    2;  6; 10; 14; 18; 22; 26; 30; 34; 38; 42; 46; 50; 54; 58; 62;
   66; 70; 74; 78; 82; 86; 90; 94; 98;102;106;110;114;118;122;126;
    3;  7; 11; 15; 19; 23; 27; 31; 35; 39; 43; 47; 51; 55; 59; 63;
   67; 71; 75; 79; 83; 87; 91; 95; 99;103;107;111;115;119;123;127]`;

val IPFun_def=Define
`IPFun x = EL x IPTable`; 

val FPFun_def=Define
`FPFun x = EL x FPTable`;

(*precomputed to speed things up*) 
val IPFunVal=Q.store_thm(
"IPFunVal",
`
  (IPFun   0=  0) /\ (IPFun   1= 32) /\ (IPFun   2= 64) /\ (IPFun   3= 96) /\
  (IPFun   4=  1) /\ (IPFun   5= 33) /\ (IPFun   6= 65) /\ (IPFun   7= 97) /\
  (IPFun   8=  2) /\ (IPFun   9= 34) /\ (IPFun  10= 66) /\ (IPFun  11= 98) /\
  (IPFun  12=  3) /\ (IPFun  13= 35) /\ (IPFun  14= 67) /\ (IPFun  15= 99) /\
  (IPFun  16=  4) /\ (IPFun  17= 36) /\ (IPFun  18= 68) /\ (IPFun  19=100) /\
  (IPFun  20=  5) /\ (IPFun  21= 37) /\ (IPFun  22= 69) /\ (IPFun  23=101) /\
  (IPFun  24=  6) /\ (IPFun  25= 38) /\ (IPFun  26= 70) /\ (IPFun  27=102) /\
  (IPFun  28=  7) /\ (IPFun  29= 39) /\ (IPFun  30= 71) /\ (IPFun  31=103) /\
  (IPFun  32=  8) /\ (IPFun  33= 40) /\ (IPFun  34= 72) /\ (IPFun  35=104) /\
  (IPFun  36=  9) /\ (IPFun  37= 41) /\ (IPFun  38= 73) /\ (IPFun  39=105) /\
  (IPFun  40= 10) /\ (IPFun  41= 42) /\ (IPFun  42= 74) /\ (IPFun  43=106) /\
  (IPFun  44= 11) /\ (IPFun  45= 43) /\ (IPFun  46= 75) /\ (IPFun  47=107) /\
  (IPFun  48= 12) /\ (IPFun  49= 44) /\ (IPFun  50= 76) /\ (IPFun  51=108) /\
  (IPFun  52= 13) /\ (IPFun  53= 45) /\ (IPFun  54= 77) /\ (IPFun  55=109) /\
  (IPFun  56= 14) /\ (IPFun  57= 46) /\ (IPFun  58= 78) /\ (IPFun  59=110) /\
  (IPFun  60= 15) /\ (IPFun  61= 47) /\ (IPFun  62= 79) /\ (IPFun  63=111) /\
  (IPFun  64= 16) /\ (IPFun  65= 48) /\ (IPFun  66= 80) /\ (IPFun  67=112) /\
  (IPFun  68= 17) /\ (IPFun  69= 49) /\ (IPFun  70= 81) /\ (IPFun  71=113) /\
  (IPFun  72= 18) /\ (IPFun  73= 50) /\ (IPFun  74= 82) /\ (IPFun  75=114) /\
  (IPFun  76= 19) /\ (IPFun  77= 51) /\ (IPFun  78= 83) /\ (IPFun  79=115) /\
  (IPFun  80= 20) /\ (IPFun  81= 52) /\ (IPFun  82= 84) /\ (IPFun  83=116) /\
  (IPFun  84= 21) /\ (IPFun  85= 53) /\ (IPFun  86= 85) /\ (IPFun  87=117) /\
  (IPFun  88= 22) /\ (IPFun  89= 54) /\ (IPFun  90= 86) /\ (IPFun  91=118) /\
  (IPFun  92= 23) /\ (IPFun  93= 55) /\ (IPFun  94= 87) /\ (IPFun  95=119) /\
  (IPFun  96= 24) /\ (IPFun  97= 56) /\ (IPFun  98= 88) /\ (IPFun  99=120) /\
  (IPFun 100= 25) /\ (IPFun 101= 57) /\ (IPFun 102= 89) /\ (IPFun 103=121) /\
  (IPFun 104= 26) /\ (IPFun 105= 58) /\ (IPFun 106= 90) /\ (IPFun 107=122) /\
  (IPFun 108= 27) /\ (IPFun 109= 59) /\ (IPFun 110= 91) /\ (IPFun 111=123) /\
  (IPFun 112= 28) /\ (IPFun 113= 60) /\ (IPFun 114= 92) /\ (IPFun 115=124) /\
  (IPFun 116= 29) /\ (IPFun 117= 61) /\ (IPFun 118= 93) /\ (IPFun 119=125) /\
  (IPFun 120= 30) /\ (IPFun 121= 62) /\ (IPFun 122= 94) /\ (IPFun 123=126) /\
  (IPFun 124= 31) /\ (IPFun 125= 63) /\ (IPFun 126= 95) /\ (IPFun 127=127)`,
	
EVAL_TAC);

val FPFunVal=Q.store_thm(
"FPFunVal",
`
  (FPFun   0=  0) /\ (FPFun   1=  4) /\ (FPFun   2=  8) /\ (FPFun   3= 12) /\
  (FPFun   4= 16) /\ (FPFun   5= 20) /\ (FPFun   6= 24) /\ (FPFun   7= 28) /\
  (FPFun   8= 32) /\ (FPFun   9= 36) /\ (FPFun  10= 40) /\ (FPFun  11= 44) /\
  (FPFun  12= 48) /\ (FPFun  13= 52) /\ (FPFun  14= 56) /\ (FPFun  15= 60) /\
  (FPFun  16= 64) /\ (FPFun  17= 68) /\ (FPFun  18= 72) /\ (FPFun  19= 76) /\
  (FPFun  20= 80) /\ (FPFun  21= 84) /\ (FPFun  22= 88) /\ (FPFun  23= 92) /\
  (FPFun  24= 96) /\ (FPFun  25=100) /\ (FPFun  26=104) /\ (FPFun  27=108) /\
  (FPFun  28=112) /\ (FPFun  29=116) /\ (FPFun  30=120) /\ (FPFun  31=124) /\
  (FPFun  32=  1) /\ (FPFun  33=  5) /\ (FPFun  34=  9) /\ (FPFun  35= 13) /\
  (FPFun  36= 17) /\ (FPFun  37= 21) /\ (FPFun  38= 25) /\ (FPFun  39= 29) /\
  (FPFun  40= 33) /\ (FPFun  41= 37) /\ (FPFun  42= 41) /\ (FPFun  43= 45) /\
  (FPFun  44= 49) /\ (FPFun  45= 53) /\ (FPFun  46= 57) /\ (FPFun  47= 61) /\
  (FPFun  48= 65) /\ (FPFun  49= 69) /\ (FPFun  50= 73) /\ (FPFun  51= 77) /\
  (FPFun  52= 81) /\ (FPFun  53= 85) /\ (FPFun  54= 89) /\ (FPFun  55= 93) /\
  (FPFun  56= 97) /\ (FPFun  57=101) /\ (FPFun  58=105) /\ (FPFun  59=109) /\
  (FPFun  60=113) /\ (FPFun  61=117) /\ (FPFun  62=121) /\ (FPFun  63=125) /\
  (FPFun  64=  2) /\ (FPFun  65=  6) /\ (FPFun  66= 10) /\ (FPFun  67= 14) /\
  (FPFun  68= 18) /\ (FPFun  69= 22) /\ (FPFun  70= 26) /\ (FPFun  71= 30) /\
  (FPFun  72= 34) /\ (FPFun  73= 38) /\ (FPFun  74= 42) /\ (FPFun  75= 46) /\
  (FPFun  76= 50) /\ (FPFun  77= 54) /\ (FPFun  78= 58) /\ (FPFun  79= 62) /\
  (FPFun  80= 66) /\ (FPFun  81= 70) /\ (FPFun  82= 74) /\ (FPFun  83= 78) /\
  (FPFun  84= 82) /\ (FPFun  85= 86) /\ (FPFun  86= 90) /\ (FPFun  87= 94) /\
  (FPFun  88= 98) /\ (FPFun  89=102) /\ (FPFun  90=106) /\ (FPFun  91=110) /\
  (FPFun  92=114) /\ (FPFun  93=118) /\ (FPFun  94=122) /\ (FPFun  95=126) /\
  (FPFun  96=  3) /\ (FPFun  97=  7) /\ (FPFun  98= 11) /\ (FPFun  99= 15) /\
  (FPFun 100= 19) /\ (FPFun 101= 23) /\ (FPFun 102= 27) /\ (FPFun 103= 31) /\
  (FPFun 104= 35) /\ (FPFun 105= 39) /\ (FPFun 106= 43) /\ (FPFun 107= 47) /\
  (FPFun 108= 51) /\ (FPFun 109= 55) /\ (FPFun 110= 59) /\ (FPFun 111= 63) /\
  (FPFun 112= 67) /\ (FPFun 113= 71) /\ (FPFun 114= 75) /\ (FPFun 115= 79) /\
  (FPFun 116= 83) /\ (FPFun 117= 87) /\ (FPFun 118= 91) /\ (FPFun 119= 95) /\
  (FPFun 120= 99) /\ (FPFun 121=103) /\ (FPFun 122=107) /\ (FPFun 123=111) /\
  (FPFun 124=115) /\ (FPFun 125=119) /\ (FPFun 126=123) /\ (FPFun 127=127)`,
	
EVAL_TAC);


(*permutation *)
val permu_def = Define
`(permu 0 permFun (block:word128) 
  = let sourceBit = word128$WORD_BIT (permFun 0) block 
    in
    if sourceBit 
       then (1w:word128)
       else (0w:word128))  
 /\
 (permu (SUC i) permFun  block 
 = let sourceBit = word128$WORD_BIT (permFun (SUC i)) block 
   in
   let maskedWord = if sourceBit 
                       then (1w:word128) << (SUC i)
       		       else (0w:word128)
   in
   maskedWord | (permu i permFun  block))`;  

(*for evaluation*)  
val permuEval = Q.store_thm(
"permuEval",
` !m  (block:word128).
	permu m permFun (block:word128) 
	= if m=0 
	     then let sourceBit = word128$WORD_BIT (permFun 0) block 
	          in
		  if sourceBit 
		     then (1w:word128)
		     else (0w:word128)
             else let sourceBit = word128$WORD_BIT (permFun m) block 
	          in
		  let maskedWord = if sourceBit 
		                      then (1w:word128) << m
		       		      else (0w:word128)
 		  in
		  maskedWord | (permu (m-1) permFun  block) `,    

RW_TAC  list_ss [permu_def,LET_THM] THENL [
	Cases_on `m` THEN
	RW_TAC list_ss [permu_def,LET_THM],
	Cases_on `m` THEN
	RW_TAC list_ss [permu_def,LET_THM]]);
		

(*desired properties of permu *)	
val perm_recur_inv1_w128=Q.store_thm(
"perm_recur_inv1_w128",
`!permFun block from to d.
	(!x. x<word128$WL ==> permFun x <word128$WL) /\
	(d < word128$WL) /\
	(to < word128$WL) /\
	(permFun to = from) /\  
	to >d
	==>
	~(WORD_BIT to (permu d permFun block))`,
		
Induct_on `d` THEN 
RW_TAC arith_ss [permu_def,LET_THM] THEN 
RW_TAC arith_ss [word128Theory.WORD_BIT_def,
                 word128Theory.WORD_BIT_BOOLOPS,word128Theory.WORD_BIT_LSL,
		 w2n_zero128, BIT_ZERO,word_1_bit128]);

val perm_recur_inv2_w128=Q.store_thm(
"perm_recur_inv2_w128",
`!permFun block from to d.
	(!x. x<word128$WL ==> permFun x <word128$WL) /\
	(d < word128$WL) /\
	(to < word128$WL) /\
	(permFun to = from) /\  
	to <=d 
	==>
	(WORD_BIT to (permu d permFun block) = WORD_BIT from block)`, 
		
Induct_on `d` THEN 
RW_TAC arith_ss [permu_def,LET_THM] THENL [
	FULL_SIMP_TAC arith_ss [word128Theory.WORD_BIT_def, 
	                        w2n_one128,BIT_def, BITS_THM],
	FULL_SIMP_TAC arith_ss [word128Theory.WORD_BIT_def, 
	                        w2n_zero128,BIT_def, BITS_THM ],
	Cases_on `to <=d`  THEN Cases_on `to=d` THENL [
		RW_TAC arith_ss [word128Theory.WORD_BIT_BOOLOPS,
		                 word128Theory.WORD_BIT_LSL],
		RW_TAC arith_ss [word128Theory.WORD_BIT_BOOLOPS,
		                 word128Theory.WORD_BIT_LSL],
		FULL_SIMP_TAC arith_ss [],
		`to = SUC d` by RW_TAC arith_ss [] THEN
		FULL_SIMP_TAC arith_ss [word128Theory.WORD_BIT_BOOLOPS,
		                        word128Theory.WORD_BIT_LSL,
					word128Theory.WORD_BIT_def,
					w2n_one128,BIT_def, BITS_THM]],
		FULL_SIMP_TAC arith_ss [word128Theory.WORD_BIT_BOOLOPS,
		                        word128Theory.WORD_BIT_def, w2n_zero128,
					BIT_ZERO,DECIDE ``SUC x<y==>x<y``] THEN
		Cases_on `to<=d` THENL [
			FULL_SIMP_TAC arith_ss [],
			`to>d /\ (to = SUC d)` by METIS_TAC 
			                          [DECIDE ``~(x<=y) /\
						           x <= SUC y=(x=SUC y) /\
						           (x>y)``] THEN
			FULL_SIMP_TAC arith_ss [GSYM word128Theory.WORD_BIT_def,
			                        perm_recur_inv1_w128]]]);
									

		
(*composite of 2 permutations*)		
val permu_compose_w128=Q.store_thm(
"permu_compose_w128",
`!permFun1 permFun2 block i.
	i<word128$WL  /\
	(!x. x < word128$WL ==> permFun1 x < word128$WL) /\	 
	(!x. x < word128$WL ==> permFun2 x < word128$WL)
	 ==>
	(word128$WORD_BIT i (permu word128$HB permFun2 
	                           (permu word128$HB permFun1 block))
	 = word128$WORD_BIT i (permu word128$HB (permFun1 o permFun2)  block))`,
		
RW_TAC std_ss [] THEN
`word128$WORD_BIT i (permu word128$HB permFun2 
                           (permu word128$HB permFun1 block))
 = word128$WORD_BIT (permFun2 i) (permu word128$HB permFun1 block)`
	by FULL_SIMP_TAC arith_ss [perm_recur_inv2_w128,word128Theory.HB_def,
	                           word128Theory.WL_def] THEN
`word128$WORD_BIT i (permu word128$HB (permFun1 o permFun2) block)
 =word128$WORD_BIT ((permFun1 o permFun2) i) block` 
	by FULL_SIMP_TAC arith_ss [perm_recur_inv2_w128,word128Theory.HB_def,
	                           word128Theory.WL_def] THEN
`permFun2 i < word128$WL` by METIS_TAC [] THEN
`word128$WORD_BIT (permFun2 i) (permu word128$HB permFun1 block)
 = word128$WORD_BIT (permFun1 ( permFun2 i)) block` 
	by FULL_SIMP_TAC arith_ss [perm_recur_inv2_w128,word128Theory.HB_def,
	word128Theory.WL_def] THEN
RW_TAC std_ss []);

(*two permutations cancel each other*)			
val permu_comp_reverse_w128=Q.store_thm(
"permu_comp_reverse_w128",
`!permFun1 permFun2 block.
	(!x. x < word128$WL ==> permFun1 x < word128$WL) /\	 
	(!x. x < word128$WL ==> permFun2 x < word128$WL) /\
	(!x. x < word128$WL ==> ((permFun1 o permFun2) x =x))==>
	(permu word128$HB permFun2 (permu word128$HB permFun1 block)=block)`,    
		
RW_TAC arith_ss [GSYM WORD_EQ, permu_compose_w128,perm_recur_inv2_w128,
                 word128Theory.HB_def,word128Theory.WL_def]);    
			
val IP_def = Define
`IP w128=permu word128$HB IPFun w128`;

val FP_def = Define
`FP w128=permu word128$HB FPFun w128`;

val invIP_def = Define
`invIP w128=FP w128`;

val invFP_def = Define
`invFP w128=IP w128`;

val IP_FP_fact = Q.store_thm(
"IP_FP_fact",
`!x .
	x < word128$WL ==> ((IPFun x < word128$WL) /\
	(FPFun x < word128$WL) /\
	((FPFun o IPFun) x=x) /\ 
	((IPFun o FPFun) x=x))`,

FULL_SIMP_TAC arith_ss [BOUNDED_FORALL_THM,IPFunVal,FPFunVal,
	                word128Theory.WL_def,word128Theory.HB_def]);
(*permutations using given IP and FP tables cancel*) 
val invFP_FP_cancel=Q.store_thm(
"invFP_FP_cancel",
`! block. 
	invFP (FP block)=block`,

SIMP_TAC std_ss [invFP_def,IP_def,FP_def,permu_comp_reverse_w128,IP_FP_fact]);

val invIP_IP_cancel=Q.store_thm(
"invIP_IP_cancel",
`! block. 
	invIP (IP block)=block`,

SIMP_TAC std_ss [invIP_def,IP_def,FP_def,permu_comp_reverse_w128,IP_FP_fact]);

val _ = export_theory();
