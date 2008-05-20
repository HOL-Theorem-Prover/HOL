(*********************************************************)
(*                         SBox                          *)
(*********************************************************)

open HolKernel Parse boolLib bossLib wordsTheory wordsLib
     Serpent_Reference_UtilityTheory listTheory rich_listTheory bitTheory
     markerTheory pairTheory arithmeticTheory;

val _ = new_theory "Serpent_Reference_SBox";


(*sbox table used in encrytion
*)
val SBox_def=Define 
`SBox=MAP (MAP (n2w:num->word4))
[[ 3; 8;15; 1;10; 6; 5;11;14;13; 4; 2; 7; 0; 9;12];
 [15;12; 2; 7; 9; 0; 5;10; 1;11;14; 8; 6;13; 3; 4];
 [ 8; 6; 7; 9; 3;12;10;15;13; 1;14; 4; 0;11; 5; 2];
 [ 0;15;11; 8;12; 9; 6; 3;13; 1; 2; 4;10; 7; 5;14];
 [ 1;15; 8; 3;12; 0;11; 6; 2; 5; 4;10; 9;14; 7;13];
 [15; 5; 2;11; 4;10; 9;12; 0; 3;14; 8;13; 6; 7; 1];
 [ 7; 2;12; 5; 8; 4; 6;11;14; 9; 1;15;13; 3;10; 0];
 [ 1;13;15; 0;14; 8; 2;11; 7; 4;12;10; 9; 3; 5; 6]]`;


(*inverse sbox table used in decrytion
*)
val invSBox_def=Define
`invSBox= MAP (MAP (n2w:num->word4))
[[13; 3;11; 0;10; 6; 5;12; 1;14; 4; 7;15; 9; 8; 2];
 [ 5; 8; 2;14;15; 6;12; 3;11; 4; 7; 9; 1;13;10; 0];
 [12; 9;15; 4;11;14; 1; 2; 0; 3; 6;13; 5; 8;10; 7];
 [ 0; 9;10; 7;11;14; 6;13; 3; 5;12; 2; 4; 8;15; 1];
 [ 5; 0; 8; 3;10; 9; 7;14; 2;12;11; 6; 4;15;13; 1];
 [ 8;15; 2; 9; 4; 1;13;14;11; 6; 5; 3; 7;12;10; 0];
 [15;10; 1;13; 5; 3; 6; 0; 4; 9;14; 7; 2;12; 8;11];
 [ 3; 0; 6;13; 9;14;15; 8; 5;12;11; 7;10; 1; 4; 2]]`;

val S_def = Define
`(S:num->num->word4) x y= EL y (EL x SBox)`;

val invS_def = Define
`(invS:num->num->word4) x y= EL y (EL x invSBox)`;

(*preevaluated to speed things up
*)
val SBoxVal=Q.store_thm(
"SBoxVal",
`
  (S 0  0= 3w) /\ (S 0  1= 8w) /\ (S 0  2=15w) /\ (S 0  3= 1w) /\
  (S 0  4=10w) /\ (S 0  5= 6w) /\ (S 0  6= 5w) /\ (S 0  7=11w) /\
  (S 0  8=14w) /\ (S 0  9=13w) /\ (S 0 10= 4w) /\ (S 0 11= 2w) /\
  (S 0 12= 7w) /\ (S 0 13= 0w) /\ (S 0 14= 9w) /\ (S 0 15=12w) /\
  (S 1  0=15w) /\ (S 1  1=12w) /\ (S 1  2= 2w) /\ (S 1  3= 7w) /\
  (S 1  4= 9w) /\ (S 1  5= 0w) /\ (S 1  6= 5w) /\ (S 1  7=10w) /\
  (S 1  8= 1w) /\ (S 1  9=11w) /\ (S 1 10=14w) /\ (S 1 11= 8w) /\
  (S 1 12= 6w) /\ (S 1 13=13w) /\ (S 1 14= 3w) /\ (S 1 15= 4w) /\
  (S 2  0= 8w) /\ (S 2  1= 6w) /\ (S 2  2= 7w) /\ (S 2  3= 9w) /\
  (S 2  4= 3w) /\ (S 2  5=12w) /\ (S 2  6=10w) /\ (S 2  7=15w) /\
  (S 2  8=13w) /\ (S 2  9= 1w) /\ (S 2 10=14w) /\ (S 2 11= 4w) /\
  (S 2 12= 0w) /\ (S 2 13=11w) /\ (S 2 14= 5w) /\ (S 2 15= 2w) /\
  (S 3  0= 0w) /\ (S 3  1=15w) /\ (S 3  2=11w) /\ (S 3  3= 8w) /\ 
  (S 3  4=12w) /\ (S 3  5= 9w) /\ (S 3  6= 6w) /\ (S 3  7= 3w) /\
  (S 3  8=13w) /\ (S 3  9= 1w) /\ (S 3 10= 2w) /\ (S 3 11= 4w) /\
  (S 3 12=10w) /\ (S 3 13= 7w) /\ (S 3 14= 5w) /\ (S 3 15=14w) /\
  (S 4  0= 1w) /\ (S 4  1=15w) /\ (S 4  2= 8w) /\ (S 4  3= 3w) /\
  (S 4  4=12w) /\ (S 4  5= 0w) /\ (S 4  6=11w) /\ (S 4  7= 6w) /\
  (S 4  8= 2w) /\ (S 4  9= 5w) /\ (S 4 10= 4w) /\ (S 4 11=10w) /\
  (S 4 12= 9w) /\ (S 4 13=14w) /\ (S 4 14= 7w) /\ (S 4 15=13w) /\
  (S 5  0=15w) /\ (S 5  1= 5w) /\ (S 5  2= 2w) /\ (S 5  3=11w) /\
  (S 5  4= 4w) /\ (S 5  5=10w) /\ (S 5  6= 9w) /\ (S 5  7=12w) /\
  (S 5  8= 0w) /\ (S 5  9= 3w) /\ (S 5 10=14w) /\ (S 5 11= 8w) /\
  (S 5 12=13w) /\ (S 5 13= 6w) /\ (S 5 14= 7w) /\ (S 5 15= 1w) /\
  (S 6  0= 7w) /\ (S 6  1= 2w) /\ (S 6  2=12w) /\ (S 6  3= 5w) /\
  (S 6  4= 8w) /\ (S 6  5= 4w) /\ (S 6  6= 6w) /\ (S 6  7=11w) /\
  (S 6  8=14w) /\ (S 6  9= 9w) /\ (S 6 10= 1w) /\ (S 6 11=15w) /\
  (S 6 12=13w) /\ (S 6 13= 3w) /\ (S 6 14=10w) /\ (S 6 15= 0w) /\
  (S 7  0= 1w) /\ (S 7  1=13w) /\ (S 7  2=15w) /\ (S 7  3= 0w) /\
  (S 7  4=14w) /\ (S 7  5= 8w) /\ (S 7  6= 2w) /\ (S 7  7=11w) /\
  (S 7  8= 7w) /\ (S 7  9= 4w) /\ (S 7 10=12w) /\ (S 7 11=10w) /\
  (S 7 12= 9w) /\ (S 7 13= 3w) /\ (S 7 14= 5w) /\ (S 7 15= 6w)`,

EVAL_TAC);


(*inverse sbox table used in decrytion
*)
val invSBoxVal=Q.store_thm(
"invSBoxVal",
`
  (invS 0  0=13w) /\ (invS 0  1= 3w) /\ (invS 0  2=11w) /\ (invS 0  3= 0w) /\
  (invS 0  4=10w) /\ (invS 0  5= 6w) /\ (invS 0  6= 5w) /\ (invS 0  7=12w) /\
  (invS 0  8= 1w) /\ (invS 0  9=14w) /\ (invS 0 10= 4w) /\ (invS 0 11= 7w) /\
  (invS 0 12=15w) /\ (invS 0 13= 9w) /\ (invS 0 14= 8w) /\ (invS 0 15= 2w) /\
  (invS 1  0= 5w) /\ (invS 1  1= 8w) /\ (invS 1  2= 2w) /\ (invS 1  3=14w) /\
  (invS 1  4=15w) /\ (invS 1  5= 6w) /\ (invS 1  6=12w) /\ (invS 1  7= 3w) /\
  (invS 1  8=11w) /\ (invS 1  9= 4w) /\ (invS 1 10= 7w) /\ (invS 1 11= 9w) /\
  (invS 1 12= 1w) /\ (invS 1 13=13w) /\ (invS 1 14=10w) /\ (invS 1 15= 0w) /\
  (invS 2  0=12w) /\ (invS 2  1= 9w) /\ (invS 2  2=15w) /\ (invS 2  3= 4w) /\
  (invS 2  4=11w) /\ (invS 2  5=14w) /\ (invS 2  6= 1w) /\ (invS 2  7= 2w) /\
  (invS 2  8= 0w) /\ (invS 2  9= 3w) /\ (invS 2 10= 6w) /\ (invS 2 11=13w) /\
  (invS 2 12= 5w) /\ (invS 2 13= 8w) /\ (invS 2 14=10w) /\ (invS 2 15= 7w) /\
  (invS 3  0= 0w) /\ (invS 3  1= 9w) /\ (invS 3  2=10w) /\ (invS 3  3= 7w) /\
  (invS 3  4=11w) /\ (invS 3  5=14w) /\ (invS 3  6= 6w) /\ (invS 3  7=13w) /\
  (invS 3  8= 3w) /\ (invS 3  9= 5w) /\ (invS 3 10=12w) /\ (invS 3 11= 2w) /\
  (invS 3 12= 4w) /\ (invS 3 13= 8w) /\ (invS 3 14=15w) /\ (invS 3 15= 1w) /\
  (invS 4  0= 5w) /\ (invS 4  1= 0w) /\ (invS 4  2= 8w) /\ (invS 4  3= 3w) /\
  (invS 4  4=10w) /\ (invS 4  5= 9w) /\ (invS 4  6= 7w) /\ (invS 4  7=14w) /\
  (invS 4  8= 2w) /\ (invS 4  9=12w) /\ (invS 4 10=11w) /\ (invS 4 11= 6w) /\
  (invS 4 12= 4w) /\ (invS 4 13=15w) /\ (invS 4 14=13w) /\ (invS 4 15= 1w) /\
  (invS 5  0= 8w) /\ (invS 5  1=15w) /\ (invS 5  2= 2w) /\ (invS 5  3= 9w) /\
  (invS 5  4= 4w) /\ (invS 5  5= 1w) /\ (invS 5  6=13w) /\ (invS 5  7=14w) /\
  (invS 5  8=11w) /\ (invS 5  9= 6w) /\ (invS 5 10= 5w) /\ (invS 5 11= 3w) /\ 
  (invS 5 12= 7w) /\ (invS 5 13=12w) /\ (invS 5 14=10w) /\ (invS 5 15= 0w) /\
  (invS 6  0=15w) /\ (invS 6  1=10w) /\ (invS 6  2= 1w) /\ (invS 6  3=13w) /\
  (invS 6  4= 5w) /\ (invS 6  5= 3w) /\ (invS 6  6= 6w) /\ (invS 6  7= 0w) /\
  (invS 6  8= 4w) /\ (invS 6  9= 9w) /\ (invS 6 10=14w) /\ (invS 6 11= 7w) /\
  (invS 6 12= 2w) /\ (invS 6 13=12w) /\ (invS 6 14= 8w) /\ (invS 6 15=11w) /\
  (invS 7  0= 3w) /\ (invS 7  1= 0w) /\ (invS 7  2= 6w) /\ (invS 7  3=13w) /\
  (invS 7  4= 9w) /\ (invS 7  5=14w) /\ (invS 7  6=15w) /\ (invS 7  7= 8w) /\
  (invS 7  8= 5w) /\ (invS 7  9=12w) /\ (invS 7 10=11w) /\ (invS 7 11= 7w) /\
  (invS 7 12=10w) /\ (invS 7 13= 1w) /\ (invS 7 14= 4w) /\ (invS 7 15= 2w)`,
	
EVAL_TAC);


(*apply SBox on a nibble (word4)*)
val sNibble_def = Define
`sNibble round (w4:word4) = S (round MOD 8) (w2n w4)`;

(*apply invSBox on a nibble (word4)*)
val invSNibble_def = Define
`invSNibble round (w4:word4) = invS (round MOD 8) (w2n w4)`;

(*SBox and invSBox cancels *)
val invS_S_cancel=Q.store_thm(
"invS_S_cancel",
`!round. 
	round<8 
	==>
	(!n. n<16==> (invS  round (w2n (S round n))=n2w n))`, 

SIMP_TAC arith_ss [BOUNDED_FORALL_THM] THEN
  SRW_TAC [] [SBoxVal, invSBoxVal]);
	
val invSNibble_sNibble_cancel=Q.store_thm(
"invSNibble_sNibble_cancel",
`!round w.
	round<32
	==>
	(invSNibble round (sNibble round w)=w)`,

SRW_TAC [] [invSNibble_def,sNibble_def,invS_S_cancel,
            WORD_DECIDE ``w2n (w:word4) < 16``]);

val w4l_fact=Q.store_thm(
"w4l_fact",
`!wl round. 
	round<32
	==> 
	ALL_EL (\x. (invSNibble round o sNibble round) x =x) wl`,
	
Induct_on `wl` THENL [
	 RW_TAC list_ss [],
	 RW_TAC list_ss [invSNibble_sNibble_cancel]]);   	
	 



(*apply SBox and invSBox on a word128*)  
val sBlock_def=Define
`sBlock round w128=word4ltow128 (MAP (sNibble round) (word128tow4l w128))`;

val invSBlock_def=Define
`invSBlock round w128=word4ltow128 (MAP (invSNibble round) (word128tow4l w128))`;	

(*invSBlock and sBlock cancel*)
val invSBlock_sBlock_cancel=Q.store_thm(
"invSBlock_sBlock_cancel",
`!w128 round. 
	round <32
	==>
	(invSBlock round (sBlock round w128)=w128)`,	

RW_TAC std_ss [invSBlock_def,sBlock_def] THEN
`LENGTH  (MAP (sNibble round) (word128tow4l w128))=32` by METIS_TAC [LENGTH_MAP,LENGTH_word128tow4l] THEN
RW_TAC std_ss [word128tow4l_conversion,MAP_MAP_o,w4l_fact,MAP_ID,word4ltow128_conversion]);


val _ = export_theory();
