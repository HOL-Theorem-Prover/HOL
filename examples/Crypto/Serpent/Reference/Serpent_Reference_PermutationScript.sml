open HolKernel Parse boolLib bossLib listTheory rich_listTheory bitTheory
     markerTheory pairTheory arithmeticTheory
     wordsTheory Serpent_Reference_UtilityTheory wordsLib;

val _ = new_theory "Serpent_Reference_Permutation";

(*initial/inverse final permutation table*)
val IPTable_def = Define
`IPTable =
 [  0; 32; 64; 96;  1; 33; 65; 97;  2; 34; 66; 98;  3; 35; 67; 99;
    4; 36; 68;100;  5; 37; 69;101;  6; 38; 70;102;  7; 39; 71;103;
    8; 40; 72;104;  9; 41; 73;105; 10; 42; 74;106; 11; 43; 75;107;
   12; 44; 76;108; 13; 45; 77;109; 14; 46; 78;110; 15; 47; 79;111;
   16; 48; 80;112; 17; 49; 81;113; 18; 50; 82;114; 19; 51; 83;115;
   20; 52; 84;116; 21; 53; 85;117; 22; 54; 86;118; 23; 55; 87;119;
   24; 56; 88;120; 25; 57; 89;121; 26; 58; 90;122; 27; 59; 91;123;
   28; 60; 92;124; 29; 61; 93;125; 30; 62; 94;126; 31; 63; 95;127]`;

(*final/inverse initial permutation table*)
val FPTable_def = Define
`FPTable =
 [  0;  4;  8; 12; 16; 20; 24; 28; 32; 36; 40; 44; 48; 52; 56; 60;
   64; 68; 72; 76; 80; 84; 88; 92; 96;100;104;108;112;116;120;124;
    1;  5;  9; 13; 17; 21; 25; 29; 33; 37; 41; 45; 49; 53; 57; 61;
   65; 69; 73; 77; 81; 85; 89; 93; 97;101;105;109;113;117;121;125;
    2;  6; 10; 14; 18; 22; 26; 30; 34; 38; 42; 46; 50; 54; 58; 62;
   66; 70; 74; 78; 82; 86; 90; 94; 98;102;106;110;114;118;122;126;
    3;  7; 11; 15; 19; 23; 27; 31; 35; 39; 43; 47; 51; 55; 59; 63;
   67; 71; 75; 79; 83; 87; 91; 95; 99;103;107;111;115;119;123;127]`;

val IPFun_def = Define
`IPFun x = EL x IPTable`;

val FPFun_def = Define
`FPFun x = EL x FPTable`;

(*precomputed to speed things up*)

val IPFunVal = save_thm(
 "IPFunVal",
 LIST_CONJ
   (map EVAL (for 0 127 (fn i => ``IPFun ^(numSyntax.term_of_int i)``))));

val FPFunVal = save_thm(
 "FPFunVal",
 LIST_CONJ
   (map EVAL (for 0 127 (fn i => ``FPFun ^(numSyntax.term_of_int i)``))));

(*permutation *)
val permu_def = Define
`(permu 0 permFun (block:word128)
  = let sourceBit = block ' (permFun 0)
    in
    if sourceBit
       then (1w:word128)
       else (0w:word128))
 /\
 (permu (SUC i) permFun  block
 = let sourceBit = block ' (permFun (SUC i))
   in
   let maskedWord = if sourceBit
                       then (1w:word128) << (SUC i)
                      else (0w:word128)
   in
   maskedWord !! (permu i permFun  block))`;

(*for evaluation*)
val permuEval = Q.store_thm(
"permuEval",
`!m (block:word128).
    permu m permFun (block:word128)
    = if m = 0
         then let sourceBit = block ' (permFun 0)
              in
          if sourceBit
             then (1w:word128)
             else (0w:word128)
             else let sourceBit = block ' (permFun m)
              in
          let maskedWord = if sourceBit
                           then (1w:word128) << m
                           else (0w:word128)
           in
          maskedWord !! (permu (m-1) permFun  block) `,
 RW_TAC  list_ss [permu_def,LET_THM] THENL [
    Cases_on `m` THEN
    RW_TAC list_ss [permu_def,LET_THM],
    Cases_on `m` THEN
    RW_TAC list_ss [permu_def,LET_THM]]);

(*desired properties of permu *)
val perm_recur_inv1_w128 = Q.store_thm(
"perm_recur_inv1_w128",
`!permFun block from to d.
    (!x. x < 128 ==> permFun x < 128) /\
    (d < 128) /\
    (to < 128) /\
    (permFun to = from) /\
    to > d
    ==>
    ~((permu d permFun block) ' to)`,
 Induct_on `d` THEN
 SRW_TAC [ARITH_ss] [permu_def,LET_THM] THEN
 SRW_TAC [WORD_BIT_EQ_ss,BIT_ss] [n2w_def]);

val perm_recur_inv2_w128 = Q.store_thm(
"perm_recur_inv2_w128",
`!permFun block from to d.
    (!x. x < 128 ==> permFun x < 128) /\
    (d < 128) /\
    (to < 128) /\
    (permFun to = from) /\
    to <= d
    ==>
    ((permu d permFun block) ' to = block ' from)`,
 Induct_on `d` THEN
 SRW_TAC [ARITH_ss] [permu_def,LET_THM] THEN
 SRW_TAC [WORD_BIT_EQ_ss,BIT_ss] [n2w_def] THEN
 Cases_on `to <= d`  THEN Cases_on `to = d` THEN
 SRW_TAC [WORD_BIT_EQ_ss,BIT_ss] [n2w_def] THEN
 FULL_SIMP_TAC arith_ss [] THEN
 `to > d /\ (to = SUC d)` by DECIDE_TAC THEN
 ASM_SIMP_TAC arith_ss [perm_recur_inv1_w128]);

(*composite of 2 permutations*)
val permu_compose_w128 = Q.store_thm(
"permu_compose_w128",
`!permFun1 permFun2 block i.
    i < 128  /\
    (!x. x < 128 ==> permFun1 x < 128) /\
    (!x. x < 128 ==> permFun2 x < 128)
     ==>
    ((permu 127 permFun2 (permu 127 permFun1 block)) ' i =
     (permu 127 (permFun1 o permFun2)  block) ' i)`,
  SRW_TAC [] [] THEN
  `(permu 127 permFun2 (permu 127 permFun1 block)) ' i =
   (permu 127 permFun1 block) ' (permFun2 i)`
    by FULL_SIMP_TAC arith_ss [perm_recur_inv2_w128] THEN
  `(permu 127 (permFun1 o permFun2) block) ' i =
    block ' ((permFun1 o permFun2) i)`
    by FULL_SIMP_TAC arith_ss [perm_recur_inv2_w128] THEN
  `permFun2 i < 128` by METIS_TAC [] THEN
  `(permu 127 permFun1 block)' (permFun2 i) =
    block ' (permFun1 ( permFun2 i))`
    by FULL_SIMP_TAC arith_ss [perm_recur_inv2_w128] THEN
  RW_TAC std_ss []);

(*two permutations cancel each other*)
val permu_comp_reverse_w128 = Q.store_thm(
"permu_comp_reverse_w128",
`!permFun1 permFun2 block.
    (!x. x < 128 ==> permFun1 x < 128) /\
    (!x. x < 128 ==> permFun2 x < 128) /\
    (!x. x < 128 ==> ((permFun1 o permFun2) x = x)) ==>
    (permu 127 permFun2 (permu 127 permFun1 block) = block)`,
  SRW_TAC [] [] THEN
    SRW_TAC [WORD_BIT_EQ_ss] [permu_compose_w128, perm_recur_inv2_w128]);

val IP_def = Define `IP w128 = permu 127 IPFun w128`;
val FP_def = Define `FP w128 = permu 127 FPFun w128`;

val invIP_def = Define `invIP w128 = FP w128`;
val invFP_def = Define `invFP w128 = IP w128`;

val IP_FP_fact = Q.store_thm(
"IP_FP_fact",
`!x.
    x < 128 ==> ((IPFun x < 128) /\
    (FPFun x < 128) /\
    ((FPFun o IPFun) x = x) /\
    ((IPFun o FPFun) x = x))`,
 FULL_SIMP_TAC arith_ss [BOUNDED_FORALL_THM,IPFunVal,FPFunVal]);

(*permutations using given IP and FP tables cancel*)
val invFP_FP_cancel = Q.store_thm(
"invFP_FP_cancel",
`!block.
    invFP (FP block) = block`,
 SIMP_TAC std_ss [invFP_def,IP_def,FP_def,permu_comp_reverse_w128,IP_FP_fact]);

val invIP_IP_cancel = Q.store_thm(
"invIP_IP_cancel",
`!block.
    invIP (IP block)= block`,
 SIMP_TAC std_ss [invIP_def,IP_def,FP_def,permu_comp_reverse_w128,IP_FP_fact]);

val _ = export_theory();
