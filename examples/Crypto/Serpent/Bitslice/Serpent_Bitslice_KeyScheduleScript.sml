open HolKernel Parse boolLib bossLib listTheory rich_listTheory bitTheory
     markerTheory pairTheory arithmeticTheory wordsTheory wordsLib
     Serpent_Bitslice_UtilityTheory Serpent_Bitslice_SBoxTheory;

val _ = new_theory "Serpent_Bitslice_KeySchedule";

(*number of rounds*)                   
val R_def = Define `R = 32`;

(* PHI: Constant used in the key schedule *)

val PHI_def = Define `PHI = 0x9e3779b9w : word32`;

val short2longKey_def = Define 
`short2longKey k kl = let nw256 = n2w (k MOD  (2**kl)) in
  nw256 !! (1w<<kl) : word256`;

(*used in making preKey*)
val (makeSubKeyBitSlice_def,makeSubKeyBitSlice_termi) = Defn.tstore_defn(
Hol_defn "makeSubKeyBitSlice"
`makeSubKeyBitSlice (w_1::w_2::w_3::w_4::w_5::w_6::w_7::w_8::t) i 
 = let nl =((w_1 ?? w_3 ??  w_5 ?? w_8 ?? PHI ?? (n2w:num->word32) (131-i)) #>> 
            (32-11)) 
       ::(w_1::w_2::w_3::w_4::w_5::w_6::w_7::w_8::t) 
   in
   if i = 0 
      then nl
      else makeSubKeyBitSlice nl (i-1)`,
 WF_REL_TAC `measure SND`);


(*reversed preKey*)
val makeRevPreKey_def = Define
`makeRevPreKey longKey = let keySlices = word256to32l longKey in
 myBUTLASTN 8 (makeSubKeyBitSlice keySlices 131)`;


val revPreKey2SubKey_def = Define
`revPreKey2SubKey revPreKey
 = let w = REVERSE revPreKey 
  in
  RND03 (EL 0 w, EL 1 w, EL 2 w, EL 3 w)::
  RND02(EL 4 w, EL 5 w, EL 6 w, EL 7 w)::
  RND01(EL  8 w, EL  9 w, EL 10 w, EL 11 w)::
  RND00(EL 12 w, EL 13 w, EL 14 w, EL 15 w)::
  RND31(EL 16 w, EL 17 w, EL 18 w, EL 19 w)::
  RND30(EL 20 w, EL 21 w, EL 22 w, EL 23 w)::
  RND29(EL 24 w, EL 25 w, EL 26 w, EL 27 w)::
  RND28(EL 28 w, EL 29 w, EL 30 w, EL 31 w)::
  RND27(EL 32 w, EL 33 w, EL 34 w, EL 35 w)::
  RND26(EL 36 w, EL 37 w, EL 38 w, EL 39 w)::
  RND25(EL 40 w, EL 41 w, EL 42 w, EL 43 w)::
  RND24(EL 44 w, EL 45 w, EL 46 w, EL 47 w)::
  RND23(EL 48 w, EL 49 w, EL 50 w, EL 51 w)::
  RND22(EL 52 w, EL 53 w, EL 54 w, EL 55 w)::
  RND21(EL 56 w, EL 57 w, EL 58 w, EL 59 w)::
  RND20(EL 60 w, EL 61 w, EL 62 w, EL 63 w)::
  RND19(EL 64 w, EL 65 w, EL 66 w, EL 67 w)::
  RND18(EL 68 w, EL 69 w, EL 70 w, EL 71 w)::
  RND17(EL 72 w, EL 73 w, EL 74 w, EL 75 w)::
  RND16(EL 76 w, EL 77 w, EL 78 w, EL 79 w)::
  RND15(EL 80 w, EL 81 w, EL 82 w, EL 83 w)::
  RND14(EL 84 w, EL 85 w, EL 86 w, EL 87 w)::
  RND13(EL 88 w, EL 89 w, EL 90 w, EL 91 w)::
  RND12(EL 92 w, EL 93 w, EL 94 w, EL 95 w)::
  RND11(EL 96 w, EL 97 w, EL 98 w, EL 99 w)::
  RND10(EL 100 w, EL 101 w, EL 102 w, EL 103 w)::
  RND09(EL 104 w, EL 105 w, EL 106 w, EL 107 w)::
  RND08(EL 108 w, EL 109 w, EL 110 w, EL 111 w)::
  RND07(EL 112 w, EL 113 w, EL 114 w, EL 115 w)::
  RND06(EL 116 w, EL 117 w, EL 118 w, EL 119 w)::
  RND05(EL 120 w, EL 121 w, EL 122 w, EL 123 w)::
  RND04(EL 124 w, EL 125 w, EL 126 w, EL 127 w)::
  RND03(EL 128 w, EL 129 w, EL 130 w, EL 131 w)::[]`;


val makeKey_def = Define  
`makeKey userKey kl 
 = let longKey = short2longKey userKey kl 
  in
  let revPreKey = makeRevPreKey longKey 
  in 
  revPreKey2SubKey revPreKey`;
     
val makeSubKeyBitSliceLength = Q.store_thm(
"makeSubKeyBitSliceLength",
`!longKey n. 
    (LENGTH longKey>= 8)
    ==> 
    (LENGTH (makeSubKeyBitSlice longKey n ) = n+LENGTH longKey+1)`,
  Induct_on `n` THENL [
    FULL_SIMP_TAC list_ss [makeSubKeyBitSlice_def,LENGTH,LET_THM] THEN
    RW_TAC std_ss [] THEN
    `?v_1 v_2 v_3 v_4 v_5 v_6 v_7 v_8 t.
       longKey = (v_1::v_2::v_3::v_4::v_5::v_6::v_7::v_8::t)`
      by METIS_TAC [listInstGreaterEq8] THEN
    FULL_SIMP_TAC list_ss [makeSubKeyBitSlice_def] THEN
    METIS_TAC [LENGTH,SUC_ONE_ADD,ADD_COMM],
    RW_TAC std_ss [] THEN
    `?v_1 v_2 v_3 v_4 v_5 v_6 v_7 v_8 t.
       longKey = (v_1::v_2::v_3::v_4::v_5::v_6::v_7::v_8::t)`
      by METIS_TAC [listInstGreaterEq8] THEN
    FULL_SIMP_TAC list_ss [makeSubKeyBitSlice_def] THEN
    RW_TAC list_ss [] THEN
    FULL_SIMP_TAC list_ss [Abbrev_def]]);

val makeRevPreKeyLength = Q.store_thm(
"makeRevPreKeyLength",
`!userKey. 
    LENGTH (makeRevPreKey userKey) = 132`,
  RW_TAC std_ss [makeRevPreKey_def,LET_THM] THEN
  `LENGTH (word256to32l userKey) = 8` by METIS_TAC [word256to32lLength] THEN
  `LENGTH (word256to32l userKey)>= 8` by RW_TAC arith_ss [] THEN
  `LENGTH  (makeSubKeyBitSlice (word256to32l userKey) 131) =
     131+LENGTH (word256to32l userKey) +1`
     by METIS_TAC [makeSubKeyBitSliceLength,LENGTH_REVERSE] THEN
  `8 <=  LENGTH (makeSubKeyBitSlice (word256to32l userKey) 131)`
     by FULL_SIMP_TAC arith_ss [] THEN
  FULL_SIMP_TAC list_ss [LENGTH_myBUTLASTN,LENGTH_REVERSE]);

(*only length matters in functional correctness*)
val makeKeyLength = Q.store_thm(
"makeKeyLength",
`!userKey kl. 
    LENGTH (makeKey userKey kl) = 33`,
  RW_TAC list_ss [makeKey_def,revPreKey2SubKey_def,LET_THM]);

val _ = export_theory();
