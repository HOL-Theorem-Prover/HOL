(*             Serpent reference cipher
 This is an Standard ML implementation of reference Serpent
 encryption algorithm, which was a candidate in
 Advanced Encryption Standard. For detailed information about Serpent,
 please refer to
 http://www.cl.cam.ac.uk/~rja14/serpent.html
*)


open HolKernel Parse boolLib bossLib listTheory arithmeticTheory
     wordsTheory wordsLib
     Serpent_Reference_UtilityTheory
     Serpent_Reference_PermutationTheory
     Serpent_Reference_TransformationTheory
     Serpent_Reference_SBoxTheory
     Serpent_Reference_KeyScheduleTheory;

val _ = new_theory "Serpent_Reference";

(****************************ENCRYPTION*******************************)
(*each normal encryption round*)

val enRound_def = Define
`enRound pt round (revSubKeyHat::kt) =
  if round=0
     then let afterKeying= pt ?? revSubKeyHat
          in
      let afterS = sBlock 0 afterKeying
      in
      LT afterS
     else
          let BHat=enRound pt (round-1) kt
      in
      let afterKeying= BHat ?? revSubKeyHat
      in
      let afterS = sBlock round afterKeying
      in
      LT afterS`;

(*special encryption round 31*)
val enRound31_def=Define
`enRound31 pt (revSubKeyHat32::revSubKeyHat31::kt)
 =let afterEnRound30= enRound pt 30 kt
  in
  let afterKeying= afterEnRound30 ?? revSubKeyHat31
  in
  let afterS = sBlock 31 afterKeying
  in
  afterS ?? revSubKeyHat32`;

(*encryption*)
val doAllEnRound_def = Define
`doAllEnRound pt subKeyHat
 =let revSubKeyHat = REVERSE subKeyHat
  in
  enRound31 pt revSubKeyHat`;


val encryptwithKeyHat_def= Define
`encryptwithKeyHat pt subKeyHat = FP (doAllEnRound (IP pt) subKeyHat)`;


val serpentBlockEncrypt_def = Define
`serpentBlockEncrypt pt userKey kl
 = let subKeyHat =makeKeyHat userKey kl
   in
   encryptwithKeyHat pt subKeyHat`;

(**********************************DECRYPTION***********************)


(*each normal decryption round*)
val deRound_def = Define
`deRound (BHat:word128) round (revSubKeyHat::kt)
 = let afterInvLT =invLT BHat
   in
   let afterInvS= invSBlock (31-round) afterInvLT
   in
   let nextBHat = afterInvS ?? revSubKeyHat
   in
   if round <(R-1)
      then deRound nextBHat (SUC round) kt
      else nextBHat`;

(*special decryption round 0*)
val deRound0_def=Define
`deRound0 BHat0 revSubKeyHat_1 revSubKeyHat0
 = let afterRevKeying_1=BHat0 ?? revSubKeyHat_1
   in
   let afterInvS= invSBlock 31 afterRevKeying_1
   in
   afterInvS ?? revSubKeyHat0`;


(*decryption,
in reverse order as encryption*)
val doAllDeRound_def=Define
`doAllDeRound et (revSubKeyHat_1::revSubKeyHat0::kt)
 = let afterDeRound0=deRound0 et revSubKeyHat_1 revSubKeyHat0
   in
   deRound afterDeRound0 1 kt`;


val decryptwithKeyHat_def= Define
`decryptwithKeyHat et subKeyHat
 = let revSubKeyHat=REVERSE subKeyHat
   in
   let afterInvFP=invFP et
   in
   let afterDeRound = doAllDeRound afterInvFP revSubKeyHat
   in
   invIP afterDeRound`;


val serpentBlockDecrypt_def = Define
`serpentBlockDecrypt et userKey kl
 = let subKeyHat = makeKeyHat userKey kl
   in
   decryptwithKeyHat et subKeyHat`;


(********* FUNCTIONAL CORRECTNESS*********************************)

(*use induction*)
val deRound_enRound_cancel=Q.store_thm(
"deRound_enRound_cancel",
`!r t revKeyHat.
    r >0 /\
    r<31 /\
    (LENGTH revKeyHat=r+1)
    ==>
    (deRound (enRound t r revKeyHat) (31-r) revKeyHat=t)`,
  Induct_on `r` THENL [
    FULL_SIMP_TAC arith_ss [],
    RW_TAC std_ss [] THEN
    Cases_on `r` THEN Cases_on `revKeyHat` THENL [
        FULL_SIMP_TAC list_ss [],
        SRW_TAC [] [enRound_def,deRound_def,invSBlock_sBlock_cancel,
                    invLT_LT_cancel,LET_THM,R_def] THEN
        Cases_on `t'` THENL [
            FULL_SIMP_TAC list_ss [],
            SRW_TAC [] [enRound_def,deRound_def,invSBlock_sBlock_cancel,
                        invLT_LT_cancel,LET_THM,R_def]],
        FULL_SIMP_TAC list_ss [],
        `SUC (31 - SUC (SUC n)) = 31 - SUC n` by RW_TAC arith_ss [] THEN
        FULL_SIMP_TAC (srw_ss()++ARITH_ss)
          [enRound_def,deRound_def,invSBlock_sBlock_cancel,
           invLT_LT_cancel,LET_THM,R_def]]]);

val decryptwithKeyHat_encryptwithKeyHat_cancel=Q.store_thm(
"decryptwithKeyHat_encryptwithKeyHat_cancel",
`!keyHat pt.
    (LENGTH keyHat=33)
    ==>
    (decryptwithKeyHat (encryptwithKeyHat pt keyHat) keyHat= pt)`,
  RW_TAC std_ss [encryptwithKeyHat_def, decryptwithKeyHat_def,
                 LET_THM,invFP_FP_cancel] THEN
  `?v_0 v_1 v_2 v_3 v_4 v_5 v_6 v_7 v_8 v_9 v_10 v_11 v_12 v_13 v_14 v_15
    v_16 v_17 v_18 v_19 v_20 v_21 v_22 v_23 v_24 v_25 v_26 v_27 v_28 v_29
    v_30 v_31 v_32.
    keyHat=[v_0; v_1; v_2; v_3; v_4; v_5; v_6; v_7; v_8; v_9; v_10; v_11; v_12;
            v_13; v_14; v_15; v_16; v_17; v_18; v_19; v_20; v_21; v_22;v_23;
            v_24; v_25; v_26; v_27; v_28; v_29; v_30; v_31; v_32]`
        by METIS_TAC [listInstEq33] THEN
  SRW_TAC [] [doAllDeRound_def,doAllEnRound_def,deRound0_def,
              enRound31_def,LET_THM,invSBlock_sBlock_cancel] THEN
  `LENGTH [v_30; v_29; v_28; v_27; v_26; v_25; v_24; v_23; v_22; v_21; v_20;
           v_19; v_18; v_17; v_16; v_15; v_14; v_13; v_12; v_11; v_10; v_9;
           v_8; v_7; v_6; v_5; v_4; v_3; v_2; v_1; v_0] = 30 + 1`
    by RW_TAC list_ss [] THEN
  METIS_TAC [deRound_enRound_cancel,invIP_IP_cancel,
             DECIDE ``30 > 0 /\ 30 < 31 /\ (31 = 30 + 1) /\ (1 = 31 - 30)``]);

(*based on deRound_enRound_cancel*)
val serpentBlockDecrypt_serpentBlockEncrypt_cancel_rec=Q.store_thm(
"serpentBlockDecrypt_serpentBlockEncrypt_cancel_rec",
`!userKey pt kl.
    serpentBlockDecrypt (serpentBlockEncrypt pt userKey kl) userKey kl=pt`,
  RW_TAC std_ss [serpentBlockDecrypt_def,serpentBlockEncrypt_def,LET_THM] THEN
  METIS_TAC [makeKeyHatLength,decryptwithKeyHat_encryptwithKeyHat_cancel]);

(*without induction,brutal force*)
val serpentBlockDecrypt_serpentBlockEncrypt_cancel_whole=Q.store_thm(
"serpentBlockDecrypt_serpentBlockEncrypt_cancel_whole",
`!userKey pt kl.
    serpentBlockDecrypt (serpentBlockEncrypt pt userKey kl) userKey kl = pt`,
 RW_TAC std_ss [serpentBlockDecrypt_def,serpentBlockEncrypt_def,
                LET_THM,encryptwithKeyHat_def, decryptwithKeyHat_def] THEN
  `?v_0 v_1 v_2 v_3 v_4 v_5 v_6 v_7 v_8 v_9 v_10 v_11 v_12 v_13 v_14 v_15
    v_16 v_17 v_18 v_19 v_20 v_21 v_22 v_23 v_24 v_25 v_26 v_27 v_28 v_29
    v_30 v_31 v_32.
     makeKeyHat userKey kl
     =[v_0; v_1; v_2; v_3; v_4; v_5; v_6; v_7; v_8; v_9;
       v_10; v_11; v_12; v_13; v_14; v_15; v_16; v_17; v_18;
       v_19; v_20; v_21; v_22;v_23; v_24; v_25; v_26; v_27;
       v_28; v_29; v_30; v_31; v_32]`
    by METIS_TAC [makeKeyHatLength, listInstEq33] THEN
  SRW_TAC [] [doAllDeRound_def,deRound_def,doAllEnRound_def,
              enRound_def,enRound31_def,deRound0_def,invFP_FP_cancel,
              invIP_IP_cancel,invSBlock_sBlock_cancel,invLT_LT_cancel,
              LET_THM,R_def]);

val _ = export_theory();
