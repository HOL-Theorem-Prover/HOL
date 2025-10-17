(*             Serpent reference cipher
 This is an Standard ML implementation of reference Serpent
 encryption algorithm, which was a candidate in
 Advanced Encryption Standard. For detailed information about Serpent,
 please refer to
 http://www.cl.cam.ac.uk/~rja14/serpent.html
*)
Theory Serpent_Reference
Ancestors
  list arithmetic words Serpent_Reference_Utility
  Serpent_Reference_Permutation Serpent_Reference_Transformation
  Serpent_Reference_SBox Serpent_Reference_KeySchedule
Libs
  wordsLib



(****************************ENCRYPTION*******************************)
(*each normal encryption round*)

Definition enRound_def:
 enRound pt round (revSubKeyHat::kt) =
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
      LT afterS
End

(*special encryption round 31*)
Definition enRound31_def:
 enRound31 pt (revSubKeyHat32::revSubKeyHat31::kt)
 =let afterEnRound30= enRound pt 30 kt
  in
  let afterKeying= afterEnRound30 ?? revSubKeyHat31
  in
  let afterS = sBlock 31 afterKeying
  in
  afterS ?? revSubKeyHat32
End

(*encryption*)
Definition doAllEnRound_def:
 doAllEnRound pt subKeyHat
 =let revSubKeyHat = REVERSE subKeyHat
  in
  enRound31 pt revSubKeyHat
End


Definition encryptwithKeyHat_def:
 encryptwithKeyHat pt subKeyHat = FP (doAllEnRound (IP pt) subKeyHat)
End


Definition serpentBlockEncrypt_def:
 serpentBlockEncrypt pt userKey kl
 = let subKeyHat =makeKeyHat userKey kl
   in
   encryptwithKeyHat pt subKeyHat
End

(**********************************DECRYPTION***********************)


(*each normal decryption round*)
Definition deRound_def:
 deRound (BHat:word128) round (revSubKeyHat::kt)
 = let afterInvLT =invLT BHat
   in
   let afterInvS= invSBlock (31-round) afterInvLT
   in
   let nextBHat = afterInvS ?? revSubKeyHat
   in
   if round <(R-1)
      then deRound nextBHat (SUC round) kt
      else nextBHat
End

(*special decryption round 0*)
Definition deRound0_def:
 deRound0 BHat0 revSubKeyHat_1 revSubKeyHat0
 = let afterRevKeying_1=BHat0 ?? revSubKeyHat_1
   in
   let afterInvS= invSBlock 31 afterRevKeying_1
   in
   afterInvS ?? revSubKeyHat0
End


(*decryption,
in reverse order as encryption*)
Definition doAllDeRound_def:
 doAllDeRound et (revSubKeyHat_1::revSubKeyHat0::kt)
 = let afterDeRound0=deRound0 et revSubKeyHat_1 revSubKeyHat0
   in
   deRound afterDeRound0 1 kt
End


Definition decryptwithKeyHat_def:
 decryptwithKeyHat et subKeyHat
 = let revSubKeyHat=REVERSE subKeyHat
   in
   let afterInvFP=invFP et
   in
   let afterDeRound = doAllDeRound afterInvFP revSubKeyHat
   in
   invIP afterDeRound
End


Definition serpentBlockDecrypt_def:
 serpentBlockDecrypt et userKey kl
 = let subKeyHat = makeKeyHat userKey kl
   in
   decryptwithKeyHat et subKeyHat
End


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

