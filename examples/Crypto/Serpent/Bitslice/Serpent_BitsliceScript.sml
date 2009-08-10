(*             Serpent optimized cipher
 This is an Standard ML implementation of the optimized Serpent encryption algorithm,
 which is a candidate in Advanced Encryption Standard.
 For detailed information about MARS, please refer to
 http://www.cl.cam.ac.uk/~rja14/serpent.html
*)

open HolKernel Parse boolLib bossLib listTheory rich_listTheory bitTheory
     wordsTheory wordsLib pairTheory arithmeticTheory
     Serpent_Bitslice_UtilityTheory Serpent_Bitslice_SBoxTheory;

val _ = new_theory "Serpent_Bitslice";

(*****************TRANSFORMATION*******************************)

val transform_def = Define`
 transform (x0:word32, x1:word32, x2:word32, x3:word32)=
   (let y0 = x0 #>> (32 - 13) in
    let y2 = x2 #>> (32 - 3) in
    let y1 = (x1 ?? y0) ?? y2 in
    let y3 = (x3 ?? y2) ?? y0 << 3 in
    let y11 = y1 #>> (32 - 1) in
    let y31 = y3 #>> (32 - 7) in
    let y01 = (y0 ?? y11) ?? y31 in
    let y21 = (y2 ?? y31) ?? y11 << 7 in
    let y02 = y01 #>> (32 - 5) in
    let y22 = y21 #>> (32 - 22) in
      (y02,y11,y22,y31))`;

val inv_transform_def = Define`
  inv_transform (x0:word32, x1:word32, x2:word32, x3:word32)=
   (let y2 = x2 #>> 22 in
    let y0 = x0 #>> 5 in
    let y21 = (y2 ?? x3) ?? x1 << 7 in
    let y01 = (y0 ?? x1) ?? x3 in
    let y3 = x3 #>> 7 in
    let y1 = x1 #>> 1 in
    let y31 = (y3 ?? y21) ?? y01 << 3 in
    let y11 = (y1 ?? y01) ?? y21 in
    let y22 = y21 #>> 3 in
    let y02 = y01 #>> 13 in
      (y02,y11,y22,y31))`;

val transform_THM = Q.store_thm (
"transform_THM",
`!v. inv_transform (transform v) = v`,
 SIMP_TAC std_ss [FORALL_PROD,transform_def,inv_transform_def,LET_THM] THEN
 SRW_TAC [] []);

(********************************APPLYING KEYING**************************)
val keying_def = Define
`keying (x0:word32, x1:word32, x2:word32, x3:word32)
        (subkey0:word32, subkey1:word32, subkey2:word32, subkey3:word32)
 = (x0 ?? subkey0, x1 ?? subkey1, x2 ?? subkey2,x3 ?? subkey3)`;

val keying_THM = Q.store_thm (
"keying_THM",
`!d sk.
    keying (keying d sk) sk = d`,
  SIMP_TAC std_ss [FORALL_PROD,keying_def] THEN SRW_TAC [] []);

(**************************BLOCK ENCRYPTION******************************)
val f_def = Define `f a (op,sk) = op a sk`;

val encryptRnd00_def = Define
    `encryptRnd00 a b = transform (RND00 (keying a b))`;
val encryptRnd01_def = Define
    `encryptRnd01 a b = transform (RND01 (keying a b))`;
val encryptRnd02_def = Define
    `encryptRnd02 a b = transform (RND02 (keying a b))`;
val encryptRnd03_def = Define
    `encryptRnd03 a b = transform (RND03 (keying a b))`;
val encryptRnd04_def = Define
    `encryptRnd04 a b = transform (RND04 (keying a b))`;
val encryptRnd05_def = Define
    `encryptRnd05 a b = transform (RND05 (keying a b))`;
val encryptRnd06_def = Define
    `encryptRnd06 a b = transform (RND06 (keying a b))`;
val encryptRnd07_def = Define
    `encryptRnd07 a b = transform (RND07 (keying a b))`;
val encryptRnd08_def = Define
    `encryptRnd08 a b = transform (RND08 (keying a b))`;
val encryptRnd09_def = Define
    `encryptRnd09 a b = transform (RND09 (keying a b))`;
val encryptRnd10_def = Define
    `encryptRnd10 a b = transform (RND10 (keying a b))`;
val encryptRnd11_def = Define
    `encryptRnd11 a b = transform (RND11 (keying a b))`;
val encryptRnd12_def = Define
    `encryptRnd12 a b = transform (RND12 (keying a b))`;
val encryptRnd13_def = Define
    `encryptRnd13 a b = transform (RND13 (keying a b))`;
val encryptRnd14_def = Define
    `encryptRnd14 a b = transform (RND14 (keying a b))`;
val encryptRnd15_def = Define
    `encryptRnd15 a b = transform (RND15 (keying a b))`;
val encryptRnd16_def = Define
    `encryptRnd16 a b = transform (RND16 (keying a b))`;
val encryptRnd17_def = Define
    `encryptRnd17 a b = transform (RND17 (keying a b))`;
val encryptRnd18_def = Define
    `encryptRnd18 a b = transform (RND18 (keying a b))`;
val encryptRnd19_def = Define
    `encryptRnd19 a b = transform (RND19 (keying a b))`;
val encryptRnd20_def = Define
    `encryptRnd20 a b = transform (RND20 (keying a b))`;
val encryptRnd21_def = Define
    `encryptRnd21 a b = transform (RND21 (keying a b))`;
val encryptRnd22_def = Define
    `encryptRnd22 a b = transform (RND22 (keying a b))`;
val encryptRnd23_def = Define
    `encryptRnd23 a b = transform (RND23 (keying a b))`;
val encryptRnd24_def = Define
    `encryptRnd24 a b = transform (RND24 (keying a b))`;
val encryptRnd25_def = Define
    `encryptRnd25 a b = transform (RND25 (keying a b))`;
val encryptRnd26_def = Define
    `encryptRnd26 a b = transform (RND26 (keying a b))`;
val encryptRnd27_def = Define
    `encryptRnd27 a b = transform (RND27 (keying a b))`;
val encryptRnd28_def = Define
    `encryptRnd28 a b = transform (RND28 (keying a b))`;
val encryptRnd29_def = Define
    `encryptRnd29 a b = transform (RND29 (keying a b))`;
val encryptRnd30_def = Define
    `encryptRnd30 a b = transform (RND30 (keying a b))`;
val encryptRnd31_1_def = Define
    `encryptRnd31_1 a b31 = RND31 (keying a b31)`;
val encryptRnd31_2_def = Define
    `encryptRnd31_2 a b32 = keying a b32`;

val decryptRnd00_1_def = Define
    `decryptRnd00_1 a b32 = keying a b32`;
val decryptRnd00_2_def = Define
    `decryptRnd00_2 a b31 = keying (InvRND31 a) b31`;
val decryptRnd01_def = Define
    `decryptRnd01 a b = keying (InvRND30 (inv_transform a)) b`;
val decryptRnd02_def = Define
    `decryptRnd02 a b = keying (InvRND29 (inv_transform a)) b`;
val decryptRnd03_def = Define
    `decryptRnd03 a b = keying (InvRND28 (inv_transform a)) b`;
val decryptRnd04_def = Define
    `decryptRnd04 a b = keying (InvRND27 (inv_transform a)) b`;
val decryptRnd05_def = Define
    `decryptRnd05 a b = keying (InvRND26 (inv_transform a)) b`;
val decryptRnd06_def = Define
    `decryptRnd06 a b = keying (InvRND25 (inv_transform a)) b`;
val decryptRnd07_def = Define
    `decryptRnd07 a b = keying (InvRND24 (inv_transform a)) b`;
val decryptRnd08_def = Define
    `decryptRnd08 a b = keying (InvRND23 (inv_transform a)) b`;
val decryptRnd09_def = Define
    `decryptRnd09 a b = keying (InvRND22 (inv_transform a)) b`;
val decryptRnd10_def = Define
    `decryptRnd10 a b = keying (InvRND21 (inv_transform a)) b`;
val decryptRnd11_def = Define
    `decryptRnd11 a b = keying (InvRND20 (inv_transform a)) b`;
val decryptRnd12_def = Define
    `decryptRnd12 a b = keying (InvRND19 (inv_transform a)) b`;
val decryptRnd13_def = Define
    `decryptRnd13 a b = keying (InvRND18 (inv_transform a)) b`;
val decryptRnd14_def = Define
    `decryptRnd14 a b = keying (InvRND17 (inv_transform a)) b`;
val decryptRnd15_def = Define
    `decryptRnd15 a b = keying (InvRND16 (inv_transform a)) b`;
val decryptRnd16_def = Define
    `decryptRnd16 a b = keying (InvRND15 (inv_transform a)) b`;
val decryptRnd17_def = Define
    `decryptRnd17 a b = keying (InvRND14 (inv_transform a)) b`;
val decryptRnd18_def = Define
    `decryptRnd18 a b = keying (InvRND13 (inv_transform a)) b`;
val decryptRnd19_def = Define
    `decryptRnd19 a b = keying (InvRND12 (inv_transform a)) b`;
val decryptRnd20_def = Define
    `decryptRnd20 a b = keying (InvRND11 (inv_transform a)) b`;
val decryptRnd21_def = Define
    `decryptRnd21 a b = keying (InvRND10 (inv_transform a)) b`;
val decryptRnd22_def = Define
    `decryptRnd22 a b = keying (InvRND09 (inv_transform a)) b`;
val decryptRnd23_def = Define
    `decryptRnd23 a b = keying (InvRND08 (inv_transform a)) b`;
val decryptRnd24_def = Define
    `decryptRnd24 a b = keying (InvRND07 (inv_transform a)) b`;
val decryptRnd25_def = Define
    `decryptRnd25 a b = keying (InvRND06 (inv_transform a)) b`;
val decryptRnd26_def = Define
    `decryptRnd26 a b = keying (InvRND05 (inv_transform a)) b`;
val decryptRnd27_def = Define
    `decryptRnd27 a b = keying (InvRND04 (inv_transform a)) b`;
val decryptRnd28_def = Define
    `decryptRnd28 a b = keying (InvRND03 (inv_transform a)) b`;
val decryptRnd29_def = Define
    `decryptRnd29 a b = keying (InvRND02 (inv_transform a)) b`;
val decryptRnd30_def = Define
    `decryptRnd30 a b = keying (InvRND01 (inv_transform a)) b`;
val decryptRnd31_def = Define
    `decryptRnd31 a b = keying (InvRND00 (inv_transform a)) b`;

val encryptSchedule_def = Define
`encryptSchedule = encryptRnd00::encryptRnd01::encryptRnd02::encryptRnd03::
    encryptRnd04::encryptRnd05::encryptRnd06::encryptRnd07::
    encryptRnd08::encryptRnd09::encryptRnd10::encryptRnd11::
    encryptRnd12::encryptRnd13::encryptRnd14::encryptRnd15::
    encryptRnd16::encryptRnd17::encryptRnd18::encryptRnd19::
    encryptRnd20::encryptRnd21::encryptRnd22::encryptRnd23::
    encryptRnd24::encryptRnd25::encryptRnd26::encryptRnd27::
    encryptRnd28::encryptRnd29::encryptRnd30::encryptRnd31_1::encryptRnd31_2::[]`;


val decryptSchedule_def = Define
`decryptSchedule = decryptRnd00_1::decryptRnd00_2::decryptRnd01::
    decryptRnd02::decryptRnd03::
    decryptRnd04::decryptRnd05::decryptRnd06::decryptRnd07::
    decryptRnd08::decryptRnd09::decryptRnd10::decryptRnd11::
    decryptRnd12::decryptRnd13::decryptRnd14::decryptRnd15::
    decryptRnd16::decryptRnd17::decryptRnd18::decryptRnd19::
    decryptRnd20::decryptRnd21::decryptRnd22::decryptRnd23::
    decryptRnd24::decryptRnd25::decryptRnd26::decryptRnd27::
    decryptRnd28::decryptRnd29::decryptRnd30::decryptRnd31::[]`;


val serpent_encrypt_def = Define
    `serpent_encrypt plaintext subkeys =
    let opKey = ZIP (encryptSchedule, subkeys)
    in
    FOLDL f plaintext opKey`;

val serpent_decrypt_def = Define
    `serpent_decrypt ciphertext subkeys =
    let opKey = ZIP (decryptSchedule, REVERSE subkeys)
    in
    FOLDL f ciphertext opKey`;

(*********************FUNCTIONAL CORRECTNESS********************)

val serpent_THM = Q.store_thm(
"serpent_THM",
`!pt sk.
    (LENGTH sk = 33)
    ==>
    (serpent_decrypt (serpent_encrypt pt sk) sk = pt)`,
 RW_TAC list_ss [serpent_decrypt_def,serpent_encrypt_def,LET_THM] THEN
  `?v_0 v_1 v_2 v_3 v_4 v_5 v_6 v_7 v_8 v_9 v_10 v_11
    v_12 v_13 v_14 v_15 v_16 v_17 v_18 v_19 v_20 v_21 v_22
    v_23 v_24 v_25 v_26 v_27 v_28 v_29 v_30 v_31 v_32.
   sk =[v_0; v_1; v_2; v_3; v_4; v_5; v_6; v_7; v_8; v_9; v_10; v_11;
        v_12; v_13; v_14; v_15; v_16; v_17; v_18; v_19; v_20; v_21; v_22;
        v_23; v_24; v_25; v_26; v_27; v_28; v_29; v_30; v_31; v_32]`
     by METIS_TAC [listInstEq33] THEN
 RW_TAC list_ss [encryptSchedule_def, decryptSchedule_def,f_def,
    encryptRnd00_def,encryptRnd01_def,encryptRnd02_def,encryptRnd03_def,
    encryptRnd04_def,encryptRnd05_def,encryptRnd06_def,encryptRnd07_def,
    encryptRnd08_def,encryptRnd09_def,encryptRnd10_def,encryptRnd11_def,
    encryptRnd12_def,encryptRnd13_def,encryptRnd14_def,encryptRnd15_def,
    encryptRnd16_def,encryptRnd17_def,encryptRnd18_def,encryptRnd19_def,
    encryptRnd20_def,encryptRnd21_def,encryptRnd22_def,encryptRnd23_def,
    encryptRnd24_def,encryptRnd25_def,encryptRnd26_def,encryptRnd27_def,
    encryptRnd28_def,encryptRnd29_def,encryptRnd30_def,encryptRnd31_1_def,
    encryptRnd31_2_def,
    decryptRnd00_1_def,decryptRnd00_2_def,decryptRnd01_def,decryptRnd02_def,
    decryptRnd03_def,decryptRnd04_def,decryptRnd05_def,decryptRnd06_def,
    decryptRnd07_def,decryptRnd08_def,decryptRnd09_def,decryptRnd10_def,
    decryptRnd11_def,decryptRnd12_def,decryptRnd13_def,decryptRnd14_def,
    decryptRnd15_def,decryptRnd16_def,decryptRnd17_def,decryptRnd18_def,
    decryptRnd19_def,decryptRnd20_def,decryptRnd21_def,decryptRnd22_def,
    decryptRnd23_def,decryptRnd24_def,decryptRnd25_def,decryptRnd26_def,
    decryptRnd27_def,decryptRnd28_def,decryptRnd29_def,decryptRnd30_def,
    decryptRnd31_def,

    RND00_THM,RND01_THM,RND02_THM,RND03_THM,
    RND04_THM,RND05_THM,RND06_THM,RND07_THM,
    RND08_THM,RND09_THM,RND10_THM,RND11_THM,
    RND12_THM,RND13_THM,RND14_THM,RND15_THM,
    RND16_THM,RND17_THM,RND18_THM,RND19_THM,
    RND20_THM,RND21_THM,RND22_THM,RND23_THM,
    RND24_THM,RND25_THM,RND26_THM,RND27_THM,
    RND28_THM,RND29_THM,RND30_THM,RND31_THM,
    keying_THM,transform_THM]);

val _ = export_theory();
