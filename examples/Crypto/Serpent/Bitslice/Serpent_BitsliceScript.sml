(*             Serpent optimized cipher
 This is an Standard ML implementation of the optimized Serpent encryption algorithm,
 which is a candidate in Advanced Encryption Standard.
 For detailed information about MARS, please refer to
 http://www.cl.cam.ac.uk/~rja14/serpent.html
*)
Theory Serpent_Bitslice
Ancestors
  list rich_list bit words pair arithmetic
  Serpent_Bitslice_Utility Serpent_Bitslice_SBox
Libs
  wordsLib


(*****************TRANSFORMATION*******************************)

Definition transform_def:
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
      (y02,y11,y22,y31))
End

Definition inv_transform_def:
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
      (y02,y11,y22,y31))
End

Theorem transform_THM:
 !v. inv_transform (transform v) = v
Proof
 SIMP_TAC std_ss [FORALL_PROD,transform_def,inv_transform_def,LET_THM] THEN
 SRW_TAC [] []
QED

(********************************APPLYING KEYING**************************)
Definition keying_def:
 keying (x0:word32, x1:word32, x2:word32, x3:word32)
        (subkey0:word32, subkey1:word32, subkey2:word32, subkey3:word32)
 = (x0 ?? subkey0, x1 ?? subkey1, x2 ?? subkey2,x3 ?? subkey3)
End

Theorem keying_THM:
 !d sk.
    keying (keying d sk) sk = d
Proof
  SIMP_TAC std_ss [FORALL_PROD,keying_def] THEN SRW_TAC [] []
QED

(**************************BLOCK ENCRYPTION******************************)
Definition f_def:   f a (op,sk) = op a sk
End

Definition encryptRnd00_def:
     encryptRnd00 a b = transform (RND00 (keying a b))
End
Definition encryptRnd01_def:
     encryptRnd01 a b = transform (RND01 (keying a b))
End
Definition encryptRnd02_def:
     encryptRnd02 a b = transform (RND02 (keying a b))
End
Definition encryptRnd03_def:
     encryptRnd03 a b = transform (RND03 (keying a b))
End
Definition encryptRnd04_def:
     encryptRnd04 a b = transform (RND04 (keying a b))
End
Definition encryptRnd05_def:
     encryptRnd05 a b = transform (RND05 (keying a b))
End
Definition encryptRnd06_def:
     encryptRnd06 a b = transform (RND06 (keying a b))
End
Definition encryptRnd07_def:
     encryptRnd07 a b = transform (RND07 (keying a b))
End
Definition encryptRnd08_def:
     encryptRnd08 a b = transform (RND08 (keying a b))
End
Definition encryptRnd09_def:
     encryptRnd09 a b = transform (RND09 (keying a b))
End
Definition encryptRnd10_def:
     encryptRnd10 a b = transform (RND10 (keying a b))
End
Definition encryptRnd11_def:
     encryptRnd11 a b = transform (RND11 (keying a b))
End
Definition encryptRnd12_def:
     encryptRnd12 a b = transform (RND12 (keying a b))
End
Definition encryptRnd13_def:
     encryptRnd13 a b = transform (RND13 (keying a b))
End
Definition encryptRnd14_def:
     encryptRnd14 a b = transform (RND14 (keying a b))
End
Definition encryptRnd15_def:
     encryptRnd15 a b = transform (RND15 (keying a b))
End
Definition encryptRnd16_def:
     encryptRnd16 a b = transform (RND16 (keying a b))
End
Definition encryptRnd17_def:
     encryptRnd17 a b = transform (RND17 (keying a b))
End
Definition encryptRnd18_def:
     encryptRnd18 a b = transform (RND18 (keying a b))
End
Definition encryptRnd19_def:
     encryptRnd19 a b = transform (RND19 (keying a b))
End
Definition encryptRnd20_def:
     encryptRnd20 a b = transform (RND20 (keying a b))
End
Definition encryptRnd21_def:
     encryptRnd21 a b = transform (RND21 (keying a b))
End
Definition encryptRnd22_def:
     encryptRnd22 a b = transform (RND22 (keying a b))
End
Definition encryptRnd23_def:
     encryptRnd23 a b = transform (RND23 (keying a b))
End
Definition encryptRnd24_def:
     encryptRnd24 a b = transform (RND24 (keying a b))
End
Definition encryptRnd25_def:
     encryptRnd25 a b = transform (RND25 (keying a b))
End
Definition encryptRnd26_def:
     encryptRnd26 a b = transform (RND26 (keying a b))
End
Definition encryptRnd27_def:
     encryptRnd27 a b = transform (RND27 (keying a b))
End
Definition encryptRnd28_def:
     encryptRnd28 a b = transform (RND28 (keying a b))
End
Definition encryptRnd29_def:
     encryptRnd29 a b = transform (RND29 (keying a b))
End
Definition encryptRnd30_def:
     encryptRnd30 a b = transform (RND30 (keying a b))
End
Definition encryptRnd31_1_def:
     encryptRnd31_1 a b31 = RND31 (keying a b31)
End
Definition encryptRnd31_2_def:
     encryptRnd31_2 a b32 = keying a b32
End

Definition decryptRnd00_1_def:
     decryptRnd00_1 a b32 = keying a b32
End
Definition decryptRnd00_2_def:
     decryptRnd00_2 a b31 = keying (InvRND31 a) b31
End
Definition decryptRnd01_def:
     decryptRnd01 a b = keying (InvRND30 (inv_transform a)) b
End
Definition decryptRnd02_def:
     decryptRnd02 a b = keying (InvRND29 (inv_transform a)) b
End
Definition decryptRnd03_def:
     decryptRnd03 a b = keying (InvRND28 (inv_transform a)) b
End
Definition decryptRnd04_def:
     decryptRnd04 a b = keying (InvRND27 (inv_transform a)) b
End
Definition decryptRnd05_def:
     decryptRnd05 a b = keying (InvRND26 (inv_transform a)) b
End
Definition decryptRnd06_def:
     decryptRnd06 a b = keying (InvRND25 (inv_transform a)) b
End
Definition decryptRnd07_def:
     decryptRnd07 a b = keying (InvRND24 (inv_transform a)) b
End
Definition decryptRnd08_def:
     decryptRnd08 a b = keying (InvRND23 (inv_transform a)) b
End
Definition decryptRnd09_def:
     decryptRnd09 a b = keying (InvRND22 (inv_transform a)) b
End
Definition decryptRnd10_def:
     decryptRnd10 a b = keying (InvRND21 (inv_transform a)) b
End
Definition decryptRnd11_def:
     decryptRnd11 a b = keying (InvRND20 (inv_transform a)) b
End
Definition decryptRnd12_def:
     decryptRnd12 a b = keying (InvRND19 (inv_transform a)) b
End
Definition decryptRnd13_def:
     decryptRnd13 a b = keying (InvRND18 (inv_transform a)) b
End
Definition decryptRnd14_def:
     decryptRnd14 a b = keying (InvRND17 (inv_transform a)) b
End
Definition decryptRnd15_def:
     decryptRnd15 a b = keying (InvRND16 (inv_transform a)) b
End
Definition decryptRnd16_def:
     decryptRnd16 a b = keying (InvRND15 (inv_transform a)) b
End
Definition decryptRnd17_def:
     decryptRnd17 a b = keying (InvRND14 (inv_transform a)) b
End
Definition decryptRnd18_def:
     decryptRnd18 a b = keying (InvRND13 (inv_transform a)) b
End
Definition decryptRnd19_def:
     decryptRnd19 a b = keying (InvRND12 (inv_transform a)) b
End
Definition decryptRnd20_def:
     decryptRnd20 a b = keying (InvRND11 (inv_transform a)) b
End
Definition decryptRnd21_def:
     decryptRnd21 a b = keying (InvRND10 (inv_transform a)) b
End
Definition decryptRnd22_def:
     decryptRnd22 a b = keying (InvRND09 (inv_transform a)) b
End
Definition decryptRnd23_def:
     decryptRnd23 a b = keying (InvRND08 (inv_transform a)) b
End
Definition decryptRnd24_def:
     decryptRnd24 a b = keying (InvRND07 (inv_transform a)) b
End
Definition decryptRnd25_def:
     decryptRnd25 a b = keying (InvRND06 (inv_transform a)) b
End
Definition decryptRnd26_def:
     decryptRnd26 a b = keying (InvRND05 (inv_transform a)) b
End
Definition decryptRnd27_def:
     decryptRnd27 a b = keying (InvRND04 (inv_transform a)) b
End
Definition decryptRnd28_def:
     decryptRnd28 a b = keying (InvRND03 (inv_transform a)) b
End
Definition decryptRnd29_def:
     decryptRnd29 a b = keying (InvRND02 (inv_transform a)) b
End
Definition decryptRnd30_def:
     decryptRnd30 a b = keying (InvRND01 (inv_transform a)) b
End
Definition decryptRnd31_def:
     decryptRnd31 a b = keying (InvRND00 (inv_transform a)) b
End

Definition encryptSchedule_def:
 encryptSchedule = encryptRnd00::encryptRnd01::encryptRnd02::encryptRnd03::
    encryptRnd04::encryptRnd05::encryptRnd06::encryptRnd07::
    encryptRnd08::encryptRnd09::encryptRnd10::encryptRnd11::
    encryptRnd12::encryptRnd13::encryptRnd14::encryptRnd15::
    encryptRnd16::encryptRnd17::encryptRnd18::encryptRnd19::
    encryptRnd20::encryptRnd21::encryptRnd22::encryptRnd23::
    encryptRnd24::encryptRnd25::encryptRnd26::encryptRnd27::
    encryptRnd28::encryptRnd29::encryptRnd30::encryptRnd31_1::encryptRnd31_2::[]
End


Definition decryptSchedule_def:
 decryptSchedule = decryptRnd00_1::decryptRnd00_2::decryptRnd01::
    decryptRnd02::decryptRnd03::
    decryptRnd04::decryptRnd05::decryptRnd06::decryptRnd07::
    decryptRnd08::decryptRnd09::decryptRnd10::decryptRnd11::
    decryptRnd12::decryptRnd13::decryptRnd14::decryptRnd15::
    decryptRnd16::decryptRnd17::decryptRnd18::decryptRnd19::
    decryptRnd20::decryptRnd21::decryptRnd22::decryptRnd23::
    decryptRnd24::decryptRnd25::decryptRnd26::decryptRnd27::
    decryptRnd28::decryptRnd29::decryptRnd30::decryptRnd31::[]
End


Definition serpent_encrypt_def:
     serpent_encrypt plaintext subkeys =
    let opKey = ZIP (encryptSchedule, subkeys)
    in
    FOLDL f plaintext opKey
End

Definition serpent_decrypt_def:
     serpent_decrypt ciphertext subkeys =
    let opKey = ZIP (decryptSchedule, REVERSE subkeys)
    in
    FOLDL f ciphertext opKey
End

(*********************FUNCTIONAL CORRECTNESS********************)

Theorem serpent_THM:
 !pt sk.
    (LENGTH sk = 33)
    ==>
    (serpent_decrypt (serpent_encrypt pt sk) sk = pt)
Proof
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
    keying_THM,transform_THM]
QED

