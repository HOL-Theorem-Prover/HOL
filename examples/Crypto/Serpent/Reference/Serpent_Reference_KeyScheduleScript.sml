open HolKernel Parse boolLib bossLib listTheory rich_listTheory bitTheory
     markerTheory pairTheory arithmeticTheory wordsTheory wordsLib
     Serpent_Reference_UtilityTheory Serpent_Reference_SBoxTheory
     Serpent_Reference_PermutationTheory;

val _ = new_theory "Serpent_Reference_KeySchedule";

(*32 rounds*)

val R_def = Define `R = 32`;

val PHI_def = Define `PHI = 0x9e3779b9w : word32`;

(*padding*)

val short2longKey_def =
  Define
   `short2longKey k kl =
      let nw256 = (n2w:num->word256) (k MOD  (2**kl))
      in
        nw256 !! (1w << kl)`;

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

(*in reverse order

round  from 31 to 0

bitPos from 31 to 0

(k3,k2,k1,k0) =(0w,0w,0w,0w) when bitPos = 31

efficient
A version with mainly bit shifts, rotation and bitwise operation has been tried,
it is slow
*)

val makeRoundKey_def = Define
`makeRoundKey (w3:word32,w2:word32,w1:word32,w0:word32)
   (k3:word32,k2:word32,k1:word32,k0:word32) bitPos round =
  let bitofw0 = if w0 ' bitPos then 1 else 0 in
  let bitofw1 = if w1 ' bitPos then 2 else 0 in
  let bitofw2 = if w2 ' bitPos then 4 else 0 in
  let bitofw3 = if w3 ' bitPos then 8 else 0 in
  let subed = S (((R+3-round) MOD R) MOD 8)
                (bitofw3 + bitofw2 + bitofw1 + bitofw0)
  in
  let subedbitofw0 = if subed ' 0 then 2 ** bitPos else 0 in
  let subedbitofw1 = if subed ' 1 then 2 ** bitPos else 0 in
  let subedbitofw2 = if subed ' 2 then 2 ** bitPos else 0 in
  let subedbitofw3 = if subed ' 3 then 2 ** bitPos else 0 in
  let bitofk0 = subedbitofw0 + w2n k0 in
  let bitofk1 = subedbitofw1 + w2n k1 in
  let bitofk2 = subedbitofw2 + w2n k2 in
  let bitofk3 = subedbitofw3 + w2n k3 in
    if bitPos = 0 then
     (n2w (bitofk3 * 2 ** 96 +
           bitofk2 * 2 ** 64 +
           bitofk1 * 2 ** 32 +
           bitofk0) : word128)
    else
      makeRoundKey (w3,w2,w1,w0)
        (n2w bitofk3, n2w bitofk2, n2w bitofk1, n2w bitofk0) (bitPos-1) round`;

(* EL 0 is the 128bit key for first round MSBit(127)...LSBit(0) for each key
   initialize round with 32 still in reversed order here *)

val makeRevSubKey_def = Define
`(makeRevSubKey [] round = []) /\
 (makeRevSubKey (w3::w2::w1::w0::t) round =
   let roundKey = makeRoundKey (w3,w2,w1,w0) (0w,0w,0w,0w) 31 round in
     roundKey::(makeRevSubKey t (round-1)))`;

(*this is the key used in the optimized version*)

val makeSubKey_def = Define
 `makeSubKey revPreKey = REVERSE ( makeRevSubKey revPreKey 32)`;

(*this is the key used in the reference version*)

val makeSubKeyHat_def = Define
 `makeSubKeyHat subKey = MAP IP subKey`;

val makeKeyHat_def = Define
`makeKeyHat userKey kl =
  let longKey = short2longKey userKey kl in
  let revPreKey = makeRevPreKey longKey in
  let subKey = makeSubKey revPreKey in
    makeSubKeyHat subKey`;

val makeSubKeyBitSliceLength = Q.store_thm(
"makeSubKeyBitSliceLength",
`!longKey n.
    (LENGTH longKey>= 8)
    ==>
    (LENGTH (makeSubKeyBitSlice longKey n) = n + LENGTH longKey + 1)`,
  Induct_on `n` THENL [
    FULL_SIMP_TAC list_ss [makeSubKeyBitSlice_def,LENGTH,Abbrev_def] THEN
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
  `LENGTH (word256to32l userKey)= 8` by METIS_TAC [word256to32lLength] THEN
  `LENGTH (word256to32l userKey)>= 8` by RW_TAC arith_ss [] THEN
  `LENGTH (makeSubKeyBitSlice (word256to32l userKey) 131)
   = 131+LENGTH (word256to32l userKey) +1`
      by METIS_TAC [makeSubKeyBitSliceLength,LENGTH_REVERSE] THEN
  `8 <= LENGTH (makeSubKeyBitSlice (word256to32l userKey) 131)`
      by FULL_SIMP_TAC arith_ss [] THEN
  FULL_SIMP_TAC list_ss [LENGTH_myBUTLASTN,LENGTH_REVERSE]);

val makeRevSubKeyLength = Q.store_thm(
"makeRevSubKeyLength",
`!n revPreKey.
    (LENGTH revPreKey = 4 * (n+1)) ==>
    (LENGTH (makeRevSubKey revPreKey n) = n + 1)`,
  Induct_on `n` THENL [
    RW_TAC arith_ss [] THEN
    `?w_1 w_2 w_3 w_4.
        revPreKey = (w_1::w_2::w_3::w_4::[])`
        by METIS_TAC [listInstEq4] THEN
    FULL_SIMP_TAC list_ss [makeRevSubKey_def] THEN
    RW_TAC std_ss [] THEN
    FULL_SIMP_TAC list_ss [LENGTH,Abbrev_def],
    `4 * (SUC n + 1) = 4 +  4 * (n + 1)` by RW_TAC arith_ss [] THEN
    `4 * (SUC n + 1) >= 4` by  RW_TAC arith_ss [] THEN
    RW_TAC std_ss [] THEN
    `?v_1 v_2 v_3 v_4 t.
        revPreKey = (v_1::v_2::v_3::v_4::t)`
        by METIS_TAC [listInstGreaterEq4] THEN
    `LENGTH t = 4 * (n + 1)` by FULL_SIMP_TAC list_ss [LENGTH] THEN
    FULL_SIMP_TAC list_ss [makeRevSubKey_def,LET_THM]]);

val makeSubKeyLength = Q.store_thm(
"makeSubKeyLength",
`!revPreKey.
    (LENGTH revPreKey = 132) ==> (LENGTH (makeSubKey revPreKey) = 33)`,
 RW_TAC list_ss [makeSubKey_def,makeRevSubKeyLength,LENGTH_REVERSE]);

(* the only property of key shecduling which matters for the functional
   correctness of Serpent is the length of the generated key *)

val makeKeyHatLength = Q.store_thm(
"makeKeyHatLength",
`!userKey kl.
    LENGTH (makeKeyHat userKey kl) = 33`,
  RW_TAC std_ss [makeKeyHat_def,makeSubKeyHat_def] THEN
  RW_TAC std_ss [LENGTH_MAP] THEN
  FULL_SIMP_TAC std_ss [Abbrev_def] THEN
  `LENGTH  (makeRevPreKey (short2longKey userKey kl))= 132`
      by METIS_TAC [makeRevPreKeyLength] THEN
  `132 = 4*(32+1)` by EVAL_TAC THEN
  FULL_SIMP_TAC arith_ss [makeSubKeyLength]);

val _ = export_theory();
