(* For interactive use
app load ["word16Lib", "metisLib", "intLib","ideaMultTheory"];
quietdec := true;
open word16Lib word16Theory metisLib pairTheory 
     intLib integerTheory ideaMultTheory;
quietdec := false;
*)

open HolKernel Parse boolLib bossLib
     word16Lib word16Theory metisLib pairTheory 
     intLib integerTheory ideaMultTheory;

val RESTR_EVAL_TAC = computeLib.RESTR_EVAL_TAC;

(*- security stuff start here -*)
val _ = new_theory "idea";

val ARW = RW_TAC arith_ss;
val ASP = FULL_SIMP_TAC arith_ss;

(*- disable integer parsing here-*)

val _ = intLib.deprecate_int();

(*---------------------------------------------------------------------------*)
(* Useful type abbreviations                                                 *)
(*---------------------------------------------------------------------------*)

val _ = type_abbrev("Block",    ``:word16 # word16 # word16 # word16``);
val _ = type_abbrev("OddKey",   ``:word16 # word16 # word16 # word16``);
val _ = type_abbrev("EvenKey",  ``:word16 # word16``);

val _ = type_abbrev("InputKey", 
        ``:word16 # word16 # word16 # word16 # 
           word16 # word16 # word16 # word16``);

val _ = type_abbrev ("OddKeySched", 
        ``:OddKey#OddKey#OddKey#OddKey#
           OddKey#OddKey#OddKey#OddKey#OddKey``);

val _ = type_abbrev ("EvenKeySched",
        ``:EvenKey#EvenKey#EvenKey#EvenKey#
           EvenKey#EvenKey#EvenKey#EvenKey``);

val FORALL_BLOCK = Q.store_thm
("FORALL_BLOCK",
 `(!b:Block. Q b) =
   !w1 w2 w3 w4.
    Q (w1,w2,w3,w4)`,
 SIMP_TAC std_ss [FORALL_PROD]);

val FORALL_ODDKEYSCHED = Q.prove
(`(!x:OddKeySched. Q x) = !k1 k2 k3 k4 k5 k6 k7 k8 k9. 
                        Q(k1,k2,k3,k4,k5,k6,k7,k8,k9)`,
 EQ_TAC THEN RW_TAC std_ss [] THEN
 `?a1 a2 a3 a4 a5 a6 a7 a8 a9. 
     x = (a1,a2,a3,a4,a5,a6,a7,a8,a9)`
   by METIS_TAC [ABS_PAIR_THM]
 THEN ASM_REWRITE_TAC[]);

val FORALL_EVENKEYSCHED = Q.prove
(`(!x:EvenKeySched. Q x) = !k1 k2 k3 k4 k5 k6 k7 k8. 
                        Q(k1,k2,k3,k4,k5,k6,k7,k8)`,
 EQ_TAC THEN RW_TAC std_ss [] THEN
 `?a1 a2 a3 a4 a5 a6 a7 a8. 
     x = (a1,a2,a3,a4,a5,a6,a7,a8)`
   by METIS_TAC [ABS_PAIR_THM]
 THEN ASM_REWRITE_TAC[]);

val FORALL_EVENKEY = Q.prove
(`(!x:EvenKey. Q x) = !kw1 kw2. 
                        Q(kw1,kw2)`,
 EQ_TAC THEN RW_TAC std_ss [] THEN
 `?a1 a2. 
     x = (a1,a2)`
   by METIS_TAC [ABS_PAIR_THM]
 THEN ASM_REWRITE_TAC[]);

val FORALL_ODDKEY = Q.prove
(`(!x:OddKey. Q x) = !kw1 kw2 kw3 kw4. 
                        Q(kw1,kw2,kw3,kw4)`,
 EQ_TAC THEN RW_TAC std_ss [] THEN
 `?a1 a2 a3 a4. 
     x = (a1,a2,a3,a4)`
   by METIS_TAC [ABS_PAIR_THM]
 THEN ASM_REWRITE_TAC[]);

val ZeroOddKey_def =  Define `ZeroOddKey = (0w,0w,0w,0w) : OddKey`;
val ZeroEvenKey_def =  Define `ZeroEvenKey = (0w,0w) : EvenKey`;
val ZeroOddKeys_def = 
 Define
      `ZeroOddKeys = (ZeroOddKey,ZeroOddKey,ZeroOddKey,ZeroOddKey,ZeroOddKey,
                      ZeroOddKey,ZeroOddKey,ZeroOddKey,ZeroOddKey) : OddKeySched`;
val ZeroEvenKeys_def = 
 Define
      `ZeroEvenKeys = (ZeroEvenKey,ZeroEvenKey,ZeroEvenKey,ZeroEvenKey,
                       ZeroEvenKey,ZeroEvenKey,ZeroEvenKey,ZeroEvenKey) : EvenKeySched`;

(*---Use Both Additive and Multiplicative Inverses Now---*)
val InverseKey_def = 
 Define 
   `InverseKey (k1,k2,k3,k4) = (winv k1, ~k3, ~k2, winv k4) : OddKey`;

val InverseKeys_def = 
 Define
   `InverseKeys (ok1,ok2,ok3,ok4,ok5,ok6,ok7,ok8,ok9) =
                (InverseKey ok9,InverseKey ok8,InverseKey ok7,InverseKey ok6,
                 InverseKey ok5,InverseKey ok4,InverseKey ok3,InverseKey ok2,
                 InverseKey ok1) : OddKeySched`;

val ReverseKeys_def = 
 Define
   `ReverseKeys (ek1,ek2,ek3,ek4,ek5,ek6,ek7,ek8) =
                (ek8,ek7,ek6,ek5,ek4,ek3,ek2,ek1) : EvenKeySched`;

val RotateOddKeys_def = 
 Define
   `RotateOddKeys (k1,k2,k3,k4,k5,k6,k7,k8,k9) =
            (k2,k3,k4,k5,k6,k7,k8,k9,k1) : OddKeySched`;

val RotateEvenKeys_def = 
 Define
   `RotateEvenKeys (k1,k2,k3,k4,k5,k6,k7,k8) =
            (k2,k3,k4,k5,k6,k7,k8,k1) : EvenKeySched`;

(*-1st and 4th are multiplications now-*)
val OddRound_def = 
 Define 
   `OddRound ((Ka, Kb, Kc, Kd):OddKey) ((Xa, Xb, Xc, Xd):Block) =
          (Xa wmul Ka, Xc + Kc, Xb + Kb,Xd wmul Kd) :Block`;

val OddRound_Lemma1 = Q.store_thm
("OddRound_Lemma1",
 `!w1:word16 w2:word16. w1 + w2 + ~w2 = w1`,
 SIMP_TAC std_ss [WORD_ADD_COMM] THEN
 SIMP_TAC std_ss [WORD_ADD_ASSOC] THEN 
 ONCE_REWRITE_TAC [WORD_ADD_COMM] THEN
 SIMP_TAC std_ss [WORD_ADD_ASSOC, WORD_ADD_RINV, WORD_ADD]);

val OddRound_Inversion = Q.store_thm
("OddRound_Inversion",
 `!s:Block k:OddKey. OddRound (InverseKey k) (OddRound k s) = s`,
 SIMP_TAC std_ss [FORALL_BLOCK, FORALL_ODDKEY] THEN
 ARW [InverseKey_def, OddRound_def] THEN
 ARW [wmul_ASSOC, wmul_Theorem, wmul_Mul1, OddRound_Lemma1]);

val Mangler1_def = Define `Mangler1 ((Yin:word16), (Zin:word16), (Ke:word16), (Kf:word16)) = ((Ke * Yin) + Zin) * Kf`;
val Mangler2_def = Define `Mangler2 ((Yin:word16), (Ke:word16), (Yout:word16)) = (Ke * Yin) + Yout`;

val Mangler1_Lemma1 = Q.store_thm
("Mangler1_Lemma1",
 `!w1 w2 w3 w4 w5 w6. w5 # Mangler1 (w1, w2, w3, w4) # (w6 # Mangler1 (w1, w2, w3, w4)) = w5 # w6`,
 SIMP_TAC std_ss [WORD_EOR_ASSOC] THEN 
 SIMP_TAC std_ss [WORD_EOR_COMM] THEN
 SIMP_TAC std_ss [WORD_EOR_ASSOC] THEN 
 ONCE_REWRITE_TAC [WORD_EOR_COMM] THEN
 SIMP_TAC std_ss [WORD_EOR_ASSOC, WORD_EOR_INV, WORD_EOR_ID]);

val Mangler1_Lemma2 = Q.store_thm
("Mangler1_Lemma2",
 `!w1 w2 w3 w4 w5. w5 # Mangler1 (w1, w2, w3, w4) # Mangler1 (w1, w2, w3, w4) = w5`,
 SIMP_TAC std_ss [WORD_EOR_COMM] THEN 
 SIMP_TAC std_ss [WORD_EOR_ASSOC] THEN
 ONCE_REWRITE_TAC [WORD_EOR_COMM] THEN
 SIMP_TAC std_ss [WORD_EOR_ASSOC, WORD_EOR_INV, WORD_EOR_ID]);

val Mangler2_Lemma1 = Q.store_thm
("Mangler2_Lemma1",
 `!w1 w2 w3 w4 w5. w4 # Mangler2 (w1, w2, w3) # (w5 # Mangler2 (w1, w2, w3)) = w4 # w5`,
 SIMP_TAC std_ss [WORD_EOR_ASSOC] THEN 
 SIMP_TAC std_ss [WORD_EOR_COMM] THEN
 SIMP_TAC std_ss [WORD_EOR_ASSOC] THEN 
 ONCE_REWRITE_TAC [WORD_EOR_COMM] THEN
 SIMP_TAC std_ss [WORD_EOR_ASSOC, WORD_EOR_INV, WORD_EOR_ID]);

val Mangler2_Lemma2 = Q.store_thm
("Mangler2_Lemma2",
 `!w1 w2 w3 w4. w4 # Mangler2 (w1, w2, w3) # Mangler2 (w1, w2, w3) = w4`,
 SIMP_TAC std_ss [WORD_EOR_COMM] THEN 
 SIMP_TAC std_ss [WORD_EOR_ASSOC] THEN
 ONCE_REWRITE_TAC [WORD_EOR_COMM] THEN
 SIMP_TAC std_ss [WORD_EOR_ASSOC, WORD_EOR_INV, WORD_EOR_ID]);

val EvenRound_def = Define
 `EvenRound ((Ke, Kf):EvenKey) ((Xa, Xb, Xc, Xd):Block) = 
   let Yout =  Mangler1 ((Xa # Xb), (Xc # Xd), Ke, Kf) in
     let Zout = Mangler2 ((Xa # Xb), Ke, Yout) in 
       (Xa # Yout, Xb # Yout, Xc # Zout, Xd # Zout):Block`;

val [Mangler1] = decls "Mangler1";
val [Mangler2] = decls "Mangler2";

val EvenRound_Inversion = Q.store_thm
("EvenRound_Inversion",
 `!s:Block k:EvenKey. EvenRound k (EvenRound k s) = s`,
 SIMP_TAC std_ss [FORALL_BLOCK, FORALL_EVENKEY] THEN
 RESTR_EVAL_TAC [Mangler1, Mangler2] THEN
 SIMP_TAC std_ss [Mangler1_Lemma1, Mangler1_Lemma2, Mangler2_Lemma1, Mangler2_Lemma2]);

val (Round_def,Round_ind) = 
  Defn.tprove 
    (Hol_defn 
      "Round"
      `Round n (oddkeys: OddKeySched) (evenkeys: EvenKeySched) (state:Block) = 
      if (n = 0) then
        state
      else
        if (EVEN n) then
          Round (n-1) oddkeys (RotateEvenKeys evenkeys) (EvenRound (FST evenkeys) state)
        else 
          Round (n-1) (RotateOddKeys oddkeys) evenkeys (OddRound (FST oddkeys) state)`,    
   WF_REL_TAC `measure (FST)`
   THEN CONJ_TAC
   THEN REPEAT PairRules.PGEN_TAC
   THEN SRW_TAC[ARITH_ss][]);

val IdeaFwd_def = Define `IdeaFwd oddkeys evenkeys= Round 17 oddkeys evenkeys`;

val [OddRound] = decls "OddRound";
val [EvenRound] = decls "EvenRound";

val IDEA_LEMMA = Q.store_thm
("IDEA_LEMMA",
 `!plaintext:Block oddkeys:OddKeySched evenkeys:EvenKeySched. 
     IdeaFwd (InverseKeys oddkeys) (ReverseKeys evenkeys) (IdeaFwd oddkeys evenkeys plaintext) = plaintext`,
 SIMP_TAC std_ss [FORALL_ODDKEYSCHED, FORALL_EVENKEYSCHED] THEN 
 RESTR_EVAL_TAC [OddRound, EvenRound] THEN 
 SIMP_TAC std_ss [OddRound_Inversion, EvenRound_Inversion]);

val (MakeEnKeys_def,MakeEnKeys_ind) = 
  Defn.tprove 
    (Hol_defn 
      "MakeEnKeys"
      `MakeEnKeys n (K8::K7::K6::K5::K4::K3::K2::K1::rst) = 
      let (NK1, NK2, NK3, NK4, NK5, NK6, NK7, NK8) = 
        ((K2<<9) # (K3>>>7), (K3<<9) # (K4>>>7), 
         (K4<<9) # (K5>>>7), (K5<<9) # (K6>>>7), 
         (K6<<9) # (K7>>>7), (K7<<9) # (K8>>>7), 
         (K8<<9) # (K1>>>7), (K1<<9) # (K2>>>7)) 
      in 
        if n = 0 then
          (NK4::NK3::NK2::NK1::K8::K7::K6::K5::K4::K3::K2::K1::rst)
        else 
          MakeEnKeys (n-1) (NK8::NK7::NK6::NK5::NK4::NK3::NK2::NK1
                           ::K8::K7::K6::K5::K4::K3::K2::K1::rst)`,
   WF_REL_TAC `measure (FST)`);

val MakeKeys_def = Define
   `MakeKeys ((K1, K2, K3, K4, K5, K6, K7, K8):InputKey)  = 
      MakeEnKeys 6 [K8;K7;K6;K5;K4;K3;K2;K1]`;

val ListToOddKeys_def = 
 Define
  `(ListToOddKeys [] oddkeys = oddkeys) /\
   (ListToOddKeys ((k1::k2::k3::k4::k5::k6::t): word16 list) 
        ((ok1,ok2,ok3,ok4,ok5,ok6,ok7,ok8,ok9): OddKeySched)  =
    ListToOddKeys t ((k1,k2,k3,k4),ok1,ok2,ok3,ok4,ok5,ok6,ok7,ok8))   /\
   (ListToOddKeys ((k1::k2::k3::k4::t): word16 list) 
               ((ok1,ok2,ok3,ok4,ok5,ok6,ok7,ok8,ok9): OddKeySched) =
    ListToOddKeys t ((k1,k2,k3,k4),ok1,ok2,ok3,ok4,ok5,ok6,ok7,ok8))`;

val ListToEvenKeys_def = 
 Define
  `(ListToEvenKeys [] evenkeys = evenkeys) /\
   (ListToEvenKeys ((k1::k2::k3::k4::k5::k6::t): word16 list) 
            ((ek1,ek2,ek3,ek4,ek5,ek6,ek7,ek8): EvenKeySched) =
    ListToEvenKeys t ((k5,k6),ek1,ek2,ek3,ek4,ek5,ek6,ek7))`;

val IDEA_def = Define `IDEA key = 
  let oddkeys = ListToOddKeys (MakeKeys key) ZeroOddKeys in
  let evenkeys = ListToEvenKeys (MakeKeys key) ZeroEvenKeys in 
    (IdeaFwd oddkeys evenkeys, IdeaFwd (InverseKeys oddkeys) (ReverseKeys evenkeys))`;


val IDEA_CORRECT = Q.store_thm
  ("IDEA_CORRECT",
   `!key plaintext. 
      ((encrypt,decrypt) = IDEA key) 
      ==> 
       (decrypt (encrypt plaintext) = plaintext)`,
 RW_TAC std_ss [IDEA_def,LET_THM,IDEA_LEMMA]);

val () = export_theory();
