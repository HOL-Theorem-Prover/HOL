(* For interactive use
app load ["wordsLib", "intLib","ideaMultTheory"];
quietdec := true;
open wordsLib wordsTheory pairTheory intLib integerTheory ideaMultTheory;
quietdec := false;
*)
Theory idea
Ancestors
  words pair integer ideaMult
Libs
  wordsLib intLib


val RESTR_EVAL_TAC = computeLib.RESTR_EVAL_TAC;

(*- security stuff start here -*)
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

Theorem FORALL_BLOCK:
  (!b:Block. Q b) =
   !w1 w2 w3 w4.
    Q (w1,w2,w3,w4)
Proof
 SIMP_TAC std_ss [FORALL_PROD]
QED

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

Definition ZeroOddKey_def:    ZeroOddKey = (0w,0w,0w,0w) : OddKey
End
Definition ZeroEvenKey_def:    ZeroEvenKey = (0w,0w) : EvenKey
End
Definition ZeroOddKeys_def:
   ZeroOddKeys = (ZeroOddKey,ZeroOddKey,ZeroOddKey,ZeroOddKey,ZeroOddKey,
                  ZeroOddKey,ZeroOddKey,ZeroOddKey,ZeroOddKey) : OddKeySched
End
Definition ZeroEvenKeys_def:
   ZeroEvenKeys = (ZeroEvenKey,ZeroEvenKey,ZeroEvenKey,ZeroEvenKey,
                   ZeroEvenKey,ZeroEvenKey,ZeroEvenKey,ZeroEvenKey) : EvenKeySched
End

(*---Use Both Additive and Multiplicative Inverses Now---*)
Definition InverseKey_def:
    InverseKey (k1,k2,k3,k4) = (winv k1, - k3, - k2, winv k4) : OddKey
End

Definition InverseKeys_def:
    InverseKeys (ok1,ok2,ok3,ok4,ok5,ok6,ok7,ok8,ok9) =
                (InverseKey ok9,InverseKey ok8,InverseKey ok7,InverseKey ok6,
                 InverseKey ok5,InverseKey ok4,InverseKey ok3,InverseKey ok2,
                 InverseKey ok1) : OddKeySched
End

Definition ReverseKeys_def:
    ReverseKeys (ek1,ek2,ek3,ek4,ek5,ek6,ek7,ek8) =
                (ek8,ek7,ek6,ek5,ek4,ek3,ek2,ek1) : EvenKeySched
End

Definition RotateOddKeys_def:
    RotateOddKeys (k1,k2,k3,k4,k5,k6,k7,k8,k9) =
            (k2,k3,k4,k5,k6,k7,k8,k9,k1) : OddKeySched
End

Definition RotateEvenKeys_def:
    RotateEvenKeys (k1,k2,k3,k4,k5,k6,k7,k8) =
            (k2,k3,k4,k5,k6,k7,k8,k1) : EvenKeySched
End

(*-1st and 4th are multiplications now-*)
Definition OddRound_def:
    OddRound ((Ka, Kb, Kc, Kd):OddKey) ((Xa, Xb, Xc, Xd):Block) =
          (Xa wmul Ka, Xc + Kc, Xb + Kb,Xd wmul Kd) :Block
End

Theorem OddRound_Lemma1:
  !w1:word16 w2:word16. w1 + w2 + - w2 = w1
Proof
 SRW_TAC [] []
QED

Theorem OddRound_Inversion:
  !s:Block k:OddKey. OddRound (InverseKey k) (OddRound k s) = s
Proof
 SIMP_TAC std_ss [FORALL_BLOCK, FORALL_ODDKEY] THEN
 ARW [InverseKey_def, OddRound_def] THEN
 ARW [wmul_ASSOC, wmul_Theorem, wmul_Mul1, OddRound_Lemma1]
QED

Definition Mangler1_def:
 Mangler1 ((Yin:word16), (Zin:word16), (Ke:word16), (Kf:word16)) =
   ((Ke * Yin) + Zin) * Kf
End

Definition Mangler2_def:
  Mangler2 ((Yin:word16), (Ke:word16), (Yout:word16)) = (Ke * Yin) + Yout
End

Definition EvenRound_def:
  EvenRound ((Ke, Kf):EvenKey) ((Xa, Xb, Xc, Xd):Block) =
   let Yout =  Mangler1 ((Xa ?? Xb), (Xc ?? Xd), Ke, Kf) in
     let Zout = Mangler2 ((Xa ?? Xb), Ke, Yout) in
       (Xa ?? Yout, Xb ?? Yout, Xc ?? Zout, Xd ?? Zout):Block
End

val [Mangler1] = decls "Mangler1";
val [Mangler2] = decls "Mangler2";

Theorem EvenRound_Inversion:
  !s:Block k:EvenKey. EvenRound k (EvenRound k s) = s
Proof
  SIMP_TAC std_ss [FORALL_BLOCK, FORALL_EVENKEY] THEN
  RESTR_EVAL_TAC [Mangler1, Mangler2] THEN
  SRW_TAC [] []
QED

val Round_def =
  tDefine "Round"
    `Round n (oddkeys: OddKeySched) (evenkeys: EvenKeySched) (state:Block) =
      if (n = 0) then
        state
      else
        if (EVEN n) then
          Round (n-1) oddkeys (RotateEvenKeys evenkeys)
            (EvenRound (FST evenkeys) state)
        else
          Round (n-1) (RotateOddKeys oddkeys) evenkeys
            (OddRound (FST oddkeys) state)`
  (WF_REL_TAC `measure (FST)` THEN RW_TAC arith_ss [ELIM_UNCURRY]);

Definition IdeaFwd_def:   IdeaFwd oddkeys evenkeys= Round 17 oddkeys evenkeys
End

val [OddRound] = decls "OddRound";
val [EvenRound] = decls "EvenRound";

Theorem IDEA_LEMMA:
  !plaintext:Block oddkeys:OddKeySched evenkeys:EvenKeySched.
     IdeaFwd (InverseKeys oddkeys) (ReverseKeys evenkeys)
       (IdeaFwd oddkeys evenkeys plaintext) = plaintext
Proof
 SIMP_TAC std_ss [FORALL_ODDKEYSCHED, FORALL_EVENKEYSCHED] THEN
 RESTR_EVAL_TAC [OddRound, EvenRound] THEN
 SIMP_TAC std_ss [OddRound_Inversion, EvenRound_Inversion]
QED

val MakeEnKeys_def =
  tDefine "MakeEnKeys"
   `MakeEnKeys n (K8::K7::K6::K5::K4::K3::K2::K1::rst) =
      let (NK1, NK2, NK3, NK4, NK5, NK6, NK7, NK8) =
        ((K2<<9) ?? (K3>>>7), (K3<<9) ?? (K4>>>7),
         (K4<<9) ?? (K5>>>7), (K5<<9) ?? (K6>>>7),
         (K6<<9) ?? (K7>>>7), (K7<<9) ?? (K8>>>7),
         (K8<<9) ?? (K1>>>7), (K1<<9) ?? (K2>>>7))
      in
        if n = 0 then
          (NK4::NK3::NK2::NK1::K8::K7::K6::K5::K4::K3::K2::K1::rst)
        else
          MakeEnKeys (n-1) (NK8::NK7::NK6::NK5::NK4::NK3::NK2::NK1
                           ::K8::K7::K6::K5::K4::K3::K2::K1::rst)`
   (WF_REL_TAC `measure (FST)`);

Definition MakeKeys_def:
    MakeKeys ((K1, K2, K3, K4, K5, K6, K7, K8):InputKey)  =
      MakeEnKeys 6 [K8;K7;K6;K5;K4;K3;K2;K1]
End

Definition ListToOddKeys_def:
   (ListToOddKeys [] oddkeys = oddkeys) /\
   (ListToOddKeys ((k1::k2::k3::k4::k5::k6::t): word16 list)
        ((ok1,ok2,ok3,ok4,ok5,ok6,ok7,ok8,ok9): OddKeySched)  =
    ListToOddKeys t ((k1,k2,k3,k4),ok1,ok2,ok3,ok4,ok5,ok6,ok7,ok8))   /\
   (ListToOddKeys ((k1::k2::k3::k4::t): word16 list)
               ((ok1,ok2,ok3,ok4,ok5,ok6,ok7,ok8,ok9): OddKeySched) =
    ListToOddKeys t ((k1,k2,k3,k4),ok1,ok2,ok3,ok4,ok5,ok6,ok7,ok8))
End

Definition ListToEvenKeys_def:
   (ListToEvenKeys [] evenkeys = evenkeys) /\
   (ListToEvenKeys ((k1::k2::k3::k4::k5::k6::t): word16 list)
            ((ek1,ek2,ek3,ek4,ek5,ek6,ek7,ek8): EvenKeySched) =
    ListToEvenKeys t ((k5,k6),ek1,ek2,ek3,ek4,ek5,ek6,ek7))
End

Definition IDEA_def:   IDEA key =
  let oddkeys = ListToOddKeys (MakeKeys key) ZeroOddKeys in
  let evenkeys = ListToEvenKeys (MakeKeys key) ZeroEvenKeys in
    (IdeaFwd oddkeys evenkeys, IdeaFwd (InverseKeys oddkeys)
    (ReverseKeys evenkeys))
End

Theorem IDEA_CORRECT:
    !key plaintext.
      ((encrypt,decrypt) = IDEA key)
      ==>
       (decrypt (encrypt plaintext) = plaintext)
Proof
 RW_TAC std_ss [IDEA_def,LET_THM,IDEA_LEMMA]
QED

