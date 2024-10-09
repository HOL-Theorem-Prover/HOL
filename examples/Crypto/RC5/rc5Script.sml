(*===========================================================================*)
(*  The Data Encryption Standard (DES) in HOL                                *)
(*===========================================================================*)

open HolKernel Parse boolLib bossLib;

open arithmeticTheory numLib pairTheory fcpTheory fcpLib wordsTheory wordsLib
     listTheory listLib sortingTheory pred_setTheory combinTheory hurdUtils;

val _ = guessing_word_lengths := true;
val _ = new_theory "rc5";

val fcp_ss = std_ss ++ fcpLib.FCP_ss;

(* Data Table *)
Definition P16_data:
    P16_data=0xB7E1w
End

Definition P32_data:
    P32_data=0xB7E15163w
End

Definition P64_data:
    P64_data=0xB7E151628AED2A6Bw
End

Definition Q16_data:
    Q16_data=0x9E37w
End

Definition Q32_data:
    Q32_data=0x9E3779B9w
End

Definition Q64_data:
    Q64_data=0x9E3779B97F4A7C15w
End

(* function *)
Definition Split32_def :
   Split32 (w:word32)= ((31 >< 16)w, (15 >< 0)w)
End

Definition Split64_def :
   Split64 (w:word64)= ((63 >< 32)w, (31 >< 0)w)
End

Definition Split128_def :
   Split128 (w:word128)= ((127 >< 64)w, (63 >< 0)w)
End

Definition Join32_def :
   Join32 (u:word16,v:word16) :word32= u @@ v
End

Definition Join64_def :
   Join64 (u:word32,v:word32) = (u @@ v) :word64
End

Definition Join128_def :
   Join128 (u:word64,v:word64) :word128= u @@ v
End

Theorem Split32_Join32:
    !u v. Split32(Join32(u,v))=(u,v) 
Proof
    rw [Join32_def, Split32_def]
 >- WORD_DECIDE_TAC
 >> WORD_DECIDE_TAC 
QED

Theorem Join32_Split32:
    !w. Join32(Split32 w)=w
Proof
    rw [Join32_def, Split32_def]
 >> WORD_DECIDE_TAC
QED

Theorem Split64_Join64:
    !u v. Split64(Join64(u,v))=(u,v) 
Proof
    rw [Join64_def, Split64_def]
 >- WORD_DECIDE_TAC
 >> WORD_DECIDE_TAC
QED

Theorem Join64_Split64:
    !w. Join64(Split64 w)=w
Proof
    rw [Join64_def, Split64_def]
 >> WORD_DECIDE_TAC
QED

Theorem Split128_Join128:
    !u v. Split128(Join128(u,v))=(u,v) 
Proof
    rw [Join128_def, Split128_def]
 >- WORD_DECIDE_TAC
 >> WORD_DECIDE_TAC
QED

Theorem Join128_Split128:
    !w. Join128(Split128 w)=w
Proof
    rw [Join128_def, Split128_def]
 >> WORD_DECIDE_TAC
QED

(* Key function *)
Definition SkeysT32_def:
   SkeysT32 (l:num) 0=[P32_data]
   /\ SkeysT32 l (SUC t)= let ks=SkeysT32 l t; key=HD ks in 
     (key+Q32_data) :: ks
End

Definition SkeysT64_def:
   SkeysT64 (l:num) 0=[P64_data]
   /\ SkeysT64 l (SUC t)= let ks=SkeysT64 l t; key=HD ks in 
     (key+Q64_data) :: ks
End

Definition SkeysT16_def:
   SkeysT16 (l:num) 0=[P16_data]
   /\ SkeysT16 l (SUC t)= let ks=SkeysT16 l t; key=HD ks in (key+Q16_data) :: ks
End

Definition Skeys_def:
   Skeys (l:num) r= 
     if l=32 then REVERSE (SkeysT32 l (2*(r+1)-1))
     else if l=64 then REVERSE (SkeysT64 l (2*(r+1)-1))
     else REVERSE (SkeysT16 l (2*(r+1)-1))
End

Theorem LENGTH_Skeys:
   !l n. l=32 \/ l=64 \/ l=16 ==> LENGTH(Skeys l n)= 2*(n+1)
Proof
     Q.X_GEN_TAC ‘l’
  >> Induct_on ‘n’
  >- (rw[Skeys_def]\\
      (‘SkeysT32 32 (SUC 0)=(P32_data+Q32_data)::(SkeysT32 32 0)’ by rw[SkeysT32_def]\\
       POP_ASSUM MP_TAC \\
       rw[]\\
       rw[SkeysT32_def])\\
      (‘SkeysT64 64 (SUC 0)=(P64_data+Q64_data)::(SkeysT64 64 0)’ by rw[SkeysT64_def]\\
       POP_ASSUM MP_TAC \\
       rw[]\\
       rw[SkeysT64_def])\\
       ‘SkeysT16 16 (SUC 0)=(P16_data+Q16_data)::(SkeysT16 16 0)’ by rw[SkeysT16_def]\\
       POP_ASSUM MP_TAC \\
       rw[]\\
       rw[SkeysT16_def])
  >> rw[Skeys_def]
  >- (rw[]\\
      Know ‘(2 *(SUC n + 1) − 1)=SUC (SUC (2 * (n + 1) − 1))’
      >-(rw[])\\
      Rewr'\\
      rw[SkeysT32_def])
  >- (rw[]\\
      Know ‘(2 *(SUC n + 1) − 1)=SUC (SUC (2 * (n + 1) − 1))’
      >-(rw[])\\
      Rewr'\\
      rw[SkeysT64_def])
  >> Know ‘(2 *(SUC n + 1) − 1)=SUC (SUC (2 * (n + 1) − 1))’
  >- rw[]
  >> Rewr'
  >> rw[SkeysT16_def]
QED

Definition lenW_def:
   lenW w=
     if word_len w=dimindex(:16) then 16
     else if word_len w=dimindex(:32) then 32
     else if word_len w=dimindex(:64) then 64
     else 128
End

Definition lenKeyw_def:
  lenKeyw k w=(MAX (lenW k) 1) DIV (lenW w)
End

Definition LkeysIni_def:
   LkeysIni 0=[] /\
   LkeysIni (SUC c)= 0x0w ::LkeysIni c
End

Definition keysIni_def:
   keysIni k 0= [w2w ((7 >< 0) k)] /\
   keysIni k (SUC r)=
     let ks=keysIni k r;n=((SUC r)*8) in
       ((n+7) >< n) k :: ks
End

(*u= (lenW w) DIV 8; b=len w DIV 8; c=len k DIV len w*)
Definition LkeysSup_def:
   (LkeysSup c u k 0 b= let ks=LkeysIni c ;keys=keysIni k (b-1) in
     (GENLIST (λm. if (m=(b-1) DIV u) then (((EL m ks) #<< 8)+(EL (b-1) keys)) else EL m ks) c)) /\
   LkeysSup c u k (SUC r) b=
     let ks=LkeysSup c u k r b;i= b-1-(SUC r); (keys=keysIni k i) in
       (GENLIST (λm. if (m=i DIV u) then (((EL m ks) #<< 8)+(EL i keys)) else EL m ks) c)
End

Definition Lkeys_def:
   Lkeys w k= let c=lenKeyw k w; u= (lenW w) DIV 8; r= ((lenW k) DIV 8)-1; b= ((lenW k) DIV 8)-1 in LkeysSup c u k r b
End

Theorem LENGTH_LkeysIni:
   !c. LENGTH(LkeysIni c)=c
Proof
     Induct_on‘c’
  >- rw[LkeysIni_def]
  >> rw[LkeysIni_def]
QED

Theorem LENGTH_LkeysSup:
   !c u k n b. LENGTH(LkeysSup c u k n b)= c 
Proof
     Q.X_GEN_TAC ‘c’
  >> Q.X_GEN_TAC ‘u’
  >> Q.X_GEN_TAC ‘k’
  >> Induct_on ‘n’
  >- (rw[LkeysSup_def]\\
      rw[LENGTH_LkeysIni])
  >> rw[LkeysSup_def]
QED

Theorem LENGTH_Lkeys:
   !w k. c=lenKeyw k w ==> LENGTH(Lkeys w k)= c 
Proof
     rw[lenKeyw_def,Lkeys_def]
  >> rw[LENGTH_LkeysSup]
QED

Definition keys_def:
   (keys 0 r c l k w= let Lk=Lkeys w k;Sk=Skeys l r;A=EL 0 Sk;B=EL 0 Lk in (A,B,Lk,Sk,0,0)) /\
   keys (SUC n) r c l k w=
     let ((A,B,Lk,Sk,i,j)= keys n r c l k w);
         (Anew= (((EL i Sk)+A+B) #<< 3));
         (Bnew=((EL i Lk)+Anew+B) #<< (w2n (Anew+B)));
         (Sknew= GENLIST (λm. if m=i then (((EL i Sk)+A+B) #<< 3) else EL m Sk) (2*(r+1)));
         (Lknew= GENLIST (λm. if m=j then (((EL j Lk)+Anew+B)#<< (w2n (Anew+B))) else (EL m Lk)) (lenKeyw k w));
         (inew= (i+1) MOD (2*(r+1)));
         (jnew= (j+1) MOD c) in 
       (Anew,Bnew,Lknew,Sknew,inew,jnew)
End

Theorem LENGTH_key_Skeys:
   !n r c l k w A B Lk Sk i j. (l=32 \/ l=64 \/ l=16) /\ (A,B,Lk,Sk,i,j)=keys n r c l k w ==> LENGTH(Sk)= 2*(r+1)
Proof
     rpt GEN_TAC
  >> Cases_on ‘n’
  >- (rw[keys_def]
      >> rw[LENGTH_Skeys])
  >> rw[keys_def]
  >> Q.ABBREV_TAC ‘X=(keys n' r c l k w)’
  >> pairarg_tac
  >> fs[]
QED

Theorem LENGTH_key_Lkeys:
   !n r c l k w A B Lk Sk i j. (A,B,Lk,Sk,i,j)=keys n r c l k w ==> LENGTH(Lk)= (lenKeyw k w)
Proof
     rpt GEN_TAC
  >> Cases_on ‘n’
  >- (rw[keys_def]\\
      rw[lenKeyw_def,Lkeys_def]\\
      rw[LENGTH_LkeysSup])
  >> rw[keys_def]
  >> Q.ABBREV_TAC ‘X=(keys n' r c l k w)’
  >> pairarg_tac
  >> fs[]
QED

Definition rc5keys_def:
   rc5keys r k w= let c=lenKeyw k w; n=3* (MAX (2*(r+1)) c); l=lenW w in keys n r c l k w
End

(* Round function and Encryption *)
Definition RoundEn_def:
   (RoundEn 0 w1 w2 ks=
     let k1=EL 0 ks;k2=EL 1 ks in (w1+k1,w2+k2))   /\
   RoundEn (SUC n) w1 w2 ks=
     let ki=EL (2*(SUC n)) ks; ki2=EL (2*(SUC n)+1) ks; E= ((w1 ⊕ w2) #<< (w2n w2))
    in (E+ki,((w2 ⊕ (E+ki))#<<(w2n (E+ki))) +ki2)
End

Definition RoundEn32_def:
   RoundEn32 r w k= let (w1,w2)= Split32(w);(A,B,Lk,Sk,i,j)=(rc5keys r k w) in
      Join32(RoundEn r w1 w2 Sk)
End

Definition RoundEn64_def:
   RoundEn64 r w k= let (w1,w2)= Split64(w);(A,B,Lk,Sk,i,j)=(rc5keys r k w) in
      Join64(RoundEn r w1 w2 Sk)
End

Definition RoundEn128_def:
   RoundEn128 r w k= let (w1,w2)= Split128(w);(A,B,Lk,Sk,i,j)=(rc5keys r k w) in
      Join128(RoundEn r w1 w2 Sk)
End

(* Decryption *)
Definition RoundDe_def :
   (RoundDe 0 r ks w1 w2= (w1,w2))  /\
   RoundDe (SUC n) r ks w1 w2=
     let ki=EL (2*n) (REVERSE(ks)); ki2=EL (2*n+1) (REVERSE(ks)); (w1',w2')= (RoundDe n r ks w1 w2); B=((w2'-ki) #>> w2n w1') ⊕ w1' in
       if SUC n> r then (w1'-ki2,w2'-ki)
       else (((w1'-ki2)#>>w2n B) ⊕ B , B)
End

Definition RoundDe32_def :
    RoundDe32 r w k= let (w1,w2)= Split32(w);(A,B,Lk,Sk,i,j)=(rc5keys r k w) in
       Join32(RoundDe (r+1) r Sk w1 w2)
End

Definition RoundDe64_def :
    RoundDe64 r w k= let (w1,w2)= Split64(w);(A,B,Lk,Sk,i,j)=(rc5keys r k w) in
       Join64(RoundDe (r+1) r Sk w1 w2)
End

Definition RoundDe128_def :
    RoundDe128 r w k= let (w1,w2)= Split128(w);(A,B,Lk,Sk,i,j)=(rc5keys r k w) in
       Join128(RoundDe (r+1) r Sk w1 w2)
End

(*Theorem DES_EnDe:
   !n (w1:word32) (w2:word32) (key:word64) Sk. (A,B,Lk,Sk,i,j)=(rc5keys n key (Join64(w1,w2))) /\ RoundEn n w1 w2 Sk= (w1',w2') /\ Join64(w1',w2')=encryptW /\ RoundDe (SUC n) n Sk  w1' w2'=decryptW ==> Join64(decryptW)= Join64(w1,w2)
Proof
     rw[RoundEn64_def,RoundDe64_def]
  >> Suff ‘(RoundDe (SUC n) n Sk w1' w2')=(w1,w2)’
  >- rw[Join64_def]
  >> Induct_on ‘n’
  >- (rw[RoundDe_def,RoundEn_def,rc5keys_def]
      >- (Suff ‘LENGTH(Sk)=2’
          >- rw[EL_REVERSE]\\
          POP_ASSUM MP_TAC \\
          rw[lenW_def,lenKeyw_def]\\
          rw[LENGTH_key_Skeys] cheat)\\
       Suff ‘LENGTH(Sk)=2’
       >- (rw[]\\
           Know ‘Sk <>[]’ ASM_REWRITE_TAC [GSYM LENGTH_NIL]
           rw[]
           >- cheat\\
           rw[HD_REVERSE]\\
           rw[LAST_EL])\\
       POP_ASSUM MP_TAC \\
       rw[lenW_def,lenKeyw_def]\\
       rw[LENGTH_key_Skeys] cheat)

  >> rw[RoundDe_def,RoundEn_def,rc5keys_def]
     
QED*)

val _ = export_theory();
val _ = html_theory "des_prop";
