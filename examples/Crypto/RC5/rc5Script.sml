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
Definition Split16_def :
   Split16 (w:word16)= ((15 >< 8)w, (7 >< 0)w)
End

Definition Split32_def :
   Split32 (w:word32)= ((31 >< 16)w, (15 >< 0)w)
End

Definition Split64_def :
   Split64 (w:word64)= ((63 >< 32)w, (31 >< 0)w)
End

Definition Join16_def :
   Join16 (u:word8,v:word8) :word16= u @@ v
End

Definition Join32_def :
   Join32 (u:word16,v:word16) :word32= u @@ v
End

Definition Join64_def :
   Join64 (u:word32,v:word32) = (u @@ v) :word64
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

Theorem Split16_Join16:
    !u v. Split16(Join16(u,v))=(u,v) 
Proof
    rw [Join16_def, Split16_def]
 >- WORD_DECIDE_TAC
 >> WORD_DECIDE_TAC
QED

Theorem Join16_Split16:
    !w. Join16(Split16 w)=w
Proof
    rw [Join16_def, Split16_def]
 >> WORD_DECIDE_TAC
QED

(* Key function *)
Definition SkeysT32_def:
   SkeysT32 (l:num) 0=[P32_data]
   /\ SkeysT32 l (SUC t)= let ks=SkeysT32 l t; key=HD ks in (key+Q32_data) :: ks
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
   keysIni k 0=[(7 >< 0) k] /\
   keysIni k (SUC r)=
     let ks=keysIni k r;n=((SUC r)*8) in
       ((n+7 >< n) k):: ks
End

(u= (lenW w) DIV 8; b=len w DIV 8; c=len k DIV len w)
Definition LkeysSup_def:
   LkeysSup c u k 0= LkeysIni c /\
   LkeysSup c u k (SUC r)=
     let ks=LkeysSup c u k r; keys=keysIni k (SUC r) in
       (GENLIST (λm. if (m=(SUC r) DIV u) then (((EL m ks) #<< 8)+(EL (SUC r) keys)) else EL m ks) c)
End

Definition Lkeys_def:
   Lkeys w k= let c=lenKeyw k w; u= (lenW w) DIV 8; r= ((lenW w) DIV 8)-1 in LkeysSup c u k r
End

Definition keys_def:
   (keys 0 r c l k w= let Lk=Lkeys w k;Sk=Skeys l r;A=EL 0 Sk;B=EL 0 Lk in (A,B,Lk,Sk,0,0)) /\
   keys (SUC n) r c l k w=
     let ((A,B,Lk,Sk,i,j)= keys n r c l k w);
         (Anew= (((EL i Sk)+A+B) #<< 3));
         (Bnew=((EL i Lk)+Anew+B) #<< (w2n (Anew+B)));
         (Sknew= GENLIST (λm. if m=i then (((EL i Sk)+A+B) #<< 3) else EL m Sk) (2*(r+1)));
         (Lknew= GENLIST (λm. if m=j then (((EL j Lk)+Anew+B)#<< (w2n (Anew+B))) else (EL m Lk)) (((lenW k) DIV 8)-1));
         (inew= (i+1) MOD (2*(r+1)));
         (jnew= (j+1) MOD c) in 
       if ((SUC n) <= 3* (MAX (2*(r+1)) c)) then (Anew,Bnew,Lknew,Sknew,inew,jnew)
       else (A,B,Lk,Sk,i,j)
End

Definition rc5keys_def:
   rc5keys r c l k w= keys r r c l k w
End


(* Round function and Encryption *)
Definition RoundEn_def:
   (RoundEn 0 w1 w2 ks=
     let k1=EL 0 ks;k2=EL 1 ks in (w1+k1,w2+k2))   /\
   RoundEn (SUC n) w1 w2 ks=
     let ki=EL (2*(SUC n)) ks; ki2=EL (2*(SUC n)+1) ks; E= ((w1 ⊕ w2) #<< (w2n w2))
    in (E+ki,((w2 ⊕ (E+ki))#<<(w2n (E+ki))) +ki2)
End

Definition RoundEn'_def:
   RoundEn' r w1 w2 k=let w= Join32(w1,w2);(c=lenKeyw k w); (A,B,Lk,Sk,i,j)=(rc5keys r c (lenW w) k w)
     in RoundEn r w1 w2 Sk
End

Definition RoundEn32_def:
   RoundEn32 r w ks= let (w1,w2)= Split32(w) in
      RoundEn r w1 w2 ks
End

Definition RoundEn64_def:
   RoundEn64 r w ks= let (w1,w2)= Split64(w) in
      RoundEn r w1 w2 ks
End

Definition RoundEn128_def:
   RoundEn128 r w ks= let (w1,w2)= Split128(w) in
      RoundEn r w1 w2 ks
End

Definition rc5Encry_def:
   rc5Encry r w k=
      if lenW w= 32 then
         let (c=lenKeyw k w);((A,B,Lk,Sk,i,j)= (rc5keys r c 32 k w)) in
             RoundEn32 r w Sk
      else if lenW w= 64 then
         let (c=lenKeyw k w);((A,B,Lk,Sk,i,j)= (rc5keys r c 64 k w)) in
             RoundEn64 r w Sk
      else let (c=lenKeyw k w);((A,B,Lk,Sk,i,j)= (rc5keys r c 128 k w)) in RoundEn128 r w Sk
End

Definition rc5Encry_def:
   rc5Encry r w k=
      if lenW w= 32 then (RoundEn32 r w k)
      else if lenW w= 64 then (RoundEn64 r w k)
      else (RoundEn128 r w k)
End

(* Decryption *)
Definition RoundDe_def :
   (RoundDe 0 r ks l w=
     let (w1,w2)=(Split w l)in (w1,w2))   /\
   RoundDe (SUC n) r ks l w=
     let ki=EL (2*(SUC n)) (REVERSE(ks)); ki2=EL (2*(SUC n)+1) (REVERSE(ks)); (w1,w2)= (RoundDe n r ks l w); B=((w2-ki) #>> w2n w1) ⊕ w1 in
       if SUC n> r then (w1-ki2,w2-ki)
       else (((w1-ki2)#>>w2n B) ⊕ B , B)
End

Definition desRoundDe_def :
    desRoundDe n ks l w= RoundDe (n+1) n ks l w
End

Definition DES_def :
   DES n key l w= let keys = Skeys l r in
     if l=32 then (Join32(RoundEn n ks l w), Join32(desRoundDe n ks l w))
     else if l=64 then (Join64(RoundEn n ks l w), Join64(desRoundDe n ks l w))
     else (Join128(RoundEn n ks l w), Join128(desRoundDe n ks l w))
End

Theorem DES_En0:
   !key l w. DES 0 key l w=(encrypt,decrypt) /\ Split w=(w1,w2) /\ k1=EL 0 ks; k2=EL 1 ks ==> encrypt= (w1+k1,w2+k2)
Proof

QED
val _ = export_theory();
val _ = html_theory "des_prop";
