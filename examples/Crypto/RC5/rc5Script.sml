(*===========================================================================*)
(*  The Data Encryption Standard (DES) in HOL                                *)
(*===========================================================================*)

open HolKernel Parse boolLib bossLib;

open arithmeticTheory numLib pairTheory fcpTheory fcpLib wordsTheory wordsLib
     listTheory listLib sortingTheory pred_setTheory combinTheory hurdUtils;

open desTheory;

val _ = guessing_word_lengths := true;
val _ = new_theory "rc5";

val fcp_ss = std_ss ++ fcpLib.FCP_ss;

(* Data Table *)
Definition P32_data:
    P32_data=0xB7E1w
End

Definition P64_data:
    P64_data=0xB7E15163w
End

Definition P128_data:
    P128_data=0xB7E151628AED2A6Bw
End

Definition Q32_data:
    Q32_data=0x9E37w
End

Definition Q64_data:
    Q64_data=0x9E3779B9w
End

Definition Q128_data:
    Q128_data=0x9E3779B97F4A7C15w
End

(* function *)
Definition Split_def :
    Split w l=
      if l = 32 then ((31 >< 16)w, (15 >< 0)w)
      else if l=64 then ((63 >< 32)w, (31 >< 0)w)
      else ((127 >< 64)w, (63 >< 0)w)
End

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
   /\ SkeysT32 l (SUC t)= let ks=SkeysT32 l t; key=HD ks in (key+Q32_data) :: ks
End

Definition SkeysT64_def:
   SkeysT64 (l:num) 0=[P64_data]
   /\ SkeysT64 l (SUC t)= let ks=SkeysT64 l t; key=HD ks in 
     (key+Q64_data) :: ks
End

Definition SkeysT128_def:
   SkeysT128 (l:num) 0=[P128_data]
   /\ SkeysT128 l (SUC t)= let ks=SkeysT128 l t; key=HD ks in (key+Q128_data) :: ks
End

Definition Skeys_def:
   Skeys (l:num) r= 
   if l=32 then REVERSE (SkeysT32 l (2*(r+1)-1))
   else if l=64 then REVERSE (SkeysT64 l (2*(r+1)-1))
   else REVERSE (SkeysT128 l (2*(r+1)-1))
End

Theorem LENGTH_Skeys:
   !l n. l=32 \/ l=64 \/ l=128 ==> LENGTH(Skeys l n)= 2*(n+1)
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
       ‘SkeysT128 128 (SUC 0)=(P128_data+Q128_data)::(SkeysT128 128 0)’ by rw[SkeysT128_def]\\
       POP_ASSUM MP_TAC \\
       rw[]\\
       rw[SkeysT128_def])
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
  >> rw[SkeysT128_def]
QED

Definition keyslen_def:
   keyslen k=
     if word_len k=dimindex(:16) then 16
     else if word_len k=dimindex(:32) then 32
     else if word_len k=dimindex(:64) then 64
     else 128
End

Definition LkeysSup_def:
   LkeysSup k 0= [(7 >< 0) k] /\
   LkeysSup k (SUC r)=
     let ks=LkeysSup k r;b=keyslen k;n=((SUC r)*8) in
       if n+8<=b then ((n+7>< n) k):: ks
       else ks
End

Definition Lkeys_def:
   Lkeys k= let r= ((keyslen k) DIV 8)-1 in LkeysSup k r
End

Definition keys_Def:
   (keys 0 r c l k= let Lk=Lkeys k;Sk=Skeys l r;A=EL 0 Sk;B=EL 0 Lk in (A,B,Lk,Sk,0,0)) /\
   keys (SUC n) r c l k=
     let ((A,B,Lk,Sk,i,j)= keys n r c l k);
         (Anew= (((EL i Sk)+A+B) #<< 3));
         (Bnew=((EL i Lk)+Anew+B) #<< (w2n (Anew+B)));
         (Sknew= GENLIST (λm. if m=i then (((EL i Sk)+A+B) #<< 3) else EL m Sk) (2*(r+1)));
         (Lknew= GENLIST (λm. if m=j then (((EL j Lk)+Anew+B)#<< (w2n (Anew+B))) else (EL m Lk)) (((keyslen k) DIV 8)-1));
         (inew= (i+1) MOD (2*(r+1)));
         (jnew= (j+1) MOD c) in 
       if ((SUC n) <= 3* (MAX (2*(r+1)) c)) then (Anew,Bnew,Lknew,Sknew,inew,jnew)
       else (A,B,Lk,Sk,i,j)
End

Definition c_def:
  
End

(* Round function and Encryption *)
Definition RoundEn_def :
   (RoundEn 0 (l:num) w=
     let (w1,w2)=(Split w l); ks=(Skeys l 0);k1=EL 0 ks;k2=EL 1 ks in (w1+k1,w2+k2))    /\
   RoundEn (SUC n) l w=
     let ks=(Skeys l (SUC n));ki=EL (2*(SUC n)) ks; ki2=EL (2*(SUC n)+1) ks; (w1,w2)= (RoundEn n l w); E= ((w1 ⊕ w2)#<< (w2n w2))
    in (E+ki,((w2 ⊕ (E+ki))#<<(w2n (E+ki))) +ki2)
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
