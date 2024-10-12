(*===========================================================================*)
(*  The Data Encryption Standard (DES) in HOL                                *)
(*===========================================================================*)

open HolKernel Parse boolLib bossLib;

open arithmeticTheory numLib pairTheory fcpTheory fcpLib wordsTheory wordsLib
     listTheory listLib sortingTheory pred_setTheory combinTheory hurdUtils;

val _ = guessing_word_lengths := true;
val _ = new_theory "rc5";

val fcp_ss = std_ss ++ fcpLib.FCP_ss;
Type    block[pp] = “:word32 # word32”
(* Data Table *)
Definition P32_data:
    P32_data=0xB7E15163w
End

Definition Q32_data:
    Q32_data=0x9E3779B9w
End

(* function *)
Definition Split64_def :
   Split64 (w:word64)= ((63 >< 32)w:word32, (31 >< 0)w:word32)
End

Definition Join64_def :
   Join64 (u:word32,v:word32) = (u @@ v) :word64
End

Definition Join64'_def :
   Join64' (b:block) = let (u,v)=b in u@@v
End

Theorem Split64_Join64:
    !u v. Split64 (Join64(u,v))=(u,v) 
Proof
    rw [Join64_def, Split64_def]
 >- WORD_DECIDE_TAC
 >> WORD_DECIDE_TAC
QED

Theorem Split64_Join64':
    !b. Split64 (Join64'(b))=b 
Proof
    rw [Join64'_def, Split64_def]
 >> pairarg_tac
 >> fs[]
 >> WORD_DECIDE_TAC
QED

Theorem Join64_Split64:
    !w. Join64(Split64 w)=w
Proof
    rw [Join64_def, Split64_def]
 >> WORD_DECIDE_TAC
QED

Theorem Join64'_Split64:
    !w. Join64'(Split64 w)=w
Proof
    rw [Join64'_def, Split64_def]
 >> WORD_DECIDE_TAC
QED

(* Key function *)
Definition SkeysT32_def:
   SkeysT32 (l:num) 0=[P32_data:word32]
   /\ SkeysT32 l (SUC t)= let ks=SkeysT32 l t; key=HD ks in 
     (key+Q32_data) :: ks
End

Definition Skeys_def:
   Skeys r= REVERSE (SkeysT32 32 (2*(r+1)-1))
End

Theorem LENGTH_Skeys:
   !n. LENGTH(Skeys n)= 2*(n+1)
Proof
     Induct_on ‘n’
  >- (rw[Skeys_def]\\
      ‘SkeysT32 32 (SUC 0)=(P32_data+Q32_data)::(SkeysT32 32 0)’ by rw[SkeysT32_def]\\
       POP_ASSUM MP_TAC \\
       rw[]\\
       rw[SkeysT32_def])
       
  >> POP_ASSUM MP_TAC
  >> rw[Skeys_def]
  >> Know ‘(2 *(SUC n + 1) − 1)=SUC (SUC (2 * (n + 1) − 1))’
  >- rw[]
  >> Rewr'
  >> rw[SkeysT32_def]
QED

(* b= (len k) DIV 8*)
Definition lenKinbyt_def:
  lenKinbyt= 8
End

(* u= (len w) DIV 8*)
Definition lenWinbyt_def:
  lenWinbyt= 4
End

(* c= (MAX (len k) 1) DIV (len w)*)
Definition lenKeyw_def:
  lenKeyw= 2
End

Definition LkeysIni_def:
   LkeysIni= [(0x0w:word32);0x0w] 
End

Definition keysIni_def:
   keysIni k=
      [((7 >< 0) k):word32;(15 >< 8) k;(23 >< 16) k;(31 >< 24) k;(39 >< 32) k;(47 >< 40) k;(55 >< 48) k;(63 >< 56) k]
End

Definition LkeysSup_def:
   (LkeysSup k 0= let ks=LkeysIni;keys=(keysIni k) in
     (GENLIST (λm. if (m=7 DIV 4) then (((EL m ks) #<< 8)+(EL 7 keys)) else EL m ks) 2)) /\
   LkeysSup k (SUC r)=
     let ks=LkeysSup k r;(keys=keysIni k); i=7-(SUC r) in
       (GENLIST (λm. if (m=i DIV 4) then (((EL m ks) #<< 8)+(EL i keys)) else EL m ks) 2)
End

Definition Lkeys_def:
   Lkeys (k:word64)= LkeysSup k 7
End

Theorem LENGTH_LkeysSup:
   !k r. LENGTH(LkeysSup k r)= 2 
Proof
     Q.X_GEN_TAC ‘k’
  >> Induct_on ‘r’
  >- (rw[LkeysSup_def])
  >> rw[LkeysSup_def]
QED

Theorem LENGTH_Lkeys:
   !k. LENGTH(Lkeys k)= 2 
Proof
     rw[lenKeyw_def,Lkeys_def]
  >> rw[LENGTH_LkeysSup]
QED

Definition keys_def:
   (keys 0 r k= let Lk=Lkeys k;Sk=Skeys r;A=EL 0 Sk;B=EL 0 Lk in (A,B,Lk,Sk,0,0)) /\
   keys (SUC n) r k=
     let ((A,B,Lk,Sk,i,j)= keys n r k);
         (Anew= (((EL i Sk)+A+B) #<< 3));
         (Bnew=((EL i Lk)+Anew+B) #<< (w2n (Anew+B)));
         (Sknew= GENLIST (λm. if m=i then (((EL i Sk)+A+B) #<< 3) else EL m Sk) (2*(r+1)));
         (Lknew= GENLIST (λm. if m=j then (((EL j Lk)+Anew+B)#<< (w2n (Anew+B))) else (EL m Lk)) 2);
         (inew= (i+1) MOD (2*(r+1)));
         (jnew= (j+1) MOD 2) in 
       (Anew,Bnew,Lknew,Sknew,inew,jnew)
End

Theorem LENGTH_key_Skeys:
   !n r k. (A,B,Lk,Sk,i,j)=keys n r k ==> LENGTH(Sk)= 2*(r+1)
Proof
     rpt GEN_TAC
  >> Cases_on ‘n’
  >- (rw[keys_def]
      >> rw[LENGTH_Skeys])
  >> rw[keys_def]
  >> Q.ABBREV_TAC ‘X=(keys n' r k)’
  >> pairarg_tac
  >> fs[]
QED

Theorem LENGTH_key_Lkeys:
   !n r k. (A,B,Lk,Sk,i,j)=keys n r k ==> LENGTH(Lk)= 2
Proof
     rpt GEN_TAC
  >> Cases_on ‘n’
  >- (rw[keys_def]\\
      rw[Lkeys_def]\\
      rw[LENGTH_LkeysSup])
  >> rw[keys_def]
  >> Q.ABBREV_TAC ‘X=(keys n' r k)’
  >> pairarg_tac
  >> fs[]
QED

Definition rc5keys_def:
   rc5keys r k= let n=3* (MAX (2*(r+1)) 2) in keys n r k
End

(* Round function and Encryption *)
(*Definition RoundEn_def:
   (RoundEn 0 (w1:word32) w2 (ks:word32 list)=
      let s0=EL 0 ks;
          s1=EL 1 ks in
             (w1+s0,w2+s1))   /\
   RoundEn (SUC n) w1 w2 ks=
     let ki=EL (2*(SUC n)) ks; ki2=EL (2*(SUC n)+1) ks; A= ((w1 ⊕ w2) #<< (w2n w2))+ki; B= ((w2 ⊕ (A))#<<(w2n (A))) +ki2
    in (RoundEn n A B ks)
End*)

Definition RoundEn_def:
   (RoundEn 0 (w1:word32) w2 (ks:word32 list)=
      let s0=EL 0 ks;
          s1=EL 1 ks in
             (w1+s0,w2+s1))   /\
   RoundEn (SUC n) w1 w2 ks=
     let (w1',w2')=RoundEn n w1 w2 ks;
         ki=EL (2*(SUC n)) ks;
         ki2=EL (2*(SUC n)+1) ks;
         A= ((w1' ⊕ w2') #<< (w2n w2'))+ki;
         B= ((w2' ⊕ (A))#<<(w2n (A))) +ki2
     in (A,B)
End

Definition RoundEn64_def:
   RoundEn64 r (w:word64) k= let (w1,w2)= Split64(w);(A,B,Lk,Sk,i,j)=(rc5keys r k) in
      Join64'(RoundEn r w1 w2 Sk)
End

Definition half_messageEn_def :
    half_messageEn (w1:word32) w2 ks n =
      let ki=EL n ks;
          ki2=EL n ks in
      if n = 0 then w1+ki
      else if n = 1 then w2+ki2
      else if n MOD 2=1 then
         (((half_messageEn w1 w2 ks (n - 2)) ⊕ (half_messageEn w1 w2 ks (n - 1)))
         #<< (w2n (half_messageEn w1 w2 ks (n - 1))))+ki
      else
         (((half_messageEn w1 w2 ks (n - 2)) ⊕ (half_messageEn w1 w2 ks (n - 1)))
         #<<(w2n (half_messageEn w1 w2 ks (n - 1))))+ki2
End

Theorem RoundEn_alt_half_messageEn:
    !w1 w2 ks n. RoundEn n w1 w2 ks  =
     (half_messageEn w1 w2 ks (2*n), half_messageEn w1 w2 ks (2*n+1))
Proof
     NTAC 3 GEN_TAC
  >> Induct_on ‘n’
  >- (rw[RoundEn_def,Once half_messageEn_def]\\
     rw[Once half_messageEn_def])
  >> rw[RoundEn_def]
  >- (Q.ABBREV_TAC ‘m0 = half_messageEn w1 w2 ks (2*n)’\\
      Q.ABBREV_TAC ‘m1 = half_messageEn w1 w2 ks (2*n+1)’\\
      Know ‘(2 * SUC n)= 2*n+2’
      >- rw[]\\
      Rewr'\\
      rw[Once half_messageEn_def])
  >> Q.ABBREV_TAC ‘m0 = half_messageEn w1 w2 ks (2*n)’
  >> Q.ABBREV_TAC ‘m1 = half_messageEn w1 w2 ks (2*n+1)’
  >> Know ‘(2 * SUC n+1)= 2*n+3’
  >- rw[]
  >> Rewr'
  >> rw[Once half_messageEn_def]
  >> Know ‘EL (2 * SUC n) ks + (m0 ⇆ w2n m1 ⊕ m1 ⇆ w2n m1) =
  half_messageEn w1 w2 ks (2 * SUC n)’
  >- (Know ‘(2 * SUC n)= 2*n+2’
      >- rw[]\\
      Rewr'\\
      rw[Once half_messageEn_def])
  >> Know ‘(2 * SUC n)= 2*n+2’
  >- rw[]
  >> Rewr'
  >> rw[]
QED

Theorem RoundEn64_alt_half_messageEn:
    !w k r. (w1,w2)=Split64(w) /\ (A,B,Lk,Sk,i,j)=(rc5keys r k) ==>       RoundEn64 r (w:word64) k  =
       Join64' (half_messageEn w1 w2 Sk (2*r), half_messageEn w1 w2 Sk (2*r+1))
Proof
     rw[RoundEn64_def,RoundEn_alt_half_messageEn]
  >> pairarg_tac
  >> fs[]
  >> pairarg_tac
  >> fs[]
QED

(* Decryption *)
(*Definition RoundDe_def :
   (RoundDe 0 ks (w1:word32) w2=
      let s1=EL 0 (REVERSE(ks));
          s0=EL 1 (REVERSE(ks)) in
             (w1-s0,w2-s1)) /\
   RoundDe (SUC n) ks w1 w2=
     let ki=EL (2*(SUC n)) (REVERSE(ks));
         ki2=EL (2*(SUC n)+1) (REVERSE(ks));
         B=((w2 -ki) #>> w2n w1) ⊕ w1;
         A= ((w1-ki2) #>>w2n B) ⊕ B in
             (RoundDe n ks A B)
End*)

Definition RoundDe_def :
   (RoundDe 0 ks (w1:word32) w2=
      let s1=EL 0 (REVERSE(ks));
          s0=EL 1 (REVERSE(ks)) in
             (w1-s0,w2-s1)) /\
   RoundDe (SUC n) ks w1 w2=
     let (w1',w2')=RoundDe n ks w1 w2;
         ki=EL (2*(SUC n)) (REVERSE(ks));
         ki2=EL (2*(SUC n)+1) (REVERSE(ks));
         B=((w2' -ki) #>> w2n w1') ⊕ w1';
         A= ((w1'-ki2) #>>w2n B) ⊕ B in
             (A,B)
End

Definition RoundDe64_def :
    RoundDe64 r (w:word64) k= let (w1,w2)= Split64(w);(A,B,Lk,Sk,i,j)=(rc5keys r k) in
       Join64'(RoundDe r Sk w1 w2)
End

Definition half_messageDe_def :
    half_messageDe (w1:word32) w2 ks n =
      let ki=EL n (REVERSE(ks));
          ki2=EL n (REVERSE(ks)) in
      if n = 0 then w2-ki
      else if n = 1 then w1-ki2
      else if n MOD 2=1 then
         (((half_messageDe w1 w2 ks (n - 2)) -ki)
         #>> w2n (half_messageDe w1 w2 ks (n - 1))) ⊕ (half_messageDe w1 w2 ks (n - 1))
         
      else
         (((half_messageDe w1 w2 ks (n - 2))-ki2)
         #>>w2n (half_messageDe w1 w2 ks (n - 1))) ⊕ (half_messageDe w1 w2 ks (n - 1))
End

Theorem RoundDe_alt_half_messageDe:
    !w1 w2 ks n. RoundDe n ks w1 w2 =
     (half_messageDe w1 w2 ks (2*n+1), half_messageDe w1 w2 ks (2*n))
Proof
     NTAC 3 GEN_TAC
  >> Induct_on ‘n’
  >- (rw[RoundDe_def,Once half_messageDe_def]\\
     rw[Once half_messageDe_def])
  >> rw[RoundDe_def]
  >- (Q.ABBREV_TAC ‘m0 = half_messageDe w1 w2 ks (2*n+1)’\\
      Q.ABBREV_TAC ‘m1 = half_messageDe w1 w2 ks (2*n)’\\
      Know ‘(2 * SUC n+1)= 2*n+3’
      >- rw[]\\
      Rewr'\\
      rw[Once half_messageDe_def]\\
      Know ‘m0 ⊕ (m0 + -1w * EL (2 * n + 3) (REVERSE ks)) ⇄
            w2n (m0 ⊕ (m1 + -1w * EL (2 * SUC n) (REVERSE ks))
            ⇄ w2n m0) ⊕(m1 + -1w * EL (2 * SUC n) (REVERSE ks))
            ⇄ w2n m0=
            (m0 + -1w * EL (2 * n + 3) (REVERSE ks)) ⇄
            w2n (m0 ⊕ (m1 + -1w * EL (2 * SUC n) (REVERSE ks))
            ⇄ w2n m0) ⊕m0 ⊕(m1 + -1w * EL (2 * SUC n) (REVERSE ks))
            ⇄ w2n m0’
      >- rw[]\\
      Rewr'\\
      Know ‘(m0 ⊕ (m1 + -1w * EL (2 * SUC n) (REVERSE ks))
             ⇄ w2n m0)= half_messageDe w1 w2 ks (2 * SUC n)’
      >- (Know ‘(2 * SUC n)= 2*n+2’
          >- rw[]\\
          Rewr'\\
          rw[Once half_messageDe_def])\\
      Rewr'\\
      Know ‘(2 * SUC n)= 2*n+2’
      >- rw[]\\
      Rewr'\\
      rw[])
  >> Q.ABBREV_TAC ‘m0 = half_messageDe w1 w2 ks (2*n+1)’
  >> Q.ABBREV_TAC ‘m1 = half_messageDe w1 w2 ks (2*n)’
  >> Know ‘(2 * SUC n)= 2*n+2’
  >- rw[]
  >> Rewr'
  >> rw[Once half_messageDe_def]
QED

Theorem RoundDe64_alt_half_messageDe:
    !w k r. (w1,w2)=Split64(w) /\ (A,B,Lk,Sk,i,j)=(rc5keys r k) ==>       RoundDe64 r (w:word64) k  =
       Join64' (half_messageDe w1 w2 Sk (2*r+1), half_messageDe w1 w2 Sk (2*r))
Proof
     rw[RoundDe64_def,RoundDe_alt_half_messageDe]
  >> pairarg_tac
  >> fs[]
  >> pairarg_tac
  >> fs[]
QED
! w1 w2 Sk r. RoundEn r w1 w2 Sk=(w1',w2') ==> RoundDe r Sk w1' w2'=(w1,w2)
Theorem DES_EnDe:
   !r (w:word64) (k:word64). RoundDe64 r (RoundEn64 r w k) k= w
Proof
     rpt GEN_TAC
  >> rw[RoundEn64_def,RoundDe64_def]
  >> pairarg_tac
  >> fs[]
  >> pairarg_tac
  >> fs[]
  >> pairarg_tac
  >> fs[]
  >> Induct_on ‘r’
  >- (rw[RoundDe_def,RoundEn_def,rc5keys_def]\\
      POP_ASSUM MP_TAC \\
      POP_ASSUM MP_TAC \\
      rw[Split64_Join64']\\
      Know ‘LENGTH(Sk)=2’
      >- (Know ‘2= 2*(0+1)’
          >- rw[]\\
          Rewr'\\
          MATCH_MP_TAC LENGTH_key_Skeys\\
          Q.EXISTS_TAC ‘6’\\
          Q.EXISTS_TAC ‘k’\\
          rw[])\\
          
      rw[EL_REVERSE]\\
      Know ‘Sk <>[]’
      >- (ASM_REWRITE_TAC [GSYM LENGTH_NIL]\\
          rw[])\\
          
      rw[HD_REVERSE]\\
      rw[LAST_EL]\\
      Know ‘(w1',w2')=Split64 w ’
      >- rw[]\\
      Rewr'\\
      rw[Join64'_Split64])
      
   >> POP_ASSUM MP_TAC
   >> rw[Split64_Join64']
   >> POP_ASSUM MP_TAC
   >> POP_ASSUM MP_TAC
   >> POP_ASSUM MP_TAC
   >> rw[RoundDe_alt_half_messageDe,RoundEn_alt_half_messageEn,rc5keys_def]
   >> Q.ABBREV_TAC ‘a=half_messageEn w1' w2' Sk (2 * r)’
   >> Q.ABBREV_TAC ‘b=half_messageEn w1' w2' Sk (2 * r + 1)’
   >> Q.ABBREV_TAC ‘c=half_messageEn w1' w2' Sk (2 * SUC r)’
   >> Q.ABBREV_TAC ‘d=half_messageEn w1' w2' Sk (2 * SUC r + 1)’
   >> Know ‘(2 * SUC r)=(2*r+2)’
   >- rw[]
   >> Rewr'
   >> rw[]
   >- (rw[Once half_messageEn_def]\\
       rw[Once half_messageDe_def])
   
   >> Suff ‘(half_messageDe (half_messageEn w1' w2' Sk
            (2 * SUC r)) (half_messageEn w1' w2' Sk
            (2 * SUC r + 1)) Sk (2 * SUC r + 1),
            half_messageDe (half_messageEn w1' w2' Sk
            (2 * SUC r)) (half_messageEn w1' w2' Sk
            (2 * SUC r + 1)) Sk (2 * SUC r))
            =(w1',w2')’
   >- (Rewr'\\
       Know ‘(w1',w2')=Split64 w’
       >- rw[]\\
       Rewr'\\
       rw[Join64'_Split64])

   
QED

val _ = export_theory();
val _ = html_theory "RC5";
