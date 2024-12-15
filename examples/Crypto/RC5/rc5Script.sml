(*===========================================================================*)
(*  The RC5 in HOL                                *)
(*===========================================================================*)

open HolKernel Parse boolLib bossLib;

open arithmeticTheory numLib pairTheory fcpTheory fcpLib wordsTheory wordsLib
     listTheory listLib sortingTheory pred_setTheory combinTheory hurdUtils;


val _ = new_theory "rc5";
val _ = guessing_word_lengths := true;
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
   (keys 0 r k= let Lk=Lkeys k;Sk=Skeys r;A=0x0w;B=0x0w in (A,B,Lk,Sk,0,0)) /\
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
Definition RoundEn_def:
   (RoundEn 0 (w1:word32) w2 (ks:word32 list)=
     let s0=EL 0 ks;
         s1=EL 1 ks in
        (w1,w2))   /\
   RoundEn (SUC n) w1 w2 ks=
     let (w1',w2')=RoundEn n w1 w2 ks;
         ki=EL (2*(SUC n)) ks;
         ki2=EL (2*(SUC n)+1) ks;
         A= ((w1' ⊕ w2') #<< (w2n w2'))+ki;
         B= ((w2' ⊕ (A))#<<(w2n (A))) +ki2
     in (A,B)
End

Definition half_messageEn_def :
    half_messageEn (w1:word32) w2 ks n =
      let ki=EL n ks;
          ki2=EL (n-1) ks in
      if n = 0 then w1
      else if n = 1 then w2
      else
         (((half_messageEn w1 w2 ks (n - 2)) ⊕ (half_messageEn w1 w2 ks (n - 1)))
         #<<(w2n (half_messageEn w1 w2 ks (n - 1))))+ki
End

Definition RoundEn64_def:
   RoundEn64 n (w:word64) k=
      let (w1,w2)= Split64(w);
          (A,B,Lk,Sk,i,j)=(rc5keys n k);
          k0=EL 0 Sk;
          k1=EL 1 Sk in
      Join64' (RoundEn n (w1+k0) (w2+k1) Sk)
End

Theorem RoundEn_alt_half_messageEn:
    !w1 w2 ks n. RoundEn n w1 w2 ks=
    (half_messageEn w1 w2 ks (2*n), half_messageEn w1 w2 ks (2*n+1))
Proof
     rw[]
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
    !w k r. (w1,w2)=Split64(w) /\ (A,B,Lk,Sk,i,j)=(rc5keys r k)/\
             k0=EL 0 Sk /\ k1=EL 1 Sk ==>
             RoundEn64 r (w:word64) k  =
             Join64' ((half_messageEn (w1+k0) (w2+k1) Sk (2*r)), (half_messageEn (w1+k0) (w2+k1) Sk (2*r+1)))
Proof
     rw[RoundEn64_def,RoundEn_alt_half_messageEn]
  >> pairarg_tac
  >> fs[]
  >> pairarg_tac
  >> fs[]
QED

(* Decryption *)
Definition RoundDe_def :
   (RoundDe 0 ks ((w1:word32),w2)=
      let s1=EL 1 ks;
          s0=EL 0 ks in
             (w1,w2)) /\
   RoundDe (SUC n) ks (w1,w2)=
     let (w1',w2')=RoundDe n ks (w1, w2);
         ki=EL (2*(SUC n)-2) (REVERSE(ks));
         ki2=EL (2*(SUC n)-1) (REVERSE(ks));
         B=((w2' -ki) #>> w2n w1') ⊕ w1';
         A= ((w1'-ki2) #>>w2n B) ⊕ B in
             (A,B)
End

Definition half_messageDe_def :
    half_messageDe (w1:word32) w2 ks n =
      let ki=EL (n-2) (REVERSE(ks));
          ki2=EL (n-2) (REVERSE(ks)) in
      if n = 0 then w2
      else if n = 1 then w1
      else
         (((half_messageDe w1 w2 ks (n - 2)) -ki)
         #>> w2n (half_messageDe w1 w2 ks (n - 1))) ⊕ (half_messageDe w1 w2 ks (n - 1))
End

Definition RoundDe64_def :
    RoundDe64 n (w:word64) k=
      let (w1,w2)= Split64(w);
          (A,B,Lk,Sk,i,j)=(rc5keys n k);
          (w1',w2')= RoundDe n Sk (w1,w2);
          k0= EL 0 Sk;
          k1= EL 1 Sk in
       Join64'(w1'-k0,w2'-k1)
End

Theorem RoundDe_alt_half_messageDe:
    !w1 w2 ks n. RoundDe n ks (w1, w2) =
     (half_messageDe w1 w2 ks (2*n+1), half_messageDe w1 w2 ks (2*n))
Proof
     NTAC 3 GEN_TAC
  >> Induct_on ‘n’
  >- (rw[RoundDe_def,Once half_messageDe_def]\\
     rw[Once half_messageDe_def])
  >> rw[RoundDe_def]
  >- (Q.ABBREV_TAC ‘m0 = half_messageDe w1 w2 ks (2*n+1)’\\
      Q.ABBREV_TAC ‘m1 = half_messageDe w1 w2 ks (2*n)’\\
      Know ‘(2 * SUC n)= 2*n+2’
      >- rw[]\\
      Rewr'\\
      rw[]\\
      rw[Once half_messageDe_def]\\
      Know ‘m0 ⊕ (m0 + -1w * EL (2 * n +1) (REVERSE ks)) ⇄
            w2n (m0 ⊕ (m1 + -1w * EL (2 * n) (REVERSE ks))
            ⇄ w2n m0) ⊕(m1 + -1w * EL (2 * n) (REVERSE ks))
            ⇄ w2n m0=
            (m0 + -1w * EL (2 * n+1) (REVERSE ks)) ⇄
            w2n (m0 ⊕ (m1 + -1w * EL (2 * n) (REVERSE ks))
            ⇄ w2n m0) ⊕m0 ⊕(m1 + -1w * EL (2 * n) (REVERSE ks))
            ⇄ w2n m0’
      >- rw[]\\
      Rewr'\\
      Know ‘(m0 ⊕ (m1 + -1w * EL (2 * n) (REVERSE ks))
             ⇄ w2n m0)= half_messageDe w1 w2 ks (2 * n + 2)’
      >- (rw[Once half_messageDe_def])\\
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
    !w k r. (w1,w2)=Split64(w) /\ (A,B,Lk,Sk,i,j)=(rc5keys r k)/\
              k0=EL 0 Sk /\ k1=EL 1 Sk ==>
             RoundDe64 r (w:word64) k  =
             Join64' ((half_messageDe w1 w2 Sk (2*r+1))-k0, (half_messageDe w1 w2 Sk (2*r))-k1)
Proof
     rw[RoundDe64_def,RoundDe_alt_half_messageDe]
  >> pairarg_tac
  >> fs[]
  >> pairarg_tac
  >> fs[]
  >> rw[]
QED

(*Theorem RC5_EnDe:
   !n (w:word64) (k:word64) w1 w2 A B Lk Sk i j. Split64(w)=(w1,w2)/\ rc5keys n k = (A,B,Lk,Sk,i,j) ==>
   RoundDe64 n (RoundEn64 n w k) k= w
Proof

     simp[rc5keys_def]
  >> Induct_on ‘n’
  >- (rw[RoundEn64_def,RoundDe64_def]\\
      pairarg_tac\\
      fs[]\\
      pairarg_tac\\
      fs[]\\
      POP_ASSUM MP_TAC \\
      POP_ASSUM MP_TAC \\
      rw[Split64_Join64',RoundDe_def,RoundEn_def,rc5keys_def]\\
      rw[]\\
      Know ‘(w1,w2)=Split64 w ’
      >- rw[]\\
      Rewr'\\
      rw[Join64'_Split64]) cheat
   >> Suff ‘(half_messageDe (half_messageEn w1 w2 Sk (2 * SUC n))
             (half_messageEn w1 w2 Sk (2 * SUC n + 1)) Sk (2 * SUC n + 1),
           half_messageDe (half_messageEn w1 w2 Sk (2 * SUC n))
             (half_messageEn w1 w2 Sk (2 * SUC n + 1)) Sk (2 * SUC n))=(w1,w2)’

   >> Q.PAT_X_ASSUM ‘!w k w1 w2 A B Lk Sk i j. P’ (MP_TAC o Q.SPECL [‘w’,‘k’,‘w1’,‘w2’])
   >> DISCH_THEN (MP_TAC o Q.SPECL [])
   >> POP_ASSUM MP_TAC
   >> fs[RoundEn64_def,RoundDe64_def]
   >> POP_ASSUM MP_TAC
   >> POP_ASSUM MP_TAC
   >> fs[RoundDe_alt_half_messageDe,RoundEn_alt_half_messageEn]
   >> Know ‘(half_messageDe (half_messageEn w1 w2 Sk (2 * SUC n))
             (half_messageEn w1 w2 Sk (2 * SUC n + 1)) Sk (2 * SUC n + 1)= ’
   >> pairarg_tac
   >> fs[]
   >> pairarg_tac
   >> fs[]
   >> pairarg_tac
   >> fs[]
   >> POP_ASSUM MP_TAC
   >> POP_ASSUM MP_TAC
   >> POP_ASSUM MP_TAC
   >> POP_ASSUM MP_TAC
   >> POP_ASSUM MP_TAC
   >> rw[Split64_Join64',rc5keys_def]
   >> Know ‘(2 * SUC r)=(2*r+2)’
   >- rw[]
   >> Rewr'
   >> Suff ‘(half_messageDe (half_messageEn w1 w2 Sk (2 * r + 2))
             (half_messageEn w1 w2 Sk (2 * r + 2 + 1)) Sk (2 * r + 2
             + 1),
             half_messageDe (half_messageEn w1 w2 Sk (2 * r + 2))
             (half_messageEn w1 w2 Sk (2 * r + 2 + 1)) Sk (2 * r + 2)
             )= (w1,w2)’
   >- rw[]
   >> rw[]

   >- (rw[Once half_messageDe_def]\\
       Q.ABBREV_TAC ‘a=half_messageEn w1 w2 Sk (2 * r +2)’\\
       Q.ABBREV_TAC ‘b=half_messageEn w1 w2 Sk (2 * r + 3)’\\
       Know ‘half_messageDe a b Sk (2 * r + 2)=
             a’)
   >> rw[]

   >> rw[]
   >- (Q.ABBREV_TAC ‘a=(half_messageDe w1' w2' Sk (2 * r + 1))’\\
       Q.ABBREV_TAC ‘b=(half_messageDe w1' w2' Sk (2 * r))’\\
       Know ‘(half_messageEn a b Sk (2 * r + 2))=
             (((half_messageEn a b Sk (2 * r)) ⊕
             (half_messageEn a b Sk (2 * r + 1)))
             #<<(w2n (half_messageEn a b Sk (2 * r + 1))))+EL (2 * r + 2
             ) Sk’

       >- rw[Once half_messageEn_def]\\
       Rewr'\\
       Know ‘(half_messageEn a b Sk (2 * r + 3)) =
             (((half_messageEn a b Sk (2* r + 1))
             ⊕ (half_messageEn a b Sk (2* r +2)))
             #<< (w2n (half_messageEn a b Sk (2 * r + 2))))+EL (2 * r +
             3) Sk’
       >- rw[Once half_messageEn_def]\\
       Rewr'\\
       Know ‘half_messageEn a b Sk (2 * r) = w1'’
       >- rw[]\\
       Rewr'
       Know ‘half_messageEn a b Sk (2 * r + 1) = w2'’
       >- rw[]\\
       Rewr'\\
       Q.ABBREV_TAC ‘c=half_messageEn a b Sk (2 * r + 2)’\\
       Know ‘half_messageDe ((w1' ⊕ w2') ⇆ w2n w2' + EL (2 * r + 2) Sk)
             ((w2' ⊕ c) ⇆ w2n c + EL (2 * r + 3) Sk) Sk (2 * r + 2)=
             ’

Q.ABBREV_TAC ‘d=(EL (2 * r + 2) Sk +
           (half_messageEn a b Sk (2 * r) ⇆
            w2n (half_messageEn a b Sk (2 * r + 1)) ⊕
            half_messageEn a b Sk (2 * r + 1) ⇆
            w2n (half_messageEn a b Sk (2 * r + 1))))’
     Q.ABBREV_TAC ‘e=(EL (2 * r + 3) Sk +
            (half_messageEn a b Sk (2 * r + 1) ⇆
             w2n (half_messageEn a b Sk (2 * r + 2)) ⊕
             half_messageEn a b Sk (2 * r + 2) ⇆
             w2n (half_messageEn a b Sk (2 * r + 2))))’
cheat
             )

  Q.ABBREV_TAC ‘a=
              (EL (2 * n + 2) Sk +
               (half_messageEn w1 w2 Sk (2 * n) ⇆
                w2n (half_messageEn w1 w2 Sk (2 * n + 1)) ⊕
                half_messageEn w1 w2 Sk (2 * n + 1) ⇆
                w2n (half_messageEn w1 w2 Sk (2 * n + 1))))’
  Q.ABBREV_TAC ‘a= 2*r’
  rw[Once half_messageEn_def]
  rw[Once half_messageEn_def]
  rw[Once half_messageEn_def]
  rw[Once half_messageEn_def]
  rw[Once half_messageDe_def]
  rw[Once half_messageDe_def]
  Know ‘(w1,w2)=Split64 w’
  rw[]
  Rewr'
  rw[Join64'_Split64]

QED*)

Definition RoundEnSg_def:
   RoundEnSg (b) ki ki2=
     let (w1,w2)=b;
         A= ((w1 ⊕ w2) #<< (w2n w2))+ki;
         B= ((w2 ⊕ (A))#<< (w2n (A))) +ki2
     in (A,B)
End

Definition RoundDeSg_def :
   RoundDeSg (b) ki ki2=
     let (w1,w2)=b;
         B=((w2 -ki2) #>> w2n w1) ⊕ w1;
         A= ((w1-ki) #>>w2n B) ⊕ B in
             (A,B)
End

Theorem RoundDe_EnSg:
    !b ki ki2.
       RoundDeSg (RoundEnSg (b) ki ki2) ki ki2=(b)
Proof
     rw[]
  >> rw[RoundEnSg_def,RoundDeSg_def]
  >> pairarg_tac
  >> fs[]
  >> pairarg_tac
  >> fs[]
  >> rw[]
QED

Definition RoundEn'_def:
   (RoundEn' 0 ki ki2 (b)= (b))
   /\
   RoundEn' (SUC n) ki ki2 (b)=
     let (b')= RoundEn' n ki ki2 (b);
     in (RoundEnSg (b') ki ki2)
End

Definition RoundDe'_def :
   (RoundDe' 0 ki ki2 (b:block)= (b))
   /\
   RoundDe' (SUC n) ki ki2 (b)=
     let (b')= RoundDe' n ki ki2 (b)
     in (RoundDeSg (b') ki ki2)
End

Theorem RoundDe'_comm:
    !n b ks ki ki2. RoundDeSg (RoundDe' n ki ki2 (b)) ki ki2
        = RoundDe' n ki ki2 (RoundDeSg b ki ki2)
Proof
     rw[]
  >> Induct_on ‘n’
  >- rw[RoundDe'_def,RoundDeSg_def]

  >> rw[RoundDe'_def,RoundDeSg_def]
QED

Theorem RoundEn'_comm:
    !n b ks ki ki2. RoundEnSg (RoundEn' n ki ki2 (b)) ki ki2
        = RoundEn' n ki ki2 (RoundEnSg b ki ki2)
Proof
     rw[]
  >> Induct_on ‘n’
  >- rw[RoundEn'_def,RoundEnSg_def]

  >> rw[RoundEn'_def,RoundEnSg_def]
QED

Theorem RoundEn'_De':
   !n b ki ki2. RoundDe' n ki ki2 (RoundEn' n ki ki2 (b))= (b)
Proof
     rw[]
  >> Induct_on ‘n’
  >- rw[RoundDe'_def,RoundEn'_def]

  >> rw[RoundEn'_def]
  >> rw[RoundDe'_def]
  >> Know ‘RoundDeSg (RoundDe' n ki ki2 (RoundEnSg (RoundEn' n ki ki2
           b) ki ki2)) ki ki2 =
           RoundDe' n ki ki2 (RoundDeSg (RoundEnSg (RoundEn' n ki ki2
           b) ki ki2) ki ki2)’
  >- rw[RoundDe'_comm]
  >> Rewr'
  >> Know ‘RoundDeSg (RoundEnSg (RoundEn' n ki ki2 b) ki ki2) ki ki2
           = (RoundEn' n ki ki2 b)’
  >- rw[RoundDe_EnSg]
  >> Rewr'
  >> rw[]
QED

(* TEST *)
Theorem Skeys_l32_r1 :
    (Skeys 1):word32 list= [0xB7E15163w;0x15618CB1Cw;0x1F45044D5w;0x29287BE8Ew]
Proof
    EVAL_TAC
QED

Theorem half_messageTest1:
    half_messageDe
       (half_messageEn 0x3w 0x2w [0x2w;0x1w;0x3w;0x1w] (2*1))
       (half_messageEn 0x3w 0x2w [0x2w;0x1w;0x3w;0x1w] (2*1+1))
       [0x2w;0x1w;0x3w;0x1w] (2*1) = 0x2w
Proof
    EVAL_TAC
QED

Theorem half_messageTest2:
    half_messageDe
        (half_messageEn 0x3w 0x2w [0x2w;0x1w] (1))
        (half_messageEn 0x3w 0x2w [0x2w;0x1w] (1+1))
        [0x2w;0x1w] (1) = 0x2w
Proof
    EVAL_TAC
QED

Theorem RoundEn_De_Test:
    RoundDe 1 [0x2w;0x1w;0x3w;0x1w]
       (RoundEn 1 0x3w 0x2w [0x2w;0x1w;0x3w;0x1w])= (0x3w,0x2w)
Proof
    EVAL_TAC
QED

val _ = export_theory();
val _ = html_theory "rc5";
