(*===========================================================================*)
(*  The Data Encryption Standard (DES) Property in HOL                       *)
(*                                                                           *)
(*  Author: Ruofan Yang                                                      *)
(*===========================================================================*)

open HolKernel Parse boolLib bossLib;

open arithmeticTheory numLib pairTheory fcpTheory fcpLib wordsTheory wordsLib
     listTheory listLib sortingTheory pred_setTheory combinTheory hurdUtils;

open desTheory;

val _ = guessing_word_lengths := true;
val _ = new_theory "des_prop";

val fcp_ss = std_ss ++ fcpLib.FCP_ss;

Theorem compl_IIP:
  !m. IIP(~m) = ~ (IIP m)
Proof
    RW_TAC fcp_ss[IIP_def, bitwise_perm_def,dimindex_64]
  >>Q.ABBREV_TAC ‘p=(64 − EL (63 − i) IIP_data)’
  >>Know ‘p<64’
  >- (fs [Abbr ‘p’, dimindex_64] \\
      POP_ASSUM MP_TAC \\
      Q.SPEC_TAC (‘i’, ‘n’) \\
      rpt (CONV_TAC (BOUNDED_FORALL_CONV (SIMP_CONV list_ss [IIP_data]))) \\
      REWRITE_TAC [])
  >>rw[word_1comp_def]
  >>rw[FCP_BETA]
QED

Theorem compl_E:
  ∀m. E (¬m)=~ (E m)
Proof
    RW_TAC fcp_ss[E_def, bitwise_perm_def,dimindex_64]
  >>Know ‘ (dimindex (:32) − EL (dimindex (:48) − 1 − i) E_data)<32’
  >- (fs [dimindex_48] \\
      POP_ASSUM MP_TAC \\
      Q.SPEC_TAC (‘i’, ‘n’) \\
      rpt (CONV_TAC (BOUNDED_FORALL_CONV (SIMP_CONV list_ss [E_data]))) \\
      REWRITE_TAC [])
  >>rw[word_1comp_def]
  >>rw[FCP_BETA]
QED

Theorem compl_IP:
  ∀m. IP (¬m)=~ (IP m)
Proof
    RW_TAC fcp_ss[IP_def,bitwise_perm_def, dimindex_64]
  >>Know ‘(64 − EL (63 − i) IP_data)<64’
  >- (fs [dimindex_64] \\
      POP_ASSUM MP_TAC \\
      Q.SPEC_TAC (‘i’, ‘n’) \\
      rpt (CONV_TAC (BOUNDED_FORALL_CONV (SIMP_CONV list_ss [IP_data]))) \\
      REWRITE_TAC [])
  >>rw[word_1comp_def]
  >>rw[FCP_BETA]
QED

Theorem compl_join:
  !m n. Join (~m,~n) = ~Join (m,n)
Proof
     RW_TAC fcp_ss[Join_def]
  >> rw[word_concat_def,word_join_def]
  >> rw[w2w,word_1comp_def,word_or_def,FCP_BETA,word_lsl_def]
  >> POP_ASSUM MP_TAC
  >> fs[dimindex_64]
  >> rw[FCP_BETA]
  >> rw[w2w]
  >> Cases_on ‘i<32’
  >- rw[FCP_BETA]
  >> rw[FCP_BETA]
QED

Theorem compl_extract_1:
  !(m:word64). ((63 >< 32) ~m):word32 = ~(63 >< 32) m
Proof
     RW_TAC fcp_ss[word_extract_def]
  >> rw[word_bits_def]
  >> rw[w2w,word_1comp_def,FCP_BETA]
  >> POP_ASSUM MP_TAC
  >> fs[dimindex_32]
  >> rw[FCP_BETA]
QED

Theorem compl_extract_2:
  !(m:word64). ((31 >< 0) ~m):word32 = ~(31 >< 0) m
Proof
     RW_TAC fcp_ss[word_extract_def]
  >> rw[word_bits_def]
  >> rw[w2w,word_1comp_def,FCP_BETA]
  >> POP_ASSUM MP_TAC
  >> fs[dimindex_32]
  >> rw[FCP_BETA]
QED

Definition roundk_L:
    RK_L 0 (k:word64) = FST(PC1 k) /\
    RK_L (SUC n) (k :word64) =
      let c = RK_L n k; r= EL n R_data
      in (c #<< r)
End

Definition roundk_R:
    RK_R 0 (k:word64) = SND(PC1 k) /\
    RK_R (SUC n) (k :word64) =
      let c = RK_R n k; r= EL n R_data
      in (c #<< r)
End

Definition roundk_supp:
    RK n (k:word64) = (RK_L n k,RK_R n k)
End

Theorem compl_RK_L:
  !n (k:word64). 17 > n ==>(RK_L n ~k)=~(RK_L n k)
Proof
    rw[]
  >> Induct_on `n`
  >- (rw[]\\
     rw[roundk_L]\\
     rw[PC1_def]\\
     rw[bitwise_perm_def]\\
     RW_TAC fcp_ss[word_extract_def]\\
     rw[word_bits_def]\\
     rw[w2w,word_1comp_def,FCP_BETA]\\
     POP_ASSUM MP_TAC\\
     fs[dimindex_28]\\
     rw[word_1comp_def,FCP_BETA]\\
     Suff ‘(64 − EL (27 − i) PC1_data)<64’
     >-rw[word_1comp_def,FCP_BETA] \\
     fs [dimindex_64] \\
     POP_ASSUM MP_TAC \\
     Q.SPEC_TAC (‘i’, ‘n’) \\
     rpt (CONV_TAC (BOUNDED_FORALL_CONV (SIMP_CONV list_ss [PC1_data]))) \\
     REWRITE_TAC [])
  >> rw[roundk_L]
  >> Q.ABBREV_TAC`a=RK_L n k`
  >> Q.ABBREV_TAC`b=EL n R_data `
  >> rw[word_rol_def]
  >> RW_TAC fcp_ss[word_ror_def]
  >> Suff ‘((i + (28 − b MOD 28)) MOD dimindex (:28))<64’
  >- (rw[word_1comp_def]\\
      rw[FCP_BETA])
  >> fs [dimindex_64]
  >> rw[Abbr `b`]
  >> qabbrev_tac ‘m = (i + (28 − EL n R_data MOD 28))’
  >> MATCH_MP_TAC LESS_TRANS
  >> Q.EXISTS_TAC ‘28’
  >> rw[MOD_LESS]
QED

Theorem compl_RK_R :
   !n (k:word64). 17 > n ==>(RK_R n ~k)=~(RK_R n k)
Proof
     rw[]
  >> Induct_on `n`
  >- (rw[]\\
     rw[roundk_R]\\
     rw[PC1_def]\\
     rw[bitwise_perm_def]\\
     RW_TAC fcp_ss[word_extract_def]\\
     rw[word_bits_def]\\
     rw[w2w,word_1comp_def,FCP_BETA]\\
     POP_ASSUM MP_TAC\\
     fs[dimindex_28]\\
     rw[word_1comp_def,FCP_BETA]\\
     Suff ‘(64 − EL (55 − i) PC1_data)<64’
     >- rw[word_1comp_def,FCP_BETA] \\
     fs [dimindex_64] \\
     POP_ASSUM MP_TAC \\
     Q.SPEC_TAC (‘i’, ‘n’) \\
     rpt (CONV_TAC (BOUNDED_FORALL_CONV (SIMP_CONV list_ss [PC1_data]))) \\
     REWRITE_TAC [])
  >> rw[roundk_R]
  >> Q.ABBREV_TAC`a=RK_R n k`
  >> Q.ABBREV_TAC`b=EL n R_data `
  >> rw[word_rol_def]
  >> RW_TAC fcp_ss[word_ror_def]
  >> Suff ‘((i + (28 − b MOD 28)) MOD dimindex (:28))<64’
  >- (rw[word_1comp_def]\\
      rw[FCP_BETA])
  >> fs [dimindex_64]
  >> rw[Abbr `b`]
  >> qabbrev_tac ‘m = (i + (28 − EL n R_data MOD 28))’
  >> MATCH_MP_TAC LESS_TRANS
  >> Q.EXISTS_TAC ‘28’
  >> rw[MOD_LESS]
QED

Theorem convert_RK:
  !(k:word64) n. RoundKey n k
  =REVERSE (GENLIST (λi. RK i k) (SUC n))
Proof
    Induct_on `n`
  >- (RW_TAC fcp_ss[RoundKey_def,GENLIST,roundk_supp,REVERSE_DEF,roundk_R,roundk_L]\\
      rw[])
  >> RW_TAC fcp_ss[RoundKey_def,GENLIST,roundk_supp,REVERSE_DEF,roundk_R,roundk_L]
  >> Suff `HD ks = (c',c)`
  >- (rw []\\
      rw[Abbr `ks`])
  >> rw[Abbr `ks`]
  >- (Q.PAT_X_ASSUM ‘HD (REVERSE (SNOC (c',c) (GENLIST (λi. (RK_L i k,RK_R i k)) n))) = _’ MP_TAC \\
      rw[HD_REVERSE])
  >> Q.PAT_X_ASSUM ‘HD (REVERSE (SNOC (c',c) (GENLIST (λi. (RK_L i k,RK_R i k)) n))) = _’ MP_TAC
  >> rw[HD_REVERSE]
QED

Theorem comple_PC2:
  ∀(a:word28) (b:word28). PC2 (~a,~b) = ~PC2(a,b)
Proof
     rw[PC2_def]
  >> RW_TAC fcp_ss[bitwise_perm_def]
  >> Suff ` a @@ b = ~(~a @@ ~b)`
  >- (rw[]\\
      Know `(56 − EL (47 − i) PC2_data)<56`
      >- (fs [dimindex_56] \\
      POP_ASSUM MP_TAC \\
      POP_ASSUM MP_TAC \\
      Q.SPEC_TAC (‘i’, ‘n’) \\
      rpt (CONV_TAC (BOUNDED_FORALL_CONV (SIMP_CONV list_ss [PC2_data]))) \\
      REWRITE_TAC []) \\
      rw[word_1comp_def]\\
      rw[FCP_BETA])
   >> RW_TAC fcp_ss[]
   >> rw[word_concat_def,word_join_def]
   >> rw[w2w,word_1comp_def,word_or_def,FCP_BETA,word_lsl_def]
   >> POP_ASSUM MP_TAC
   >> POP_ASSUM MP_TAC
   >> fs[dimindex_48]
   >> rw[FCP_BETA]
   >> rw[w2w]
   >> Cases_on ‘i'<28’
   >- rw[FCP_BETA]
   >> rw[FCP_BETA]
QED

Overload M[local] = “half_message RoundOp”
Theorem comple_property:
  ∀k m n.0 < n /\ n< 17 /\ (DES n k=(encrypt,decrypt)) /\(DES n (~k) = (encrypt',decrypt'))
    ==>  ~(encrypt m)= (encrypt') (~ m)
Proof
     RW_TAC fcp_ss[DES_def,o_DEF, desCore_def, desRound_alt_Round']
  >> POP_ASSUM MP_TAC
  >> POP_ASSUM MP_TAC
  >> POP_ASSUM MP_TAC
  >> rw[]
  >> RW_TAC fcp_ss[desRound_alt_Round']
  >> Q.ABBREV_TAC ‘keys=(KS k n)’
  >> Q.ABBREV_TAC ‘keys'=(KS (~k) n)’
  >> Suff ‘(Join (Swap (Round n keys (Split (IP m)))))=
              ~(Join (Swap (Round n keys' (Split (IP (¬m))))))’
  >- (Rewr' \\
      rw[compl_IIP])
  >> rw[Split_def]
  >> REWRITE_TAC [Round_alt_half_message]
  >> rw[Swap_def]
  >>  Q.ABBREV_TAC ‘u=(63 >< 32) (IP m)’
  >>  Q.ABBREV_TAC ‘v=(31 >< 0) (IP m)’
  >>  Q.ABBREV_TAC ‘u'=(63 >< 32) (IP (¬m))’
  >>  Q.ABBREV_TAC ‘v'=(31 >< 0) (IP (¬m))’
  >> Suff ‘(M (u',v') keys' (SUC n),M (u',v') keys' n)=
              (~M (u,v) keys (SUC n),~M (u,v) keys n)’
  >- (Rewr' \\
      rw [compl_join] \\
      rw[])
  >>Suff ‘ (M (u',v') keys' n,M (u',v') keys' (SUC n)) =
          (¬M (u,v) keys n,¬M (u,v) keys (SUC n))’
  >- rw[]
  >>Suff ‘∀x.x<=n ==>(M (u',v') keys' x,M (u',v') keys' (SUC(x)))
          = (¬M (u,v) keys x,¬M (u,v) keys (SUC(x)))’
  >- rw[]
  >> Induct_on ‘x’
  >- (simp [] \\
      Know ‘(M (u',v') keys' 0,M (u',v') keys' (SUC 0))=
            Round 0 keys' (u',v')’
  >- RW_TAC fcp_ss[Round_alt_half_message']
  >> Know ‘Round 0 keys' (u',v')= (u',v')’
  >- rw [Round_def]
  >> Know ‘(M (u,v) keys 0,M (u,v) keys (SUC 0))=Round 0 keys (u,v)’
  >- RW_TAC fcp_ss[Round_alt_half_message']
  >> Know ‘Round 0 keys (u,v)= (u,v)’
  >- rw [Round_def]
  >> rw[]
  >| [ (* goal 1 (of 2) *)
       rw [Abbr ‘u'’,Abbr ‘u’] \\
       Know `(IP m)=~(IP (¬m))` \\
       rw[compl_IP] \\
       rw [compl_extract_1] \\
       rw[],
       (* goal 2 (of 2) *)
       rw [Abbr ‘v'’,Abbr ‘v’]\\
       Know `(IP m)=~(IP (¬m))` \\
       rw[compl_IP]\\
       rw [compl_extract_2] \\
       rw[] ])
  >> DISCH_TAC
  >> ‘x <= n’ by rw []
  >> fs []
  >> Know ‘(SUC (SUC x))= x+2’
  >- rw[]
  >> Rewr'
  >> Q.PAT_X_ASSUM ‘M (u',v') keys' (SUC x) = _’ MP_TAC
  >> Know ‘(SUC x)= x+1’
  >- rw[]
  >> Rewr'
  >> rw[]
  >> Know ‘ M (u',v') keys' (x+2)=
              M (u',v') keys' x ?? (RoundOp (M(u',v') keys' (x+1)) (EL x keys'))’
  >- rw[half_message']
  >> Rewr'
  >> Know ‘ ~M (u,v) keys (x+2)=
              ~(M (u,v) keys x ?? (RoundOp (M (u,v) keys (x+1)) (EL x keys)))’
  >- rw[half_message']
  >> Rewr'
  >> rw[]
  >> Suff ‘RoundOp (¬M (u,v) keys (x + 1)) (EL x keys')=
              RoundOp (M (u,v) keys (x + 1)) (EL x keys)’
  >- (rw[WORD_NOT_XOR])
  >> rw[RoundOp_def]
  >> Know ‘E (~M (u,v) keys (x + 1))=~E (M (u,v) keys (x + 1))’
  >- (rw[compl_E])
  >> Rewr'
  >> Suff ‘EL x keys'=~EL x keys’
  >- rw[WORD_NOT_XOR]
  >> rw [Abbr ‘keys'’, Abbr ‘keys’]
  >> rw[KS_def]
  >> rw[convert_RK]
  >> qabbrev_tac ‘l = GENLIST (λi. RK i k) (SUC n)’
  >>  Know ‘GENLIST (\i. RK i (~k)) (SUC n) =
           MAP (\(a,b). (~a,~b)) l’
  >- (rw [Abbr ‘l’, LIST_EQ_REWRITE] \\
      rename1 ‘j < SUC n’ \\
      rw [EL_MAP] \\
      rw [roundk_supp]
      >| [rw [compl_RK_L],
          rw [compl_RK_R] ])
  >> Rewr'
  >> ‘SUC x < LENGTH l’ by rw[Abbr ‘l’]
  >> qabbrev_tac ‘l' = MAP PC2 (TL l)’
  >> ‘x < LENGTH l'’
    by (rw [Abbr ‘l'’, LENGTH_MAP, LENGTH_TL])
  >> Know ‘~EL x l' = EL x (MAP (\e. ~e) l')’
  >- (rw [EL_MAP, LENGTH_MAP])
  >> Rewr'
  >> qunabbrev_tac ‘l'’
  >> simp [GSYM MAP_TL]
  >> simp [MAP_MAP_o]
  >> simp [o_DEF]
  >> Suff ‘(λx. PC2 ((λ(a,b). (¬a,¬b)) x)) =
           (λx. ¬PC2 x)’
  >- rw []
  >> simp [FUN_EQ_THM]
  >> simp [FORALL_PROD]
  >> rw[comple_PC2]
QED

(* weak key *)
Definition Wkey_def:
  Wkey= [0x0101010101010101w:word64;0xfefefefefefefefew:word64;0xe0e0e0e0f1f1f1f1w:word64;0x1f1f1f1f0e0e0e0ew:word64]
End

Theorem weakK_proper:
  !k plaintext. MEM k Wkey /\ (FullDES k =(encrypt,decrypt))  ⇒ (encrypt (encrypt plaintext) = plaintext)
Proof
     rw[DES_def]
  >> Know ‘LENGTH (KS k 16)=16’
  >- rw [LENGTH_KS]
  >> Suff ‘desCore 16 (KS k 16) (desCore 16 (KS k 16) plaintext)=
     desCore 16 (REVERSE (KS k 16)) (desCore 16 (KS k 16) plaintext)’
  >- rw [desCore_CORRECT]
  >> Suff ‘((REVERSE (KS k 16))=KS k 16)’
  >- rw[]
  >> POP_ASSUM MP_TAC
  >> rw[Wkey_def]
  >- EVAL_TAC
  >- EVAL_TAC
  >- EVAL_TAC
  >> EVAL_TAC
QED

(* semi-weak key *)
Definition Semiwkey_def:
  Semiwkey =[
  (0x01fe01fe01fe01few:word64,0xfe01fe01fe01fe01w:word64);
  (0x1fe01fe00ef10ef1w:word64,0xe01fe01ff10ef10ew:word64);
  (0x01e001e001f101f1w:word64,0xe001e001f101f101w:word64);
  (0x1ffe1ffe0efe0efew:word64,0xfe1ffe1ffe0efe0ew:word64);
  (0x011f011f010e010ew:word64,0x1f011f010e010e01w:word64);
  (0xe0fee0fef1fef1few:word64,0xfee0fee0fef1fef1w:word64)
  ]
End

Theorem semiK_proper1:
  !plaintext pair. MEM pair Semiwkey /\ pair= (s1,s2) /\(FullDES s1 = (encrypt,decrypt)) /\ (FullDES s2= (encrypt',decrypt') ) ==>
  (encrypt (encrypt' plaintext) = plaintext)
Proof
     rw[DES_def]
  >> Know ‘LENGTH ((KS s2 16))=16’
  >- rw [LENGTH_KS]
  >> Suff ‘KS s1 16 =REVERSE (KS s2 16)’
  >- rw [desCore_CORRECT]
  >> POP_ASSUM MP_TAC
  >> rw[Semiwkey_def]
  >- EVAL_TAC
  >- EVAL_TAC
  >- EVAL_TAC
  >- EVAL_TAC
  >- EVAL_TAC
  >> EVAL_TAC
QED

Theorem semiK_proper2:
  !plaintext pair. MEM pair Semiwkey /\ pair= (s1,s2)/\ (FullDES s1= (encrypt,decrypt)) /\ (FullDES s2= (encrypt',decrypt')) ==>
  (encrypt' (encrypt plaintext) = plaintext)
Proof
     rw[DES_def]
  >> Know ‘LENGTH ((KS s1 16))=16’
  >- rw [LENGTH_KS]
  >> Suff ‘KS s2 16 =REVERSE (KS s1 16)’
  >- rw [desCore_CORRECT]
  >> POP_ASSUM MP_TAC
  >> rw[Semiwkey_def]
  >- EVAL_TAC
  >- EVAL_TAC
  >- EVAL_TAC
  >- EVAL_TAC
  >- EVAL_TAC
  >> EVAL_TAC
QED

Definition Wkey1_def:
  Wkey1= 0x0101010101010101w:word64
End

Definition Wkey2_def:
  Wkey2= 0xfefefefefefefefew:word64
End

Definition Wkey3_def:
  Wkey3= 0xe0e0e0e0f1f1f1f1w:word64
End

Definition Wkey4_def:
  Wkey4= 0x1f1f1f1f0e0e0e0ew:word64
End

(* Added by Chun Tian *)
Definition Wtext_def :
  Wtext key = {x:word64| ?w. (Split (IP (desCore 8 (KS key 8) x))) = (w,w)}
End

Overload Wtext1 = “Wtext Wkey1”
Overload Wtext2 = “Wtext Wkey2”
Overload Wtext3 = “Wtext Wkey3”
Overload Wtext4 = “Wtext Wkey4”

Theorem Wtext1_def:
  Wtext1= {x:word64| ?w. (Split (IP (desCore 8 (KS Wkey1 8) x))) = (w,w)}
Proof
  rw [Wtext_def]
QED

Theorem Wtext2_def:
  Wtext2= {x:word64| ?w. (Split (IP (desCore 8 (KS Wkey2 8) x))) = (w,w)}
Proof
  rw [Wtext_def]
QED

Theorem Wtext3_def:
  Wtext3= {x:word64| ?w. (Split (IP (desCore 8 (KS Wkey3 8) x))) = (w,w)}
Proof
  rw [Wtext_def]
QED

Theorem Wtext4_def:
  Wtext4= {x:word64| ?w. (Split (IP (desCore 8 (KS Wkey4 8) x))) = (w,w)}
Proof
  rw [Wtext_def]
QED

Definition Wtextlist_def:
  Wtextlist= [Wtext1;Wtext2;Wtext3;Wtext4]
End

Theorem wkey1_equal:
   !x n k.MEM k Wkey /\ n<=8 ==> Round n (KS k 8) (Split(x))= Round n (KS k 16) (Split(x))
Proof
     rw[]
  >> Induct_on ‘n’
  >- rw[Round_def]
  >> POP_ASSUM MP_TAC
  >> rw[Round_alt_half_message',SUC_ONE_ADD]
  >> Know ‘M (Split x) (KS k 8) (n+2) =
           M (Split x) (KS k 8) n ?? (RoundOp (M (Split x) (KS k 8) (n+1)) (EL n (KS k 8)))’
  >- rw[half_message']
  >> Rewr'
  >> Know ‘M (Split x) (KS k 16) (n+2) =
           M (Split x) (KS k 16) n ?? (RoundOp (M (Split x) (KS k 16) (n+1)) (EL n (KS k 16)))’
  >- rw[half_message']
  >> Rewr'
  >> rw[]
  >> Suff ‘(EL n (KS k 8))=(EL n (KS k 16))’
  >- rw[]
  >> POP_ASSUM MP_TAC
  >> POP_ASSUM MP_TAC
  >> POP_ASSUM MP_TAC
  >> rw[Wkey_def]
  >- (EVAL_TAC\\
      qabbrev_tac ‘l2 :word48 list =
      [0w; 0w; 0w; 0w; 0w; 0w; 0w; 0w; 0w; 0w; 0w; 0w; 0w; 0w; 0w; 0w]’\\
      qabbrev_tac ‘l1 :word48 list = [0w; 0w; 0w; 0w; 0w; 0w; 0w; 0w]’\\
      ‘LENGTH l2 = 16’ by rw [Abbr ‘l2’,Abbr ‘l1’]\\
      ‘LENGTH l1 = 8’ by rw [Abbr ‘l1’]\\
      ‘n < 8’ by rw []\\
      Suff ‘!i. i < 8 ==> EL i l1 = 0w /\ EL i l2 = 0w’
      >- rw[] \\
      rw [Abbr ‘l1’,Abbr ‘l2’]\\
      ‘i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7 ’ by rw []\\
       rw[])
  >- (EVAL_TAC\\
      qabbrev_tac ‘l2 :word48 list =
       [0xFFFFFFFFFFFFw; 0xFFFFFFFFFFFFw; 0xFFFFFFFFFFFFw; 0xFFFFFFFFFFFFw;
        0xFFFFFFFFFFFFw; 0xFFFFFFFFFFFFw; 0xFFFFFFFFFFFFw; 0xFFFFFFFFFFFFw;
        0xFFFFFFFFFFFFw; 0xFFFFFFFFFFFFw; 0xFFFFFFFFFFFFw; 0xFFFFFFFFFFFFw;
        0xFFFFFFFFFFFFw; 0xFFFFFFFFFFFFw; 0xFFFFFFFFFFFFw; 0xFFFFFFFFFFFFw]’\\
      qabbrev_tac ‘l1 :word48 list =
       [0xFFFFFFFFFFFFw; 0xFFFFFFFFFFFFw; 0xFFFFFFFFFFFFw;0xFFFFFFFFFFFFw;
        0xFFFFFFFFFFFFw; 0xFFFFFFFFFFFFw;0xFFFFFFFFFFFFw; 0xFFFFFFFFFFFFw]’\\
      ‘LENGTH l2 = 16’ by rw [Abbr ‘l2’,Abbr ‘l1’]\\
      ‘LENGTH l1 = 8’ by rw [Abbr ‘l1’]\\
      ‘n < 8’ by rw []\\
      Suff ‘!i. i < 8 ==> EL i l1 = 0xFFFFFFFFFFFFw /\ EL i l2 = 0xFFFFFFFFFFFFw’
      >- rw[] \\
      rw [Abbr ‘l1’,Abbr ‘l2’]\\
      ‘i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7 ’ by rw []\\
       rw[])
  >- (EVAL_TAC\\
      qabbrev_tac ‘l2 :word48 list =
       [0xFFFFFF000000w; 0xFFFFFF000000w; 0xFFFFFF000000w; 0xFFFFFF000000w;
        0xFFFFFF000000w; 0xFFFFFF000000w; 0xFFFFFF000000w; 0xFFFFFF000000w;
        0xFFFFFF000000w; 0xFFFFFF000000w; 0xFFFFFF000000w; 0xFFFFFF000000w;
        0xFFFFFF000000w; 0xFFFFFF000000w; 0xFFFFFF000000w; 0xFFFFFF000000w]’\\
      qabbrev_tac ‘l1 :word48 list =
       [0xFFFFFF000000w; 0xFFFFFF000000w; 0xFFFFFF000000w; 0xFFFFFF000000w;
        0xFFFFFF000000w; 0xFFFFFF000000w; 0xFFFFFF000000w; 0xFFFFFF000000w]’\\
      ‘LENGTH l2 = 16’ by rw [Abbr ‘l2’,Abbr ‘l1’]\\
      ‘LENGTH l1 = 8’ by rw [Abbr ‘l1’]\\
      ‘n < 8’ by rw []\\
      Suff ‘!i. i < 8 ==> EL i l1 = 0xFFFFFF000000w /\ EL i l2 = 0xFFFFFF000000w’
      >- rw[] \\
      rw [Abbr ‘l1’,Abbr ‘l2’]\\
      ‘i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7 ’ by rw []\\
       rw[])
  >> EVAL_TAC
  >> qabbrev_tac ‘l2 :word48 list =
     [0xFFFFFFw; 0xFFFFFFw; 0xFFFFFFw; 0xFFFFFFw;
      0xFFFFFFw; 0xFFFFFFw; 0xFFFFFFw; 0xFFFFFFw;
      0xFFFFFFw; 0xFFFFFFw; 0xFFFFFFw; 0xFFFFFFw;
      0xFFFFFFw; 0xFFFFFFw; 0xFFFFFFw; 0xFFFFFFw]’
  >> qabbrev_tac ‘l1 :word48 list =
     [0xFFFFFFw; 0xFFFFFFw; 0xFFFFFFw; 0xFFFFFFw;
      0xFFFFFFw; 0xFFFFFFw; 0xFFFFFFw; 0xFFFFFFw]’
  >> ‘LENGTH l2 = 16’ by rw [Abbr ‘l2’,Abbr ‘l1’]
  >> ‘LENGTH l1 = 8’ by rw [Abbr ‘l1’]
  >> ‘n < 8’ by rw []
  >> Suff ‘!i. i < 8 ==> EL i l1 = 0xFFFFFFw /\ EL i l2 = 0xFFFFFFw’
  >- rw[]
  >> rw [Abbr ‘l1’,Abbr ‘l2’]
  >>‘i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7 ’ by rw []
  >>rw[]
QED

Theorem weakK_sup:
   !n k . MEM k Wkey /\ 0<=n /\ n<=8 /\
         (Split (IP (desCore 8 (KS k 8) x))) = (w,w) ==>
         (Round (8-n) (KS k 16) (Split (IP x))) = Swap ((Round (8+n) (KS k 16) (Split (IP x))))
Proof
     rw[]
  >> POP_ASSUM MP_TAC
  >> Know ‘(desCore 8 (KS k 8) x)=(desCore 8 (KS k 16) x)’
  >- (rw[desCore_alt]\\
      rw[wkey1_equal])
  >> Rewr'
  >> Q.ABBREV_TAC‘ks=(KS Wkey1 16)’
  >> Induct_on ‘n’
  >- (rw[]\\
      POP_ASSUM MP_TAC\\
      rw[desCore_alt,Swap_def,IP_IIP_Inverse,Split_Join_Inverse]\\
      Cases_on ‘Round 8 (KS k 16) (Split (IP x))’\\
      POP_ASSUM MP_TAC\\
      POP_ASSUM MP_TAC\\
      rw[Swap_def])
  >> POP_ASSUM MP_TAC
  >> rw[Round_alt_half_message']
  >> POP_ASSUM MP_TAC
  >> POP_ASSUM MP_TAC
  >> POP_ASSUM MP_TAC
  >> rw[SUC_ONE_ADD]
  >> Know ‘M (Split (IP x)) (KS k 16) (n+10) =
           M (Split (IP x)) (KS k 16) (n + 8) ??
           (RoundOp (M (Split (IP x)) (KS k 16) (n+9)) (EL (n+8) (KS k 16)))’
  >- rw[half_message']
  >> Rewr'
  >> Know ‘M (Split (IP x)) (KS k 16) (7-n) =
           M (Split (IP x)) (KS k 16) (9-n) ??
           (RoundOp (M (Split (IP x)) (KS k 16) (8-n)) (EL (7-n) (KS k 16)))’
  >- rw[half_message']
  >> Rewr'
  >> POP_ASSUM MP_TAC
  >> POP_ASSUM MP_TAC
  >> POP_ASSUM MP_TAC
  >> rw[Swap_def]
  >> Suff ‘(EL (7 − n) (KS k 16))=(EL (n + 8) (KS k 16))’
  >- rw[]
  >> Q.PAT_X_ASSUM ‘MEM k Wkey’ MP_TAC
  >> rw[Wkey_def]
  >- (EVAL_TAC\\
      qabbrev_tac ‘l :word48 list =
      [0w; 0w; 0w; 0w; 0w; 0w; 0w; 0w; 0w; 0w; 0w; 0w; 0w; 0w; 0w; 0w]’\\
      ‘LENGTH l = 16’ by rw [Abbr ‘l’]\\
      ‘7 - n < 16’ by rw []\\
      ‘n + 8 < 16’ by rw []\\
      Suff ‘!i. i < 16 ==> EL i l = 0w’ >- rw []\\
      rw [Abbr ‘l’]\\
     ‘i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/
      i = 4 \/ i = 5 \/ i = 6 \/ i = 7 \/
      i = 8 \/ i = 9 \/ i = 10 \/ i = 11 \/
      i = 12 \/ i = 13 \/ i = 14 \/ i = 15’ by rw []\\
      rw[])
  >- (EVAL_TAC\\
      qabbrev_tac ‘l :word48 list =
      [0xFFFFFFFFFFFFw; 0xFFFFFFFFFFFFw; 0xFFFFFFFFFFFFw;
           0xFFFFFFFFFFFFw; 0xFFFFFFFFFFFFw; 0xFFFFFFFFFFFFw;
           0xFFFFFFFFFFFFw; 0xFFFFFFFFFFFFw; 0xFFFFFFFFFFFFw;
           0xFFFFFFFFFFFFw; 0xFFFFFFFFFFFFw; 0xFFFFFFFFFFFFw;
           0xFFFFFFFFFFFFw; 0xFFFFFFFFFFFFw; 0xFFFFFFFFFFFFw;
           0xFFFFFFFFFFFFw]’\\
      ‘LENGTH l = 16’ by rw [Abbr ‘l’]\\
      ‘7 - n < 16’ by rw []\\
      ‘n + 8 < 16’ by rw []\\
      Suff ‘!i. i < 16 ==> EL i l = 0xFFFFFFFFFFFFw’ >- rw []\\
      rw [Abbr ‘l’]\\
     ‘i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/
      i = 4 \/ i = 5 \/ i = 6 \/ i = 7 \/
      i = 8 \/ i = 9 \/ i = 10 \/ i = 11 \/
      i = 12 \/ i = 13 \/ i = 14 \/ i = 15’ by rw []\\
      rw[])
  >- (EVAL_TAC\\
      qabbrev_tac ‘l :word48 list =
      [0xFFFFFF000000w; 0xFFFFFF000000w; 0xFFFFFF000000w;
           0xFFFFFF000000w; 0xFFFFFF000000w; 0xFFFFFF000000w;
           0xFFFFFF000000w; 0xFFFFFF000000w; 0xFFFFFF000000w;
           0xFFFFFF000000w; 0xFFFFFF000000w; 0xFFFFFF000000w;
           0xFFFFFF000000w; 0xFFFFFF000000w; 0xFFFFFF000000w;
           0xFFFFFF000000w]’\\
      ‘LENGTH l = 16’ by rw [Abbr ‘l’]\\
      ‘7 - n < 16’ by rw []\\
      ‘n + 8 < 16’ by rw []\\
      Suff ‘!i. i < 16 ==> EL i l = 0xFFFFFF000000w’ >- rw []\\
      rw [Abbr ‘l’]\\
     ‘i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/
      i = 4 \/ i = 5 \/ i = 6 \/ i = 7 \/
      i = 8 \/ i = 9 \/ i = 10 \/ i = 11 \/
      i = 12 \/ i = 13 \/ i = 14 \/ i = 15’ by rw []\\
      rw[])
  >> EVAL_TAC
  >> qabbrev_tac ‘l :word48 list =
     [0xFFFFFFw; 0xFFFFFFw; 0xFFFFFFw; 0xFFFFFFw;
      0xFFFFFFw; 0xFFFFFFw; 0xFFFFFFw; 0xFFFFFFw;
      0xFFFFFFw; 0xFFFFFFw; 0xFFFFFFw; 0xFFFFFFw;
      0xFFFFFFw; 0xFFFFFFw; 0xFFFFFFw; 0xFFFFFFw]’
  >> ‘LENGTH l = 16’ by rw [Abbr ‘l’]
  >> ‘7 - n < 16’ by rw []
  >> ‘n + 8 < 16’ by rw []
  >> Suff ‘!i. i < 16 ==> EL i l = 0xFFFFFFw’ >- rw []
  >> rw [Abbr ‘l’]
  >> ‘i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/
      i = 4 \/ i = 5 \/ i = 6 \/ i = 7 \/
      i = 8 \/ i = 9 \/ i = 10 \/ i = 11 \/
      i = 12 \/ i = 13 \/ i = 14 \/ i = 15’ by rw []
  >> rw[]
QED

Theorem weakK1_proper2:
  !x. x IN Wtext1 /\  (FullDES Wkey1= (encrypt,decrypt))
   ==>  encrypt x=x
Proof
     rw[DES_def,Wtext1_def]
  >> Suff ‘desCore 16 (KS Wkey1 16) x=desCore 0 (KS Wkey1 16) x’
  >- rw[desCore_0]
  >> rw[desCore_alt,desCore_0]
  >> Know ‘Swap (Round (8+8) (KS Wkey1 16) (Split (IP x))) =
           ((Round (8-8) (KS Wkey1 16) (Split (IP x))))’
  >- (Know ‘MEM Wkey1 Wkey’
      >- rw[Wkey_def,Wkey1_def]\\
      rw[weakK_sup])
  >> rw[]
  >> rw[Round_def]
  >> rw[IIP_IP_Inverse,Join_Split_Inverse]
QED

Theorem weakK2_proper2:
  !x. x IN Wtext2 /\  (FullDES Wkey2= (encrypt,decrypt))
   ==>  encrypt x=x
Proof
     rw[DES_def,Wtext2_def]
  >> Suff ‘desCore 16 (KS Wkey2 16) x=desCore 0 (KS Wkey2 16) x’
  >- rw[desCore_0]
  >> rw[desCore_alt,desCore_0]
  >> Know ‘Swap (Round (8+8) (KS Wkey2 16) (Split (IP x))) =
           ((Round (8-8) (KS Wkey2 16) (Split (IP x)))) ’
  >- (Know ‘MEM Wkey2 Wkey’
      >- rw[Wkey_def,Wkey2_def]\\
      rw[weakK_sup])
  >> rw[]
  >> rw[Round_def]
  >> rw[IIP_IP_Inverse,Join_Split_Inverse]
QED

Theorem weakK3_proper2:
  !x. x IN Wtext3 /\  (FullDES Wkey3= (encrypt,decrypt))
   ==>  encrypt x=x
Proof
     rw[DES_def,Wtext3_def]
  >> Suff ‘desCore 16 (KS Wkey3 16) x=desCore 0 (KS Wkey3 16) x’
  >- rw[desCore_0]
  >> rw[desCore_alt,desCore_0]
  >> Know ‘Swap (Round (8+8) (KS Wkey3 16) (Split (IP x))) =
           ((Round (8-8) (KS Wkey3 16) (Split (IP x)))) ’
  >- (Know ‘MEM Wkey3 Wkey’
      >- rw[Wkey_def,Wkey3_def]\\
      rw[weakK_sup])
  >> rw[]
  >> rw[Round_def]
  >> rw[IIP_IP_Inverse,Join_Split_Inverse]
QED

Theorem weakK4_proper2:
  !x. x IN Wtext4 /\  (FullDES Wkey4= (encrypt,decrypt))
   ==>  encrypt x=x
Proof
     rw[DES_def,Wtext4_def]
  >> Suff ‘desCore 16 (KS Wkey4 16) x=desCore 0 (KS Wkey4 16) x’
  >- rw[desCore_0]
  >> rw[desCore_alt,desCore_0]
  >> Know ‘Swap (Round (8+8) (KS Wkey4 16) (Split (IP x))) =
           ((Round (8-8) (KS Wkey4 16) (Split (IP x)))) ’
  >- (Know ‘MEM Wkey4 Wkey’
      >- rw[Wkey_def,Wkey4_def]\\
      rw[weakK_sup])
  >> rw[]
  >> rw[Round_def]
  >> rw[IIP_IP_Inverse,Join_Split_Inverse]
QED

Definition w1trans1_def:
  w1trans1 (x:word64) = FST (Split(IP(desCore 8 (KS Wkey1 8) x)))
End

Definition w1trans2_def:
  w1trans2 (x:word32)= desCore 8 (KS Wkey1 8) (IIP(Join(x,x)))
End

Definition w2trans1_def:
  w2trans1 (x:word64) = FST (Split(IP(desCore 8 (KS Wkey2 8) x)))
End

Definition w2trans2_def:
  w2trans2 (x:word32)= desCore 8 (KS Wkey2 8) (IIP(Join(x,x)))
End

Definition w3trans1_def:
  w3trans1 (x:word64) = FST (Split(IP(desCore 8 (KS Wkey3 8) x)))
End

Definition w3trans2_def:
  w3trans2 (x:word32)= desCore 8 (KS Wkey3 8) (IIP(Join(x,x)))
End

Definition w4trans1_def:
  w4trans1 (x:word64) = FST (Split(IP(desCore 8 (KS Wkey4 8) x)))
End

Definition w4trans2_def:
  w4trans2 (x:word32)= desCore 8 (KS Wkey4 8) (IIP(Join(x,x)))
End

Theorem BIJ_wtext1:
   BIJ w1trans1 Wtext1 univ(:word32)
Proof
     rw[BIJ_IFF_INV]
  >> EXISTS_TAC “w1trans2”
  >> rw[]
  >- (rw[w1trans2_def,Wtext1_def] \\
      Know ‘LENGTH (KS Wkey1 8)=8’
      >- (rw[Wkey1_def]\\
          EVAL_TAC) \\
      Suff ‘(desCore 8 (KS Wkey1 8) (desCore 8 (KS Wkey1 8) (IIP (Join (x,x))))) =
            (desCore 8 (REVERSE (KS Wkey1 8)) (desCore 8 (KS Wkey1 8) (IIP (Join (x,x)))))’
  >- (Rewr'\\
     rw[desCore_CORRECT]\\
     rw[IP_IIP_Inverse,Split_Join_Inverse])
  >> Know ‘(REVERSE (KS Wkey1 8))=(KS Wkey1 8)’
  >- (rw[Wkey1_def]\\
       EVAL_TAC)
  >> rw[])
  >- (POP_ASSUM MP_TAC
  >> rw[w1trans2_def,Wtext1_def,w1trans1_def]
  >> rw[]
  >> Know ‘(w,w)=Split (IP (desCore 8 (KS Wkey1 8) x))’
  >- rw[]
  >> Rewr'
  >> rw[IIP_IP_Inverse,Join_Split_Inverse]
  >> Know ‘LENGTH (KS Wkey1 8)=8’
  >- (rw[Wkey1_def]\\
     EVAL_TAC)
  >> Suff ‘(desCore 8 (KS Wkey1 8) (desCore 8 (KS Wkey1 8) x)) =
           (desCore 8 (REVERSE (KS Wkey1 8)) (desCore 8 (KS Wkey1 8) x))’
  >- (Rewr'\\
      rw[desCore_CORRECT])
  >> Know ‘(REVERSE (KS Wkey1 8))=(KS Wkey1 8)’
  >- (rw[Wkey1_def]\\
       EVAL_TAC)
  >> rw[])
  >> rw[w1trans1_def,w1trans2_def]
  >> Know ‘LENGTH (KS Wkey1 8)=8’
  >- (rw[Wkey1_def]\\
     EVAL_TAC)
  >> Suff ‘(desCore 8 (KS Wkey1 8) (desCore 8 (KS Wkey1 8) (IIP (Join (x,x))))) =
           (desCore 8 (REVERSE (KS Wkey1 8)) (desCore 8 (KS Wkey1 8) (IIP (Join (x,x)))))’
  >- (Rewr'\\
      rw[desCore_CORRECT]\\
      rw[IP_IIP_Inverse,Split_Join_Inverse])
  >> Know ‘(REVERSE (KS Wkey1 8))=(KS Wkey1 8)’
  >- (rw[Wkey1_def]\\
       EVAL_TAC)
  >> rw[]
QED

Theorem BIJ_wtext2:
   BIJ w2trans1 Wtext2 univ(:word32)
Proof
     rw[BIJ_IFF_INV]
  >> EXISTS_TAC “w2trans2”
  >> rw[]
  >- (rw[w2trans2_def,Wtext2_def] \\
      Know ‘LENGTH (KS Wkey2 8)=8’
      >- (rw[Wkey2_def]\\
          EVAL_TAC) \\
      Suff ‘(desCore 8 (KS Wkey2 8) (desCore 8 (KS Wkey2 8) (IIP (Join (x,x))))) =
            (desCore 8 (REVERSE (KS Wkey2 8)) (desCore 8 (KS Wkey2 8) (IIP (Join (x,x)))))’
  >- (Rewr'\\
     rw[desCore_CORRECT]\\
     rw[IP_IIP_Inverse,Split_Join_Inverse])
  >> Know ‘(REVERSE (KS Wkey2 8))=(KS Wkey2 8)’
  >- (rw[Wkey2_def]\\
       EVAL_TAC)
  >> rw[])
  >- (POP_ASSUM MP_TAC
  >> rw[w2trans2_def,Wtext2_def,w2trans1_def]
  >> rw[]
  >> Know ‘(w,w)=Split (IP (desCore 8 (KS Wkey2 8) x))’
  >- rw[]
  >> Rewr'
  >> rw[IIP_IP_Inverse,Join_Split_Inverse]
  >> Know ‘LENGTH (KS Wkey2 8)=8’
  >- (rw[Wkey1_def]\\
     EVAL_TAC)
  >> Suff ‘(desCore 8 (KS Wkey2 8) (desCore 8 (KS Wkey2 8) x)) =
           (desCore 8 (REVERSE (KS Wkey2 8)) (desCore 8 (KS Wkey2 8) x))’
  >- (Rewr'\\
      rw[desCore_CORRECT])
  >> Know ‘(REVERSE (KS Wkey2 8))=(KS Wkey2 8)’
  >- (rw[Wkey2_def]\\
       EVAL_TAC)
  >> rw[])
  >> rw[w2trans1_def,w2trans2_def]
  >> Know ‘LENGTH (KS Wkey2 8)=8’
  >- (rw[Wkey2_def]\\
     EVAL_TAC)
  >> Suff ‘(desCore 8 (KS Wkey2 8) (desCore 8 (KS Wkey2 8) (IIP (Join (x,x))))) =
           (desCore 8 (REVERSE (KS Wkey2 8)) (desCore 8 (KS Wkey2 8) (IIP (Join (x,x)))))’
  >- (Rewr'\\
      rw[desCore_CORRECT]\\
      rw[IP_IIP_Inverse,Split_Join_Inverse])
  >> Know ‘(REVERSE (KS Wkey2 8))=(KS Wkey2 8)’
  >- (rw[Wkey2_def]\\
       EVAL_TAC)
  >> rw[]
QED

Theorem BIJ_wtext3:
   BIJ w3trans1 Wtext3 univ(:word32)
Proof
     rw[BIJ_IFF_INV]
  >> EXISTS_TAC “w3trans2”
  >> rw[]
  >- (rw[w3trans2_def,Wtext3_def] \\
      Know ‘LENGTH (KS Wkey3 8)=8’
      >- (rw[Wkey3_def]\\
          EVAL_TAC) \\
      Suff ‘(desCore 8 (KS Wkey3 8) (desCore 8 (KS Wkey3 8) (IIP (Join (x,x))))) =
            (desCore 8 (REVERSE (KS Wkey3 8)) (desCore 8 (KS Wkey3 8) (IIP (Join (x,x)))))’
  >- (Rewr'\\
     rw[desCore_CORRECT]\\
     rw[IP_IIP_Inverse,Split_Join_Inverse])
  >> Know ‘(REVERSE (KS Wkey3 8))=(KS Wkey3 8)’
  >- (rw[Wkey3_def]\\
       EVAL_TAC)
  >> rw[])
  >- (POP_ASSUM MP_TAC
  >> rw[w3trans2_def,Wtext3_def,w3trans1_def]
  >> rw[]
  >> Know ‘(w,w)=Split (IP (desCore 8 (KS Wkey3 8) x))’
  >- rw[]
  >> Rewr'
  >> rw[IIP_IP_Inverse,Join_Split_Inverse]
  >> Know ‘LENGTH (KS Wkey3 8)=8’
  >- (rw[Wkey3_def]\\
     EVAL_TAC)
  >> Suff ‘(desCore 8 (KS Wkey3 8) (desCore 8 (KS Wkey3 8) x)) =
           (desCore 8 (REVERSE (KS Wkey3 8)) (desCore 8 (KS Wkey3 8) x))’
  >- (Rewr'\\
      rw[desCore_CORRECT])
  >> Know ‘(REVERSE (KS Wkey3 8))=(KS Wkey3 8)’
  >- (rw[Wkey3_def]\\
       EVAL_TAC)
  >> rw[])
  >> rw[w3trans1_def,w3trans2_def]
  >> Know ‘LENGTH (KS Wkey3 8)=8’
  >- (rw[Wkey3_def]\\
     EVAL_TAC)
  >> Suff ‘(desCore 8 (KS Wkey3 8) (desCore 8 (KS Wkey3 8) (IIP (Join (x,x)))))=(desCore 8 (REVERSE (KS Wkey3 8)) (desCore 8 (KS Wkey3 8) (IIP (Join (x,x)))))’
  >- (Rewr'\\
      rw[desCore_CORRECT]\\
      rw[IP_IIP_Inverse,Split_Join_Inverse])
  >> Know ‘(REVERSE (KS Wkey3 8))=(KS Wkey3 8)’
  >- (rw[Wkey3_def]\\
       EVAL_TAC)
  >> rw[]
QED

Theorem BIJ_wtext4:
   BIJ w4trans1 Wtext4 univ(:word32)
Proof
     rw[BIJ_IFF_INV]
  >> EXISTS_TAC “w4trans2”
  >> rw[]
  >- (rw[w4trans2_def,Wtext4_def] \\
      Know ‘LENGTH (KS Wkey4 8)=8’
      >- (rw[Wkey4_def]\\
          EVAL_TAC) \\
      Suff ‘(desCore 8 (KS Wkey4 8) (desCore 8 (KS Wkey4 8) (IIP (Join (x,x))))) =
            (desCore 8 (REVERSE (KS Wkey4 8)) (desCore 8 (KS Wkey4 8) (IIP (Join (x,x)))))’
  >- (Rewr'\\
     rw[desCore_CORRECT]\\
     rw[IP_IIP_Inverse,Split_Join_Inverse])
  >> Know ‘(REVERSE (KS Wkey4 8))=(KS Wkey4 8)’
  >- (rw[Wkey4_def]\\
       EVAL_TAC)
  >> rw[])
  >- (POP_ASSUM MP_TAC
  >> rw[w4trans2_def,Wtext4_def,w4trans1_def]
  >> rw[]
  >> Know ‘(w,w)=Split (IP (desCore 8 (KS Wkey4 8) x))’
  >- rw[]
  >> Rewr'
  >> rw[IIP_IP_Inverse,Join_Split_Inverse]
  >> Know ‘LENGTH (KS Wkey4 8)=8’
  >- (rw[Wkey4_def]\\
     EVAL_TAC)
  >> Suff ‘(desCore 8 (KS Wkey4 8) (desCore 8 (KS Wkey4 8) x)) =
           (desCore 8 (REVERSE (KS Wkey4 8)) (desCore 8 (KS Wkey4 8) x))’
  >- (Rewr'\\
      rw[desCore_CORRECT])
  >> Know ‘(REVERSE (KS Wkey4 8))=(KS Wkey4 8)’
  >- (rw[Wkey4_def]\\
       EVAL_TAC)
  >> rw[])
  >> rw[w4trans1_def,w4trans2_def]
  >> Know ‘LENGTH (KS Wkey4 8)=8’
  >- (rw[Wkey4_def]\\
     EVAL_TAC)
  >> Suff ‘(desCore 8 (KS Wkey4 8) (desCore 8 (KS Wkey4 8) (IIP (Join (x,x))))) =
           (desCore 8 (REVERSE (KS Wkey4 8)) (desCore 8 (KS Wkey4 8) (IIP (Join (x,x)))))’
  >- (Rewr'\\
      rw[desCore_CORRECT]\\
      rw[IP_IIP_Inverse,Split_Join_Inverse])
  >> Know ‘(REVERSE (KS Wkey4 8))=(KS Wkey4 8)’
  >- (rw[Wkey4_def]\\
       EVAL_TAC)
  >> rw[]
QED

(* Added by Chun Tian *)
Theorem BIJ_for_weak_keys :
    !x. MEM x Wtextlist ==> ?f. BIJ f x univ(:word32)
Proof
    rw [Wtextlist_def]
 >| [ (* goal 1 (of 4) *)
      Q.EXISTS_TAC ‘w1trans1’ >> rw [BIJ_wtext1],
      (* goal 2 (of 4) *)
      Q.EXISTS_TAC ‘w2trans1’ >> rw [BIJ_wtext2],
      (* goal 3 (of 4) *)
      Q.EXISTS_TAC ‘w3trans1’ >> rw [BIJ_wtext3],
      (* goal 4 (of 4) *)
      Q.EXISTS_TAC ‘w4trans1’ >> rw [BIJ_wtext4] ]
QED

Definition wtrans1_def :
    wtrans1 = [w1trans1;w2trans1;w3trans1;w4trans1]
End

(* Added by Chun Tian *)
Theorem BIJ_for_weak_keys_explicit :
    !i. i < 4 ==> BIJ (EL i wtrans1) (EL i Wtextlist) univ(:word32)
Proof
    NTAC 2 STRIP_TAC
 >> ‘i = 0 \/ i = 1 \/ i = 2 \/ i = 3’ by rw []
 >| [ (* goal 1 (of 4) *)
      rw [wtrans1_def, Wtextlist_def, BIJ_wtext1],
      (* goal 2 (of 4) *)
      rw [wtrans1_def, Wtextlist_def, BIJ_wtext2],
      (* goal 3 (of 4) *)
      rw [wtrans1_def, Wtextlist_def, BIJ_wtext3],
      (* goal 4 (of 4) *)
      rw [wtrans1_def, Wtextlist_def, BIJ_wtext4] ]
QED

Theorem text_num:
   !x. MEM x Wtextlist ==> CARD x= CARD univ(:word32)
Proof
     rw[Wtextlist_def]
  >- (MATCH_MP_TAC FINITE_BIJ_CARD\\
      Q.EXISTS_TAC ‘w1trans1’\\
      CONJ_TAC >- rw[Wtext1_def]\\
      rw[BIJ_wtext1])

  >- (MATCH_MP_TAC FINITE_BIJ_CARD\\
      Q.EXISTS_TAC ‘w2trans1’\\
      CONJ_TAC >- rw[Wtext2_def]\\
      rw[BIJ_wtext2])

  >- (MATCH_MP_TAC FINITE_BIJ_CARD\\
      Q.EXISTS_TAC ‘w3trans1’\\
      CONJ_TAC >- rw[Wtext3_def]\\
      rw[BIJ_wtext3])

  >> MATCH_MP_TAC FINITE_BIJ_CARD
  >> Q.EXISTS_TAC ‘w4trans1’
  >> CONJ_TAC >- rw[Wtext4_def]
  >> rw[BIJ_wtext4]
QED

(* Added by Chun Tian *)
Theorem DES_weak_fp_card :
    !x. MEM x Wtextlist ==> CARD x = 2 ** 32
Proof
    RW_TAC std_ss [GSYM card_word32, BIJ_for_weak_keys]
 >> MATCH_MP_TAC FINITE_BIJ_CARD
 >> ‘FINITE x’ by fs [Wtextlist_def]
 >> simp []
 >> MATCH_MP_TAC BIJ_for_weak_keys >> art []
QED

(* See N. Tihanyi, “Report on the First DES Fixed Points for Non-Weak Keys: Case-Study
   of Hacking an IoT Environment,” IEEE Access, vol. 10, pp. 77802–77809, Jan. 2022.
 *)
Definition non_weak_keys_def :
    non_weak_keys :(word64 # word64) list = [
      (* format: (non-weak key, plaintext) *)
      (0xB0B351C802C83DE0w,0x4739A2F04B7EAB28w);
      (0x5D460701328F2962w,0x9FE10D2E8C496143w);
      (0x4F4CAE37FD37C21Fw,0xB8C65D0FB48154D7w);
      (0xA2B9F8FECD70D69Dw,0x601EF2D173B69EBCw)
    ]
End

(* Added by Chun Tian *)
Theorem DES_fp_non_weak_keys :
    !i. i < LENGTH non_weak_keys ==>
        let (key,plaintext) = EL i non_weak_keys;
            (encrypt,decrypt) = FullDES key
        in
           encrypt plaintext = plaintext
Proof
    rw [non_weak_keys_def, DES_def]
 >> ‘i = 0 \/ i = 1 \/ i = 2 \/ i = 3’ by rw []
 >> rw []
 >> EVAL_TAC
QED

Definition AllpairXor_def:
    AllpairXor (X:word6)= {(x1,x2)| x1 ⊕ x2=X}
End

Definition trans1_def:
  trans1 (x1:word6,x2:word6) = x1
End

Definition trans2_def:
  trans2 (x:word6)= (x,x)
End

Theorem BIJ_XORL:
   BIJ trans1 (AllpairXor 0x0w) univ(:word6)
Proof
     rw[BIJ_IFF_INV]
  >> EXISTS_TAC “trans2”
  >> rw[]

  >- (rw[AllpairXor_def,trans2_def])
  >- (POP_ASSUM MP_TAC\\
      rw[AllpairXor_def,trans2_def,trans1_def]\\
      Know ‘x1 ⊕ x1 ⊕ x2=x1 ⊕ 0w’
      >- RW_TAC fcp_ss[]\\
      rw[WORD_XOR_CLAUSES]
      )

  >>  rw[trans2_def,trans1_def]
QED

Theorem xor_P:
   !x1 x2. P(x1) ⊕ P(x2)=P(x1⊕x2)
Proof
     RW_TAC fcp_ss[P_def,bitwise_perm_def,dimindex_32]
  >> Q.ABBREV_TAC ‘p=(32 − EL (31 − i) P_data)’
  >>Know ‘p<32’
  >-(fs [Abbr ‘p’, dimindex_32] \\
      POP_ASSUM MP_TAC \\
      Q.SPEC_TAC (‘i’, ‘n’) \\
      rpt (CONV_TAC (BOUNDED_FORALL_CONV (SIMP_CONV list_ss [P_data]))) \\
      REWRITE_TAC [])
  >> rw[word_xor_def]
  >> rw[FCP_BETA]
QED

Theorem xor_E:
   !x1 x2. E(x1) ⊕ E(x2)=E(x1⊕x2)
Proof
     RW_TAC fcp_ss[E_def,bitwise_perm_def,dimindex_32,dimindex_48]
  >> Q.ABBREV_TAC ‘p=(32 − EL (47 − i) E_data)’
  >> Know ‘p<32’
  >- (fs [Abbr ‘p’, dimindex_48] \\
      POP_ASSUM MP_TAC \\
      Q.SPEC_TAC (‘i’, ‘n’) \\
      rpt (CONV_TAC (BOUNDED_FORALL_CONV (SIMP_CONV list_ss [E_data]))) \\
      REWRITE_TAC [])
  >> rw[word_xor_def]
  >> rw[FCP_BETA]
QED

Theorem xor_S1:
   ?x1 x2. S1(x1) ⊕ S1(x2)<>S1(x1⊕x2)
Proof
     rw[SBox_def,S1_data]
  >> Q.EXISTS_TAC ‘0b0w’
  >> Q.EXISTS_TAC ‘0b0w’
  >> EVAL_TAC
QED

val _ = export_theory();
val _ = html_theory "des_prop";
