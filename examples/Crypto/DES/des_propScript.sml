(*===========================================================================*)
(*  The Data Encryption Standard (DES) Property in HOL                       *)
(*                                                                           *)
(*  Author: Ruofan Yang                                                      *)
(*===========================================================================*)
Theory des_prop
Ancestors
  arithmetic pair fcp words list sorting pred_set combin des
  measure probability extreal
Libs
  numLib fcpLib wordsLib listLib hurdUtils realLib


val _ = HOLFlags.set_bflag (guessing_word_lengths, true);
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

Theorem compl_IP:
  !m. IP (~m) = ~ (IP m)
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

Theorem compl_E:
  !m. E (~m)= ~ (E m)
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
  !n (k:word64). 17 > n ==>(RK_L n ~k)= ~ (RK_L n k)
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
   !n (k:word64). 17 > n ==>(RK_R n ~k)= ~ (RK_R n k)
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
  >- rw[SNOC_APPEND, Abbr `ks`]
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
      >- RW_TAC fcp_ss[Round_alt_half_message']\\
      Know ‘Round 0 keys' (u',v')= (u',v')’
      >- rw [Round_def]\\
      Know ‘(M (u,v) keys 0,M (u,v) keys (SUC 0))=Round 0 keys (u,v)’
      >- RW_TAC fcp_ss[Round_alt_half_message']\\
      Know ‘Round 0 keys (u,v)= (u,v)’
      >- rw [Round_def]\\
      rw[]
      >| [ (* goal 1 (of 2) *)
           rw [Abbr ‘u'’,Abbr ‘u’] \\
           Know ‘(IP m)= ~ (IP (¬m))’
           >- rw[compl_IP] \\
           rw [compl_extract_1] \\
           rw[],
           (* goal 2 (of 2) *)
           rw [Abbr ‘v'’,Abbr ‘v’]\\
           Know ‘(IP m)= ~ (IP (¬m))’
           >- rw[compl_IP]\\
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
  >> Know ‘E (~M (u,v) keys (x + 1))= ~ E (M (u,v) keys (x + 1))’
  >- rw[compl_E]
  >> Rewr'
  >> Suff ‘EL x keys'= ~ EL x keys’
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
  trans2 X (x:word6)= (x,x?? X)
End

Theorem BIJ_XORL:
   !X. BIJ (trans2 X) univ(:word6) (AllpairXor X)
Proof
     rw[BIJ_IFF_INV]
  >- (rw[AllpairXor_def,trans2_def])

  >> Q.EXISTS_TAC ‘trans1’
  >> rw[]

  >- rw[trans2_def,trans1_def]

  >> POP_ASSUM MP_TAC
  >> rw[AllpairXor_def,trans2_def,trans1_def]
QED

Theorem AllpairXor_card :
    !X. CARD (AllpairXor X) = 2 ** 6
Proof
    Suff ‘!X. 2 ** 6=CARD (AllpairXor X)’
 >- rw[]
 >> RW_TAC std_ss [GSYM card_word6, BIJ_XORL]
 >> MATCH_MP_TAC FINITE_BIJ_CARD
 >> Q.EXISTS_TAC ‘trans2 X’
 >> CONJ_TAC
 >- rw[]
 >> rw[BIJ_XORL]
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

Theorem xor_twice:
   !x1 x2 k. (x1  ?? k) ?? (x2 ?? k) = x1 ?? x2
Proof
    rw[WORD_XOR_CLAUSES]
QED

Theorem xor_Com:
    !x1 x2 k X. (x1 ?? x2)=X ==>
          (E(x1) ?? k) ?? (E(x2) ?? k ) = E(X)
Proof
     rw[xor_twice]
  >> rw[xor_E]
QED

Theorem xor_S1:
   ?x1 x2. S1(x1) ⊕ S1(x2)<>S1(x1⊕x2)
Proof
     rw[SBox_def,S1_data]
  >> Q.EXISTS_TAC ‘0b0w’
  >> Q.EXISTS_TAC ‘0b0w’
  >> EVAL_TAC
QED

Definition S_list_def:
   S_list= [S1;S2;S3;S4;S5;S6;S7;S8]
End

Theorem xor_Sbox:
   !Sbox .?x1 x2.MEM Sbox S_list ==>
       Sbox(x1) ⊕ Sbox(x2)<>Sbox(x1⊕x2)
Proof
     rw[S_list_def]
  >> Q.EXISTS_TAC ‘0b0w’
  >> Q.EXISTS_TAC ‘0b0w’
  >> rw[SBox_def]
  >- (rw[S1_data]\\
      EVAL_TAC)

  >- (rw[S2_data]\\
      EVAL_TAC)

  >- (rw[S3_data]\\
      EVAL_TAC)

  >- (rw[S4_data]\\
      EVAL_TAC)

  >- (rw[S5_data]\\
      EVAL_TAC)

  >- (rw[S6_data]\\
      EVAL_TAC)

  >- (rw[S7_data]\\
      EVAL_TAC)

  >> rw[S8_data]
  >> EVAL_TAC
QED

Theorem xor_trans:
   !x x' k. x ?? k= x' ==> x ?? x'=k
Proof
     WORD_DECIDE_TAC
QED

Definition word6_set1_def:
   word6_set1 (X:word6) (Y:word4) Sb=
       {x | Sb x ⊕ Sb (x ⊕ X) = Y}
End

Definition word6_set2_def:
   word6_set2 (X:word6) (Y:word4) Sb=
       {(x1,x2) | (x1 ?? x2)= X /\Sb x1 ⊕ Sb (x2) = Y}
End

Definition word6_trans1_def:
   (word6_trans1 X) x= (x,x??X)
End

Definition word6_trans2_def:
   word6_trans2 (x1,x2)= x1
End

Theorem BIJ_pairXcY:
   !X Y Sb. BIJ (word6_trans1 X) (word6_set1 X Y Sb) (word6_set2 X Y Sb)
Proof
     rw[BIJ_IFF_INV]
  >- (POP_ASSUM MP_TAC\\
      rw[word6_set2_def,word6_set1_def]\\
      rw[word6_trans1_def])

  >> Q.EXISTS_TAC ‘word6_trans2’
  >> rw[]

  >- (POP_ASSUM MP_TAC\\
      rw[word6_set2_def,word6_set1_def]\\
      rw[word6_trans2_def])

  >- (POP_ASSUM MP_TAC\\
      rw[word6_set1_def]\\
      rw[word6_trans2_def,word6_trans1_def])

  >> POP_ASSUM MP_TAC
  >> rw[word6_set2_def]
  >> rw[word6_trans2_def,word6_trans1_def]
QED

Theorem pairXcY_card :
    ! X Y Sb. CARD (word6_set1 X Y Sb)
                = CARD (word6_set2 X Y Sb)
Proof
    rw[]
 >> MATCH_MP_TAC FINITE_BIJ_CARD
 >> Q.EXISTS_TAC ‘(word6_trans1 X)’
 >> CONJ_TAC
 >- rw[word6_set1_def]
 >> rw[BIJ_pairXcY]
QED

Theorem prob_uniform_on_finite_set :
    !p. FINITE (p_space p) /\ p_space p <> {} /\ events p = POW (p_space
p) /\
        (!s. s IN events p ==> prob p s = &CARD s / &CARD (p_space p)) ==>
        prob_space p
Proof
    rw [p_space_def, events_def, prob_def]
 >> ‘CARD (m_space p) <> 0’ by rw [CARD_EQ_0]
 >> rw [prob_on_finite_set]
 >| [ (* goal 1 (of 3) *)
      rw [positive_def]
      >- (MATCH_MP_TAC zero_div >> rw [extreal_of_num_def]) \\
      qabbrev_tac ‘N = CARD (m_space p)’ \\
     ‘&N = Normal (&N)’ by rw [extreal_of_num_def] >> POP_ORW \\
      MATCH_MP_TAC le_div \\
      rw [extreal_lt_eq, extreal_of_num_def],
      (* goal 2 (of 3) *)
      rw [prob_def, p_space_def] \\
     ‘m_space p IN measurable_sets p’ by rw [IN_POW] \\
      rw [] \\
      MATCH_MP_TAC div_refl >> rw [extreal_of_num_def],
      (* goal 3 (of 3) *)
      rw [additive_def] \\
      Know ‘CARD (s UNION t) = CARD s + CARD t’
      >- (MATCH_MP_TAC CARD_UNION_DISJOINT >> art [] \\
          fs [IN_POW] \\
          CONJ_TAC \\ (* 2 subgoals, same tactics *)
          MATCH_MP_TAC SUBSET_FINITE_I >> Q.EXISTS_TAC ‘m_space p’ >> art
[]) >> Rewr' \\
      Know ‘&(CARD s + CARD t) = &CARD s + (&CARD t :extreal)’
      >- rw [extreal_of_num_def, extreal_add_def] >> Rewr' \\
      ONCE_REWRITE_TAC [EQ_SYM_EQ] \\
      MATCH_MP_TAC div_add >> rw [extreal_of_num_def] ]
QED

Definition word6x6_def:
   word6x6=(univ(:word6 # word6),
             POW (univ(:word6 # word6)),
             (\s:(word6 # word6) set.
               (&(CARD s))/(&(2 ** 12)) :extreal))
End

Theorem prob_space_word6x6:
   prob_space word6x6
Proof
     MATCH_MP_TAC prob_uniform_on_finite_set
  >> rw[]

  >- (rw[p_space_def]\\
      rw[word6x6_def])

  >- (rw[p_space_def]\\
      rw[word6x6_def])

  >- (rw[p_space_def,events_def]\\
      rw[word6x6_def])

  >> rw[prob_def]
  >> rw[word6x6_def]
  >> rw[p_space_def]
  >> Suff ‘&CARD 𝕌(:word6 # word6)=4096’
  >- rw[]
  >> Know ‘CARD 𝕌(:word6 # word6)=CARD 𝕌(:word6)*CARD 𝕌(:word6)’
  >- (rw[CROSS_UNIV]\\
      rw[CARD_CROSS])
  >> rw[card_word6]
QED

Definition word6p_def:
   word6p=(univ(:word6),
             POW (univ(:word6)),
             (\s:(word6) set.
               (&(CARD s))/(&(2 ** 6)) :extreal))
End

Theorem prob_space_word6p:
   prob_space word6p
Proof
     MATCH_MP_TAC prob_uniform_on_finite_set
  >> rw[]

  >- (rw[p_space_def]\\
      rw[word6p_def])

  >- (rw[p_space_def,events_def]\\
      rw[word6p_def])

  >> rw[prob_def]
  >> rw[word6p_def]
  >> rw[p_space_def]
  >> rw[card_word6]
QED

Definition XcauseYp_def :
   XcauseYp X Y Sb p <=>
   prob word6p {x| Sb(x) ?? Sb(x ?? X)= Y}=p
End

Definition XcauseY_def :
   XcauseY X Y Sb =
   prob word6p {x| Sb(x) ?? Sb(x ?? X)= Y}
End

Theorem word6p_convert:
   {x | S1 x ⊕ S1 (x ⊕ 52w) = 4w} = {0x13w;0x27w}
Proof
     rw[EXTENSION]
  >> CONV_TAC(UNBETA_CONV “x:word6”)
  >> Q.MATCH_ABBREV_TAC ‘f (x:word6)’
  >> Q.ID_SPEC_TAC ‘x’
  >> Suff ‘!i:num. i<64 ==> f (n2w i) ’
  >- (rpt STRIP_TAC \\
      POP_ASSUM (MP_TAC o Q.SPEC ‘w2n (x:word6)’)\\
      MP_TAC (Q.ISPEC ‘x:word6’ w2n_lt)\\
      simp[dimword_6])
  >> rpt (CONV_TAC (BOUNDED_FORALL_CONV (SIMP_CONV (srw_ss()) []))\\
          CONJ_TAC
          >- (rw[Abbr ‘f’]\\
              EVAL_TAC)
             )
  >> rw[]
QED

Theorem XcauseYp_test:
   XcauseYp 0x34w 0x4w S1 (2/64)
Proof
     rw[XcauseYp_def]
  >> rw[word6p_def]
  >> rw[prob_def]
  >> Suff ‘&CARD {x | S1 x ⊕ S1 (x ⊕ 52w) = 4w}=2’
  >- rw[]
  >> rw[word6p_convert]
QED

Definition word48Xor_def:
    word48Xor (X:word48)= {(x1,x2)| x1 ⊕ x2=X}
End

Definition trans48_1_def:
  trans48_1 (x1:word48,x2:word48) = x1
End

Definition trans48_2_def:
  trans48_2 X (x:word48)= (x,x?? X)
End

Theorem BIJ_XOR48:
   !X. BIJ (trans48_2 X) univ(:word48) (word48Xor X)
Proof
     rw[BIJ_IFF_INV]
  >- (rw[word48Xor_def,trans48_2_def])

  >> Q.EXISTS_TAC ‘trans48_1’
  >> rw[]

  >- rw[trans48_2_def,trans48_1_def]

  >> POP_ASSUM MP_TAC
  >> rw[word48Xor_def,trans48_2_def,trans48_1_def]
QED

Theorem word48Xor_card :
    !X. CARD (word48Xor X) = 2 ** 48
Proof
    Suff ‘!X. 2 ** 48=CARD (word48Xor X)’
 >- rw[]
 >> RW_TAC std_ss [GSYM card_word48, BIJ_XOR48]
 >> MATCH_MP_TAC FINITE_BIJ_CARD
 >> Q.EXISTS_TAC ‘trans48_2 X’
 >> CONJ_TAC
 >- rw[]
 >> rw[BIJ_XOR48]
QED

Definition word48_set1_def:
   word48_set1 (X:word32) (Y:word32)=
       {x | S x ⊕ S (x ⊕ E(X)) = Y}
End

Definition word48_set2_def:
   word48_set2 (X:word32) (Y:word32)=
       {(x1,x2) | x1 ?? x2= E(X) /\ S x1 ⊕ S (x2) = Y}
End

Definition word48_trans1_def:
   (word48_trans1 X) x= (x,x ?? E(X))
End

Definition word48_trans2_def:
   word48_trans2 (x1,x2) = (x1)
End

Theorem BIJ_pairXcYF:
   !X Y. BIJ (word48_trans1 X) (word48_set1 X Y) (word48_set2 X Y)
Proof
     rw[BIJ_IFF_INV]
  >- (POP_ASSUM MP_TAC\\
      rw[word48_set2_def,word48_set1_def]\\
      rw[word48_trans1_def])

  >> Q.EXISTS_TAC ‘word48_trans2’
  >> rw[]

  >- (POP_ASSUM MP_TAC\\
      rw[word48_set2_def,word48_set1_def]\\
      rw[word48_trans2_def]\\
      Know ‘(x1 ⊕ E X)=x2’
      >- rw[xor_trans]\\
      Rewr'\\
      rw[])

  >- (POP_ASSUM MP_TAC\\
      rw[word48_set1_def]\\
      rw[word48_trans2_def,word48_trans1_def])

  >> POP_ASSUM MP_TAC
  >> rw[word48_set2_def]
  >> rw[word48_trans2_def,word48_trans1_def]
  >> rw[xor_trans]
QED

Theorem pairXcYF_card :
    ! X Y. CARD (word48_set1 X Y)
                = CARD (word48_set2 X Y)
Proof
    rw[]
 >> MATCH_MP_TAC FINITE_BIJ_CARD
 >> Q.EXISTS_TAC ‘(word48_trans1 X)’
 >> CONJ_TAC
 >- rw[word48_set1_def]
 >> rw[BIJ_pairXcYF]
QED

Definition word48p_def:
   word48p=(univ(:word48),
             POW (univ(:word48)),
             (\s:(word48) set.
               (&(CARD s))/(&(2 ** 48)) :extreal))
End

Theorem prob_space_word48p:
   prob_space word48p
Proof
     MATCH_MP_TAC prob_uniform_on_finite_set
  >> rw[]

  >- (rw[p_space_def]\\
      rw[word48p_def])

  >- (rw[p_space_def,events_def]\\
      rw[word48p_def])

  >> rw[prob_def]
  >> rw[word48p_def]
  >> rw[p_space_def]
  >> rw[card_word48]
QED

Definition XcauseYFkey_def:
   XcauseYFkey (X:word32) (Y:word32) (x:word48)=
     let x'= x?? E(X) in
        prob word48p {k| S(x ?? k) ?? S(x' ?? k)= Y}
End

Definition XcauseYFp'_def:
   XcauseYF' (X:word32) (Y:word32) p <=>
     prob word48p {x| S(x) ?? S(x ?? E(X))= Y}=p
End

Definition XcauseYF'_def:
   XcauseYF' (X:word32) (Y:word32) =
     prob word48p {x| S(x) ?? S(x ?? E(X))= Y}
End

Definition splitXF_def:
   splitXF (Xe:word48)=[(5><0) Xe; (11><6) Xe;(17><12) Xe;(23><18) Xe ;(29><24) Xe;(35><30) Xe ;(41><36) Xe;(47><42) Xe]
End

Definition splitYF_def:
   splitYF (Ye:word32)=[(3><0) Ye; (7><4) Ye;(11><8) Ye;(15><12) Ye ;(19><16) Ye;(23><20) Ye ;(27><24) Ye;(31><28) Ye]
End

Definition S_data_def:
   S_data=[S8_data;S7_data;S6_data;S5_data;S4_data;S3_data;S2_data;S1_data]
End

Definition XpairF_def:
   XpairF X (Y:word32)= {(x1,x2,x3,x4,x5,x6,x7,x8) | S8 x8 ⊕ S8 (x8 ⊕ (5 >< 0) (E X)) = (3 >< 0) Y /\ S7 x7 ⊕ S7 (x7 ⊕ (11 >< 6) (E X)) = (7 >< 4) Y /\S6 x6 ⊕ S6 (x6 ⊕ (17 >< 12) (E X)) = (11 >< 8) Y /\ S5 x5 ⊕ S5 (x5 ⊕ (23 >< 18) (E X)) = (15 >< 12) Y /\ S4 x4 ⊕ S4 (x4 ⊕ (29 >< 24) (E X)) = (19 >< 16) Y /\ S3 x3 ⊕ S3 (x3 ⊕ (35 >< 30) (E X)) = (23 >< 20) Y /\ S2 x2 ⊕ S2 (x2 ⊕ (41 >< 36) (E X)) = (27 >< 24) Y /\S1 x1 ⊕ S1 (x1 ⊕ (47 >< 42) (E X)) = (31 >< 28) Y}
End

Theorem F_convert:
   !X Y. XpairF X (Y:word32) =
   ({x | S1 x ⊕ S1 (x ⊕ (47 >< 42) (E X)) = (31 >< 28) Y}) CROSS
   ({x | S2 x ⊕ S2 (x ⊕ (41 >< 36) (E X)) = (27 >< 24) Y}) CROSS
   ({x | S3 x ⊕ S3 (x ⊕ (35 >< 30) (E X)) = (23 >< 20) Y}) CROSS
   ({x | S4 x ⊕ S4 (x ⊕ (29 >< 24) (E X)) = (19 >< 16) Y}) CROSS
   ({x | S5 x ⊕ S5 (x ⊕ (23 >< 18) (E X)) = (15 >< 12) Y}) CROSS
   ({x | S6 x ⊕ S6 (x ⊕ (17 >< 12) (E X)) = (11 >< 8) Y}) CROSS
   ({x | S7 x ⊕ S7 (x ⊕ (11 >< 6) (E X)) = (7 >< 4) Y} ) CROSS
   ({x | S8 x ⊕ S8 (x ⊕ (5 >< 0) (E X)) = (3 >< 0) Y})
Proof
     rw[XpairF_def]
  >> rw[EXTENSION]
  >> ONCE_REWRITE_TAC [GSYM PAIR]
  >> rw[]
  >> ONCE_REWRITE_TAC [GSYM PAIR]
  >> rw[]
  >> ONCE_REWRITE_TAC [GSYM PAIR]
  >> rw[]
  >> ONCE_REWRITE_TAC [GSYM PAIR]
  >> rw[]
  >> ONCE_REWRITE_TAC [GSYM PAIR]
  >> rw[]
  >> ONCE_REWRITE_TAC [GSYM PAIR]
  >> rw[]
  >> ONCE_REWRITE_TAC [GSYM PAIR]
  >> rw[]
  >> WORD_DECIDE_TAC
QED

Definition transF1_def:
  transF1 ((x1,x2,x3,x4,x5,x6,x7,x8):word6 # word6 # word6 # word6 # word6 # word6 # word6 # word6)= x1@@ x2@@ x3@@ x4@@ x5@@ x6@@ x7@@ x8
End

Definition transF2_def:
  transF2 (x:word48)= ((47 >< 42) x,(41 >< 36) x,(35 >< 30) x,(29 >< 24) x,(23 >< 18) x,(17 >< 12) x,(11 >< 6) x,(5 >< 0) x)
End

Theorem BIJ_F:
   !X Y. BIJ transF2 {x | S x ⊕ S (x ⊕ E X) = Y} (XpairF X Y)
Proof
     rw[XpairF_def]
  >> rw[BIJ_IFF_INV]
  >- (Q.EXISTS_TAC ‘(47 >< 42) x’\\
      Q.EXISTS_TAC ‘(41 >< 36) x’\\
      Q.EXISTS_TAC ‘(35 >< 30) x’\\
      Q.EXISTS_TAC ‘(29 >< 24) x’\\
      Q.EXISTS_TAC ‘(23 >< 18) x’\\
      Q.EXISTS_TAC ‘(17 >< 12) x’\\
      Q.EXISTS_TAC ‘(11 >< 6) x’\\
      Q.EXISTS_TAC ‘(5 >< 0) x’\\
      rw[transF2_def]
      >> (rw[S_def]\\
          WORD_DECIDE_TAC))

  >> Q.EXISTS_TAC ‘transF1’
  >> rw[]

  >- (rw[transF1_def]\\
     rw[S_def]\\
     Know ‘(5 >< 0) (x1 @@ x2 @@ x3 @@ x4 @@ x5 @@ x6 @@ x7 @@ x8)= x8’
     >- WORD_DECIDE_TAC\\
     Rewr'\\
     Know ‘(11 >< 6)(x1 @@ x2 @@ x3 @@ x4 @@ x5 @@ x6 @@ x7 @@ x8)= x7’
     >- WORD_DECIDE_TAC\\
     Rewr'\\
     Know ‘(17 >< 12)(x1 @@ x2 @@ x3 @@ x4 @@ x5 @@ x6 @@ x7 @@ x8)= x6’
     >- WORD_DECIDE_TAC\\
     Rewr'\\
     Know ‘(23 >< 18)(x1 @@ x2 @@ x3 @@ x4 @@ x5 @@ x6 @@ x7 @@ x8)= x5’
     >- WORD_DECIDE_TAC\\
     Rewr'\\
     Know ‘(29 >< 24)(x1 @@ x2 @@ x3 @@ x4 @@ x5 @@ x6 @@ x7 @@ x8)= x4’
     >- WORD_DECIDE_TAC\\
     Rewr'\\
     Know ‘(35 >< 30)(x1 @@ x2 @@ x3 @@ x4 @@ x5 @@ x6 @@ x7 @@ x8)= x3’
     >- WORD_DECIDE_TAC\\
     Rewr'\\
     Know ‘(41 >< 36)(x1 @@ x2 @@ x3 @@ x4 @@ x5 @@ x6 @@ x7 @@ x8)= x2’
     >- WORD_DECIDE_TAC\\
     Rewr'\\
     Know ‘(47 >< 42)(x1 @@ x2 @@ x3 @@ x4 @@ x5 @@ x6 @@ x7 @@ x8)= x1’
     >- WORD_DECIDE_TAC\\
     Rewr'\\
     Know ‘(5 >< 0) (E X ⊕ x1 @@ x2 @@ x3 @@ x4 @@ x5 @@ x6 @@ x7 @@ x8)= (x8 ⊕ (5 >< 0) (E X))’
     >- WORD_DECIDE_TAC\\
     Rewr'\\
     Know ‘(11 >< 6) (E X ⊕ x1 @@ x2 @@ x3 @@ x4 @@ x5 @@ x6 @@ x7 @@ x8)= (x7 ⊕ (11 >< 6) (E X))’
     >- WORD_DECIDE_TAC\\
     Rewr'\\
     Know ‘(17 >< 12) (E X ⊕ x1 @@ x2 @@ x3 @@ x4 @@ x5 @@ x6 @@ x7 @@ x8)= (x6 ⊕ (17 >< 12) (E X))’
     >- WORD_DECIDE_TAC\\
     Rewr'\\
     Know ‘(23 >< 18) (E X ⊕ x1 @@ x2 @@ x3 @@ x4 @@ x5 @@ x6 @@ x7 @@ x8)= (x5 ⊕ (23 >< 18) (E X))’
     >- WORD_DECIDE_TAC\\
     Rewr'\\
     Know ‘(29 >< 24) (E X ⊕ x1 @@ x2 @@ x3 @@ x4 @@ x5 @@ x6 @@ x7 @@ x8)= (x4 ⊕ (29 >< 24) (E X))’
     >- WORD_DECIDE_TAC\\
     Rewr'\\
     Know ‘(35 >< 30) (E X ⊕ x1 @@ x2 @@ x3 @@ x4 @@ x5 @@ x6 @@ x7 @@ x8)= (x3 ⊕ (35 >< 30) (E X))’
     >- WORD_DECIDE_TAC\\
     Rewr'\\
     Know ‘(41 >< 36) (E X ⊕ x1 @@ x2 @@ x3 @@ x4 @@ x5 @@ x6 @@ x7 @@ x8)= (x2 ⊕ (41 >< 36) (E X))’
     >- WORD_DECIDE_TAC\\
     Rewr'\\
     Know ‘(47 >< 42) (E X ⊕ x1 @@ x2 @@ x3 @@ x4 @@ x5 @@ x6 @@ x7 @@ x8)= (x1 ⊕ (47 >< 42) (E X))’
     >- WORD_DECIDE_TAC\\
     Rewr'\\
     Know ‘((w2w (S8 x8) ‖ w2w (S1 x1) << 28 ‖ w2w (S2 x2) << 24 ‖
         w2w (S3 x3) << 20 ‖ w2w (S4 x4) << 16 ‖ w2w (S5 x5) << 12 ‖
         w2w (S6 x6) << 8 ‖ w2w (S7 x7) << 4) ⊕
        (w2w (S8 (x8 ⊕ (5 >< 0) (E X))) ‖
         w2w (S1 (x1 ⊕ (47 >< 42) (E X))) << 28 ‖
         w2w (S2 (x2 ⊕ (41 >< 36) (E X))) << 24 ‖
         w2w (S3 (x3 ⊕ (35 >< 30) (E X))) << 20 ‖
         w2w (S4 (x4 ⊕ (29 >< 24) (E X))) << 16 ‖
         w2w (S5 (x5 ⊕ (23 >< 18) (E X))) << 12 ‖
         w2w (S6 (x6 ⊕ (17 >< 12) (E X))) << 8 ‖
         w2w (S7 (x7 ⊕ (11 >< 6) (E X))) << 4))=
         (w2w (S8 x8) ⊕ w2w (S8 (x8 ⊕ (5 >< 0) (E X))) ‖
        w2w((S1 x1) ⊕ (S1 (x1 ⊕ (47 >< 42) (E X)))) << 28 ‖
        w2w((S2 x2) ⊕ (S2 (x2 ⊕ (41 >< 36) (E X)))) << 24 ‖
        w2w((S3 x3) ⊕ (S3 (x3 ⊕ (35 >< 30) (E X)))) << 20 ‖
        w2w((S4 x4) ⊕ (S4 (x4 ⊕ (29 >< 24) (E X)))) << 16 ‖
        w2w((S5 x5) ⊕ (S5 (x5 ⊕ (23 >< 18) (E X)))) << 12 ‖
        w2w((S6 x6) ⊕ (S6 (x6 ⊕ (17 >< 12) (E X)))) << 8 ‖
        w2w((S7 x7) ⊕ (S7 (x7 ⊕ (11 >< 6) (E X)))) << 4):word32’
     >- WORD_DECIDE_TAC\\
     Rewr'\\
     rw[WORD_w2w_OVER_BITWISE]\\
     WORD_DECIDE_TAC)

  >- (rw[transF2_def,transF1_def]\\
      WORD_DECIDE_TAC)

  >> rw[transF1_def,transF2_def]
  >> WORD_DECIDE_TAC
QED

Theorem CARD_eqF:
   !X Y. CARD ({x | S x ⊕ S (x ⊕ E X) = Y} )=
   CARD (XpairF X Y)
Proof
     rw[]
  >> MATCH_MP_TAC FINITE_BIJ_CARD
  >> Q.EXISTS_TAC ‘transF2’
  >> CONJ_TAC
  >- rw[]
  >> rw[BIJ_F]
QED

Theorem XcauseYFp_eq:
   !X Y. Xe=E(X) /\ Xl= splitXF Xe/\ Yl= splitYF Y  ==>
   XcauseYF' X Y = EXTREAL_PROD_IMAGE (λi. XcauseY (EL i Xl) (EL i Yl) (SBox(EL i S_data))) (count 8)
Proof
     rw[]
  >> Know ‘8=SUC 7’
  >- rw[]
  >> Rewr'
  >> rw[EXTREAL_PROD_IMAGE_COUNT_SUC]
  >> Know ‘7=SUC 6’
  >- rw[]
  >> Rewr'
  >> rw[EXTREAL_PROD_IMAGE_COUNT_SUC]
  >> Know ‘6=SUC 5’
  >- rw[]
  >> Rewr'
  >> rw[EXTREAL_PROD_IMAGE_COUNT_SUC]
  >> Know ‘5=SUC 4’
  >- rw[]
  >> Rewr'
  >> rw[EXTREAL_PROD_IMAGE_COUNT_SUC]
  >> Know ‘4=SUC 3’
  >- rw[]
  >> Rewr'
  >> rw[EXTREAL_PROD_IMAGE_COUNT_SUC]
  >> Know ‘3=SUC 2’
  >- rw[]
  >> Rewr'
  >> rw[EXTREAL_PROD_IMAGE_COUNT_SUC]
  >> Know ‘2=SUC 1’
  >- rw[]
  >> Rewr'
  >> rw[EXTREAL_PROD_IMAGE_COUNT_SUC]
  >> rw[splitXF_def,splitYF_def,S_data_def]
  >> rw[XcauseY_def,XcauseYF'_def]
  >> rw[word6p_def,word48p_def]
  >> rw[prob_def]
  >> rw[CARD_eqF]
  >> rw[F_convert]
  >> rw[CARD_CROSS]
  >> Q.ABBREV_TAC ‘n1=CARD {x | S1 x ⊕ S1 (x ⊕ (47 >< 42) (E X)) = (31 >< 28) Y}’
  >> Q.ABBREV_TAC ‘n2=CARD {x | S2 x ⊕ S2 (x ⊕ (41 >< 36) (E X)) = (27 >< 24) Y}’
  >> Q.ABBREV_TAC ‘n3=CARD {x | S3 x ⊕ S3 (x ⊕ (35 >< 30) (E X)) = (23 >< 20) Y} ’
  >>  Q.ABBREV_TAC ‘n4=CARD {x | S4 x ⊕ S4 (x ⊕ (29 >< 24) (E X)) = (19 >< 16) Y}’
  >>  Q.ABBREV_TAC ‘n5=CARD {x | S5 x ⊕ S5 (x ⊕ (23 >< 18) (E X)) = (15 >< 12) Y}’
  >>  Q.ABBREV_TAC ‘n6=CARD {x | S6 x ⊕ S6 (x ⊕ (17 >< 12) (E X)) = (11 >< 8) Y}’
  >> Q.ABBREV_TAC ‘n7= CARD {x | S7 x ⊕ S7 (x ⊕ (11 >< 6) (E X)) = (7 >< 4) Y}’
  >> Q.ABBREV_TAC ‘n8=CARD {x | S8 x ⊕ S8 (x ⊕ (5 >< 0) (E X)) = (3 >< 0) Y}’
  >> rw[extreal_of_num_def]
  >> rw[div_eq_mul_linv]
  >> rw[extreal_inv_eq]
  >> rw[extreal_mul_eq]
QED

Definition transktoxF_def:
  transktoxF (x:word48) k= k ?? x
End

Definition transxtokF_def:
  transxtokF (x:word48) x'=x ?? x'
End

Theorem BIJ_ktox:
   !X Y x. BIJ (transktoxF x) {k | S (k ⊕ x) ⊕ S (k ⊕ x ⊕ E X) = Y} {x | S x ⊕ S (x ⊕ E X) = Y}
Proof
     rw[BIJ_IFF_INV]

  >- (rw[transktoxF_def])

  >> Q.EXISTS_TAC‘transxtokF x’
  >> rw[]
  >- (rw[transxtokF_def])

  >- rw[transktoxF_def,transxtokF_def]

  >> rw[transktoxF_def,transxtokF_def]
QED

Theorem CARD_kxeq:
   !X Y x. CARD {k | S (k ⊕ x) ⊕ S (k ⊕ x ⊕ E X) = Y}=CARD {x | S x ⊕ S (x ⊕ E X) = Y}
Proof
     rw[]
  >> MATCH_MP_TAC FINITE_BIJ_CARD
  >> Q.EXISTS_TAC ‘transktoxF x’
  >> CONJ_TAC
  >- rw[]
  >> rw[BIJ_ktox]
QED

Theorem XcauseYF_convert:
   !X Y x. XcauseYFkey X Y x= XcauseYF' X Y
Proof
     rw[XcauseYFkey_def,XcauseYF'_def]
  >> rw[word48p_def]
  >> rw[prob_def]
  >> Suff ‘CARD {k | S (k ⊕ x) ⊕ S (k ⊕ x ⊕ E X) = Y}=
           CARD {x | S x ⊕ S (x ⊕ E X) = Y}’
  >- rw[]
  >> rw[CARD_kxeq]
QED

Definition charapairDES_def:
   charapairDES (X:word64) (Yl:32 word list) 0= ((31 >< 0) X, (EL 0 Yl)) /\
   charapairDES X Yl (SUC n)=
      if (SUC n) = 1 then (((63 >< 32) X) ?? (EL 0 Yl), (EL 1 Yl))
      else let ((Xin,Xout)= charapairDES X Yl (n-1))
         in (Xin ?? (EL n Yl), (EL (SUC n) Yl))
End

Definition characterDES_def:
   characterDES (X:word64) (Y:word64) Yl= let
      XorR= GENLIST (λi. charapairDES X Yl i) (LENGTH Yl) in (X,XorR,Y)
End

val _ = html_theory "des_prop";
