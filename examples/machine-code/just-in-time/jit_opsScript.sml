
open HolKernel boolLib bossLib Parse;
open pred_setTheory arithmeticTheory pairTheory listTheory wordsTheory;
open addressTheory set_sepTheory progTheory prog_x86Theory;
open wordsLib x86_encodeLib helperLib;

open jit_inputTheory;

val _ = new_theory "jit_ops";

val _ = prog_x86Lib.set_x86_code_write_perm_flag true;

(* informal invariant

  eax - top of stack
  edi - point to top of rest of stack

*)

(* sub  is 2B07 i.e. x86_encode "sub eax,[edi]" *)
(* prog_x86Lib.x86_spec (x86_encode "jb 2000") *)


val X86_IMMEDIATE_def = Define `
  X86_IMMEDIATE (w:word32) =
    [w2w w; w2w (w >>> 8); w2w (w >>> 16); w2w (w >>> 24)]:word8 list`;

val X86_ENCODE_def = Define `
  (X86_ENCODE t (iPOP)    = [0x8Bw; 0x07w; 0x83w; 0xC7w; 0x04w]) /\
  (X86_ENCODE t (iSUB)    = [0x2Bw; 0x07w]) /\
  (X86_ENCODE t (iSWAP)   = [0x87w; 0x07w]) /\
  (X86_ENCODE t (iSTOP)   = [0xFFw; 0xE2w]) /\
  (X86_ENCODE t (iPUSH i) = [0x83w; 0xEFw; 0x04w; 0x89w; 0x07w; 0xB8w; w2w i; 0x00w; 0x00w; 0x00w]) /\
  (X86_ENCODE t (iJUMP i) = [0xE9w] ++ X86_IMMEDIATE (t (w2n i) - 5w)) /\
  (X86_ENCODE t (iJEQ i)  = [0x3Bw;0x07w;0x0Fw;0x84w] ++ X86_IMMEDIATE (t (w2n i) - 8w)) /\
  (X86_ENCODE t (iJLT i)  = [0x3Bw;0x07w;0x0Fw;0x82w] ++ X86_IMMEDIATE (t (w2n i) - 8w))`;

val xENC_LENGTH_def = Define `
  (xENC_LENGTH x = n2w (LENGTH (X86_ENCODE (\w. 0w) x)):word32)`;

val ADDR_def = Define `
  (ADDR ns a 0 = a) /\
  (ADDR [] a p = a) /\
  (ADDR (n::ns) a (SUC p) = ADDR ns (a + xENC_LENGTH n) p)`;

val xLIST_def = Define `
  (xLIST a [] = emp) /\
  (xLIST a (x::xs) = xM a x * xLIST (a + 4w) xs)`;

val xSPACE_def = Define `
  (xSPACE a 0 = emp) /\
  (xSPACE a (SUC n) = ~xM (a - 4w) * xSPACE (a - 4w) n)`;

val xSTACK_def = Define `
  (xSTACK ([],l,p:num,ns:input_type list) = SEP_F) /\
  (xSTACK (x::xs,l,p,ns) =
    SEP_EXISTS edi. xR EAX x * xR EDI edi * cond (ALIGNED edi) *
                    xLIST edi xs * xSPACE edi l)`;

val xJIT_INV_def = Define `
  xJIT_INV (xs,l,p,ns) a =
    xSTACK (xs,l,p,ns) * xPC (ADDR ns a p) * ~xS`;

val BYTES_IN_MEM_def = Define `
  (BYTES_IN_MEM a df f [] <=> T) /\
  (BYTES_IN_MEM a df f (b::bs) <=>
     a IN df /\ (f a = b) /\ BYTES_IN_MEM (a+1w) df f bs)`;

val CODE_IN_MEM_def = Define `
  CODE_IN_MEM (xs,l,p,ns) a df f =
  !p n. (iFETCH p ns = SOME n) ==>
        let branch = (\j. ADDR ns a j - ADDR ns a p) in
          BYTES_IN_MEM (ADDR ns a p) df f (X86_ENCODE branch n)`;

val ADDR_ADD1 = prove(
  ``!ns a p.
      (iFETCH p ns = SOME x) ==>
      (ADDR ns a (p + 1) = ADDR ns a p + n2w (LENGTH (X86_ENCODE branch x)))``,
  Induct \\ SIMP_TAC std_ss [iFETCH_def]
  \\ REPEAT STRIP_TAC \\ REVERSE (Cases_on `p`) THEN1
   (FULL_SIMP_TAC std_ss [ADDR_def,TL,HD,DECIDE ``SUC n + 1 = SUC (n + 1)``]
    \\ FULL_SIMP_TAC std_ss [DECIDE ``~(SUC n = 0)``])
  \\ FULL_SIMP_TAC std_ss [ADDR_def]
  \\ SIMP_TAC bool_ss [DECIDE ``1 = SUC 0``,ADDR_def,HD,xENC_LENGTH_def]
  \\ Cases_on `ns` \\ FULL_SIMP_TAC std_ss [ADDR_def]
  \\ Cases_on `x`
  \\ SIMP_TAC std_ss [X86_ENCODE_def,LENGTH,X86_IMMEDIATE_def,APPEND]);

val SPEC_X86_MODEL_IN_BYTE_MEM = store_thm("SPEC_X86_MODEL_IN_BYTE_MEM",
  ``SPEC X86_MODEL p {(a,xs,T)} q ==>
    (BYTES_IN_MEM a df f xs ==> SPEC X86_MODEL p (xCODE_SET df f) q)``,
  REWRITE_TAC [prog_x86Theory.X86_SPEC_EXLPODE_CODE] \\ REPEAT STRIP_TAC
  \\ MATCH_MP_TAC ((GEN_ALL o RW [AND_IMP_INTRO] o DISCH_ALL o SPEC_ALL o
       UNDISCH_ALL o SPEC_ALL) progTheory.SPEC_SUBSET_CODE)
  \\ Q.EXISTS_TAC `{(a + n2w n,[EL n xs],T) | n | n < LENGTH xs}`
  \\ ASM_SIMP_TAC std_ss [SUBSET_DEF,GSPECIFICATION,prog_x86Theory.xCODE_SET_def]
  \\ REPEAT STRIP_TAC \\ ASM_SIMP_TAC std_ss [CONS_11]
  \\ Q.PAT_X_ASSUM `x = bb` (K ALL_TAC)
  \\ Q.PAT_X_ASSUM `SPEC x p c q` (K ALL_TAC)
  \\ REPEAT (POP_ASSUM MP_TAC)
  \\ Q.SPEC_TAC (`a`,`a`) \\ Q.SPEC_TAC (`n`,`n`) \\ Induct_on `xs`
  \\ SIMP_TAC std_ss [LENGTH,BYTES_IN_MEM_def]
  \\ NTAC 4 STRIP_TAC
  \\ Cases_on `n`
  \\ FULL_SIMP_TAC std_ss [EL,WORD_ADD_0,HD,TL,RW1[ADD_COMM]ADD1]
  \\ FULL_SIMP_TAC std_ss [GSYM word_add_n2w,WORD_ADD_ASSOC]);

val SPEC_EXISTS_EXISTS = store_thm("SPEC_EXISTS_EXISTS",
  ``(!x. SPEC m (p x) c (q x)) ==> SPEC m (SEP_EXISTS x. p x) c (SEP_EXISTS x. q x)``,
  SIMP_TAC std_ss [GSYM SPEC_PRE_EXISTS]
  \\ REPEAT STRIP_TAC
  \\ POP_ASSUM (ASSUME_TAC o Q.SPEC `x`)
  \\ `SEP_IMP (q x) (SEP_EXISTS x. q x)` by
    (SIMP_TAC std_ss [SEP_IMP_def,SEP_EXISTS] \\ METIS_TAC [])
  \\ IMP_RES_TAC SPEC_WEAKEN);

val SPEC_EXISTS_EXISTS_POP = store_thm("SPEC_EXISTS_EXISTS_POP",
  ``(!x. SPEC m (p x) c (q (x + 4w))) ==> SPEC m (SEP_EXISTS x. p x) c (SEP_EXISTS x. q x)``,
  SIMP_TAC std_ss [GSYM SPEC_PRE_EXISTS]
  \\ REPEAT STRIP_TAC
  \\ POP_ASSUM (ASSUME_TAC o Q.SPEC `x`)
  \\ `SEP_IMP (q (x + 4w)) (SEP_EXISTS x. q x)` by
    (SIMP_TAC std_ss [SEP_IMP_def,SEP_EXISTS] \\ METIS_TAC [])
  \\ IMP_RES_TAC SPEC_WEAKEN);

val SPEC_EXISTS_EXISTS_PUSH = store_thm("SPEC_EXISTS_EXISTS_PUSH",
  ``(!x. SPEC m (p x) c (q (x - 4w))) ==> SPEC m (SEP_EXISTS x. p x) c (SEP_EXISTS x. q x)``,
  SIMP_TAC std_ss [GSYM SPEC_PRE_EXISTS]
  \\ REPEAT STRIP_TAC
  \\ POP_ASSUM (ASSUME_TAC o Q.SPEC `x`)
  \\ `SEP_IMP (q (x - 4w)) (SEP_EXISTS x. q x)` by
    (SIMP_TAC std_ss [SEP_IMP_def,SEP_EXISTS] \\ METIS_TAC [])
  \\ IMP_RES_TAC SPEC_WEAKEN);

val sub_lemma = let
  val (spec,_,s,_) = prog_x86Lib.x86_tools
  val ((th,_,_),_) = spec "2B07"
  val th = HIDE_STATUS_RULE true s th
  val th = SIMP_RULE (bool_ss++sep_cond_ss) [SPEC_MOVE_COND,ALIGNED_INTRO] th
  val th = Q.INST [`df`|->`{edi}`] (DISCH_ALL th)
  val th = INST [``f:word32->word32``|->``\x:word32.(w:word32)``] (DISCH_ALL th)
  val th = SIMP_RULE std_ss [IN_INSERT,NOT_IN_EMPTY,xM_THM] th
  val th = SIMP_RULE bool_ss [GSYM SPEC_MOVE_COND] th
  in save_thm("sub_lemma",th) end;

val swap_lemma = let
  val (spec,_,s,_) = prog_x86Lib.x86_tools
  val ((th,_,_),thi) = spec "8707"
  val th = HIDE_STATUS_RULE true s th
  val th = SIMP_RULE (bool_ss++sep_cond_ss) [SPEC_MOVE_COND,ALIGNED_INTRO] th
  val th = Q.INST [`df`|->`{edi}`] (DISCH_ALL th)
  val th = INST [``f:word32->word32``|->``\x:word32.(w:word32)``] (DISCH_ALL th)
  val th = SIMP_RULE std_ss [IN_INSERT,NOT_IN_EMPTY,xM_THM] th
  val th = SIMP_RULE bool_ss [GSYM SPEC_MOVE_COND,x86_astTheory.Xrm_distinct] th
  in save_thm("swap_lemma",th) end;

val jmp_lemma = let
  val (spec,_,s,_) = prog_x86Lib.x86_tools
  val ((th,_,_),_) = spec "E9"
  val th = Q.INST [`w`|->`T`] th
  in save_thm("jmp_lemma",th) end;

val X86_SPEC_COMPOSE_CODE = store_thm("X86_SPEC_COMPOSE_CODE",
  ``SPEC X86_MODEL p ((a,xs,w) INSERT (b,ys,w) INSERT c) q ==>
    (b = a + n2w (LENGTH xs)) ==>
    SPEC X86_MODEL p ((a,xs++ys,w) INSERT c) q``,
  SIMP_TAC std_ss [AND_IMP_INTRO] \\ ONCE_REWRITE_TAC [CONJ_COMM]
  \\ SIMP_TAC std_ss [GSYM AND_IMP_INTRO] \\ STRIP_TAC
  \\ ASM_SIMP_TAC std_ss [SPEC_def,X86_MODEL_def]
  \\ sg `CODE_POOL X86_INSTR ((a,xs ++ ys,w) INSERT c) =
      CODE_POOL X86_INSTR ((a,xs,w) INSERT (a + n2w (LENGTH xs),ys,w) INSERT c)`
  \\ ASM_SIMP_TAC std_ss []
  \\ SIMP_TAC std_ss [CODE_POOL_def]
  \\ MATCH_MP_TAC (METIS_PROVE [] ``(x = y) ==> ((\s. s = x) = (\s. s = y))``)
  \\ SIMP_TAC std_ss [IMAGE_INSERT,BIGUNION_INSERT]
  \\ `!xs a ys. X86_INSTR (a,xs ++ ys,w) =
             X86_INSTR (a,xs,w) UNION X86_INSTR (a + n2w (LENGTH xs),ys,w)` suffices_by
  (STRIP_TAC THEN ASM_SIMP_TAC std_ss [AC UNION_ASSOC UNION_COMM])
  \\ POP_ASSUM (K ALL_TAC) \\ Induct
  \\ ASM_SIMP_TAC std_ss [APPEND,X86_INSTR_def,UNION_EMPTY,LENGTH,WORD_ADD_0]
  \\ SIMP_TAC std_ss [RW1[ADD_COMM]ADD1,GSYM word_add_n2w,WORD_ADD_ASSOC]
  \\ SIMP_TAC std_ss [INSERT_UNION_EQ]);

val pop_lemma = let
  val (spec,_,s,_) = prog_x86Lib.x86_tools
  val ((th1,_,_),_) = spec (x86_encode "mov eax,[edi]")
  val ((th2,_,_),_) = spec (x86_encode "add edi,4")
  val th = HIDE_STATUS_RULE true s (SPEC_COMPOSE_RULE [th1,th2])
  val th = SIMP_RULE (bool_ss++sep_cond_ss) [SPEC_MOVE_COND,ALIGNED_INTRO] th
  val th = Q.INST [`df`|->`{edi}`] (DISCH_ALL th)
  val th = INST [``f:word32->word32``|->``\x:word32.(w:word32)``] (DISCH_ALL th)
  val th = SIMP_RULE std_ss [IN_INSERT,NOT_IN_EMPTY,xM_THM] th
  val th = SIMP_RULE bool_ss [GSYM SPEC_MOVE_COND] th
  val th = HIDE_POST_RULE ``xM edi`` th
  val th = MATCH_MP X86_SPEC_COMPOSE_CODE th
  val th = SIMP_RULE std_ss [LENGTH,APPEND,WORD_EQ_SUB_ZERO,precond_def] th
  in save_thm("pop_lemma",th) end;

val push_shift_lemma = prove(
  ``!i. (w2w ((w2w i):word32) = (w2w (i:word7)):word8) /\
        (w2w (((w2w i):word32) >>> 8) = 0w:word8) /\
        (w2w (((w2w i):word32) >>> 16) = 0w:word8) /\
        (w2w (((w2w i):word32) >>> 24) = 0w:word8)``,
  Cases_word \\ FULL_SIMP_TAC (std_ss++SIZES_ss) [w2w_def,w2n_n2w]
  \\ `n < 256` by DECIDE_TAC
  \\ `n < 65536` by DECIDE_TAC
  \\ `n < 16777216` by DECIDE_TAC
  \\ `n < 4294967296` by DECIDE_TAC
  \\ FULL_SIMP_TAC (std_ss++SIZES_ss) [w2w_def,w2n_n2w,w2n_lsr,LESS_DIV_EQ_ZERO]);

val push_lemma = let
  val (spec,_,s,_) = prog_x86Lib.x86_tools
  val ((th1,_,_),_) = spec (x86_encode "sub edi,4")
  val ((th2,_,_),_) = spec (x86_encode "mov [edi],eax")
  val ((th3,_,_),_) = spec "B8"
  val th3 = Q.INST [`imm32`|->`w2w (i:word7)`] th3
  val th3 = RW [push_shift_lemma] th3
  val th = HIDE_STATUS_RULE true s (SPEC_COMPOSE_RULE [th1,th2,th3])
  val th = SIMP_RULE (bool_ss++sep_cond_ss) [SPEC_MOVE_COND,ALIGNED_INTRO] th
  val th = Q.INST [`df`|->`{edi-4w}`] (DISCH_ALL th)
  val th = INST [``f:word32->word32``|->``\x:word32.(w:word32)``] (DISCH_ALL th)
  val th = SIMP_RULE std_ss [IN_INSERT,NOT_IN_EMPTY,xM_THM,ALIGNED] th
  val th = SIMP_RULE bool_ss [GSYM SPEC_MOVE_COND] th
  val th = HIDE_PRE_RULE ``xM (edi-4w)`` th
  val th = MATCH_MP X86_SPEC_COMPOSE_CODE th
  val th = SIMP_RULE std_ss [LENGTH,APPEND,WORD_EQ_SUB_ZERO,precond_def] th
  val th = MATCH_MP X86_SPEC_COMPOSE_CODE th
  val th = SIMP_RULE std_ss [LENGTH,APPEND,WORD_EQ_SUB_ZERO,precond_def] th
  in save_thm("push_lemma",th) end;

val (je_lemma,je_nop_lemma) = let
  val (spec,_,s,_) = prog_x86Lib.x86_tools
  val ((th,_,_),_) = spec "3B07"
  val ((th1,_,_),thi) = spec "0F84"
  val th2 = (case thi of SOME (x,_,_) => x | _ => hd [])
  val th1 = HIDE_STATUS_RULE true s (SPEC_COMPOSE_RULE [th,th1])
  val th2 = HIDE_STATUS_RULE true s (SPEC_COMPOSE_RULE [th,th2])
  fun foo th1 = let
    val th1 = Q.INST [`w`|->`T`] th1
    val th1 = SIMP_RULE (bool_ss++sep_cond_ss) [SPEC_MOVE_COND,ALIGNED_INTRO] th1
    val th1 = Q.INST [`df`|->`{edi}`] (DISCH_ALL th1)
    val th1 = INST [``f:word32->word32``|->``\x:word32.(v:word32)``] (DISCH_ALL th1)
    val th1 = SIMP_RULE std_ss [IN_INSERT,NOT_IN_EMPTY,xM_THM] th1
    val th1 = SIMP_RULE bool_ss [GSYM SPEC_MOVE_COND,x86_astTheory.Xrm_distinct] th1
    val th1 = MATCH_MP X86_SPEC_COMPOSE_CODE th1
    val th1 = SIMP_RULE std_ss [LENGTH,APPEND,WORD_EQ_SUB_ZERO,precond_def] th1
    val th1 = SIMP_RULE (bool_ss++sep_cond_ss) [] th1
    in th1 end
  val th1 = foo th1
  val th2 = foo th2
  in (save_thm("je_lemma",RW [SEP_CLAUSES] (Q.INST [`eax`|->`v`] th1)),
      save_thm("je_nop_lemma",th2)) end;

val (jb_lemma,jb_nop_lemma) = let
  val (spec,_,s,_) = prog_x86Lib.x86_tools
  val ((th,_,_),_) = spec "3B07"
  val ((th1,_,_),thi) = spec "0F82"
  val th2 = (case thi of SOME (x,_,_) => x | _ => hd [])
  val th1 = HIDE_STATUS_RULE true s (SPEC_COMPOSE_RULE [th,th1])
  val th2 = HIDE_STATUS_RULE true s (SPEC_COMPOSE_RULE [th,th2])
  fun foo th1 = let
    val th1 = Q.INST [`w`|->`T`] th1
    val th1 = SIMP_RULE (bool_ss++sep_cond_ss) [SPEC_MOVE_COND,ALIGNED_INTRO] th1
    val th1 = Q.INST [`df`|->`{edi}`] (DISCH_ALL th1)
    val th1 = INST [``f:word32->word32``|->``\x:word32.(v:word32)``] (DISCH_ALL th1)
    val th1 = SIMP_RULE std_ss [IN_INSERT,NOT_IN_EMPTY,xM_THM] th1
    val th1 = SIMP_RULE bool_ss [GSYM SPEC_MOVE_COND,x86_astTheory.Xrm_distinct] th1
    val th1 = MATCH_MP X86_SPEC_COMPOSE_CODE th1
    val th1 = SIMP_RULE std_ss [LENGTH,APPEND,WORD_EQ_SUB_ZERO,precond_def] th1
    val th1 = SIMP_RULE (bool_ss++sep_cond_ss) [] th1
    in th1 end
  val th1 = foo th1
  val th2 = foo th2
  in (save_thm("jb_lemma",th1), save_thm("jb_nop_lemma",th2)) end;

val jmp_edx_lemma = let
  val (spec,_,s,_) = prog_x86Lib.x86_tools
  val ((th,_,_),_) = spec (x86_encode "jmp edx")
  val th = Q.INST [`w`|->`T`] th
  in save_thm("jmp_edx_lemma",th) end;

val iSTEP_IMP_SPEC = prove(
  ``iSTEP s t /\ CODE_IN_MEM s a df f ==>
    SPEC X86_MODEL (xJIT_INV s a) (xCODE_SET df f) (xJIT_INV t a)``,
  SIMP_TAC std_ss [iSTEP_cases] \\ REPEAT STRIP_TAC
  \\ ASM_SIMP_TAC std_ss [xJIT_INV_def]
  \\ POP_ASSUM MP_TAC \\ ASM_SIMP_TAC std_ss []
  \\ IMP_RES_TAC ADDR_ADD1
  \\ ASM_REWRITE_TAC [X86_ENCODE_def]
  \\ FULL_SIMP_TAC std_ss [CODE_IN_MEM_def,LENGTH]
  \\ REPEAT STRIP_TAC \\ RES_TAC \\ POP_ASSUM MP_TAC
  \\ SIMP_TAC std_ss [LET_DEF,X86_ENCODE_def]
  \\ MATCH_MP_TAC SPEC_X86_MODEL_IN_BYTE_MEM
  THEN1
   (SIMP_TAC std_ss [xSTACK_def,xLIST_def,SEP_CLAUSES,STAR_ASSOC]
    \\ HO_MATCH_MP_TAC SPEC_EXISTS_EXISTS \\ REPEAT STRIP_TAC
    \\ Q.SPEC_TAC (`ADDR ns a p`,`i`) \\ REPEAT STRIP_TAC
    \\ SIMP_TAC (std_ss++sep_cond_ss) [SPEC_MOVE_COND,SEP_CLAUSES]
    \\ SIMP_TAC std_ss [GSYM SPEC_MOVE_COND]
    \\ SPEC_PROVE_TAC [sub_lemma])
  THEN1
   (SIMP_TAC std_ss [xSTACK_def,xLIST_def,SEP_CLAUSES,STAR_ASSOC]
    \\ HO_MATCH_MP_TAC SPEC_EXISTS_EXISTS \\ REPEAT STRIP_TAC
    \\ Q.SPEC_TAC (`ADDR ns a p`,`i`) \\ REPEAT STRIP_TAC
    \\ SIMP_TAC (std_ss++sep_cond_ss) [SPEC_MOVE_COND,SEP_CLAUSES]
    \\ SIMP_TAC std_ss [GSYM SPEC_MOVE_COND]
    \\ SPEC_PROVE_TAC [swap_lemma])
  THEN1
   (SIMP_TAC std_ss [xSTACK_def,xLIST_def,SEP_CLAUSES,STAR_ASSOC]
    \\ HO_MATCH_MP_TAC SPEC_EXISTS_EXISTS_POP \\ REPEAT STRIP_TAC
    \\ Q.SPEC_TAC (`ADDR ns a p`,`i`) \\ REPEAT STRIP_TAC
    \\ SIMP_TAC (std_ss++sep_cond_ss) [SPEC_MOVE_COND,SEP_CLAUSES]
    \\ SIMP_TAC std_ss [GSYM ADD1,xSPACE_def,WORD_ADD_SUB,ALIGNED]
    \\ SIMP_TAC std_ss [GSYM SPEC_MOVE_COND,SEP_CLAUSES,STAR_ASSOC]
    \\ SPEC_PROVE_TAC [pop_lemma])
  THEN1
   (Cases_on `xs`
    \\ SIMP_TAC std_ss [xSTACK_def,SEP_CLAUSES,SPEC_FALSE_PRE]
    \\ SIMP_TAC std_ss [xSTACK_def,xLIST_def,SEP_CLAUSES,STAR_ASSOC]
    \\ HO_MATCH_MP_TAC SPEC_EXISTS_EXISTS_PUSH \\ REPEAT STRIP_TAC
    \\ Q.SPEC_TAC (`ADDR ns a p`,`i`) \\ REPEAT STRIP_TAC
    \\ SIMP_TAC (std_ss++sep_cond_ss) [SPEC_MOVE_COND,SEP_CLAUSES]
    \\ SIMP_TAC std_ss [GSYM ADD1,xSPACE_def,WORD_SUB_ADD,ALIGNED]
    \\ SIMP_TAC std_ss [GSYM SPEC_MOVE_COND,SEP_CLAUSES,STAR_ASSOC]
    \\ Q.SPEC_TAC (`t'`,`ys`) \\ REPEAT STRIP_TAC
    \\ SPEC_PROVE_TAC [push_lemma])
  THEN1
   (Q.ABBREV_TAC `imm32 = ADDR ns a (w2n w) - ADDR ns a p - 0x5w`
    \\ SIMP_TAC std_ss [X86_IMMEDIATE_def,APPEND]
    \\ `ADDR ns a (w2n w) = ADDR ns a p + 5w + imm32` by
     (ONCE_REWRITE_TAC [WORD_ADD_COMM] \\ Q.UNABBREV_TAC `imm32`
      \\ SIMP_TAC std_ss [GSYM WORD_SUB_PLUS,WORD_SUB_ADD])
    \\ ASM_SIMP_TAC std_ss []
    \\ Q.SPEC_TAC (`ADDR ns a p`,`i`) \\ REPEAT STRIP_TAC
    \\ Cases_on `xs`
    \\ SIMP_TAC std_ss [xSTACK_def,SEP_CLAUSES,SPEC_FALSE_PRE]
    \\ HO_MATCH_MP_TAC SPEC_EXISTS_EXISTS \\ REPEAT STRIP_TAC
    \\ Q.SPEC_TAC (`t'`,`tt`) \\ STRIP_TAC
    \\ SIMP_TAC (std_ss++sep_cond_ss) [SPEC_MOVE_COND,SEP_CLAUSES]
    \\ SIMP_TAC std_ss [GSYM SPEC_MOVE_COND]
    \\ SPEC_PROVE_TAC [jmp_lemma])
  THEN1
   (SIMP_TAC std_ss [xSTACK_def,xLIST_def,SEP_CLAUSES,STAR_ASSOC]
    \\ HO_MATCH_MP_TAC SPEC_EXISTS_EXISTS \\ REPEAT STRIP_TAC
    \\ Q.ABBREV_TAC `imm32 = ADDR ns a (w2n w) - ADDR ns a p - 0x8w`
    \\ SIMP_TAC std_ss [X86_IMMEDIATE_def,APPEND]
    \\ `ADDR ns a (w2n w) = ADDR ns a p + 8w + imm32` by
     (ONCE_REWRITE_TAC [WORD_ADD_COMM] \\ Q.UNABBREV_TAC `imm32`
      \\ SIMP_TAC std_ss [GSYM WORD_SUB_PLUS,WORD_SUB_ADD])
    \\ ASM_SIMP_TAC std_ss []
    \\ Q.SPEC_TAC (`ADDR ns a p`,`i`) \\ REPEAT STRIP_TAC
    \\ SIMP_TAC (std_ss++sep_cond_ss) [SPEC_MOVE_COND,SEP_CLAUSES]
    \\ SIMP_TAC std_ss [GSYM SPEC_MOVE_COND]
    \\ SPEC_PROVE_TAC [je_lemma])
  THEN1
   (SIMP_TAC std_ss [xSTACK_def,xLIST_def,SEP_CLAUSES,STAR_ASSOC]
    \\ HO_MATCH_MP_TAC SPEC_EXISTS_EXISTS \\ REPEAT STRIP_TAC
    \\ Q.ABBREV_TAC `imm32 = ADDR ns a (w2n w) - ADDR ns a p - 0x8w`
    \\ SIMP_TAC std_ss [X86_IMMEDIATE_def,APPEND,LENGTH]
    \\ Q.SPEC_TAC (`ADDR ns a p`,`i`) \\ REPEAT STRIP_TAC
    \\ SIMP_TAC (std_ss++sep_cond_ss) [SPEC_MOVE_COND,SEP_CLAUSES]
    \\ SIMP_TAC std_ss [GSYM SPEC_MOVE_COND]
    \\ SPEC_PROVE_TAC [je_nop_lemma])
  THEN1
   (SIMP_TAC std_ss [xSTACK_def,xLIST_def,SEP_CLAUSES,STAR_ASSOC]
    \\ HO_MATCH_MP_TAC SPEC_EXISTS_EXISTS \\ REPEAT STRIP_TAC
    \\ Q.ABBREV_TAC `imm32 = ADDR ns a (w2n w) - ADDR ns a p - 0x8w`
    \\ SIMP_TAC std_ss [X86_IMMEDIATE_def,APPEND]
    \\ `ADDR ns a (w2n w) = ADDR ns a p + 8w + imm32` by
     (ONCE_REWRITE_TAC [WORD_ADD_COMM] \\ Q.UNABBREV_TAC `imm32`
      \\ SIMP_TAC std_ss [GSYM WORD_SUB_PLUS,WORD_SUB_ADD])
    \\ ASM_SIMP_TAC std_ss []
    \\ Q.SPEC_TAC (`ADDR ns a p`,`i`) \\ REPEAT STRIP_TAC
    \\ SIMP_TAC (std_ss++sep_cond_ss) [SPEC_MOVE_COND,SEP_CLAUSES]
    \\ SIMP_TAC std_ss [GSYM SPEC_MOVE_COND]
    \\ SPEC_PROVE_TAC [jb_lemma])
  THEN1
   (SIMP_TAC std_ss [xSTACK_def,xLIST_def,SEP_CLAUSES,STAR_ASSOC]
    \\ HO_MATCH_MP_TAC SPEC_EXISTS_EXISTS \\ REPEAT STRIP_TAC
    \\ Q.ABBREV_TAC `imm32 = ADDR ns a (w2n w) - ADDR ns a p - 0x8w`
    \\ SIMP_TAC std_ss [X86_IMMEDIATE_def,APPEND,LENGTH]
    \\ Q.SPEC_TAC (`ADDR ns a p`,`i`) \\ REPEAT STRIP_TAC
    \\ SIMP_TAC (std_ss++sep_cond_ss) [SPEC_MOVE_COND,SEP_CLAUSES]
    \\ SIMP_TAC std_ss [GSYM SPEC_MOVE_COND]
    \\ SPEC_PROVE_TAC [jb_nop_lemma]));

val iFETCH_iSTOP_IMP_SPEC = prove(
  ``(iFETCH ((FST o SND o SND) s) ((SND o SND o SND) s) = SOME iSTOP) /\ CODE_IN_MEM s a df f ==>
    SPEC X86_MODEL (xJIT_INV s a * xR EDX edx)
                   (xCODE_SET df f)
                   (xSTACK s * xR EDX edx * xPC edx * ~xS)``,
  REPEAT STRIP_TAC
  \\ `?xs l p ns. s = (xs,l,p,ns)` by METIS_TAC [PAIR]
  \\ FULL_SIMP_TAC std_ss [xJIT_INV_def]
  \\ POP_ASSUM (K ALL_TAC)
  \\ POP_ASSUM MP_TAC \\ ASM_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC std_ss [CODE_IN_MEM_def,LENGTH]
  \\ REPEAT STRIP_TAC \\ RES_TAC \\ POP_ASSUM MP_TAC
  \\ SIMP_TAC std_ss [LET_DEF,X86_ENCODE_def]
  \\ MATCH_MP_TAC SPEC_X86_MODEL_IN_BYTE_MEM
  \\ Q.SPEC_TAC (`ADDR ns a p`,`i`) \\ REPEAT STRIP_TAC
  \\ SPEC_PROVE_TAC [jmp_edx_lemma]);

val iEXEC_IMP_SPEC = store_thm("iEXEC_IMP_SPEC",
  ``!s t.
      iEXEC s t /\ CODE_IN_MEM s a df f ==>
      SPEC X86_MODEL (xJIT_INV s a * xR EDX edx)
                     (xCODE_SET df f)
                     (xSTACK t * xR EDX edx * xPC edx * ~xS)``,
  SIMP_TAC std_ss [GSYM AND_IMP_INTRO]
  \\ HO_MATCH_MP_TAC iEXEC_ind
  \\ REPEAT STRIP_TAC
  THEN1 (MATCH_MP_TAC iFETCH_iSTOP_IMP_SPEC \\ ASM_SIMP_TAC std_ss [])
  \\ (MATCH_MP_TAC o GEN_ALL o RW [UNION_IDEMPOT] o Q.SPECL [`x`,`p`,`c`,`m`,`c`]) SPEC_COMPOSE
  \\ Q.EXISTS_TAC `(xJIT_INV s' a * xR EDX edx)`
  \\ REPEAT STRIP_TAC
  THEN1 (METIS_TAC [SPEC_FRAME,iSTEP_IMP_SPEC])
  \\ Q.PAT_X_ASSUM `bb ==> cc` MATCH_MP_TAC
  \\ `?xs l p ns. s = (xs,l,p,ns)` by METIS_TAC [PAIR]
  \\ `?xs2 l2 p2 ns2. s' = (xs2,l2,p2,ns2)` by METIS_TAC [PAIR]
  \\ FULL_SIMP_TAC std_ss [iSTEP_cases,CODE_IN_MEM_def]);

val ADDR_0 = prove(
  ``!ns a. ADDR ns a 0 = a``,
  Cases \\ SIMP_TAC std_ss [ADDR_def]);

val _ = prog_x86Lib.set_x86_code_write_perm_flag false;

val execute_generated_code = let
  val th1 = Q.SPECL [`(xs,l,0,ns)`,`t`] iEXEC_IMP_SPEC
  val th1 = RW [xJIT_INV_def,ADDR_0] th1
  val th1 = RW1 [GSYM X86_SPEC_CODE] th1
  val th1 = RW [STAR_ASSOC] th1
  val th1 = RW [GSYM SPEC_MOVE_COND] th1
  val th1 = SPEC_COMPOSE_RULE [xCODE_INTRO,th1]
  val th1 = RW [STAR_ASSOC] (DISCH_ALL th1)
  val th1 = RW [xSTACK_def] th1
  val th1 = SIMP_RULE std_ss [SEP_CLAUSES,GSYM progTheory.SPEC_PRE_EXISTS,STAR_ASSOC] th1
  val th1 = SIMP_RULE (std_ss++sep_cond_ss) [xSPACE_def] (SPEC_ALL th1)
  val (th1,goal) = SPEC_WEAKEN_RULE th1 ``xBYTE_MEMORY_X df f *
    xSTACK t * xR EDX edx * xPC edx * ~xS * xR ESI esi``
  val lemma = prove(goal,
    SIMP_TAC std_ss [GSYM STAR_ASSOC]
    \\ METIS_TAC [SEP_IMP_FRAME,xCODE_IMP_BYTE_MEMORY])
  val th1 = MP th1 lemma
  in th1 end

val assign_eip_to_edx = let
  val (spec,_,s,_) = prog_x86Lib.x86_tools
  val ((th1,_,_),_) = spec (x86_encode "call 0")
  val ((th2,_,_),_) = spec (x86_encode "pop edx")
  val ((th3,_,_),_) = spec (x86_encode "add edx,6")
  val th = HIDE_STATUS_RULE true s (SPEC_COMPOSE_RULE [th1,th2,th3])
  val th = RW [STAR_ASSOC,combinTheory.APPLY_UPDATE_THM,WORD_ADD_0] th
  val th = SIMP_RULE (bool_ss++sep_cond_ss) [SPEC_MOVE_COND,ALIGNED_INTRO] th
  val th = Q.INST [`df`|->`{esp-4w}`] (DISCH_ALL th)
  val th = INST [``f:word32->word32``|->``\x:word32.(w:word32)``] (DISCH_ALL th)
  val th = SIMP_RULE std_ss [IN_INSERT,NOT_IN_EMPTY,xM_THM,ALIGNED,WORD_ADD_0] th
  val th = SIMP_RULE bool_ss [GSYM SPEC_MOVE_COND,x86_astTheory.Xrm_distinct] th
  val th = SIMP_RULE std_ss [word_arith_lemma1] th
  val th = HIDE_PRE_RULE ``xM (esp - 4w)`` th
  val th = HIDE_POST_RULE ``xM (esp - 4w)`` th
  val th = RW [] (DISCH_ALL th)
  in th end;

val CODE_IN_MEM_SIMP = prove(
  ``!esi f. CODE_IN_MEM (xs,l,0,ns) esi df f =
            CODE_IN_MEM ([],0,0,ns) esi df f``,
  SIMP_TAC std_ss [CODE_IN_MEM_def]);

val xCODE_IN_MEM_def = Define `
  xCODE_IN_MEM df ns =
    SEP_EXISTS f esi. cond (CODE_IN_MEM ([]:word32 list,0,0,ns) esi df f) *
      xR ESI esi * xBYTE_MEMORY_X df f`;

val execute_code_and_return = let
  val th1 = assign_eip_to_edx
  val th2 = execute_generated_code
  val th3 = SPEC_COMPOSE_RULE [th1,th2]
  val th3 = RW [STAR_ASSOC] (DISCH_ALL th3)
  val th3 = SIMP_RULE (bool_ss++sep_cond_ss) [] th3
  val th3 = HIDE_POST_RULE ``xR EDX`` th3
  val th3 = HIDE_POST_RULE ``xR ESI`` th3
  val th3 = HIDE_PRE_RULE ``xR EDX`` th3
  val th3 = HIDE_POST_RULE ``xBYTE_MEMORY_X df`` th3
  val th3 = RW [] (DISCH_ALL th3)
  val th3 = EXISTS_PRE `esi` th3
  val th3 = EXISTS_PRE `f` th3
  val (th3,goal) = SPEC_STRENGTHEN_RULE th3 ``
    xPC eip * xR ESP esp * ~xS * ~xM (esp - 0x4w) *
    xCODE_IN_MEM df ns * xSTACK (xs,l,0,ns) * ~xR EDX *
    cond (ALIGNED esp /\ iEXEC (xs,l,0,ns) t)``
  val lemma = prove(goal,
    SIMP_TAC (std_ss++sep_cond_ss) [xCODE_IN_MEM_def,SEP_CLAUSES]
    \\ SIMP_TAC (std_ss++star_ss) [AC CONJ_ASSOC CONJ_COMM,SEP_IMP_REFL,CODE_IN_MEM_SIMP])
  val th3 = MP th3 lemma
  in th3 end;

val _ = save_thm("execute_code_and_return",execute_code_and_return);

val _ = export_theory();
