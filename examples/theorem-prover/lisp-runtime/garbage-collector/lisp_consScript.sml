
open HolKernel Parse boolLib bossLib; val _ = new_theory "lisp_cons";
val _ = ParseExtras.temp_loose_equality()

open wordsTheory arithmeticTheory wordsLib listTheory pred_setTheory pairTheory;
open combinTheory finite_mapTheory addressTheory helperLib;
open set_sepTheory bitTheory fcpTheory;

open stop_and_copyTheory;
open codegenLib decompilerLib prog_x64Lib prog_x64Theory;

val RW = REWRITE_RULE;
val RW1 = ONCE_REWRITE_RULE;
fun SUBGOAL q = REVERSE (sg q)

(*
  r9 = temp
  r11 = i
  r12 = j
  r15 = to heap base
  r6 = from heap base
*)

val (thm,mc_move_def) = decompile_io_strings x64_tools "mc_move"
  (SOME (``(r6:word64,r8:word64,r10:word64,r12:word64,r15:word64,df:word64 set,f:word64->word32)``,
         ``(r6:word64,r8:word64,r10:word64,r12:word64,r15:word64,df:word64 set,f:word64->word32)``))
  (assemble "x64" `
     test r8d,1
     jne L2
     mov r9,[4*r8+r6]
     cmp r9d,r10d
     je L1
     mov [4*r12+r15],r9
     mov [4*r8+r6],r10d
     mov [4*r8+r6+4],r12d
     mov r8,r12
     add r12,2
     jmp L2
L1:  shr r9,32
     mov r8,r9
L2:  `)

val (thm,mc_move2_def) = decompile_io_strings x64_tools "mc_move2"
  (SOME (``(r6:word64,r13:word64,r10:word64,r12:word64,r15:word64,df:word64 set,f:word64->word32)``,
         ``(r6:word64,r13:word64,r10:word64,r12:word64,r15:word64,df:word64 set,f:word64->word32)``))
  (assemble "x64" `
     test r13d,1
     jne L2
     mov r9,[4*r13+r6]
     cmp r9d,r10d
     je L1
     mov [4*r12+r15],r9
     mov [4*r13+r6],r10d
     mov [4*r13+r6+4],r12d
     mov r13,r12
     add r12,2
     jmp L2
L1:  shr r9,32
     mov r13,r9
L2:  `)

val (thm,mc_gc_step_def) = decompile_io_strings x64_tools "mc_gc_step"
  (SOME (``(r6:word64,r10:word64,r11:word64,r12:word64,r15:word64,df:word64 set,f:word64->word32)``,
         ``(r6:word64,r10:word64,r11:word64,r12:word64,r15:word64,df:word64 set,f:word64->word32)``))
  (assemble "x64" `
     mov r8d,[4*r11+r15]
     mov r13d,[4*r11+r15+4]
     insert mc_move
     insert mc_move2
     mov [4*r11+r15],r8d
     mov [4*r11+r15+4],r13d
     add r11,2
     `);

val (thm,mc_gc_loop_def) = decompile_io_strings x64_tools "mc_gc_loop"
  (SOME (``(r6:word64,r10:word64,r11:word64,r12:word64,r15:word64,df:word64 set,f:word64->word32)``,
         ``(r6:word64,r10:word64,r11:word64,r12:word64,r15:word64,df:word64 set,f:word64->word32)``))
  (assemble "x64" `
     jmp L2
L1:  insert mc_gc_step
L2:  cmp r11,r12
     jne L1`);

val (thm,mc_move_list_def) = decompile_io_strings x64_tools "mc_move_list"
  (SOME (``(r6:word64,r10:word64,r12:word64,r14:word64,r15:word64,df:word64 set,f:word64->word32)``,
         ``(r6:word64,r8:word64,r10:word64,r12:word64,r14:word64,r15:word64,df:word64 set,f:word64->word32)``))
  (assemble "x64" `
     jmp L2
L1:  insert mc_move
     mov [r14],r8d
     lea r14,[r14+4]
L2:  mov r8d,[r14]
     cmp r8d,r10d
     jne L1`);

val (thm,mc_gc_def) = decompile_io_strings x64_tools "mc_gc"
  (SOME (``(r6:word64,r14:word64,r15:word64,df:word64 set,f:word64->word32)``,
         ``(r6:word64,r11:word64,r15:word64,df:word64 set,f:word64->word32)``))
  (assemble "x64" `
     xor r10,r10
     xor r11,r11
     xor r12,r12
     not r10d
     insert mc_move_list
     insert mc_gc_loop
     xchg r6,r15
     `);

val (thm,mc_full_gc_def) = decompile_io_strings x64_tools "mc_full_gc"
  (SOME (``(r3:word64,r6:word64,r7:word64,r8:word64,r9:word64,r10:word64,r11:word64,r12:word64,r13:word64,r14:word64,df:word64 set,f:word64->word32)``,
         ``(r3:word64,r6:word64,r7:word64,r8:word64,r9:word64,r10:word64,r11:word64,r12:word64,r13:word64,r14:word64,r15:word64,df:word64 set,f:word64->word32)``))
  (assemble "x64" `
     lea r14,[r7+4*r3-24]
     mov r15,[r7-232]
     mov [r14],r8d
     mov [r14+4],r9d
     mov [r14+8],r10d
     mov [r14+12],r11d
     mov [r14+16],r12d
     mov [r14+20],r13d
     insert mc_gc
     mov [r7-232],r15
     mov r14,r11
     lea r15,[r7+4*r3-24]
     mov r8d,[r15]
     mov r9d,[r15+4]
     mov r10d,[r15+8]
     mov r11d,[r15+12]
     mov r12d,[r15+16]
     mov r13d,[r15+20]
     mov r15,[r7-240]
     add r15,r15
     `);

val _ = save_thm("mc_full_thm",thm);


val SET_TAC =
  FULL_SIMP_TAC std_ss [EXTENSION,IN_INSERT,IN_UNION,IN_DELETE,SUBSET_DEF,
    DISJOINT_DEF,NOT_IN_EMPTY,EXTENSION,IN_INSERT,IN_INTER,IN_DIFF,IN_UNIV]
  \\ METIS_TAC [PAIR_EQ];

val RANGE_TAC = FULL_SIMP_TAC std_ss [RANGE_def,IN_DEF,gc_inv_def] \\ DECIDE_TAC

val ref_addr_def = Define `ref_addr k n = n2w (8 * n + k):word64`;

val ref_heap_addr_def = Define `
  (ref_heap_addr (H_ADDR a) = (n2w a << 1):word32) /\
  (ref_heap_addr (H_DATA (INL (w:word30))) = w2w w << 2 !! 1w) /\
  (ref_heap_addr (H_DATA (INR (v:29 word))) = w2w v << 3 !! 3w)`;

val ONE32 = ``0xFFFFFFFFw:word32``;
val ONE64 = ``0xFFFFFFFFw:word64``;

val word_LSL_n2w = prove(
  ``!m k. ((n2w m):'a word) << k = n2w (m * 2 ** k)``,
  SIMP_TAC std_ss [AC MULT_ASSOC MULT_COMM,WORD_MUL_LSL,word_mul_n2w]);

val ref_heap_addr_NOT_ONE32 = prove(
  ``!x. ~(ref_heap_addr x = ^ONE32)``,
  Cases \\ REPEAT (Cases_on `a`)
  \\ ASM_SIMP_TAC std_ss [ref_heap_addr_def,w2n_n2w,w2w_def]
  \\ Q.SPEC_TAC (`(n2w n):word32`,`w`)
  \\ blastLib.BBLAST_TAC);

val ref_heap_addr_and_1 = prove(
  ``(w2w (w2w (ref_heap_addr (H_ADDR a)) && 1w:word64) = 0w:word32) /\
    ~(w2w (w2w (ref_heap_addr (H_DATA b)) && 1w:word64) = 0w:word32)``,
  Cases_on `b` \\ ASM_SIMP_TAC std_ss [ref_heap_addr_def]
  \\ blastLib.BBLAST_TAC);

val ADDR_SIMP_LEMMA = prove(
  ``!a b. (w2w (0x4w * a + b && 0x3w:word64) = 0x0w:word32) = (b && 3w = 0w)``,
  blastLib.BBLAST_TAC);

val ADDR_SIMP_LEMMA2 = prove(
  ``!b. ((b + 4w) && 3w = 0w) = (b && 3w = 0w:word64)``,
  blastLib.BBLAST_TAC);

val ADDR_w2w_ALIGNED = prove(
  ``!b. ((w2w (3w && b:word64) = 0w:word32) = (b && 3w = 0w:word64)) /\
        ((w2w (b && 3w:word64) = 0w:word32) = (b && 3w = 0w:word64)) /\
        (((b+4w) && 3w = 0w) = (b && 3w = 0w:word64))``,
  REPEAT STRIP_TAC \\ blastLib.BBLAST_TAC);

val ADDR_SIMP = store_thm("ADDR_SIMP",
  ``!a b.
      ((w2w (0x4w * a + b && 0x3w:word64) = 0x0w:word32) = (b && 3w = 0w)) /\
      ((w2w (0x4w * a + b + 4w && 0x3w:word64) = 0x0w:word32) = (b && 3w = 0w))``,
  METIS_TAC [ADDR_SIMP_LEMMA,ADDR_SIMP_LEMMA2,WORD_ADD_ASSOC]);

val ref_aux_def = Define `
  (ref_aux a H_EMP = SEP_EXISTS x y. one (a:word64,x) * one (a+4w,y)) /\
  (ref_aux a (H_REF n) = one (a,^ONE32) * one (a+4w,n2w n << 1)) /\
  (ref_aux a (H_BLOCK (xs,l,())) =
     one (a,ref_heap_addr(HD xs)) * one (a+4w,ref_heap_addr(HD (TL xs))))`;

val ref_mem_def = Define `
  (ref_mem a m b 0 = emp) /\
  (ref_mem a m b (SUC e) =
     if e < b then emp else ref_aux (a + n2w (8 * e)) (m e) * ref_mem a m b e)`;

val ref_mem_EQ_EMP = prove(
  ``!e a m. ref_mem a m e e = emp``,
  Cases \\ SIMP_TAC std_ss [ref_mem_def]);

val ref_mem_SPLIT = prove(
  ``!b e i m.
      RANGE(b,e)i ==>
      (ref_mem a m b e = ref_mem a m b i * ref_mem a m i e)``,
  Induct_on `e` THEN1 (SIMP_TAC std_ss [RANGE_def])
  \\ REPEAT STRIP_TAC \\ Cases_on `i = e` \\ `~(e<b)` by RANGE_TAC
  \\ ASM_SIMP_TAC std_ss [ref_mem_EQ_EMP,AC STAR_ASSOC STAR_COMM,SEP_CLAUSES,ref_mem_def]
  \\ `RANGE (b,e) i /\ ~(e < i)` by RANGE_TAC \\ RES_TAC
  \\ ASM_SIMP_TAC std_ss [AC STAR_ASSOC STAR_COMM]);

val ref_mem_RANGE = store_thm("ref_mem_RANGE",
  ``!m b e i.
      RANGE(b,e)i ==>
      (ref_mem a m b e = ref_mem a m b i * ref_aux (a + n2w (8 * i)) (m i) *
                         ref_mem a m (SUC i) e)``,
  REPEAT STRIP_TAC \\ IMP_RES_TAC ref_mem_SPLIT
  \\ ASM_SIMP_TAC std_ss [GSYM STAR_ASSOC] \\ AP_TERM_TAC
  \\ POP_ASSUM (K ALL_TAC) \\ POP_ASSUM MP_TAC
  \\ Induct_on `e` THEN1 (SIMP_TAC std_ss [RANGE_def])
  \\ REPEAT STRIP_TAC \\ Cases_on `e = i` THEN1
   (ASM_SIMP_TAC std_ss [ref_mem_EQ_EMP]
    \\ ASM_SIMP_TAC std_ss [ref_mem_def,ref_mem_EQ_EMP])
  \\ ASM_SIMP_TAC std_ss [ref_mem_def,ref_mem_EQ_EMP]
  \\ `~(e < i) /\ ~(e < SUC i) /\ RANGE (b,e) i` by RANGE_TAC
  \\ ASM_SIMP_TAC std_ss [AC STAR_ASSOC STAR_COMM]);

val ref_mem_IGNORE = prove(
  ``!e i b m a. ~RANGE(b,e)i ==> (ref_mem a ((i =+ x) m) b e = ref_mem a m b e)``,
  Induct \\ SIMP_TAC std_ss [ref_mem_def]
  \\ REPEAT STRIP_TAC \\ Cases_on `e < b` \\ ASM_SIMP_TAC std_ss []
  \\ `~(i = e) /\ ~RANGE (b,e) i` by RANGE_TAC \\ RES_TAC
  \\ ASM_SIMP_TAC std_ss [APPLY_UPDATE_THM]);

val ref_mem_UPDATE = store_thm("ref_mem_UPDATE",
  ``!m b e i.
      RANGE(b,e)i ==>
      (ref_mem a ((i =+ x) m) b e =
       ref_mem a m b i *
       ref_aux (a + n2w (8 * i)) x *
       ref_mem a m (SUC i) e)``,
  REPEAT STRIP_TAC \\ IMP_RES_TAC ref_mem_RANGE
  \\ ASM_SIMP_TAC std_ss [APPLY_UPDATE_THM]
  \\ `~RANGE(b,i)i /\ ~RANGE(SUC i,e)i` by RANGE_TAC
  \\ ASM_SIMP_TAC std_ss [ref_mem_IGNORE]);

val memory_ok_def = Define `
  memory_ok m =
    !i xs n d. (m i = H_BLOCK (xs,n,d)) ==> (n = 0) /\ (LENGTH xs = 2)`;

val w2w_SUB_EQ = prove(
  ``!x y. (w2w (x - y:word64) = 0w:word32) = (w2w x = (w2w y):word32)``,
  blastLib.BBLAST_TAC);

val ref_heap_addr_H_ADDR = prove(
  ``n < 2147483648 ==>
    (0x4w * w2w (ref_heap_addr (H_ADDR n)) = n2w (8 * n))``,
  REPEAT STRIP_TAC \\ `2 * n < 4294967296` by DECIDE_TAC
  \\ ASM_SIMP_TAC (std_ss++SIZES_ss) [ref_heap_addr_def,WORD_MUL_LSL,
       word_mul_n2w,w2w_def,w2n_n2w,MULT_ASSOC]);

val word_32_32_def = Define `
  word_32_32 (x:word32) (y:word32) = w2w y << 32 !! (w2w x):word64`;

val w2w_word_32_32 = prove(
  ``!x y. (w2w (word_32_32 x y) = x) /\
          (word_32_32 x y >>> 32 = w2w y) /\
          ((31 >< 0) (word_32_32 x y) = x) /\
          ((63 >< 32) (word_32_32 x y) = y)``,
  SIMP_TAC std_ss [word_32_32_def] \\ blastLib.BBLAST_TAC);

val memory_ok_REF = prove(
  ``!m k n. memory_ok m ==> memory_ok ((n =+ H_REF k) m)``,
  SIMP_TAC std_ss [memory_ok_def,APPLY_UPDATE_THM] \\ REPEAT STRIP_TAC
  \\ Cases_on `n = i` \\ FULL_SIMP_TAC (srw_ss()) [] \\ METIS_TAC []);

val memory_ok_BLOCK = prove(
  ``memory_ok m /\ (LENGTH xs = 2) /\ (n = 0) ==>
    memory_ok ((i =+ H_BLOCK (xs,n,d)) m)``,
  SIMP_TAC std_ss [memory_ok_def,APPLY_UPDATE_THM] \\ REPEAT STRIP_TAC
  \\ Cases_on `i = i'` \\ FULL_SIMP_TAC (srw_ss()) [] \\ METIS_TAC []);

val mc_move_thm = prove(
  ``(split_move (x,j,mF,mT,e) = (T,x2,j2,mF2,mT2)) /\
    memory_ok mF /\ memory_ok mT /\ e < 2**31 /\ (r6 && 3w = 0w) /\ (r15 && 3w = 0w) ==>
    (ref_mem r6 mF 0 e * ref_mem r15 mT 0 e * p) (fun2set (f,df)) ==>
    ?fi.
      memory_ok mF2 /\ memory_ok mT2 /\
      mc_move_pre (r6,w2w (ref_heap_addr x),^ONE64,n2w (2 * j),r15,df,f) /\
      (mc_move (r6,w2w (ref_heap_addr x),^ONE64,n2w (2 * j),r15,df,f) =
         (r6,w2w (ref_heap_addr x2),^ONE64,n2w (2 * j2),r15,df,fi)) /\
      (ref_mem r6 mF2 0 e * ref_mem r15 mT2 0 e * p) (fun2set (fi,df))``,
  REVERSE (Cases_on `x`) \\ ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN1
   (SIMP_TAC std_ss [split_move_def] \\ ONCE_REWRITE_TAC [mc_move_def]
    \\ SIMP_TAC std_ss [ref_heap_addr_and_1])
  \\ SIMP_TAC std_ss [ALIGNED64]
  \\ SIMP_TAC std_ss [split_move_def] \\ ONCE_REWRITE_TAC [RW [ADDR_SIMP] mc_move_def]
  \\ SIMP_TAC std_ss [GSYM word_32_32_def]
  \\ SIMP_TAC std_ss [ref_heap_addr_and_1,w2w_SUB_EQ]
  \\ Cases_on `mF n` \\ ASM_SIMP_TAC (srw_ss()) [] THEN1
   (STRIP_TAC
    \\ `RANGE(0,e)n` by RANGE_TAC
    \\ IMP_RES_TAC ref_mem_RANGE
    \\ ASM_SIMP_TAC std_ss [STAR_ASSOC,ref_aux_def,SEP_CLAUSES]
    \\ `n < 2147483648` by IMP_RES_TAC LESS_TRANS
    \\ ASM_SIMP_TAC std_ss [ref_heap_addr_H_ADDR]
    \\ REPEAT STRIP_TAC \\ SEP_R_TAC
    \\ SIMP_TAC std_ss [LET_DEF,w2w_word_32_32]
    \\ SIMP_TAC (srw_ss()) []
    \\ FULL_SIMP_TAC (std_ss++star_ss) [w2w_word_32_32,ref_heap_addr_def]
    \\ FULL_SIMP_TAC std_ss [ALIGNED64])
  \\ `?xs nn d. p' = (xs,nn,d)` by METIS_TAC [PAIR]
  \\ ASM_SIMP_TAC (srw_ss()) [LET_DEF]
  \\ STRIP_TAC \\ FULL_SIMP_TAC std_ss [w2w_word_32_32]
  \\ `(nn = 0) /\ (LENGTH xs = 2)` by METIS_TAC [memory_ok_def]
  \\ `n < 2147483648` by IMP_RES_TAC LESS_TRANS
  \\ ASM_SIMP_TAC std_ss [ref_heap_addr_H_ADDR]
  \\ SIMP_TAC std_ss [word_mul_n2w,MULT_ASSOC]
  \\ `RANGE(0,e)n` by RANGE_TAC
  \\ IMP_RES_TAC ref_mem_RANGE
  \\ POP_ASSUM (ASSUME_TAC o Q.SPECL [`mF`,`r6`])
  \\ Q.PAT_X_ASSUM `RANGE (0,e) n` (K ALL_TAC)
  \\ `RANGE(0,e)j` by RANGE_TAC
  \\ IMP_RES_TAC ref_mem_RANGE
  \\ POP_ASSUM (ASSUME_TAC o Q.SPECL [`mT`,`r15`])
  \\ ASM_SIMP_TAC std_ss [ref_aux_def,oneTheory.one,SEP_CLAUSES,STAR_ASSOC]
  \\ SIMP_TAC std_ss [SEP_EXISTS_THM] \\ STRIP_TAC
  \\ SEP_R_TAC \\ SIMP_TAC std_ss [EVAL ``-1w:word32``,ref_heap_addr_NOT_ONE32]
  \\ SIMP_TAC std_ss [ref_heap_addr_def,WORD_MUL_LSL,word_mul_n2w]
  \\ FULL_SIMP_TAC std_ss [ALIGNED64]
  \\ `w2w (n2w (2 * j):word32) = n2w (2 * j):word64` by
   (`(2 * j) < 4294967296` by DECIDE_TAC
    \\ ASM_SIMP_TAC (srw_ss()) [ref_heap_addr_def,WORD_MUL_LSL,word_mul_n2w,
       w2w_def,w2n_n2w])
  \\ ASM_SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC
  THEN1 METIS_TAC [memory_ok_REF]
  THEN1 METIS_TAC [memory_ok_BLOCK]
  THEN1 (ASM_SIMP_TAC (srw_ss()) [word_add_n2w]
         \\ AP_THM_TAC \\ AP_TERM_TAC \\ DECIDE_TAC)
  \\ `RANGE(0,e)j /\ RANGE(0,e)n` by RANGE_TAC
  \\ IMP_RES_TAC ref_mem_UPDATE
  \\ ASM_SIMP_TAC std_ss [ref_aux_def,STAR_ASSOC]
  \\ SIMP_TAC (std_ss++SIZES_ss) [w2w_n2w,WORD_MUL_LSL,word_mul_n2w]
  \\ SEP_W_TAC);

val mc_move2_thm = prove(
  ``(mc_move2 = mc_move) /\ (mc_move2_pre = mc_move_pre)``,
  SIMP_TAC std_ss [mc_move2_def,mc_move_def,FUN_EQ_THM,FORALL_PROD]);

val SELECT_32_LEMMA = prove(
  ``!w. (31 -- 0) (w2w (w:word32)):word64 = w2w w``,
  blastLib.BBLAST_TAC);

val w2w_w2w_LEMMA = prove(
  ``!w. w2w ((w2w w):word64) = w:word32``,
  blastLib.BBLAST_TAC);

val mc_gc_step_thm = prove(
  ``(split_gc_step (i,j,mF,mT,e) = (T,i2,j2,mF2,mT2)) /\
    memory_ok mF /\ memory_ok mT /\ e < 2**31 /\ (r6 && 3w = 0w) /\ (r15 && 3w = 0w) ==>
    (ref_mem r6 mF 0 e * ref_mem r15 mT 0 e * p) (fun2set (f,df)) ==>
    ?r9i fi.
      memory_ok mF2 /\ memory_ok mT2 /\
      mc_gc_step_pre (r6,^ONE64,n2w (2 * i),n2w (2 * j),r15,df,f) /\
      (mc_gc_step (r6,^ONE64,n2w (2 * i),n2w (2 * j),r15,df,f) =
                  (r6,^ONE64,n2w (2 * i2),n2w (2 * j2),r15,df,fi)) /\
      (ref_mem r6 mF2 0 e * ref_mem r15 mT2 0 e * p) (fun2set (fi,df))``,
  ONCE_REWRITE_TAC [EQ_SYM_EQ]
  \\ SIMP_TAC std_ss [split_gc_step_def]
  \\ `?xs n d. getBLOCK (mT i) = (xs,n,d)` by METIS_TAC [PAIR]
  \\ ASM_SIMP_TAC std_ss [LET_DEF]
  \\ `?c3 ys3 j3 mF3 mT3. split_move_list (xs,j,mF,mT,e) = (c3,ys3,j3,mF3,mT3)` by
       METIS_TAC [PAIR]
  \\ ASM_SIMP_TAC std_ss [] \\ ONCE_REWRITE_TAC [Q.ISPEC `0w` EQ_SYM_EQ]
  \\ STRIP_TAC \\ FULL_SIMP_TAC std_ss [oneTheory.one]
  \\ `mT i = H_BLOCK (xs,n,())` by
    (Cases_on `mT i` \\ FULL_SIMP_TAC (srw_ss()) [isBLOCK_def,getBLOCK_def])
  \\ `(n = 0) /\ (LENGTH xs = 2)` by METIS_TAC [memory_ok_def]
  \\ `?x1 x2. xs = [x1;x2]` by
   (Cases_on `xs` \\ FULL_SIMP_TAC std_ss [LENGTH]
    \\ Cases_on `t` \\ FULL_SIMP_TAC std_ss [LENGTH]
    \\ Cases_on `t'` \\ FULL_SIMP_TAC std_ss [LENGTH,CONS_11,ADD1])
  \\ Q.PAT_X_ASSUM `xxx = (T,ys3,j3,mF3,mT3)` (MP_TAC o GSYM)
  \\ ASM_SIMP_TAC std_ss [split_move_list_def]
  \\ `?c5 x5 j5 mF5 mT5. split_move (x1,j,mF,mT,e) = (c5,x5,j5,mF5,mT5)` by METIS_TAC [PAIR]
  \\ `?c6 x6 j6 mF6 mT6. split_move (x2,j5,mF5,mT5,e) = (c6,x6,j6,mF6,mT6)` by METIS_TAC [PAIR]
  \\ ASM_SIMP_TAC std_ss [LET_DEF] \\ REPEAT STRIP_TAC
  \\ SIMP_TAC std_ss [RW [ADDR_SIMP] mc_gc_step_def,word_mul_n2w,MULT_ASSOC]
  \\ `(n2w (8 * i) + r15) IN df /\ (n2w (8 * i) + r15 + 4w) IN df /\
      (f (n2w (8 * i) + r15) = ref_heap_addr x1) /\
      (f (n2w (8 * i) + r15 + 4w) = ref_heap_addr x2)` by
   (POP_ASSUM MP_TAC
    \\ `RANGE(0,e)i` by RANGE_TAC
    \\ IMP_RES_TAC ref_mem_RANGE
    \\ POP_ASSUM (ASSUME_TAC o Q.SPECL [`mT`,`r15`])
    \\ FULL_SIMP_TAC std_ss [ref_mem_UPDATE] \\ POP_ASSUM (K ALL_TAC)
    \\ FULL_SIMP_TAC std_ss [ref_aux_def,HD,TL,AC WORD_ADD_ASSOC WORD_ADD_COMM]
    \\ REPEAT STRIP_TAC \\ SEP_R_TAC)
  \\ FULL_SIMP_TAC std_ss [SELECT_32_LEMMA]
  \\ SIMP_TAC std_ss [LET_DEF]
  \\ ASSUME_TAC (GEN_ALL mc_move_thm)
  \\ SEP_I_TAC "mc_move"
  \\ Q.PAT_X_ASSUM `split_move (x1,j,mF,mT,e) = (T,x5,j5,mF5,mT5)` MP_TAC
  \\ SEP_I_TAC "split_move"
  \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss []
  \\ Q.PAT_X_ASSUM `!p.bbb` (MP_TAC o Q.SPEC `p`)
  \\ ASM_SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC
  \\ ASM_SIMP_TAC std_ss [LET_DEF,mc_move2_thm]
  \\ ASSUME_TAC (GEN_ALL (Q.INST [`x2`|->`x99`] mc_move_thm))
  \\ SEP_I_TAC "mc_move"
  \\ Q.PAT_X_ASSUM `split_move (x2,j5,mF5,mT5,e) = (T,x6,j6,mF6,mT6)` MP_TAC
  \\ SEP_I_TAC "split_move"
  \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss []
  \\ Q.PAT_X_ASSUM `!p.bbb` (MP_TAC o Q.SPEC `p`)
  \\ ASM_SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC
  \\ ASM_SIMP_TAC std_ss [memory_ok_BLOCK,LENGTH]
  \\ FULL_SIMP_TAC std_ss [ALIGNED64]
  \\ STRIP_TAC THEN1 SIMP_TAC std_ss [word_add_n2w,LEFT_ADD_DISTRIB]
  \\ `RANGE(0,e)i` by RANGE_TAC
  \\ ASM_SIMP_TAC std_ss [ref_mem_UPDATE,ref_aux_def,HD,TL,STAR_ASSOC]
  \\ ASM_SIMP_TAC std_ss [w2w_w2w_LEMMA]
  \\ IMP_RES_TAC ref_mem_RANGE
  \\ POP_ASSUM (ASSUME_TAC o Q.SPECL [`mT6`,`r15`])
  \\ Q.PAT_X_ASSUM `mT6 i = nnnn` ASSUME_TAC
  \\ FULL_SIMP_TAC std_ss [STAR_ASSOC,ref_aux_def,HD,TL]
  \\ FULL_SIMP_TAC std_ss [AC WORD_ADD_ASSOC WORD_ADD_COMM]
  \\ SEP_W_TAC);

val mc_gc_loop_thm = prove(
  ``!j mF mT f i2 mF2 mT2.
      memory_ok mF /\ memory_ok mT /\ e < 2**31 /\ (r6 && 3w = 0w) /\ (r15 && 3w = 0w) ==>
      (split_gc_loop (i,j,mF,mT,e) = (T,i2,mF2,mT2)) ==>
      (ref_mem r6 mF 0 e * ref_mem r15 mT 0 e * p) (fun2set (f,df)) ==>
      ?r9i fi.
        memory_ok mF2 /\ memory_ok mT2 /\
        mc_gc_loop1_pre (r6,^ONE64,n2w (2 * i),n2w (2 * j),r15,df,f) /\
        (mc_gc_loop1 (r6,^ONE64,n2w (2 * i),n2w (2 * j),r15,df,f) =
                     (r6,^ONE64,n2w (2 * i2),n2w (2 * i2),r15,df,fi)) /\
        (ref_mem r6 mF2 0 e * ref_mem r15 mT2 0 e * p) (fun2set (fi,df))``,
  Induct_on `e-i` \\ ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN1
   (ONCE_REWRITE_TAC [split_gc_loop_def] \\ NTAC 10 STRIP_TAC
    \\ Cases_on `i = j` \\ ASM_SIMP_TAC std_ss []
    THEN1 (ONCE_REWRITE_TAC [mc_gc_loop_def] \\ ASM_SIMP_TAC std_ss [])
    \\ Cases_on `i < j` \\ ASM_SIMP_TAC std_ss []
    \\ Cases_on `j <= e` \\ ASM_SIMP_TAC std_ss []
    \\ `F` by DECIDE_TAC)
  \\ ONCE_REWRITE_TAC [split_gc_loop_def] \\ NTAC 10 STRIP_TAC
  \\ Cases_on `i = j` \\ ASM_SIMP_TAC std_ss []
  THEN1 (ONCE_REWRITE_TAC [mc_gc_loop_def] \\ ASM_SIMP_TAC std_ss [])
  \\ Cases_on `i < j` \\ ASM_SIMP_TAC std_ss []
  \\ Cases_on `j <= e` \\ ASM_SIMP_TAC std_ss []
  \\ ONCE_REWRITE_TAC [Q.ISPEC `0w` EQ_SYM_EQ]
  \\ ONCE_REWRITE_TAC [mc_gc_loop_def] \\ STRIP_TAC
  \\ `?c4 i4 j4 mF4 mT4. split_gc_step (i,j,mF,mT,e) = (c4,i4,j4,mF4,mT4)`
        by METIS_TAC [PAIR]
  \\ ASSUME_TAC (GEN_ALL mc_gc_step_thm)
  \\ SEP_I_TAC "split_gc_step"
  \\ SEP_I_TAC "mc_gc_step"
  \\ POP_ASSUM MP_TAC
  \\ ASM_SIMP_TAC std_ss [LET_DEF]
  \\ `?c5 i5 mF5 mT5. split_gc_loop (i4,j4,mF4,mT4,e) = (c5,i5,mF5,mT5)` by METIS_TAC [PAIR]
  \\ Cases_on `c4` \\ Cases_on `c5` \\ ASM_SIMP_TAC std_ss []
  \\ STRIP_TAC \\ POP_ASSUM (MP_TAC o Q.SPEC `p`)
  \\ ASM_SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss []
  \\ `e - i4 = v` by
   (SUBGOAL `i4 = i+1` THEN1 DECIDE_TAC
    \\ Q.PAT_X_ASSUM `split_gc_step xxx = yyyy` (MP_TAC o GSYM)
    \\ FULL_SIMP_TAC std_ss [split_gc_step_def,LET_DEF]
    \\ CONV_TAC (DEPTH_CONV (helperLib.FORCE_PBETA_CONV))
    \\ ASM_SIMP_TAC std_ss []
    \\ Cases_on `mT i` \\ ASM_SIMP_TAC (srw_ss()) [isBLOCK_def]
    \\ Cases_on `p'` \\ Cases_on `r`
    \\ FULL_SIMP_TAC std_ss [getBLOCK_def] \\ METIS_TAC [memory_ok_def])
  \\ Q.PAT_X_ASSUM `!ee ii. bbb` (MP_TAC o Q.SPECL [`e`,`i4`])
  \\ ASM_SIMP_TAC std_ss [] \\ STRIP_TAC
  \\ Q.PAT_X_ASSUM `split_gc_loop xxx = yyy` MP_TAC
  \\ SEP_I_TAC "split_gc_loop"
  \\ SEP_I_TAC "mc_gc_loop1"
  \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss []
  \\ Q.PAT_X_ASSUM `bbb ==> ccc` MP_TAC \\ ASM_SIMP_TAC std_ss []
  \\ REPEAT STRIP_TAC \\ ASM_SIMP_TAC std_ss []
  \\ SIMP_TAC (std_ss++SIZES_ss) [n2w_11]
  \\ `2 * i < 18446744073709551616` by DECIDE_TAC
  \\ `2 * j < 18446744073709551616` by DECIDE_TAC
  \\ `~(2 * i = 2 * j)` by DECIDE_TAC
  \\ ASM_SIMP_TAC std_ss []);

val mc_gc_loop1_THM = prove(
  ``(mc_gc_loop1 = mc_gc_loop) /\ (mc_gc_loop1_pre = mc_gc_loop_pre)``,
  REPEAT STRIP_TAC \\ SIMP_TAC std_ss [FUN_EQ_THM,FORALL_PROD]
  \\ ONCE_REWRITE_TAC [EQ_SYM_EQ]
  \\ SIMP_TAC std_ss [Once mc_gc_loop_def,LET_DEF]
  \\ CONV_TAC (DEPTH_CONV (helperLib.FORCE_PBETA_CONV))
  \\ SIMP_TAC std_ss []);

val ref_stack_def = Define `
  (ref_stack a [] = one (a:word64,^ONE32)) /\
  (ref_stack a (x::xs) = one (a,ref_heap_addr x) * ref_stack (a+4w) xs)`;

val mc_move_list1_THM = prove(
  ``(mc_move_list1 = mc_move_list) /\ (mc_move_list1_pre = mc_move_list_pre)``,
  REPEAT STRIP_TAC \\ SIMP_TAC std_ss [FUN_EQ_THM,FORALL_PROD]
  \\ ONCE_REWRITE_TAC [EQ_SYM_EQ]
  \\ SIMP_TAC std_ss [Once mc_move_list_def,LET_DEF]
  \\ CONV_TAC (DEPTH_CONV (helperLib.FORCE_PBETA_CONV))
  \\ SIMP_TAC std_ss []);

val mc_move_list_thm = prove(
  ``!xs r14 j mF mT f i2 mF2 mT2 xs2 p.
      memory_ok mF /\ memory_ok mT /\ e < 2**31 /\ (r6 && 3w = 0w) /\ (r15 && 3w = 0w) /\ (r14 && 3w = 0w) ==>
      (split_move_list (xs,j,mF,mT,e) = (T,xs2,i2,mF2,mT2)) ==>
      (ref_mem r6 mF 0 e * ref_mem r15 mT 0 e * ref_stack r14 xs * p) (fun2set (f,df)) ==>
      ?fi r8i r14i.
        memory_ok mF2 /\ memory_ok mT2 /\
        mc_move_list_pre (r6,^ONE64,n2w (2 * j),r14,r15,df,f) /\
        (mc_move_list (r6,^ONE64,n2w (2 * j),r14,r15,df,f) =
                      (r6,r8i,^ONE64,n2w (2 * i2),r14i,r15,df,fi)) /\
        (ref_mem r6 mF2 0 e * ref_mem r15 mT2 0 e * ref_stack r14 xs2 * p) (fun2set (fi,df))``,
  SIMP_TAC std_ss [GSYM mc_move_list1_THM] \\ Induct THEN1
   (ONCE_REWRITE_TAC [EQ_SYM_EQ]
    \\ ONCE_REWRITE_TAC [Q.ISPEC `0w` EQ_SYM_EQ]
    \\ SIMP_TAC std_ss [split_move_list_def,ref_stack_def]
    \\ ONCE_REWRITE_TAC [mc_move_list_def]
    \\ SIMP_TAC std_ss [w2w_SUB_EQ,SELECT_32_LEMMA,LET_DEF,w2w_w2w_LEMMA]
    \\ REPEAT STRIP_TAC \\ SEP_R_TAC
    \\ ASM_SIMP_TAC (srw_ss()) [w2w_n2w,ADDR_w2w_ALIGNED])
  \\ ONCE_REWRITE_TAC [EQ_SYM_EQ]
  \\ ONCE_REWRITE_TAC [Q.ISPEC `0w` EQ_SYM_EQ]
  \\ NTAC 12 STRIP_TAC
  \\ SIMP_TAC std_ss [split_move_list_def]
  \\ `?c5 h5 j5 mF5 mT5. split_move (h,j,mF,mT,e) = (c5,h5,j5,mF5,mT5)` by METIS_TAC [PAIR]
  \\ `?c6 xs6 j6 mF6 mT6. split_move_list (xs,j5,mF5,mT5,e) = (c6,xs6,j6,mF6,mT6)` by METIS_TAC [PAIR]
  \\ ASM_SIMP_TAC std_ss [LET_DEF] \\ STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [ref_stack_def,STAR_ASSOC] \\ REPEAT STRIP_TAC
  \\ ONCE_REWRITE_TAC [mc_move_list_def]
  \\ SIMP_TAC std_ss [w2w_SUB_EQ,SELECT_32_LEMMA,LET_DEF,w2w_w2w_LEMMA]
  \\ SEP_R_TAC \\ SIMP_TAC std_ss [EVAL ``(w2w ^ONE64):word32``]
  \\ SIMP_TAC std_ss [ref_heap_addr_NOT_ONE32]
  \\ ASSUME_TAC (GEN_ALL mc_move_thm)
  \\ SEP_I_TAC "mc_move"
  \\ Q.PAT_X_ASSUM `split_move xxx = yyy` MP_TAC
  \\ SEP_I_TAC "split_move"
  \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [w2w_0]
  \\ Q.PAT_X_ASSUM `!p. bbb ==> ccc`
       (MP_TAC o Q.SPEC `one (r14,ref_heap_addr h) * ref_stack (r14 + 0x4w) xs * p`)
  \\ FULL_SIMP_TAC (std_ss++star_ss) [] \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [STAR_ASSOC,w2w_w2w_LEMMA] \\ SEP_W_TAC
  \\ SEP_I_TAC "mc_move_list1"
  \\ Q.PAT_X_ASSUM `split_move_list xxx = yyy` MP_TAC
  \\ SEP_I_TAC "split_move_list"
  \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss []
  \\ Q.PAT_X_ASSUM `!p. bbb ==> ccc`
       (MP_TAC o Q.SPEC `one (r14,ref_heap_addr h5) * p`)
  \\ FULL_SIMP_TAC (std_ss++star_ss) [ADDR_w2w_ALIGNED] \\ REPEAT STRIP_TAC
  \\ ASM_SIMP_TAC std_ss [] \\ SEP_R_TAC);

val ref_mem_CUT = prove(
  ``!e b a m s p. (p * ref_mem a m b e) s ==> (p * ref_mem a (CUT(x,y)m) b e) s``,
  Induct \\ SIMP_TAC std_ss [ref_mem_def] \\ REPEAT STRIP_TAC
  \\ Cases_on `e<b` \\ FULL_SIMP_TAC std_ss [STAR_ASSOC] \\ RES_TAC
  \\ FULL_SIMP_TAC std_ss [CUT_def]
  \\ Cases_on `RANGE(x,y)e` \\ FULL_SIMP_TAC std_ss []
  \\ Cases_on `m e`
  \\ FULL_SIMP_TAC std_ss [ref_aux_def,SEP_CLAUSES,SEP_EXISTS_THM]
  THEN1 METIS_TAC [] THEN1 METIS_TAC []
  \\ Cases_on `p'` \\ Cases_on `r`
  \\ FULL_SIMP_TAC std_ss [ref_aux_def,SEP_CLAUSES,SEP_EXISTS_THM,oneTheory.one]
  \\ METIS_TAC []);

val mc_gc_thm = store_thm("mc_gc_thm",
  ``memory_ok mF /\ memory_ok mT /\ e < 2**31 /\ (r6 && 3w = 0w) /\ (r15 && 3w = 0w) /\ (r14 && 3w = 0w) ==>
    (split_gc (xs,mF,mT,e) = (T,i2,xs2,mT2,e)) ==>
    (ref_mem r6 mF 0 e * ref_mem r15 mT 0 e * ref_stack r14 xs * p) (fun2set (f,df)) ==>
    ?fi.
      memory_ok mT2 /\ mc_gc_pre (r6,r14,r15,df,f) /\
      (mc_gc (r6,r14,r15,df,f) = (r15,n2w (2 * i2),r6,df,fi)) /\
      (ref_mem r6 (\x.H_EMP) 0 e * ref_mem r15 mT2 0 e * ref_stack r14 xs2 * p) (fun2set (fi,df))``,
  STRIP_TAC \\ ONCE_REWRITE_TAC [EQ_SYM_EQ] \\ SIMP_TAC std_ss [split_gc_def]
  \\ `?c6 xs6 j6 mF6 mT6. split_move_list (xs,0,mF,mT,e) = (c6,xs6,j6,mF6,mT6)` by METIS_TAC [PAIR]
  \\ `?c7 i7 mF7 mT7. split_gc_loop (0,j6,mF6,mT6,e) = (c7,i7,mF7,mT7)` by METIS_TAC [PAIR]
  \\ ASM_SIMP_TAC std_ss [LET_DEF] \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss []
  \\ SIMP_TAC std_ss [mc_gc_def,LET_DEF,EVAL ``(31 -- 0) (~0x0w):word64``]
  \\ ASSUME_TAC (RW [MULT_CLAUSES] (SUBST_INST [``j:num``|->``0:num``] (GEN_ALL mc_move_list_thm)))
  \\ SEP_I_TAC "mc_move_list"
  \\ Q.PAT_X_ASSUM `split_move_list xxx=yyy` MP_TAC
  \\ SEP_I_TAC "split_move_list"
  \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss []
  \\ Q.PAT_X_ASSUM `!p.bb` (MP_TAC o Q.SPEC `p`)
  \\ FULL_SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC
  \\ ASM_SIMP_TAC std_ss []
  \\ ASSUME_TAC (RW [MULT_CLAUSES] (SUBST_INST [``i:num``|->``0:num``] (GEN_ALL mc_gc_loop_thm)))
  \\ FULL_SIMP_TAC std_ss [mc_gc_loop1_THM]
  \\ SEP_I_TAC "mc_gc_loop"
  \\ Q.PAT_X_ASSUM `split_gc_loop xxx=yyy` MP_TAC
  \\ SEP_I_TAC "split_gc_loop"
  \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss []
  \\ Q.PAT_X_ASSUM `!r6.bb` (MP_TAC o Q.SPECL [`ref_stack r14 xs6 * p`])
  \\ FULL_SIMP_TAC (std_ss++star_ss) [] \\ REPEAT STRIP_TAC
  \\ ASM_SIMP_TAC std_ss []
  \\ REPEAT STRIP_TAC
  THEN1 (SIMP_TAC std_ss [memory_ok_def,CUT_EQ] \\ METIS_TAC [memory_ok_def])
  \\ `(\x. H_EMP) = CUT (0,0) mF7` by
    (SIMP_TAC std_ss [CUT_def,FUN_EQ_THM,IN_DEF,RANGE_def])
  \\ FULL_SIMP_TAC std_ss [STAR_ASSOC]
  \\ `((p * ref_stack r14 xs6 * ref_mem r15 mT7 0 e) *
       ref_mem r6 mF7 0 e) (fun2set (fi',df))` by FULL_SIMP_TAC (std_ss++star_ss) []
  \\ `((p * ref_stack r14 xs6 * ref_mem r15 mT7 0 e) *
       ref_mem r6 (CUT (0,0) mF7) 0 e) (fun2set (fi',df))` by
         (MATCH_MP_TAC ref_mem_CUT \\ FULL_SIMP_TAC (std_ss++star_ss) [])
  \\ `((p * ref_stack r14 xs6 * ref_mem r6 (CUT (0,0) mF7) 0 e) *
       ref_mem r15 (CUT (0,i7) mT7) 0 e) (fun2set (fi',df))` by
         (MATCH_MP_TAC ref_mem_CUT \\ FULL_SIMP_TAC (std_ss++star_ss) [])
  \\ FULL_SIMP_TAC (std_ss++star_ss) []);

val word64_3232_def = Define `
  word64_3232 (w:word64) = (w2w w, w2w (w >>> 32)):word32 # word32`;

val word3232_64_def = Define `
  word3232_64 ((w0,w1):word32 # word32) = w2w w1 << 32 !! w2w w0`;

val ref_static_def = Define `
  (ref_static a [] = emp) /\
  (ref_static a (x::xs) =
     let (w0,w1) = word64_3232 x in
       one (a,w0) * one (a+4w,w1) * ref_static (a+8w) xs)`;

val ref_stack_space_def = Define `
  (ref_stack_space sp 0 = emp) /\
  (ref_stack_space sp (SUC n) =
     ref_stack_space (sp-4w) n * SEP_EXISTS w. one (sp:word64-4w,w:word32))`;

val ok_split_heap_def = Define `
  ok_split_heap (roots,m,i,e) =
    i <= e /\ ADDR_SET roots UNION D1 m SUBSET D0 m /\ memory_ok m /\ (R0 m = {}) /\
    !k. i <= k ==> (m k = H_EMP)`;

val RANGE_LEMMA = prove(
  ``(RANGE (0,0) = {}) /\
    (RANGE (0,SUC i) = i INSERT RANGE (0,i))``,
  SIMP_TAC std_ss [EXTENSION,IN_INSERT,NOT_IN_EMPTY]
  \\ SIMP_TAC std_ss [RANGE_def,IN_DEF] \\ DECIDE_TAC);

val IMP_part_heap = prove(
  ``memory_ok m /\ b <= e ==> ?t. part_heap b e m t``,
  Induct_on `e-b` \\ REPEAT STRIP_TAC
  THEN1 (`e = b` by DECIDE_TAC \\ METIS_TAC [part_heap_cases])
  \\ ONCE_REWRITE_TAC [part_heap_cases]
  \\ `(v = e - (b+1)) /\ b+1<=e /\ ~(b = e)` by DECIDE_TAC \\ RES_TAC
  \\ Cases_on `m b` \\ FULL_SIMP_TAC (srw_ss()) [isBLOCK_def]
  \\ Cases_on `p` \\ Cases_on `r` \\ FULL_SIMP_TAC std_ss [memory_ok_def]
  \\ Q.EXISTS_TAC `t` \\ RES_TAC \\ FULL_SIMP_TAC std_ss []
  \\ SIMP_TAC std_ss [EMP_RANGE_def,IN_DEF,RANGE_def] \\ REPEAT STRIP_TAC
  \\ `F` by DECIDE_TAC);

val IN_D0 = SIMP_CONV bool_ss [IN_DEF, D0_def] ``x IN D0 m``
val IN_D1 = (REWRITE_CONV [IN_DEF] THENC SIMP_CONV bool_ss [D1_def])
                ``x IN D1 m``

val ok_split_heap = store_thm("ok_split_heap",
  ``!roots m i e.
      ok_split_heap (roots,m,i,e) =
      memory_ok m /\ ?h. ok_full_heap (h,roots) (0,i,e,e,e + e,m)``,
  REPEAT STRIP_TAC \\ SIMP_TAC std_ss [ok_split_heap_def,ok_full_heap_def]
  \\ REVERSE EQ_TAC \\ STRIP_TAC \\ ASM_SIMP_TAC std_ss [] THEN1
   (FULL_SIMP_TAC std_ss [RANGE_def,NOT_LESS,UNION_SUBSET,ok_heap_def]
    \\ REPEAT STRIP_TAC THEN1
     (FULL_SIMP_TAC std_ss [SUBSET_DEF] \\ REPEAT STRIP_TAC \\ RES_TAC
      \\ FULL_SIMP_TAC std_ss [ref_heap_mem_def]
      \\ FULL_SIMP_TAC std_ss [IN_DEF,D0_def,R0_def,EXTENSION,NOT_IN_EMPTY]
      \\ SRW_TAC [] [] \\ METIS_TAC [PAIR])
    THEN1
     (ASM_SIMP_TAC std_ss [SUBSET_DEF,IN_DEF,D0_def]
      \\ FULL_SIMP_TAC std_ss [D1_def,ref_heap_mem_def,SUBSET_DEF]
      \\ REPEAT STRIP_TAC
      \\ Cases_on `k IN FDOM h` \\ FULL_SIMP_TAC (srw_ss()) []
      \\ FULL_SIMP_TAC std_ss [POINTERS_def,IN_UNIV,GSPECIFICATION]
      \\ `x IN FDOM h` by METIS_TAC []
      \\ ASM_SIMP_TAC std_ss [] \\ METIS_TAC [PAIR])
    \\ FULL_SIMP_TAC std_ss [SUBSET_DEF] \\ REPEAT STRIP_TAC \\ RES_TAC
    \\ FULL_SIMP_TAC std_ss [ref_heap_mem_def]
    \\ FULL_SIMP_TAC std_ss [IN_DEF,D0_def,R0_def,EXTENSION,NOT_IN_EMPTY]
    \\ SRW_TAC [] [])
  \\ FULL_SIMP_TAC std_ss [RANGE_def,NOT_LESS]
  \\ Q.EXISTS_TAC `FUN_FMAP (\a. getBLOCK (m a)) (D0 m)`
  \\ `FINITE (D0 m)` by
   (`D0 m = D0 m INTER RANGE(0,i)` by
      (SIMP_TAC std_ss [EXTENSION,IN_INTER]
       \\ REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC
       \\ ASM_SIMP_TAC std_ss []
       \\ SIMP_TAC std_ss [IN_DEF,RANGE_def] \\ CCONTR_TAC
       \\ FULL_SIMP_TAC std_ss [NOT_LESS] \\ RES_TAC
       \\ FULL_SIMP_TAC (srw_ss()) [IN_DEF,D0_def])
    \\ POP_ASSUM (fn th => ONCE_REWRITE_TAC [th])
    \\ MATCH_MP_TAC FINITE_INTER \\ DISJ2_TAC
    \\ REPEAT (POP_ASSUM (K ALL_TAC))
    \\ Induct_on `i`
    \\ ASM_SIMP_TAC std_ss [RANGE_LEMMA,FINITE_EMPTY,FINITE_INSERT])
  \\ REPEAT STRIP_TAC
  THEN1 (METIS_TAC [IMP_part_heap,DECIDE ``0<=m:num``])
  THEN1
   (ASM_SIMP_TAC std_ss [ref_heap_mem_def,FUN_FMAP_DEF]
    \\ STRIP_TAC \\ Cases_on `a IN D0 m` \\ ASM_SIMP_TAC std_ss []
    \\ FULL_SIMP_TAC std_ss [EXTENSION,NOT_IN_EMPTY]
    \\ FULL_SIMP_TAC std_ss [D0_def,IN_DEF,getBLOCK_def,R0_def]
    \\ Cases_on `m a` \\ FULL_SIMP_TAC (srw_ss()) [] \\ POP_ASSUM MP_TAC
    \\ FULL_SIMP_TAC (srw_ss()) [] \\ METIS_TAC [PAIR])
  THEN1
   (ASM_SIMP_TAC std_ss [ref_heap_mem_def,
      FUN_FMAP_DEF,ok_heap_def,UNION_SUBSET,POINTERS_def]
    \\ ASM_SIMP_TAC std_ss [SUBSET_DEF,GSPECIFICATION,IN_UNIV]
    \\ REPEAT STRIP_TAC \\ POP_ASSUM MP_TAC \\ POP_ASSUM MP_TAC
    \\ ASM_SIMP_TAC std_ss [FUN_FMAP_DEF,ADDR_SET_def,GSPECIFICATION]
    \\ FULL_SIMP_TAC std_ss [UNION_SUBSET]
    \\ FULL_SIMP_TAC std_ss [IN_D0,getBLOCK_def,SUBSET_DEF,IN_D1]
    \\ FULL_SIMP_TAC std_ss [ADDR_SET_def,GSPECIFICATION]
    \\ FULL_SIMP_TAC std_ss [IN_D0,getBLOCK_def,SUBSET_DEF]
    \\ FULL_SIMP_TAC std_ss [IN_D1,ADDR_SET_def,GSPECIFICATION]
    \\ METIS_TAC []));

val _ = export_theory();
