open HolKernel boolLib bossLib Parse; val _ = new_theory "lisp_equal";

open wordsTheory arithmeticTheory wordsLib listTheory pred_setTheory pairTheory; 
open combinTheory finite_mapTheory addressTheory;

open decompilerLib tailrecLib tailrecTheory cheney_gcTheory cheney_allocTheory compilerLib;
open lisp_gcTheory lisp_typeTheory lisp_invTheory;


infix \\ 
val op \\ = op THEN;
val _ = map Parse.hide ["r0","r1","r2","r3","r4","r5","r6","r7","r8","r9","r10","r11","r12","r13"];
val RW = REWRITE_RULE;
val RW1 = ONCE_REWRITE_RULE;


val (th,arm_eq_loop_def) = basic_decompile_arm "arm_eq_loop" NONE `
  E1530004 (* LOOP:cmp r3,r4 *)
  0A00000A (* beq NEXT *)
  E1835004 (* orr r5,r3,r4 *)
  E3150003 (* tst r5,#3 *)
  1A00000D (* bne EXIT *)
  E5935004 (* ldr r5,[r3,#4] *)
  E5933000 (* ldr r3,[r3] *)
  E5946004 (* ldr r6,[r4,#4] *)
  E5944000 (* ldr r4,[r4] *)
  E4875004 (* str r5,[r7],#4 *)
  E4876004 (* str r6,[r7],#4 *)
  E2888001 (* add r8,r8,#1 *)
  EAFFFFF2 (* b LOOP *)
  E3580000 (* NEXT:cmp r8,#0 *)
  0A000003 (* beq EXIT *)
  E5374004 (* ldr r4,[r7,#-4]! *)
  E5373004 (* ldr r3,[r7,#-4]! *)
  E2488001 (* sub r8,r8,#1 *)
  EAFFFFEC (* b LOOP *)`;

val (th,arm_eq_init_def) = basic_decompile_arm "arm_eq_init" NONE `
  E28A7008 (* add r7,r10,#8 *)
  E3550000 (* cmp r5,#0 *)
  10877006 (* addne r7,r7,r6 *)`;

val (th,arm_eq_assign_def) = basic_decompile_arm "arm_eq_assign" NONE `
  E1530004 (* EXIT:cmp r3,r4 *)
  03A0300F (* moveq r3,#15 *)
  13A03003 (* movne r3,#3 *)`;

val (arm_eq_thm,arm_eq_def) = basic_decompile_arm "arm_eq" NONE `
  E1530004 (* cmp r3,r4 *)
  03A0300F (* moveq r3,#15 *)
  0A000025 (* beq EXIT2 *)
  E50A4014 (* str r4,[r10,#-20] *)
  E50A5010 (* str r5,[r10,#-16] *)
  E50A600C (* str r6,[r10,#-12] *)
  E50A7008 (* str r7,[r10,#-8] *)
  E50A8004 (* str r8,[r10,#-4] *)
  E51A501C (* ldr r5,[r10,#-28] *)
  E51A6020 (* ldr r6,[r10,#-32] *)
  insert: arm_eq_init
  E3A08000 (* mov r8,#0 *)
  insert: arm_eq_loop
  insert: arm_eq_assign
  E51A4014 (* ldr r4,[r10,#-20] *)
  E51A5010 (* ldr r5,[r10,#-16] *)
  E51A600C (* ldr r6,[r10,#-12] *)
  E51A7008 (* ldr r7,[r10,#-8] *)
  E51A8004 (* ldr r8,[r10,#-4] *)`;

val _ = save_thm("arm_eq_thm",arm_eq_thm);

val _ = Hol_datatype `XExp = XDot of XExp => XExp | XNum of word30 | XSym of word30`;
val XExp_11 = fetch "-" "XExp_11";
val XExp_distinct = fetch "-" "XExp_distinct";

val lisp_tree_def = Define `
  (lisp_tree (XDot x y) (a,m) d = a IN d /\ a + 4w:word32 IN d /\ ALIGNED a /\
     lisp_tree x (m a,m) d /\ lisp_tree y (m (a + 4w),m) d) /\ 
  (lisp_tree (XNum w) (a,m) d = (a = ADDR32 w + 2w)) /\ 
  (lisp_tree (XSym w) (a,m) d = (a = ADDR32 w + 3w))`;

val lisp_stack_def = Define `
  (lisp_stack [] (a,m,d,e) = ALIGNED a) /\
  (lisp_stack ((x,y)::xs) (a,m,d,e) = (a - 4w) IN e /\ (a - 8w) IN e /\
     lisp_tree y (m (a - 4w),m) d /\ lisp_tree x (m (a - 8w),m) d /\ lisp_stack xs (a-8w,m,d,e))`;

val lisp_tree_11 = prove(
  ``!x y a m d. lisp_tree x (a,m) d /\ lisp_tree y (a,m) d ==> (x = y)``,
  Induct \\ Cases_on `y` \\ REWRITE_TAC [lisp_tree_def,SExp_11]
  \\ METIS_TAC [NOT_ALIGNED,ALIGNED_ADDR32,ALIGNED_add_2_and_3,ALIGNED_add_3_and_3,
       EVAL ``2w = 3w:word32``,WORD_EQ_ADD_RCANCEL,ADDR32_11]);        

val lisp_tree_ALIGNED_LEMMA = prove(
  ``~ALIGNED r3 /\ lisp_tree x (r3,m) d /\ ~(r3 = r4) /\ lisp_tree y (r4,m) d ==>
    ~(x = y)``,
  REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [] \\ Cases_on `y`
  \\ FULL_SIMP_TAC std_ss [lisp_tree_def]);

val XDEPTH_def = Define `
  (XDEPTH (XDot x y) = SUC (MAX (XDEPTH x) (XDEPTH y))) /\
  (XDEPTH (XSym w) = 0) /\
  (XDEPTH (XNum w) = 0)`;

val XSIZE_def = Define `
  (XSIZE (XDot x y) = SUC ((XSIZE x) + (XSIZE y))) /\
  (XSIZE (XSym w) = 0) /\
  (XSIZE (XNum w) = 0)`;

val SUM_XSIZE_def = Define `
  (SUM_XSIZE [] = 0) /\
  (SUM_XSIZE (x::xs) = XSIZE x + SUM_XSIZE xs)`;

val MAX_XDEPTH_def = Define `
  (MAX_XDEPTH [] = 0) /\
  (MAX_XDEPTH (x::xs) = MAX (XDEPTH x + LENGTH (x::xs)) (MAX_XDEPTH xs))`;

val LENGTH_LESS_EQ_SUM_XDEPTH = prove(
  ``!xs. LENGTH xs <= MAX_XDEPTH xs``,
  Cases \\ REWRITE_TAC [LENGTH,MAX_XDEPTH_def,MAX_DEF] THEN1 DECIDE_TAC
  \\ Cases_on `XDEPTH h + SUC (LENGTH t) < MAX_XDEPTH t`
  \\ ASM_SIMP_TAC std_ss [] \\ DECIDE_TAC);

val MAX_XDEPTH_DOT = prove(
  ``MAX_XDEPTH (x1::x2::ys) <= MAX_XDEPTH (XDot x1 x2::ys)``,
  SIMP_TAC std_ss [MAX_XDEPTH_def,XDEPTH_def,ADD1,LENGTH]  
  \\ SIMP_TAC std_ss [MAX_DEF] \\ DECIDE_TAC);

val MAX_ADDRESSES_def = Define `
  MAX_ADDRESSES r7 ys a = 
    ?i. (a = r7 + 8w - 8w * n2w (LENGTH ys) + n2w (4 * i)) /\ i < 2 * MAX_XDEPTH ys - 2`;

val WORD_ADD_EQ = prove(
  ``!x y. ((x + y = x) = (y = 0w)) /\ ((y + x = x) = (y = 0w))``,      
  METIS_TAC [WORD_EQ_ADD_RCANCEL,WORD_EQ_ADD_LCANCEL,WORD_ADD_0])

val lisp_tree_IGNORE_WRITE = prove(
  ``!a d. ~(a IN d) ==> !x w v m. lisp_tree x (w,(a =+ v) m) d = lisp_tree x (w,m) d``,
  NTAC 3 STRIP_TAC \\ Induct 
  \\ ASM_SIMP_TAC std_ss [lisp_tree_def,APPLY_UPDATE_THM] \\ METIS_TAC []);
    
val lisp_stack_LEMMA = prove(
  ``!ys a m d e. lisp_stack ys (a,m,d,e) ==> ALIGNED a``,
  Induct \\ ASM_SIMP_TAC std_ss [lisp_stack_def] 
  \\ Cases \\ ASM_SIMP_TAC std_ss [lisp_stack_def] 
  \\ REPEAT STRIP_TAC \\ RES_TAC
  \\ FULL_SIMP_TAC std_ss [GSYM (EVAL ``4w+4w:word32``),WORD_SUB_PLUS,ALIGNED_SUB_4]);

val LEMMA = prove(
  ``!a b. ALIGNED a /\ ALIGNED b /\ a <=+ b /\ ~(a = 0w) /\ 
          ~(a - 4w = 0w) /\ ~(a - 8w = 0w) ==>
          ~(b = a - 4w) /\ ~(b = a - 8w) /\ a - 8w <=+ b``,
  NTAC 3 STRIP_TAC
  \\ ASSUME_TAC (Q.SPEC `a - 4w` ALIGNED_LESS_ADD)
  \\ ASSUME_TAC (Q.SPEC `a - 4w - 4w` ALIGNED_LESS_ADD)
  \\ FULL_SIMP_TAC std_ss [WORD_SUB_ADD,ALIGNED_SUB_4]
  \\ RES_TAC
  \\ FULL_SIMP_TAC std_ss [GSYM WORD_SUB_PLUS,word_add_n2w]
  \\ IMP_RES_TAC WORD_LOWER_TRANS
  \\ IMP_RES_TAC WORD_LOWER_LOWER_EQ_TRANS
  \\ IMP_RES_TAC WORD_LOWER_NOT_EQ
  \\ IMP_RES_TAC WORD_LOWER_IMP_LOWER_OR_EQ
  \\ ASM_SIMP_TAC std_ss []);

val lisp_stack_IGNORE_WRITE = prove(
  ``!ys a b w m d e. ALIGNED a /\ ALIGNED b /\ a <=+ b /\ ~(0w IN e) /\ (a IN e) /\ ~(b IN d) /\
                     lisp_stack ys (a,m,d,e) ==> lisp_stack ys (a,(b =+ w) m,d,e)``,
  Induct \\ SIMP_TAC std_ss [lisp_stack_def]
  \\ Cases \\ SIMP_TAC std_ss [lisp_stack_def] \\ NTAC 7 STRIP_TAC
  \\ ASM_SIMP_TAC std_ss [lisp_tree_IGNORE_WRITE,APPLY_UPDATE_THM]
  \\ `~(a = 0w) /\ ~(a - 4w = 0w) /\ ~(a - 8w = 0w)` by METIS_TAC []
  \\ `~(b = a - 4w) /\ ~(b = a - 8w) /\ a - 8w <=+ b` by METIS_TAC [LEMMA]
  \\ FULL_SIMP_TAC std_ss []
  \\ Q.PAT_ASSUM `!x.bbb` MATCH_MP_TAC  
  \\ ASM_SIMP_TAC std_ss [word_sub_def]
  \\ MATCH_MP_TAC ALIGNED_ADD \\ ASM_SIMP_TAC std_ss [ALIGNED_NEG] \\ EVAL_TAC);

val arm_eq_loop_spec_lemma = prove(  (* VERY SLOW PROOF *)
  ``!ys:(XExp # XExp) list x y d e m r3 r4 r5 r6 r7 r8. (d INTER e = {}) /\
      (arm_eq_loop (r3,r4,r5,r6,r7,r8,df,m) = (u3,u4,u5,u6,u7,u8,udf,uf)) /\
      (r8 = n2w (LENGTH ys)) /\ (MAX_XDEPTH (x::MAP FST ys) < 2**32) /\
      (MAX_ADDRESSES r7 (x::MAP FST ys)) SUBSET e /\ ~(0w IN e) /\ e SUBSET df /\ d SUBSET df /\
      lisp_stack ys (r7,m,d,e) /\ lisp_tree x (r3,m) d /\ lisp_tree y (r4,m) d ==>
      arm_eq_loop_pre (r3,r4,r5,r6,r7,r8,df,m) /\
      ((u3 = u4) = (MAP FST ys = MAP SND ys) /\ (x = y)) /\
      (!x. ~(x IN e) ==> (m x = uf x)) /\ (df = udf)``,
  STRIP_TAC \\ STRIP_TAC \\ completeInduct_on `2 * (SUM_XSIZE (MAP FST ys) + XSIZE x) + LENGTH ys`
  \\ ONCE_REWRITE_TAC [arm_eq_loop_def] \\ NTAC 14 STRIP_TAC \\ Cases_on `r3 = r4` 
  THENL [  
    FULL_SIMP_TAC std_ss [] \\ IMP_RES_TAC lisp_tree_11
    \\ FULL_SIMP_TAC std_ss [] 
    \\ `ALIGNED r7` by METIS_TAC [lisp_stack_LEMMA]
    \\ Cases_on `ys` THEN1 
        (SIMP_TAC (std_ss++tailrecLib.tailrec_part_ss()) []
         \\ FULL_SIMP_TAC std_ss [LENGTH,MAP] \\ METIS_TAC [])
    \\ `~(n2w (LENGTH (h::t)) = 0w:word32)` by 
      (ASM_SIMP_TAC (std_ss++SIZES_ss) [n2w_11]
       \\ `LENGTH (y::MAP FST (h::t)) <= MAX_XDEPTH (y::MAP FST (h::t))` by 
           METIS_TAC [LENGTH_LESS_EQ_SUM_XDEPTH]
       \\ FULL_SIMP_TAC std_ss [LENGTH,GSYM LESS_EQ]
       \\ FULL_SIMP_TAC std_ss [LENGTH_MAP,LENGTH]
       \\ `SUC (LENGTH t) < 4294967296` by DECIDE_TAC
       \\ ASM_SIMP_TAC std_ss [LESS_MOD] \\ DECIDE_TAC)
    \\ FULL_SIMP_TAC std_ss [LENGTH,ADD1,GSYM word_add_n2w,WORD_ADD_SUB,LET_DEF]
    \\ Cases_on `h`
    \\ FULL_SIMP_TAC std_ss [lisp_stack_def,MAP,CONS_11,SUM_XSIZE_def]
    \\ `2 * (SUM_XSIZE (MAP FST t) + XSIZE q) + LENGTH t <
        2 * (XSIZE q + SUM_XSIZE (MAP FST t) + XSIZE y) + (LENGTH t + 1)` by DECIDE_TAC       
    \\ Q.PAT_ASSUM `!x. bbb` 
        (STRIP_ASSUME_TAC o RW [] o Q.SPEC `q` o Q.SPEC `t` o UNDISCH o 
         Q.SPEC `2 * (SUM_XSIZE (MAP FST t) + XSIZE q) + LENGTH (t:(XExp # XExp) list)`)
    \\ Q.PAT_ASSUM `!x. bbb` 
        (MP_TAC o Q.SPECL [`r`,`d`,`e`,`m`,`m (r7 - 8w:word32)`,`m (r7 - 4w:word32)`,`r5`,`r6`,`r7 - 8w`])
    \\ FULL_SIMP_TAC std_ss [GSYM WORD_SUB_PLUS,word_add_n2w,MAX_XDEPTH_def]       
    \\ REVERSE (`MAX_ADDRESSES (r7 - 8w) (q::MAP FST t) SUBSET e` by ALL_TAC) THENL [
      ASM_SIMP_TAC bool_ss [ALIGNED_INTRO] \\ STRIP_TAC
      \\ ONCE_REWRITE_TAC [ALIGNED_MOD_4]
      \\ ASM_SIMP_TAC std_ss [WORD_ADD_0,WORD_SUB_RZERO,AC CONJ_ASSOC CONJ_COMM]
      \\ METIS_TAC [SUBSET_DEF],
      MATCH_MP_TAC SUBSET_TRANS
      \\ Q.EXISTS_TAC `MAX_ADDRESSES r7 (y::q::MAP FST t)`
      \\ ASM_SIMP_TAC std_ss []
      \\ SIMP_TAC std_ss [SUBSET_DEF,IN_DEF,MAX_ADDRESSES_def]
      \\ REPEAT STRIP_TAC
      \\ FULL_SIMP_TAC std_ss [WORD_MULT_CLAUSES,LENGTH,n2w_SUC,WORD_SUB_PLUS]
      \\ Q.EXISTS_TAC `i` \\ REWRITE_TAC [WORD_SUB_ADD,WORD_ADD_SUB]
      \\ REVERSE (`MAX_XDEPTH (q::MAP FST t) <= MAX_XDEPTH (y::q::MAP FST t)` by ALL_TAC)
      THEN1 DECIDE_TAC
      \\ CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [MAX_XDEPTH_def]))    
      \\ SIMP_TAC std_ss [MAX_DEF]],
    FULL_SIMP_TAC std_ss [LET_DEF,RW1 [WORD_AND_COMM] (GSYM ALIGNED_def)]
    \\ SIMP_TAC std_ss [GSYM ALIGNED_def,RW1 [WORD_AND_COMM] (GSYM ALIGNED_def)]
    \\ SIMP_TAC std_ss [ALIGNED_CLAUSES,ALIGNED_SUB_4]
    \\ REVERSE (Cases_on `ALIGNED (r3 !! r4)`) \\ FULL_SIMP_TAC std_ss []
    THEN1 METIS_TAC [ALIGNED_OR,lisp_tree_ALIGNED_LEMMA]        
    \\ `ALIGNED r7` by METIS_TAC [lisp_stack_LEMMA]
    \\ FULL_SIMP_TAC std_ss [ALIGNED_OR,GSYM WORD_ADD_ASSOC,word_add_n2w]    
    \\ `?x1 x2. x = XDot x1 x2` by  
       (Cases_on `x` \\ FULL_SIMP_TAC std_ss [XExp_11,XExp_distinct,lisp_tree_def]
        \\ METIS_TAC [ALIGNED_ADDR32,NOT_ALIGNED])
    \\ `?y1 y2. y = XDot y1 y2` by 
       (Cases_on `y` \\ FULL_SIMP_TAC std_ss [XExp_11,XExp_distinct,lisp_tree_def]
        \\ METIS_TAC [ALIGNED_ADDR32,NOT_ALIGNED])
    \\ FULL_SIMP_TAC std_ss [XExp_11,lisp_tree_def]
    \\ `2 * (SUM_XSIZE (MAP FST ((x2,y2)::ys)) + XSIZE x1) +
        LENGTH ((x2,y2)::ys) <
        2 * (SUM_XSIZE (MAP FST ys) + XSIZE (XDot x1 x2)) + LENGTH ys` by     
     (SIMP_TAC std_ss [SUM_XSIZE_def,XSIZE_def,LENGTH,MAP,ADD1] \\ DECIDE_TAC)
    \\ Q.PAT_ASSUM `!x. bbb` 
        (STRIP_ASSUME_TAC o RW [MAP,CONS_11] o Q.SPECL [`(x2,y2)::ys`,`x1`] o UNDISCH o 
         Q.SPEC `2 * (SUM_XSIZE (MAP FST ((x2,y2)::ys)) + XSIZE x1) + LENGTH (((x2,y2)::ys):(XExp # XExp) list)`)
    \\ Q.PAT_ASSUM `!x. bbb` 
        (MP_TAC o Q.SPECL [`y1`,`d`,`e`,`(r7 + 4w =+ m (r4 + 4w:word32)) ((r7 =+ m (r3 + 4w:word32)) m)`,
          `m (r3:word32)`,`m (r4:word32)`,`m (r3 + 4w:word32)`,`m (r4 + 4w:word32)`,`r7 + 8w`])
    \\ ASM_SIMP_TAC std_ss [LENGTH,ADD1]           
    \\ `MAX_XDEPTH (x1::x2::MAP FST ys) < 4294967296` by METIS_TAC [LESS_EQ_LESS_TRANS,MAX_XDEPTH_DOT]
    \\ ASM_SIMP_TAC std_ss []         
    \\ `MAX_ADDRESSES (r7 + 8w) (x1::x2::MAP FST ys) SUBSET e` by ALL_TAC
    THENL [       
      MATCH_MP_TAC SUBSET_TRANS
      \\ Q.EXISTS_TAC `MAX_ADDRESSES r7 (XDot x1 x2::MAP FST ys)`
      \\ ASM_SIMP_TAC std_ss []
      \\ SIMP_TAC std_ss [SUBSET_DEF,IN_DEF,MAX_ADDRESSES_def]
      \\ REPEAT STRIP_TAC
      \\ FULL_SIMP_TAC std_ss [WORD_MULT_CLAUSES,LENGTH,n2w_SUC,WORD_SUB_PLUS,WORD_ADD_SUB]
      \\ Q.EXISTS_TAC `i` \\ REWRITE_TAC []
      \\ REVERSE (`MAX_XDEPTH (x1::x2::MAP FST ys) <= MAX_XDEPTH (XDot x1 x2::MAP FST ys)` by ALL_TAC)
      THEN1 DECIDE_TAC \\ METIS_TAC [MAX_XDEPTH_DOT],     
      ASM_SIMP_TAC std_ss []
      \\ `r7 IN MAX_ADDRESSES r7 (XDot x1 x2::MAP FST ys)` by 
       (SIMP_TAC std_ss [IN_DEF,MAX_ADDRESSES_def]
        \\ Q.EXISTS_TAC `2 * LENGTH (MAP FST ys)`
        \\ SIMP_TAC std_ss [LENGTH,n2w_SUC,WORD_MULT_CLAUSES,WORD_SUB_PLUS,WORD_ADD_SUB]
        \\ SIMP_TAC std_ss [MULT_ASSOC,word_mul_n2w,WORD_SUB_ADD]
        \\ REVERSE (`LENGTH (MAP FST ys) + 1 < MAX_XDEPTH (XDot x1 x2::MAP FST ys)` by ALL_TAC)
        THEN1 DECIDE_TAC
        \\ SIMP_TAC std_ss [MAX_XDEPTH_def,XDEPTH_def,ADD1,LENGTH] 
        \\ DISJ1_TAC \\ DECIDE_TAC)
      \\ `r7 + 4w IN MAX_ADDRESSES r7 (XDot x1 x2::MAP FST ys)` by 
       (SIMP_TAC std_ss [IN_DEF,MAX_ADDRESSES_def]
        \\ Q.EXISTS_TAC `2 * LENGTH (MAP FST ys) + 1`
        \\ SIMP_TAC std_ss [LENGTH,n2w_SUC,WORD_MULT_CLAUSES,WORD_SUB_PLUS,WORD_ADD_SUB]
        \\ SIMP_TAC std_ss [MULT_ASSOC,word_mul_n2w,WORD_SUB_ADD,LEFT_ADD_DISTRIB,GSYM word_add_n2w]
        \\ SIMP_TAC std_ss [WORD_ADD_ASSOC,WORD_SUB_ADD]        
        \\ REVERSE (`LENGTH (MAP FST ys) + 1 < MAX_XDEPTH (XDot x1 x2::MAP FST ys)` by ALL_TAC)
        THEN1 DECIDE_TAC
        \\ SIMP_TAC std_ss [MAX_XDEPTH_def,XDEPTH_def,ADD1,LENGTH] 
        \\ DISJ1_TAC \\ DECIDE_TAC)
      \\ `~(r7 IN d) /\ ~(r7 + 4w IN d)` by METIS_TAC [SUBSET_DEF,EXTENSION,IN_INTER,NOT_IN_EMPTY]            
      \\ ASM_SIMP_TAC std_ss [lisp_tree_IGNORE_WRITE]
      \\ REVERSE (`lisp_stack ((x2,y2)::ys)
         (r7 + 8w,(r7 + 4w =+ m (r4 + 4w)) ((r7 =+ m (r3 + 4w)) m),d,e)` by ALL_TAC)
      THEN1 (ASM_SIMP_TAC std_ss [APPLY_UPDATE_THM] \\ METIS_TAC [SUBSET_DEF])
      \\ ASM_SIMP_TAC std_ss [lisp_stack_def,word_arith_lemma1,word_arith_lemma2,word_arith_lemma3,word_arith_lemma4,word_arith_lemma5,WORD_ADD_0]
      \\ STRIP_TAC THEN1 METIS_TAC [SUBSET_DEF]
      \\ STRIP_TAC THEN1 METIS_TAC [SUBSET_DEF]
      \\ ASM_SIMP_TAC (std_ss++SIZES_ss) [APPLY_UPDATE_THM,lisp_tree_IGNORE_WRITE,WORD_ADD_EQ,n2w_11]
      \\ `r7 IN e /\ r7 + 4w IN e` by METIS_TAC [SUBSET_DEF]
      \\ IMP_RES_TAC lisp_stack_LEMMA
      \\ `ALIGNED (r7+4w)` by FULL_SIMP_TAC std_ss [ALIGNED_CLAUSES]
      \\ `~(r7 + 4w = 0w)` by METIS_TAC []
      \\ IMP_RES_TAC ALIGNED_LESS_ADD
      \\ IMP_RES_TAC WORD_LOWER_IMP_LOWER_OR_EQ      
      \\ MATCH_MP_TAC lisp_stack_IGNORE_WRITE
      \\ ASM_SIMP_TAC std_ss [WORD_LOWER_EQ_REFL]    
      \\ MATCH_MP_TAC lisp_stack_IGNORE_WRITE
      \\ ASM_SIMP_TAC std_ss [WORD_LOWER_EQ_REFL]]]);

val arm_eq_loop_spec = 
  RW [lisp_stack_def,MAP,LENGTH] (Q.SPECL [`[]`] arm_eq_loop_spec_lemma);

val heap_half_def = Define `
  heap_half (a:word32,u,l:num) = 
    { a + n2w (if u then 8 * l + 8 + 4 * k else 8 + 4 * k) |k| k < 2 * l }`;

val IN_heap_half_LEMMA = prove(
  ``ch_arm (r,h,l) (r1,r2,r3,r4,r5,r6,a,df,f) /\ ALIGNED r1 ==>
    r1 IN heap_half (a, f (a-28w) = 0w, l) /\ 
    r1 + 4w IN heap_half (a, f (a-28w) = 0w, l)``,
  REWRITE_TAC [ch_arm_def,ch_word_def,ch_inv_def,ok_state_def]
  \\ SIMP_TAC std_ss [LET_DEF] \\ STRIP_TAC
  \\ Cases_on `x1` \\ FULL_SIMP_TAC std_ss [ref_field_def]
  THEN1 METIS_TAC [NOT_ALIGNED,ALIGNED_ADDR32]
  \\ `~(SUC n = 0)` by DECIDE_TAC
  \\ FULL_SIMP_TAC std_ss []
  \\ REPEAT (Q.PAT_ASSUM `rx = if bsdf then bb else bbb` (K ALL_TAC))
  \\ `SUC n IN RANGE ((if u then 1 + l else 1),i)` by METIS_TAC [MEM] 
  \\ Q.PAT_ASSUM `SUC n IN RANGE ((if u then 1 + l else 1),i)` MP_TAC
  \\ Q.PAT_ASSUM `i <= (if u then 1 + l else 1) + l` MP_TAC
  \\ REPEAT (POP_ASSUM (K ALL_TAC))
  \\ SIMP_TAC std_ss [heap_half_def,ref_addr_def,GSPECIFICATION]
  \\ SIMP_TAC std_ss [IN_DEF,RANGE_def,RW1[MULT_COMM]MULT]
  \\ Cases_on `u` \\ FULL_SIMP_TAC std_ss [EVAL ``1w = 0w:word32``] THENL [
    REPEAT STRIP_TAC THENL [
      Q.EXISTS_TAC `2 * (n - l)`
      \\ SIMP_TAC std_ss [MULT_ASSOC,AC ADD_ASSOC ADD_COMM]
      \\ `l + (n - l) = n` by DECIDE_TAC
      \\ ASM_REWRITE_TAC [GSYM LEFT_ADD_DISTRIB]
      \\ DECIDE_TAC,
      Q.EXISTS_TAC `2 * (n - l) + 1`
      \\ ASM_SIMP_TAC std_ss [LEFT_ADD_DISTRIB,MULT_ASSOC]
      \\ `8 * l + 8 + (8 * (n - l) + 4) = 8 * n + 8 + 4` by DECIDE_TAC
      \\ ASM_SIMP_TAC std_ss [word_add_n2w,GSYM WORD_ADD_ASSOC] \\ DECIDE_TAC],      
    REPEAT STRIP_TAC THENL [
      Q.EXISTS_TAC `2 * n`
      \\ SIMP_TAC std_ss [MULT_ASSOC,AC ADD_ASSOC ADD_COMM] \\ DECIDE_TAC,
      Q.EXISTS_TAC `2 * n + 1`
      \\ ASM_SIMP_TAC std_ss [LEFT_ADD_DISTRIB,MULT_ASSOC]
      \\ SIMP_TAC std_ss [GSYM word_add_n2w,AC WORD_ADD_ASSOC WORD_ADD_COMM] \\ DECIDE_TAC]]);

val IN_heap_half = prove(
  ``lisp_inv (x1,x2,x3,x4,x5,x6,limit) (r1,r2,r3,r4,r5,r6,a,df,f,s,rest) /\ isDot x1 ==>
    ALIGNED r1 /\ r1 IN heap_half (a, f (a-28w) = 0w, limit) /\ 
    r1 + 4w IN heap_half (a, f (a-28w) = 0w, limit)``,
  STRIP_TAC \\ `ALIGNED r1` by METIS_TAC [ALIGNED_def,lisp_inv_address]
  \\ FULL_SIMP_TAC std_ss [lisp_inv_def] \\ METIS_TAC [IN_heap_half_LEMMA]);

val heap_half_DISJOINT = prove(
  ``!a l. 16 * l < 2**32 ==> (heap_half(a,T,l) INTER heap_half(a,F,l) = {})``,
  SIMP_TAC std_ss [EXTENSION,IN_INTER,NOT_IN_EMPTY,heap_half_def,GSPECIFICATION]
  \\ REPEAT STRIP_TAC \\ CCONTR_TAC \\ REPEAT STRIP_TAC 
  \\ FULL_SIMP_TAC std_ss [] \\ FULL_SIMP_TAC std_ss [WORD_EQ_ADD_LCANCEL]
  \\ FULL_SIMP_TAC bool_ss [GSYM (EVAL ``16 * 268435456``),LT_MULT_LCANCEL]  
  \\ `8 * l + 8 + 4 * k < 4294967296` by DECIDE_TAC    
  \\ `8 + 4 * k' < 4294967296` by DECIDE_TAC    
  \\ FULL_SIMP_TAC (std_ss++SIZES_ss) [n2w_11,LESS_MOD]
  \\ DECIDE_TAC);

val SExp2XExp_def = Define `
  (SExp2XExp (Dot x y) sym = XDot (SExp2XExp x sym) (SExp2XExp y sym)) /\
  (SExp2XExp (Num n) sym = XNum (n2w n)) /\
  (SExp2XExp (Sym s) sym = XSym (@w. (ADDR32 w,s) IN sym))`;

val set_add_LEMMA = prove(
  ``!a x. (set_add a x = {}) ==> (x = {})``,
  SIMP_TAC std_ss [set_add_def,EXTENSION,NOT_IN_EMPTY]
  \\ STRIP_TAC \\ STRIP_TAC \\ STRIP_TAC
  \\ Cases \\ POP_ASSUM (ASSUME_TAC o Q.SPEC `(q + a,r)`)
  \\ FULL_SIMP_TAC std_ss [IN_DEF,set_add_def,WORD_ADD_SUB]);
  
val lisp_symbol_table_11_Sym = prove(
  ``lisp_symbol_table x (sa,rest) ==>
    (w1,s) IN x /\ (w2,s) IN x ==> (w1 = w2)``,
  `?dm m dg g. rest = (dm,m,dg,g)` by METIS_TAC [PAIR]
  \\ ASM_SIMP_TAC std_ss [lisp_symbol_table_def]
  \\ REPEAT STRIP_TAC
  \\ `(w1+sa,s) IN (set_add sa x)` by 
       FULL_SIMP_TAC std_ss [IN_DEF,set_add_def,WORD_ADD_SUB]
  \\ `(w2+sa,s) IN (set_add sa x)` by 
       FULL_SIMP_TAC std_ss [IN_DEF,set_add_def,WORD_ADD_SUB]
  \\ IMP_RES_TAC symbol_table_eq
  \\ METIS_TAC [WORD_EQ_ADD_RCANCEL]);

val lisp_tree_INTRO = prove(
  ``!r1. lisp_inv (x1,x2,x3,x4,x5,x6,limit) (r1,r2,r3,r4,r5,r6,a,df,f,s,rest) ==>
         lisp_tree (SExp2XExp x1 s) (r1,f) (heap_half(a,f(a-28w)=0w,limit)) /\
         (LDEPTH x1 = XDEPTH (SExp2XExp x1 s))``,
  REVERSE (Induct_on `x1`) THENL [
    FULL_SIMP_TAC std_ss [lisp_inv_def,ch_arm_def,ch_inv_def,ch_word_def]
    \\ REPEAT STRIP_TAC \\ REWRITE_TAC [SExp2XExp_def,LDEPTH_def,XDEPTH_def]
    \\ REWRITE_TAC [lisp_tree_def]
    \\ FULL_SIMP_TAC std_ss [MAP,CONS_11]
    \\ Cases_on `v1`
    \\ FULL_SIMP_TAC std_ss [lisp_ref_def]
    \\ `x1 = 0` by METIS_TAC [bijection_def,ONE_ONE_DEF]
    \\ FULL_SIMP_TAC std_ss [ref_field_def]
    \\ Q.PAT_ASSUM `(w,T) = y1` (fn th => REWRITE_TAC [GSYM th])
    \\ METIS_TAC [lisp_symbol_table_11_Sym],
    FULL_SIMP_TAC std_ss [lisp_inv_def,ch_arm_def,ch_inv_def,ch_word_def]
    \\ REPEAT STRIP_TAC \\ REWRITE_TAC [SExp2XExp_def,LDEPTH_def,XDEPTH_def]
    \\ REWRITE_TAC [lisp_tree_def]
    \\ FULL_SIMP_TAC std_ss [MAP,CONS_11]
    \\ Cases_on `v1`
    \\ FULL_SIMP_TAC std_ss [lisp_ref_def]
    \\ `x1 = 0` by METIS_TAC [bijection_def,ONE_ONE_DEF]
    \\ FULL_SIMP_TAC std_ss [ref_field_def]
    \\ Q.PAT_ASSUM `(w,F) = y1` (fn th => REWRITE_TAC [GSYM th]),
    REWRITE_TAC [SExp2XExp_def,lisp_tree_def]
    \\ REWRITE_TAC [SExp2XExp_def,LDEPTH_def,XDEPTH_def]
    \\ `isDot (Dot x1 x1')` by REWRITE_TAC [isDot_def]
    \\ STRIP_TAC \\ STRIP_TAC \\ REWRITE_TAC [GSYM CONJ_ASSOC]
    \\ NTAC 3 (STRIP_TAC THEN1 METIS_TAC [IN_heap_half])
    \\ `lisp_inv (CAR (Dot x1 x1'),x2,x3,x4,x5,x6,limit) (f r1,r2,r3,r4,r5,r6,a,df,f,s,rest)` by METIS_TAC [lisp_inv_car]
    \\ `lisp_inv (CDR (Dot x1 x1'),x2,x3,x4,x5,x6,limit) (f (r1+4w),r2,r3,r4,r5,r6,a,df,f,s,rest)` by METIS_TAC [lisp_inv_cdr]
    \\ FULL_SIMP_TAC std_ss [CAR_def,CDR_def] \\ METIS_TAC []]);

val SExp2XExp_11 = prove(
  ``!x1 x2 r1 r2. 
       lisp_inv (x1,x2,x3,x4,x5,x6,limit) (r1,r2,r3,r4,r5,r6,a,df,f,s,rest) ==>
       ((SExp2XExp x1 s = SExp2XExp x2 s) = (x1 = x2))``, 
  Induct THENL [
    Cases_on `x2`
    \\ SIMP_TAC std_ss [SExp2XExp_def,XExp_11,SExp_11,XExp_distinct,SExp_distinct]
    \\ `isDot (Dot x1 x1') /\ isDot (Dot S'' S0)` by REWRITE_TAC [isDot_def]
    \\ STRIP_TAC \\ STRIP_TAC \\ STRIP_TAC 
    \\ `lisp_inv (CAR (Dot x1 x1'),Dot S'' S0,x3,x4,x5,x6,limit) (f r1,r2,r3,r4,r5,r6,a,df,f,s,rest)` by METIS_TAC [lisp_inv_car]
    \\ `lisp_inv (CAR (Dot x1 x1'),CAR (Dot S'' S0),x3,x4,x5,x6,limit) (f r1,f r2,r3,r4,r5,r6,a,df,f,s,rest)` by METIS_TAC [lisp_inv_car]
    \\ FULL_SIMP_TAC std_ss [CAR_def]
    \\ `lisp_inv (CDR (Dot x1 x1'),Dot S'' S0,x3,x4,x5,x6,limit) (f (r1+4w),r2,r3,r4,r5,r6,a,df,f,s,rest)` by METIS_TAC [lisp_inv_cdr]
    \\ `lisp_inv (CDR (Dot x1 x1'),CDR (Dot S'' S0),x3,x4,x5,x6,limit) (f (r1+4w),f (r2+4w),r3,r4,r5,r6,a,df,f,s,rest)` by METIS_TAC [lisp_inv_cdr]
    \\ FULL_SIMP_TAC std_ss [CDR_def]
    \\ METIS_TAC [],
    Cases_on `x2`
    \\ SIMP_TAC std_ss [SExp2XExp_def,XExp_11,SExp_11,XExp_distinct,SExp_distinct]
    \\ SIMP_TAC std_ss [lisp_inv_def] \\ REPEAT STRIP_TAC
    \\ Cases_on `v1` \\ Cases_on `v2`
    \\ FULL_SIMP_TAC (std_ss++SIZES_ss) [lisp_ref_def,n2w_11],
    Cases_on `x2`
    \\ SIMP_TAC std_ss [SExp2XExp_def,XExp_11,SExp_11,XExp_distinct,SExp_distinct]
    \\ SIMP_TAC std_ss [lisp_inv_def] \\ REPEAT STRIP_TAC
    \\ Cases_on `v1` \\ Cases_on `v2`
    \\ FULL_SIMP_TAC (std_ss++SIZES_ss) [lisp_ref_def,n2w_11]
    \\ `?dm m dg g. rest = (dm,m,dg,g)` by METIS_TAC [PAIR]
    \\ FULL_SIMP_TAC std_ss [lisp_symbol_table_def]
    \\ `(ADDR32 w + sa,s'') IN (set_add sa s)` by 
       FULL_SIMP_TAC std_ss [IN_DEF,set_add_def,WORD_ADD_SUB]
    \\ `(ADDR32 w' + sa,s') IN (set_add sa s)` by 
       FULL_SIMP_TAC std_ss [IN_DEF,set_add_def,WORD_ADD_SUB]
    \\ `!w s2. (ADDR32 w + sa,s2) IN (set_add sa s) = (ADDR32 w, s2) IN s` by 
       FULL_SIMP_TAC std_ss [IN_DEF,set_add_def,WORD_ADD_SUB]
    \\ `(s'' = s') = (w = w')` by METIS_TAC [symbol_table_eq,WORD_EQ_ADD_RCANCEL,ADDR32_11]
    \\ ASM_SIMP_TAC std_ss []
    \\ `!w1 w2 s1 s2. (ADDR32 w1 + sa,s1) IN (set_add sa s) /\ 
        (ADDR32 w2 + sa,s2) IN (set_add sa s) ==> 
        ((ADDR32 w1 + sa = ADDR32 w2 + sa) = (s1 = s2))` by METIS_TAC [symbol_table_eq]
    \\ POP_ASSUM MP_TAC
    \\ ASM_SIMP_TAC std_ss [WORD_EQ_ADD_RCANCEL,ADDR32_11]
    \\ METIS_TAC []]);

val lisp_tree_THM = prove(
  ``lisp_inv (x1,x2,x3,x4,x5,x6,limit) (r1,r2,r3,r4,r5,r6,a,df,f,s,rest) ==>
    ?y1 y2. lisp_tree y1 (r1,f) (heap_half(a,f(a-28w)=0w,limit)) /\
            lisp_tree y2 (r2,f) (heap_half(a,f(a-28w)=0w,limit)) /\
            ((x1 = x2) = (y1 = y2)) /\ (XDEPTH y1 = LDEPTH x1) /\
            (XDEPTH y2 = LDEPTH x2)``,
  STRIP_TAC
  \\ Q.EXISTS_TAC `SExp2XExp x1 s` \\ Q.EXISTS_TAC `SExp2XExp x2 s`
  \\ IMP_RES_TAC lisp_tree_INTRO
  \\ IMP_RES_TAC SExp2XExp_11
  \\ ASM_SIMP_TAC std_ss []
  \\ METIS_TAC [lisp_inv_swap2,lisp_tree_INTRO]);

val lisp_inv_arm_eq_loop = prove(
  ``let w = a + if f (a - 28w) = 0w then 8w else 8w + n2w (8 * limit) in
    lisp_inv (x1,x2,x3,x4,x5,x6,limit) (r3,r4,z5,z6,z7,z8,a,df,f,s,rest) /\
    (arm_eq_loop (r3,r4,r5,r6,w,0w,df,f) = (u3,u4,u5,u6,u7,u8,udf,uf)) ==>
    arm_eq_loop_pre (r3,r4,r5,r6,w,0w,df,f) /\
    ((u3 = u4) = (x1 = x2)) /\ 
    (!x. ~(x IN heap_half (a, ~((f:word32->word32) (a - 28w) = 0w),limit)) ==> (f x = uf x)) /\ (df = udf)``,
  Q.ABBREV_TAC `w = a + if f (a - (28w:word32)) = (0w:word32) then 8w else 8w + n2w (8 * limit)`
  \\ SIMP_TAC std_ss [LET_DEF] \\ STRIP_TAC
  \\ IMP_RES_TAC lisp_tree_THM \\ ASM_SIMP_TAC std_ss []
  \\ MATCH_MP_TAC arm_eq_loop_spec
  \\ Q.EXISTS_TAC `heap_half (a, (f (a - 28w) = 0w),limit)`
  \\ ASM_SIMP_TAC std_ss []
  \\ `LDEPTH x1 <= limit` by METIS_TAC [lisp_inv_LDEPTH]
  \\ ASM_SIMP_TAC std_ss []  
  \\ `16 * limit < 2**32` by
       (FULL_SIMP_TAC std_ss [lisp_inv_def,ch_arm_def,ch_word_def,ch_inv_def] \\ DECIDE_TAC)
  \\ IMP_RES_TAC heap_half_DISJOINT
  \\ STRIP_TAC THEN1
   (Cases_on `f (a - 0x1Cw) = 0x0w` \\ ASM_SIMP_TAC std_ss []
    \\ METIS_TAC [INTER_COMM])
  \\ `ALIGNED w` by (Q.UNABBREV_TAC `w`
    \\ Cases_on `(f:word32->word32) (a - 28w) = 0w` \\ ASM_SIMP_TAC std_ss []
    \\ SIMP_TAC std_ss [GSYM (EVAL ``4w + 4w:word32``),WORD_ADD_ASSOC,ALIGNED_CLAUSES]
    \\ SIMP_TAC bool_ss [GSYM (EVAL ``4*2``),GSYM word_mul_n2w,WORD_MULT_ASSOC]
    \\ REWRITE_TAC [ALIGNED_CLAUSES,GSYM WORD_MULT_ASSOC]
    \\ FULL_SIMP_TAC std_ss [lisp_inv_def,ch_arm_def,ch_word_def,ref_cheney_def,ALIGNED_def])
  \\ ASM_SIMP_TAC std_ss []
  \\ STRIP_TAC THEN1
   (REWRITE_TAC [SUBSET_DEF,GSPECIFICATION,heap_half_def]
    \\ SIMP_TAC std_ss [IN_DEF,MAX_ADDRESSES_def,LENGTH,WORD_MULT_CLAUSES,MAX_XDEPTH_def] 
    \\ SIMP_TAC std_ss [WORD_ADD_SUB]
    \\ REPEAT STRIP_TAC \\ ASM_SIMP_TAC std_ss []
    \\ FULL_SIMP_TAC std_ss []
    \\ FULL_SIMP_TAC bool_ss [GSYM (EVAL ``16 * 268435456``)]
    \\ DECIDE_TAC)
  \\ STRIP_TAC THEN1   
   (REWRITE_TAC [SUBSET_DEF,GSPECIFICATION,heap_half_def]
    \\ SIMP_TAC std_ss [IN_DEF,MAX_ADDRESSES_def,LENGTH,WORD_MULT_CLAUSES,MAX_XDEPTH_def] 
    \\ SIMP_TAC std_ss [WORD_ADD_SUB]
    \\ REPEAT STRIP_TAC \\ ASM_SIMP_TAC std_ss []
    \\ Q.UNABBREV_TAC `w`
    \\ Cases_on `f (a - 0x1Cw) = 0x0w` \\ ASM_SIMP_TAC std_ss []
    \\ Q.EXISTS_TAC `i`
    \\ REWRITE_TAC [word_add_n2w,GSYM WORD_ADD_ASSOC]
    \\ SIMP_TAC std_ss [AC ADD_ASSOC ADD_COMM]
    \\ DECIDE_TAC)
  \\ STRIP_TAC THEN1
   (SIMP_TAC std_ss [heap_half_def,GSPECIFICATION] \\ STRIP_TAC
    \\ `w2n a + 16 * limit + 20 < 4294967296` by 
      (FULL_SIMP_TAC std_ss [lisp_inv_def,ch_arm_def,ch_word_def,ch_inv_def] \\ METIS_TAC [])
    \\ Q.PAT_ASSUM `w2n a + 16 * limit + 20 < 4294967296` MP_TAC
    \\ Q.SPEC_TAC (`a`,`a`) \\ Cases_word
    \\ ASM_SIMP_TAC std_ss [w2n_n2w,word_add_n2w,n2w_11,ZERO_LT_dimword]
    \\ Cases_on `k < 2 * limit` \\ ASM_SIMP_TAC (std_ss++SIZES_ss) [] \\ STRIP_TAC
    \\ `n + (8 * limit + 8 + 4 * k) < 4294967296` by DECIDE_TAC
    \\ `n + (8 + 4 * k) < 4294967296` by DECIDE_TAC
    \\ Cases_on `(f:word32->word32) (n2w n - 28w) = 0w` \\ ASM_SIMP_TAC std_ss [])
  \\ `df = ref_set a (limit + limit + 1)` by 
    (FULL_SIMP_TAC std_ss [lisp_inv_def,ch_arm_def,ch_word_def,ref_cheney_def,ch_inv_def] 
     \\ METIS_TAC [])
  \\ ASM_SIMP_TAC std_ss [heap_half_def,SUBSET_DEF,GSPECIFICATION,ref_set_def,IN_UNION]
  \\ REPEAT STRIP_TAC \\ ASM_SIMP_TAC std_ss [WORD_EQ_ADD_LCANCEL] \\ DISJ1_TAC
  \\ Cases_on `(f:word32->word32) (a - 28w) = 0w` \\ ASM_SIMP_TAC std_ss []     
  THEN1 (Q.EXISTS_TAC `2 + k` \\ SIMP_TAC std_ss [LEFT_ADD_DISTRIB] \\ DECIDE_TAC)
  THEN1 (Q.EXISTS_TAC `2 * limit + 2 + k` 
         \\ SIMP_TAC std_ss [LEFT_ADD_DISTRIB,MULT_ASSOC] \\ DECIDE_TAC)
  THEN1 (Q.EXISTS_TAC `2 * limit + 2 + k` 
         \\ SIMP_TAC std_ss [LEFT_ADD_DISTRIB,MULT_ASSOC] \\ DECIDE_TAC)
  THEN1 (Q.EXISTS_TAC `2 + k` \\ SIMP_TAC std_ss [LEFT_ADD_DISTRIB] \\ DECIDE_TAC));




val arm_eq_init_thm = prove(
  ``arm_eq_init(r5,r6,r10) = (r5,r6,r10 + if r5 = 0w then 8w else 8w + r6,r10)``,
  SIMP_TAC std_ss [arm_eq_init_def,LET_DEF] \\ Cases_on `r5 = 0w` \\ ASM_SIMP_TAC std_ss [WORD_ADD_ASSOC]);

val WORD_EQ_ADD_CANCEL = prove(
  ``!x y. ((x + y = x) = (y = 0w)) /\ ((y + x = x) = (y = 0w)) /\ 
          ((x = x + y) = (y = 0w)) /\ ((x = y + x) = (y = 0w))``,
  METIS_TAC [WORD_EQ_ADD_LCANCEL,WORD_EQ_ADD_RCANCEL,WORD_ADD_0]);

val tac =
  FULL_SIMP_TAC std_ss [lisp_inv_def,ch_arm_def,ch_word_def]
  \\ REPEAT STRIP_TAC \\ Q.EXISTS_TAC `v1` \\ Q.EXISTS_TAC `v2` \\ Q.EXISTS_TAC `v3`
  \\ Q.EXISTS_TAC `v4` \\ Q.EXISTS_TAC `v5` \\ Q.EXISTS_TAC `v6` \\ Q.EXISTS_TAC `h`
  \\ Q.EXISTS_TAC `sa`
  \\ ASM_SIMP_TAC std_ss [] \\ Q.EXISTS_TAC `i` \\ Q.EXISTS_TAC `e` \\ Q.EXISTS_TAC `rs`
  \\ Q.EXISTS_TAC `l'` \\ Q.EXISTS_TAC `u` \\ Q.EXISTS_TAC `m`
  \\ ASM_SIMP_TAC std_ss [CONS_11] \\ SIMP_TAC std_ss [APPLY_UPDATE_THM]  
  \\ SIMP_TAC std_ss [word_sub_def,WORD_EQ_ADD_LCANCEL,WORD_EQ_ADD_CANCEL]
  \\ REWRITE_TAC [GSYM word_sub_def]  
  \\ ASM_SIMP_TAC (std_ss++SIZES_ss) [word_2comp_n2w,n2w_11]
  \\ FULL_SIMP_TAC std_ss [ref_cheney_def] \\ REPEAT STRIP_TAC 
  \\ RES_TAC \\ Cases_on `m i'` \\ FULL_SIMP_TAC std_ss [ref_mem_def]
  THENL [ALL_TAC,Cases_on `p` \\ Cases_on `r` \\ Cases_on `r'`]
  \\ FULL_SIMP_TAC std_ss [ref_mem_def] \\ REPEAT STRIP_TAC  
  \\ FULL_SIMP_TAC std_ss [APPLY_UPDATE_THM,ref_addr_def,word_sub_def]
  \\ SIMP_TAC std_ss [WORD_EQ_ADD_LCANCEL,WORD_EQ_ADD_CANCEL,GSYM WORD_ADD_ASSOC,word_add_n2w]
  \\ `8 * i' < 4294967296` by DECIDE_TAC
  \\ `8 * i' + 4 < 4294967296` by DECIDE_TAC
  \\ `8 * i' + 8 < 4294967296` by DECIDE_TAC
  \\ ASM_SIMP_TAC (std_ss++SIZES_ss) [n2w_11,word_2comp_n2w]
  \\ MATCH_MP_TAC (METIS_PROVE [] ``~b ==> ((if b then x else y) = y)``)
  \\ DECIDE_TAC

val lemma4 = prove(
  ``lisp_inv (x1,x2,x3,x4,x5,x6,limit) (r3,r4,r5,r6,r7,r8,a,df,f,s,rest) ==>
    lisp_inv (x1,x2,x3,x4,x5,x6,limit) (r3,r4,r5,r6,r7,r8,a,df,(a - 4w =+ x) f,s,rest)``,tac);
val lemma8 = prove(
  ``lisp_inv (x1,x2,x3,x4,x5,x6,limit) (r3,r4,r5,r6,r7,r8,a,df,f,s,rest) ==>
    lisp_inv (x1,x2,x3,x4,x5,x6,limit) (r3,r4,r5,r6,r7,r8,a,df,(a - 8w =+ x) f,s,rest)``,tac);
val lemma12 = prove(
  ``lisp_inv (x1,x2,x3,x4,x5,x6,limit) (r3,r4,r5,r6,r7,r8,a,df,f,s,rest) ==>
    lisp_inv (x1,x2,x3,x4,x5,x6,limit) (r3,r4,r5,r6,r7,r8,a,df,(a - 12w =+ x) f,s,rest)``,tac);
val lemma16 = prove(
  ``lisp_inv (x1,x2,x3,x4,x5,x6,limit) (r3,r4,r5,r6,r7,r8,a,df,f,s,rest) ==>
    lisp_inv (x1,x2,x3,x4,x5,x6,limit) (r3,r4,r5,r6,r7,r8,a,df,(a - 16w =+ x) f,s,rest)``,tac);
val lemma20 = prove(
  ``lisp_inv (x1,x2,x3,x4,x5,x6,limit) (r3,r4,r5,r6,r7,r8,a,df,f,s,rest) ==>
    lisp_inv (x1,x2,x3,x4,x5,x6,limit) (r3,r4,r5,r6,r7,r8,a,df,(a - 20w =+ x) f,s,rest)``,tac);

val tac2 =
     (SIMP_TAC std_ss [heap_half_def,GSPECIFICATION,word_sub_def,WORD_EQ_ADD_LCANCEL,WORD_EQ_ADD_CANCEL]
      \\ STRIP_TAC \\ Cases_on `k < 2 * limit`
      \\ Cases_on `f5 (a + 0xFFFFFFE4w) = 0w`
      \\ ASM_SIMP_TAC (std_ss++SIZES_ss) [word_2comp_n2w,n2w_11]
      \\ `(8 * limit + 8 + 4 * k) < 4294967296` by DECIDE_TAC
      \\ `(8 + 4 * k) < 4294967296` by DECIDE_TAC
      \\ ASM_SIMP_TAC std_ss [LESS_MOD] \\ DECIDE_TAC)     

val lisp_inv_equal = store_thm("lisp_inv_equal",
  ``lisp_inv (x1,x2,x3,x4,x5,x6,limit)
     (r3,r4,r5,r6,r7,r8,a,df,f,s,rest) ==>
    ?r3' r4' r5' r6' r7' r8' a' df' f'.
   (arm_eq (r3,r4,r5,r6,r7,r8,a,df,f) =
    (r3',r4',r5',r6',r7',r8',a',df',f')) /\
   arm_eq_pre (r3,r4,r5,r6,r7,r8,a,df,f) /\ (df' = df) /\ (a' = a) /\
   lisp_inv (LISP_EQUAL x1 x2,x2,x3,x4,x5,x6,limit)
     (r3',r4',r5',r6',r7',r8',a',df',f',s,rest)``,
  `?r3' r4' r5' r6' r7' r8' a' df' f'.
   (arm_eq (r3,r4,r5,r6,r7,r8,a,df,f) =
    (r3',r4',r5',r6',r7',r8',a',df',f'))` by METIS_TAC [PAIR]
  \\ ASM_SIMP_TAC std_ss []
  \\ POP_ASSUM MP_TAC
  \\ REWRITE_TAC [AND_IMP_INTRO]
  \\ ONCE_REWRITE_TAC [CONJ_COMM]
  \\ REWRITE_TAC [GSYM AND_IMP_INTRO]
  \\ REWRITE_TAC [arm_eq_def,GSYM ALIGNED_def]
  \\ ONCE_REWRITE_TAC [ALIGNED_MOD_4]
  \\ SIMP_TAC std_ss [WORD_SUB_RZERO]
  \\ Cases_on `r3 = r4` THEN1 
   (ASM_SIMP_TAC std_ss [LET_DEF] \\ ONCE_REWRITE_TAC [EQ_SYM_EQ]
    \\ SIMP_TAC std_ss []
    \\ STRIP_TAC \\ IMP_RES_TAC lisp_tree_THM
    \\ IMP_RES_TAC lisp_tree_11
    \\ FULL_SIMP_TAC std_ss [LISP_EQUAL_def]
    \\ METIS_TAC [lisp_inv_t])
  \\ ASM_SIMP_TAC std_ss [LET_DEF]
  \\ Q.ABBREV_TAC `f1 = (a - 20w =+ r4) f`    
  \\ Q.ABBREV_TAC `f2 = (a - 16w =+ r5) f1`    
  \\ Q.ABBREV_TAC `f3 = (a - 12w =+ r6) f2`    
  \\ Q.ABBREV_TAC `f4 = (a - 8w  =+ r7) f3`    
  \\ Q.ABBREV_TAC `f5 = (a - 4w  =+ r8) f4`    
  \\ Q.ABBREV_TAC `wl = (f5 (a - 32w))`
  \\ Q.ABBREV_TAC `wi = (f5 (a - 28w))`
  \\ REWRITE_TAC [GSYM CONJ_ASSOC,arm_eq_init_thm]
  \\ SIMP_TAC std_ss []
  \\ Q.ABBREV_TAC `ww = a + if wi = 0w then 8w else 8w + wl`
  \\ `?r3t r4t r5t r6t r7t r8t dft ft. arm_eq_loop (r3,r4,wi,wl,ww,0w ,df,f5) = 
       (r3t,r4t,r5t,r6t,r7t,r8t,dft,ft)` by METIS_TAC [PAIR]
  \\ `?r3u r4u. arm_eq_assign (r3t,r4t) = (r3u,r4u)` by METIS_TAC [PAIR]
  \\ ASM_SIMP_TAC std_ss [GSYM AND_IMP_INTRO]
  \\ STRIP_TAC \\ ONCE_REWRITE_TAC [EQ_SYM_EQ] \\ SIMP_TAC std_ss []
  \\ REPEAT (MATCH_MP_TAC (METIS_PROVE [] ``p ==> (b ==> p)``))
  \\ `ALIGNED a` by
      FULL_SIMP_TAC std_ss [lisp_inv_def,ch_arm_def,ch_word_def,ref_cheney_def,ALIGNED_def]
  \\ ASM_SIMP_TAC std_ss [WORD_SUB_PLUS,ALIGNED_SUB_4]
  \\ SIMP_TAC std_ss [arm_eq_init_def,LET_DEF,arm_eq_assign_def]
  \\ `lisp_inv (x1,x2,x3,x4,x5,x6,limit) (r3,r4,r5,r6,r7,r8,a,df,f5,s,rest)` by 
         METIS_TAC [lemma20,lemma16,lemma12,lemma8,lemma4]       
  \\ Q.UNABBREV_TAC `ww` \\ Q.UNABBREV_TAC `wi` \\ Q.UNABBREV_TAC `wl`
  \\ `f5 (a - 32w) = n2w (8 * limit)` by 
       FULL_SIMP_TAC std_ss [LET_DEF,lisp_inv_def,ch_arm_def,ch_word_def,ch_inv_def]
  \\ FULL_SIMP_TAC std_ss []
  \\ IMP_RES_TAC (SIMP_RULE std_ss [LET_DEF] lisp_inv_arm_eq_loop)
  \\ REPEAT (Q.PAT_ASSUM `!xx yy. bb` (K ALL_TAC))
  \\ Q.PAT_ASSUM `df = dft` (ASSUME_TAC o GSYM)
  \\ FULL_SIMP_TAC std_ss [GSYM WORD_SUB_PLUS,word_add_n2w]
  \\ REWRITE_TAC [CONJ_ASSOC] \\ STRIP_TAC THEN1
     (`df = ref_set a (limit + limit + 1)` by
        FULL_SIMP_TAC std_ss [lisp_inv_def,ch_arm_def,ch_word_def,ref_cheney_def,ch_inv_def]
      \\ REPEAT STRIP_TAC \\ ASM_SIMP_TAC std_ss [ref_set_def,IN_UNION] \\ DISJ2_TAC
      \\ SIMP_TAC std_ss [GSPECIFICATION]          
      \\ REPEAT (Q.EXISTS_TAC `1` \\ SIMP_TAC std_ss [] \\ DECIDE_TAC)
      \\ REPEAT (Q.EXISTS_TAC `2` \\ SIMP_TAC std_ss [] \\ DECIDE_TAC)
      \\ REPEAT (Q.EXISTS_TAC `3` \\ SIMP_TAC std_ss [] \\ DECIDE_TAC)
      \\ REPEAT (Q.EXISTS_TAC `4` \\ SIMP_TAC std_ss [] \\ DECIDE_TAC)
      \\ REPEAT (Q.EXISTS_TAC `5` \\ SIMP_TAC std_ss [] \\ DECIDE_TAC)
      \\ REPEAT (Q.EXISTS_TAC `6` \\ SIMP_TAC std_ss [] \\ DECIDE_TAC)
      \\ REPEAT (Q.EXISTS_TAC `7` \\ SIMP_TAC std_ss [] \\ DECIDE_TAC)
      \\ REPEAT (Q.EXISTS_TAC `8` \\ SIMP_TAC std_ss [] \\ DECIDE_TAC))
  \\ Q.PAT_ASSUM `lisp_inv (x1,x2,x3,x4,x5,x6,limit) (r3,r4,r5,r6,r7,r8,a,df,f,s,rest)` (K ALL_TAC) 
  \\ `lisp_inv (LISP_EQUAL x1 x2,x2,x3,x4,x5,x6,limit) (r3u,r4,r5,r6,r7,r8,a,df,f5,s,rest)` by
      (Cases_on `x1 = x2`      
       \\ FULL_SIMP_TAC std_ss [LISP_EQUAL_def,arm_eq_assign_def,LET_DEF]
       \\ METIS_TAC [lisp_inv_t,lisp_inv_nil])
  \\ Q.PAT_ASSUM `lisp_inv (x1,x2,x3,x4,x5,x6,limit) (r3,r4,r5,r6,r7,r8,a,df,f5,s,rest)` (K ALL_TAC)
  \\ `w2n a + 16 * limit + 20 < 4294967296` by 
      FULL_SIMP_TAC std_ss [lisp_inv_def,ch_arm_def,ch_word_def,ref_cheney_def,ch_inv_def]
  \\ `32 <= w2n a` by 
      FULL_SIMP_TAC std_ss [lisp_inv_def,ch_arm_def,ch_word_def,ref_cheney_def,ch_inv_def]
  \\ `~(a - 20w IN heap_half (a, ~(f5 (a - 28w) = 0w),limit))` by tac2
  \\ `~(a - 16w IN heap_half (a, ~(f5 (a - 28w) = 0w),limit))` by tac2
  \\ `~(a - 12w IN heap_half (a, ~(f5 (a - 28w) = 0w),limit))` by tac2
  \\ `~(a - 8w IN heap_half (a, ~(f5 (a - 28w) = 0w),limit))` by tac2
  \\ `~(a - 4w IN heap_half (a, ~(f5 (a - 28w) = 0w),limit))` by tac2
  \\ `(ft (a - 20w) = r4) /\ (ft (a - 16w) = r5) /\ (ft (a - 12w) = r6) /\
        (ft (a - 8w) = r7) /\ (ft (a - 4w) = r8)` by       
     (RES_TAC \\ REPEAT (Q.PAT_ASSUM `f5 xx = yy` (fn th => REWRITE_TAC [GSYM th]))
      \\ Q.UNABBREV_TAC `f1` \\ Q.UNABBREV_TAC `f2` \\ Q.UNABBREV_TAC `f3`
      \\ Q.UNABBREV_TAC `f4` \\ Q.UNABBREV_TAC `f5`
      \\ REPEAT (POP_ASSUM (K ALL_TAC))
      \\ SIMP_TAC (std_ss++SIZES_ss) [APPLY_UPDATE_THM,word_sub_def,
           WORD_EQ_ADD_LCANCEL,n2w_11,word_2comp_n2w])
  \\ ASM_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC std_ss [lisp_inv_def]
  \\ Q.EXISTS_TAC `v1` \\ Q.EXISTS_TAC `v2` \\ Q.EXISTS_TAC `v3`
  \\ Q.EXISTS_TAC `v4` \\ Q.EXISTS_TAC `v5` \\ Q.EXISTS_TAC `v6` \\ Q.EXISTS_TAC `h`
  \\ Q.EXISTS_TAC `sa`
  \\ FULL_SIMP_TAC std_ss [ch_arm_def]    
  \\ Q.EXISTS_TAC `i` \\ Q.EXISTS_TAC `e` \\ Q.EXISTS_TAC `rs`
  \\ Q.EXISTS_TAC `l'` \\ Q.EXISTS_TAC `u` \\ Q.EXISTS_TAC `m`
  \\ FULL_SIMP_TAC std_ss [ch_word_def,CONS_11]
  \\ REVERSE STRIP_TAC THEN1
     (`~(a - 28w IN heap_half (a, ~(f5 (a - 28w) = 0w),limit))` by tac2
      \\ `~(a - 32w IN heap_half (a, ~(f5 (a - 28w) = 0w),limit))` by tac2
      \\ `~(a + 4w IN heap_half (a, ~(f5 (a - 28w) = 0w),limit))` by tac2
      \\ `~(a IN heap_half (a, ~(f5 (a - 28w) = 0w),limit))` by tac2
      \\ Q.PAT_ASSUM `f5 (a - 28w) = (if u then 0w else 1w)` ASSUME_TAC
      \\ FULL_SIMP_TAC std_ss [] \\ RES_TAC \\ METIS_TAC [])
  \\ FULL_SIMP_TAC std_ss [ref_cheney_def] \\ REPEAT STRIP_TAC
  \\ `~((if u then 0w else 1w) = 0w:word32) = ~u` by 
      (Cases_on `u` \\ REWRITE_TAC [] \\ EVAL_TAC)
  \\ FULL_SIMP_TAC std_ss []
  \\ REVERSE (`!i. ~(m i = EMP) ==> 
         ~(ref_addr a i + 4w IN heap_half (a,~u,limit)) /\
         ~(ref_addr a i IN heap_half (a,~u,limit))` by ALL_TAC)
  THEN1
     (RES_TAC \\ Cases_on `m i'` \\ FULL_SIMP_TAC std_ss [ref_mem_def]
      THENL [ALL_TAC,Cases_on `p` \\ Cases_on `r` \\ Cases_on `r'`]
      \\ FULL_SIMP_TAC std_ss [ref_mem_def]
      \\ METIS_TAC [heap_type_distinct])
  \\ SIMP_TAC std_ss [ref_addr_def,heap_half_def,GSPECIFICATION,
       GSYM WORD_ADD_ASSOC,word_add_n2w,WORD_EQ_ADD_LCANCEL]
  \\ REPEAT (Q.PAT_ASSUM `rx = ref_field a xxx` (K ALL_TAC))
  \\ REPEAT (Q.PAT_ASSUM `lisp_ref yy zz xx ttt` (K ALL_TAC))
  \\ REPEAT (Q.PAT_ASSUM `~bbb` (K ALL_TAC))
  \\ REPEAT (Q.PAT_ASSUM `ff (a - n2w nnn) = rx` (K ALL_TAC))
  \\ REPEAT (Q.PAT_ASSUM `Abbrev rx` (K ALL_TAC))
  \\ REPEAT (Q.PAT_ASSUM `bb ==> yy` (K ALL_TAC))
  \\ REPEAT (Q.PAT_ASSUM `arm_eq_loop xxx = yyy` (K ALL_TAC))
  \\ REPEAT (Q.PAT_ASSUM `arm_eq_loop_pre xxx` (K ALL_TAC))
  \\ NTAC 2 STRIP_TAC \\ FULL_SIMP_TAC std_ss [ok_state_def,LET_DEF]
  \\ `i'' IN RANGE ((if u then 1 + l' else 1),i)` by METIS_TAC [heap_type_distinct]
  \\ REPEAT (Q.PAT_ASSUM `!bb. yy` (K ALL_TAC))
  \\ `l' = limit` by METIS_TAC [ch_inv_def]
  \\ FULL_SIMP_TAC std_ss [IN_DEF,RANGE_def]
  \\ REPEAT STRIP_TAC 
  \\ (Cases_on `k < 2 * limit` \\ ASM_SIMP_TAC std_ss []
  \\ Cases_on `u` \\ FULL_SIMP_TAC (std_ss++SIZES_ss) [n2w_11] THENL [
      `8 + 4 * k < 4294967296` by DECIDE_TAC
      \\ `8 * i'' + 4 < 4294967296` by DECIDE_TAC
      \\ `8 * i'' < 4294967296` by DECIDE_TAC
      \\ ASM_SIMP_TAC std_ss [LESS_MOD]
      \\ DECIDE_TAC,
      `8 * limit + 8 + 4 * k < 4294967296` by DECIDE_TAC
      \\ `8 * i'' + 4 < 4294967296` by DECIDE_TAC
      \\ `8 * i'' < 4294967296` by DECIDE_TAC
      \\ ASM_SIMP_TAC std_ss [LESS_MOD]
      \\ DECIDE_TAC]));


(* PowerPC implementation *)

val (th,ppc_eq_loop_def) = basic_decompile_ppc "ppc_eq_loop" 
  (SOME (``(r3:word32,r4:word32,r5:word32,r6:word32,r7:word32,r8:word32,df:word32 set,f:word32->word32)``,
         ``(r3:word32,r4:word32,r5:word32,r6:word32,r7:word32,r8:word32,df:word32 set,f:word32->word32)``)) `
  7C032000 (* LOOP:cmpw 3,4 *)
  40820034 (* bc 4,2,NEXT *)
  7C652378 (* or 5,3,4 *)
  70A20003 (* andi. 2,5,3 *)
  41820044 (* bc 12,2,EXIT *)
  80A30004 (* lwz 5,4(3) *)
  80630000 (* lwz 3,0(3) *)
  80C40004 (* lwz 6,4(4) *)
  80840000 (* lwz 4,0(4) *)
  90A70000 (* stw 5,0(7) *)
  90C70004 (* stw 6,4(7) *)
  38E70008 (* addi 7,7,8 *)
  39080001 (* addi 8,8,1 *)
  4BFFFFCC (* b LOOP *)
  2C080000 (* NEXT:cmpwi 8,0 *)
  40820018 (* bc 4,2,EXIT *)
  8087FFFC (* lwz 4,-4(7) *)
  8067FFF8 (* lwz 3,-8(7) *)
  38E7FFF8 (* addi 7,7,-8 *)
  3908FFFF (* addi 8,8,-1 *)
  4BFFFFB0 (* b LOOP *)`;

val ppc_eq_loop_EQ = prove( 
  ``(ppc_eq_loop = arm_eq_loop) /\ (ppc_eq_loop_pre = arm_eq_loop_pre)``,
  STRIP_TAC \\ REWRITE_TAC [fetch "-" "arm_eq_loop_def",fetch "-" "ppc_eq_loop_def"]
  \\ REWRITE_TAC [fetch "-" "arm_eq_loop_pre_def",fetch "-" "ppc_eq_loop_pre_def"]
  \\ MATCH_MP_TAC (METIS_PROVE [] ``(x = x') /\ (y = y') /\ (z = z') ==> (f x y z = f x' y' z')``)
  \\ SIMP_TAC (std_ss++tailrecLib.tailrec_part_ss()) [FUN_EQ_THM,FORALL_PROD]
  \\ SIMP_TAC std_ss [LET_DEF,word_arith_lemma1]
  \\ SIMP_TAC std_ss [AC WORD_AND_ASSOC WORD_AND_COMM]);

val (th,ppc_eq_init_def) = basic_decompile_ppc "ppc_eq_init" NONE `
  38EA0008 (* addi 7,10,8 *)
  2C050000 (* cmpwi 5,0 *)
  40820008 (* bc 4,2,EQ2 *)
  7CE73214 (* add 7,7,6 *)`;

val (th,ppc_eq_assign_def) = basic_decompile_ppc "ppc_eq_assign" NONE `
  7C032000 (* EXIT:cmpw 3,4 *)
  38600003 (* addi 3,0,3 *)
  41820008 (* bc 12,2,EQ3 *)
  3863000C (* addi 3,3,12 *)`;

val (ppc_eq_thm,ppc_eq_def) = basic_decompile_ppc "ppc_eq" NONE `   
  7C032000 (* cmpw 3,4 *)
  4182000C (* bc 12,2,EQ1 *)
  3860000F (* addi 3,0,15 *)
  480000AC (* b EXIT2 *)
  908AFFEC (* EQ1:stw 4,-20(10) *)
  90AAFFF0 (* stw 5,-16(10) *)
  90CAFFF4 (* stw 6,-12(10) *)
  90EAFFF8 (* stw 7,-8(10) *)
  910AFFFC (* stw 8,-4(10) *)
  80AAFFE4 (* lwz 5,-28(10) *)
  80CAFFE0 (* lwz 6,-32(10) *)
  insert: ppc_eq_init
  7CA82A78 (* EQ2:xor 8,5,5 *)
  insert: ppc_eq_loop
  insert: ppc_eq_assign
  808AFFEC (* EQ3:lwz 4,-20(10) *)
  80AAFFF0 (* lwz 5,-16(10) *)
  80CAFFF4 (* lwz 6,-12(10) *)
  80EAFFF8 (* lwz 7,-8(10) *)
  810AFFFC (* lwz 8,-4(10) *)`;

val ppc_eq_EQ = store_thm("ppc_eq_EQ", 
  ``(ppc_eq = arm_eq) /\ (ppc_eq_pre = arm_eq_pre)``,
  SIMP_TAC (std_ss) [FUN_EQ_THM,FORALL_PROD]
  \\ `!r5 r6 r10. ppc_eq_init (r5,r6,r10) = arm_eq_init (r5,r6,r10)` by 
    REWRITE_TAC [ppc_eq_init_def,arm_eq_init_def]
  \\ `!r5 r6 r10. ppc_eq_assign (r5,r6) = arm_eq_assign (r5,r6)` by 
   SIMP_TAC std_ss [ppc_eq_assign_def,arm_eq_assign_def,LET_DEF,word_add_n2w]
  \\ ASM_SIMP_TAC std_ss [arm_eq_def,ppc_eq_def,LET_DEF,ppc_eq_loop_EQ]);

val _ = save_thm("ppc_eq_thm",ppc_eq_thm);


(* x86 implementation *)

val (th,def,pre) = compile "x86" ``
  x86_eq_loop (r0:word32,r1:word32,r2:word32,r3:word32,r4:word32,r5:word32,df:word32 set,f:word32->word32) =
    (if r0 = r1 then
       (if r5 = 0x0w then
          (r0,r1,r2,r3,r4,r5,df,f)
        else
          (let r1 = f (r4 - 0x4w) in
           let r0 = f (r4 - 0x8w) in
           let r4 = r4 - 0x8w in
           let r5 = r5 - 0x1w in
             x86_eq_loop (r0,r1,r2,r3,r4,r5,df,f)))
     else
       (let r2 = r0 !! r1 in
          (if r2 && 3w = 0x0w then
             (let r2 = f (r0 + 0x4w) in
              let r0 = f r0 in
              let r3 = f (r1 + 0x4w) in
              let r1 = f r1 in
              let f = (r4 =+ r2) f in
              let f = (r4 + 4w =+ r3) f in
              let r4 = r4 + 0x8w in
              let r5 = r5 + 0x1w in
                x86_eq_loop (r0,r1,r2,r3,r4,r5,df,f))
           else
             (r0,r1,r2,r3,r4,r5,df,f))))``;

val x86_eq_loop_EQ = prove( 
  ``(x86_eq_loop = arm_eq_loop) /\ (x86_eq_loop_pre = arm_eq_loop_pre)``,
  STRIP_TAC \\ REWRITE_TAC [fetch "-" "arm_eq_loop_def",fetch "-" "x86_eq_loop_def"]
  \\ REWRITE_TAC [fetch "-" "arm_eq_loop_pre_def",fetch "-" "x86_eq_loop_pre_def"]
  \\ MATCH_MP_TAC (METIS_PROVE [] ``(x = x') /\ (y = y') /\ (z = z') ==> (f x y z = f x' y' z')``)
  \\ SIMP_TAC (std_ss++tailrecLib.tailrec_part_ss()) [FUN_EQ_THM,FORALL_PROD]
  \\ SIMP_TAC std_ss [LET_DEF,word_arith_lemma1]
  \\ SIMP_TAC std_ss [AC WORD_AND_ASSOC WORD_AND_COMM]);

val (th,def,pre) = compile "x86" ``
  x86_eq_init (r2:word32,r3:word32,r6:word32) =
    let r4 = r6 + 0x8w in
      (if r2 = 0x0w then
         (r2,r3,r4,r6)
       else
         (let r4 = r4 + r3 in (r2,r3,r4,r6)))``;

val (th,def,pre) = compile "x86" ``
  x86_eq_assign (r0:word32,r1:word32) =
    if r0 = r1 then
      (let r0 = 0xFw in (r0,r1))
    else
      (let r0 = 0x3w in (r0:word32,r1))``;

val (x86_eq_thm,def,pre) = compile "x86" ``
  x86_eq (r0,r1,r2,r3,r4,r5,r6,df,f) =
    if r0 = r1 then
      (let r0 = 0xFw in (r0,r1,r2,r3,r4,r5,r6,df,f))
    else
      (let f = (r6 - 0x14w =+ r1) f in
       let f = (r6 - 0x10w =+ r2) f in
       let f = (r6 - 0xCw =+ r3) f in
       let f = (r6 - 0x8w =+ r4) f in
       let f = (r6 - 0x4w =+ r5) f in
       let r2 = f (r6 - 0x1Cw) in
       let r3 = f (r6 - 0x20w) in
       let (r2,r3,r4,r6) = x86_eq_init (r2,r3,r6) in
       let r5 = 0x0w in
       let (r0,r1,r2,r3,r4,r5,df,f) = x86_eq_loop (r0,r1,r2,r3,r4,r5,df,f) in
       let (r0,r1) = x86_eq_assign (r0,r1) in
       let r1 = f (r6 - 0x14w) in
       let r2 = f (r6 - 0x10w) in
       let r3 = f (r6 - 0xCw) in
       let r4 = f (r6 - 0x8w) in
       let r5 = f (r6 - 0x4w) in
         (r0,r1,r2,r3,r4,r5,r6,df,f))``;

val _ = save_thm("x86_eq_thm",x86_eq_thm);

val x86_eq_EQ = store_thm("x86_eq_EQ", 
  ``(x86_eq = arm_eq) /\ (x86_eq_pre = arm_eq_pre)``,
  SIMP_TAC (std_ss) [FUN_EQ_THM,FORALL_PROD]
  \\ `!r5 r6 r10. x86_eq_init (r5,r6,r10) = arm_eq_init (r5,r6,r10)` by 
    SIMP_TAC std_ss [LET_DEF,fetch "-" "x86_eq_init",arm_eq_init_def]
  \\ `!r5 r6 r10. x86_eq_assign (r5,r6) = arm_eq_assign (r5,r6)` by 
   SIMP_TAC std_ss [fetch "-" "x86_eq_assign",arm_eq_assign_def,LET_DEF,word_add_n2w]
  \\ ASM_SIMP_TAC std_ss [arm_eq_def,fetch "-" "x86_eq",fetch "-" "x86_eq_pre",LET_DEF,x86_eq_loop_EQ]);



val _ = export_theory();
