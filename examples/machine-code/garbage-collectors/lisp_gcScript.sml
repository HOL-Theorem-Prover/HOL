
open HolKernel boolLib bossLib Parse; val _ = new_theory "lisp_gc";
val _ = ParseExtras.temp_loose_equality()

open decompilerLib compilerLib prog_armLib;

open wordsTheory arithmeticTheory wordsLib listTheory pred_setTheory pairTheory;
open combinTheory finite_mapTheory addressTheory;

open mc_tailrecLib tailrecTheory;
open cheney_gcTheory cheney_allocTheory; (* an abstract implementation is imported *)


val _ = map Parse.hide ["r0","r1","r2","r3","r4","r5","r6","r7","r8","r9","r10","r11","r12","r13"];
val RW = REWRITE_RULE;
val RW1 = ONCE_REWRITE_RULE;

val decompile_arm = decompile arm_tools;
val basic_decompile_arm = basic_decompile arm_tools;

val (th,def1) = decompile_arm "arm_move" `
  E3150003 (* tst r5,#3 *)
  1A000008 (* bne L1 *)
  E5957000 (* ldr r7,[r5] *)
  E2078003 (* and r8,r7,#3 *)
  E3580001 (* cmp r8,#1 *)
  15958004 (* ldrne r8,[r5,#4] *)
  14847004 (* strne r7,[r4],#4 *)
  14848004 (* strne r8,[r4],#4 *)
  12447007 (* subne r7,r4,#7 *)
  15857000 (* strne r7,[r5] *)
  E2475001 (* sub r5,r7,#1 *)`;

val (th,def2) = decompile_arm "arm_move2" `
  E3160003 (* L1:tst r6,#3 *)
  1A000008 (* bne L2 *)
  E5967000 (* ldr r7,[r6] *)
  E2078003 (* and r8,r7,#3 *)
  E3580001 (* cmp r8,#1 *)
  15968004 (* ldrne r8,[r6,#4] *)
  14847004 (* strne r7,[r4],#4 *)
  14848004 (* strne r8,[r4],#4 *)
  12447007 (* subne r7,r4,#7 *)
  15867000 (* strne r7,[r6] *)
  E2476001 (* sub r6,r7,#1 *)`;

val (th,def3) = decompile_arm "arm_cheney_step" `
  E5935000 (* ldr r5,[r3] *)
  E5936004 (* ldr r6,[r3,#4] *)
  insert: arm_move
  insert: arm_move2
  E4835004 (* L2:str r5,[r3],#4 *)
  E4836004 (* str r6,[r3],#4 *)`;

val (th,def4) = basic_decompile_arm "arm_cheney_loop" NONE `
  E1530004 (* CHENEY:cmp r3,r4 *)
  0A00001A (* beq EXIT *)
  insert: arm_cheney_step
  EAFFFFE2 (* b CHENEY *)`;

val (th,def5) = basic_decompile_arm "arm_move_roots" NONE `
  E3560000 (* ROOTS:cmp r6,#0 *)
  0A00000E (* beq CHENEY *)
  E5995000 (* ldr r5,[r9] *)
  insert: arm_move
  E2466001 (* RL:sub r6,r6,#1 *)
  E4895004 (* str r5,[r9],#4 *)
  EAFFFFEE (* b ROOTS *)`;

val (th,def6) = decompile_arm "arm_c_init" `
  E2355001 (* eors r5,r5,#1 *)    (* calc u *)
  E2893008 (* add r3,r9,#8 *)     (* set i *)
  00833006 (* addeq r3,r3,r6 *)`;

val (th,def7) = decompile_arm "arm_collect" `
  E519501C (* ldr r5,[r9,#-28] *)
  E5196020 (* ldr r6,[r9,#-32] *)
  insert: arm_c_init
  E509501C (* str r5,[r9,#-28] *)
  E0835006 (* add r5,r3,r6 *)
  E1A04003 (* mov r4,r3 *)
  E5895004 (* str r5,[r9,#4] *)
  E3A06006 (* mov r6,#6 *)
  E2499018 (* sub r9,r9,#24 *)
  insert: arm_move_roots
  insert: arm_cheney_loop  (* main loop *)
  E5994004 (* EXIT:ldr r4,[r9,#4] *)`;

val (th,def8) = decompile_arm "arm_alloc_aux" `
  E1530004 (* cmp r3,r4 *)
  1A000039 (* bne NO_GC *)
  insert: arm_collect`;

val (th,def9) = decompile_arm "arm_alloc_aux2" `
  E5197018 (* NO_GC:ldr r7,[r9,#-24] *)
  E5198014 (* ldr r8,[r9,#-20] *)
  E1530004 (* cmp r3,r4 *)
  15093018 (* strne r3,[r9,#-24] *)
  14837004 (* strne r7,[r3],#4 *)
  14838004 (* strne r8,[r3],#4 *)
  03A07002 (* moveq r7,#2 *)
  05097018 (* streq r7,[r9,#-24] *)
  E5893000 (* str r3,[r9] *)`;

val (th,def10) = decompile_arm "arm_alloc_mem" `
  E5993000 (* ldr r3,[r9] *)
  E5994004 (* ldr r4,[r9,#4] *)
  insert: arm_alloc_aux
  insert: arm_alloc_aux2`;

val (arm_alloc_thm,def11) = decompile_arm "arm_alloc" `
  E5093018 (* str r3,[r9,#-24] *)
  E5094014 (* str r4,[r9,#-20] *)
  E5095010 (* str r5,[r9,#-16] *)
  E509600C (* str r6,[r9,#-12] *)
  E5097008 (* str r7,[r9,#-8] *)
  E5098004 (* str r8,[r9,#-4] *)
  insert: arm_alloc_mem
  E5193018 (* ldr r3,[r9,#-24] *)
  E5194014 (* ldr r4,[r9,#-20] *)
  E5195010 (* ldr r5,[r9,#-16] *)
  E519600C (* ldr r6,[r9,#-12] *)
  E5197008 (* ldr r7,[r9,#-8] *)
  E5198004 (* ldr r8,[r9,#-4] *)`;

val _ = save_thm("arm_alloc_thm",arm_alloc_thm);


(* proof *)

val ref_addr_def = Define `
  ref_addr a n = a + n2w (8 * n):word32`;

val ref_field_def = Define `
  ref_field a (n,x) = if n = 0 then
    ADDR32 (FST x) + (if SND x then 3w else 2w) else ref_addr a n`;

val ref_mem_def = Define `
  (ref_mem i EMP (a,xs) = T) /\
  (ref_mem i (REF j) (a,xs) =
    (xs (ref_addr a i) = ref_addr a j + 1w)) /\
  (ref_mem i (DATA (x,y,z,q)) (a,xs) =
    (xs (ref_addr a i) = ref_field a (x,z)) /\
    (xs (ref_addr a i + 4w) = ref_field a (y,q)))`;

val valid_address_def = Define `
  valid_address a i = w2n a + 8 * i + 8 < 2**32`;

val ref_set_def = Define `
  ref_set a f = { a + n2w (4 * i) | i < 2 * f + 4 } UNION { a - n2w (4 * i) | i <= 8 }`;

val ref_cheney_def = Define `
  ref_cheney (m,e) (a,d,xs,ys) =
    ~(a = 0w) /\ (a && 3w = 0w) /\ (!i. i <= e ==> ref_mem i (m i) (a,xs)) /\
    (m 0 = EMP) /\ valid_address a e /\ (!i. i <+ ref_addr a 1 ==> (xs i = ys i)) /\
    (ref_set a e = d)`;

val ref_addr_NOT_ZERO = prove(
  ``!a. ref_cheney (m,e) (a,d,xs,ys) /\ x <= e /\ ~(x = 0) ==> ~(ref_addr a x = 0w)``,
  Cases_word \\ FULL_SIMP_TAC (std_ss++SIZES_ss) [ref_cheney_def,ref_addr_def,
    word_add_n2w,n2w_11,valid_address_def,w2n_n2w] \\ REPEAT STRIP_TAC
  \\ `(n + 8 * x) < 4294967296` by DECIDE_TAC
  \\ `n + 8 * x = 0` by METIS_TAC [LESS_MOD] \\ DECIDE_TAC);

val ref_field_NOT_ZERO = prove(
  ``!a. ref_cheney (m,e) (a,d,xs,ys) /\ x <= e ==> ~(ref_field a (x,xx) = 0w)``,
  REVERSE (Cases_on `x = 0`) THEN1 METIS_TAC [ref_addr_NOT_ZERO,ref_field_def]
  \\ Cases_on `xx` \\ Cases_on `r`
  \\ ASM_SIMP_TAC bool_ss [ref_field_def,FST,SND] \\ REPEAT STRIP_TAC
  \\ Q.PAT_X_ASSUM `dfg = 0w` MP_TAC \\ REWRITE_TAC [ADDR32_ADD_EQ_ZERO]);

val ref_addr_NEQ = prove(
  ``!a i j. ~(i = j) /\ valid_address a i /\ valid_address a j ==> ~(ref_addr a i = ref_addr a j)``,
  Cases_word \\ Cases \\ Cases
  \\ SIMP_TAC std_ss [ref_addr_def,valid_address_def,word_add_n2w]
  \\ ASM_SIMP_TAC (std_ss++SIZES_ss) [w2n_n2w,LESS_MOD,n2w_11,DECIDE ``~(SUC n = 0)``]
  \\ STRIP_TAC \\ IMP_RES_TAC (DECIDE ``m + n + 8 < l ==> m + n + 4 < l /\ m + n < l``)
  \\ ASM_SIMP_TAC bool_ss [LESS_MOD] \\ DECIDE_TAC);

val ref_addr_ADD_NEQ = prove(
  ``!a i j. valid_address a i /\ valid_address a j ==> ~(ref_addr a i + 4w = ref_addr a j)``,
  Cases_word \\ Cases \\ Cases
  \\ ASM_SIMP_TAC (std_ss++SIZES_ss) [ref_addr_def,word_add_n2w,n2w_11,LESS_MOD,valid_address_def,w2n_n2w,DECIDE ``~(SUC n = 0)``]
  \\ STRIP_TAC \\ IMP_RES_TAC (DECIDE ``n + 8 < l ==> n + 4 < l /\ n < l``)
  \\ ASM_SIMP_TAC bool_ss [LESS_MOD,MULT_CLAUSES]
  \\ FULL_SIMP_TAC std_ss [EQ_ADD_LCANCEL,GSYM ADD_ASSOC] \\ REPEAT STRIP_TAC
  \\ REPEAT DECIDE_TAC
  \\ IMP_RES_TAC (METIS_PROVE [] ``(m = n) ==> (m MOD 8 = n MOD 8)``)
  \\ FULL_SIMP_TAC std_ss [RW1 [MULT_COMM] (CONJ MOD_TIMES MOD_EQ_0)]);

val ALIGNED_ref_addr = prove(
  ``!n a. ALIGNED a ==> ALIGNED (ref_addr a n)``,
  REWRITE_TAC [ref_addr_def,ALIGNED_def]
  \\ REWRITE_TAC [GSYM ALIGNED_def,GSYM (EVAL ``4 * 2``),GSYM word_mul_n2w]
  \\ SIMP_TAC bool_ss [ALIGNED_MULT,GSYM WORD_MULT_ASSOC]);

val ref_cheney_ALIGNED = prove(
  ``ref_cheney (m,f) (a,d,xs,ys) ==> (ref_addr a x && 3w = 0w)``,
  METIS_TAC [ALIGNED_def,ALIGNED_ref_addr,ref_cheney_def]);

val ref_cheney_d = prove(
  ``ref_cheney (m,f) (a,d,xs,ys) /\ ~(x = 0) /\ x <= f ==> ref_addr a x IN d /\ ref_addr a x + 4w IN d``,
  REWRITE_TAC [ref_cheney_def] \\ REPEAT STRIP_TAC
  \\ Q.PAT_X_ASSUM `ref_set a f = d` (ASSUME_TAC o GSYM)
  \\ ASM_SIMP_TAC bool_ss [ref_set_def,GSPECIFICATION,IN_UNION,ref_addr_def]
  \\ DISJ1_TAC THENL [Q.EXISTS_TAC `2*x`,Q.EXISTS_TAC `2*x+1`]
  \\ ASM_SIMP_TAC std_ss [MULT_ASSOC,LEFT_ADD_DISTRIB,
      GSYM word_add_n2w,WORD_ADD_ASSOC] \\ DECIDE_TAC);

fun UPDATE_ref_addr_prove (c,tm) = prove(tm,
  Cases_word \\ Cases_word \\ REPEAT STRIP_TAC
  \\ sg c \\ ASM_SIMP_TAC bool_ss[APPLY_UPDATE_THM]
  \\ Cases_on `x` \\ FULL_SIMP_TAC bool_ss []
  \\ CCONTR_TAC \\ FULL_SIMP_TAC bool_ss [valid_address_def]
  \\ Q.PAT_X_ASSUM `n' < dimword (:32)` ASSUME_TAC
  \\ FULL_SIMP_TAC (std_ss++SIZES_ss) [LESS_MOD,w2n_n2w,ref_addr_def,WORD_LO,word_add_n2w]
  \\ `(n' + 8 * SUC n'') < 4294967296 /\ (n' + 8) < 4294967296` by DECIDE_TAC
  \\ `(n' + 8 * SUC n'' + 4) < 4294967296` by DECIDE_TAC
  \\ FULL_SIMP_TAC (std_ss++SIZES_ss) [LESS_MOD,w2n_n2w,ref_addr_def,WORD_LO,word_add_n2w]
  \\ DECIDE_TAC);

val UPDATE_ref_addr = UPDATE_ref_addr_prove(`~(n2w n = ref_addr (n2w n') x)`,
  ``!i a. valid_address a x /\ ~(x=0) /\ i <+ ref_addr a 1 /\ (xs i = ys i) ==>
          ((ref_addr a x =+ y) xs i = ys i)``);

val UPDATE_ref_addr4 = UPDATE_ref_addr_prove(`~(n2w n = ref_addr (n2w n') x + 4w)`,
  ``!i a. valid_address a x /\ ~(x=0) /\ i <+ ref_addr a 1 /\ (xs i = ys i) ==>
          ((ref_addr a x + 4w =+ y) xs i = ys i)``);

val va_IMP = prove(
  ``!a e i. valid_address a e /\ i <= e ==> valid_address a i``,
  SIMP_TAC bool_ss [valid_address_def] \\ DECIDE_TAC);

val ref_cheney_update_REF = prove(
  ``ref_cheney (m,e) (a,d,xs,ys) /\ j <= e /\ x <= e /\ ~(x = 0) ==>
    ref_cheney ((x =+ REF j) m,e) (a,d,(ref_addr a x =+ ref_addr a j + 1w) xs,ys)``,
  SIMP_TAC bool_ss [ref_cheney_def] \\ REVERSE (REPEAT STRIP_TAC)
  THEN1 (MATCH_MP_TAC UPDATE_ref_addr \\ METIS_TAC [va_IMP])
  THEN1 ASM_SIMP_TAC bool_ss [UPDATE_def]
  \\ Cases_on `i = x` \\ ASM_SIMP_TAC bool_ss [UPDATE_def,ref_mem_def]
  \\ RES_TAC \\ Cases_on `m i` \\ FULL_SIMP_TAC bool_ss [ref_mem_def]
  \\ `valid_address a i /\ valid_address a x` by METIS_TAC [va_IMP]
  \\ `~(ref_addr a i = ref_addr a x)` by METIS_TAC [ref_addr_NEQ,va_IMP]
  \\ ASM_SIMP_TAC bool_ss [] \\ Cases_on `p` \\ Cases_on `r` \\ Cases_on `r'`
  \\ FULL_SIMP_TAC std_ss [ref_mem_def] \\ METIS_TAC [ref_addr_ADD_NEQ]);

val ref_field_and_3 = prove(
  ``!n a x m e d xs ys. ref_cheney (m,e) (a,d,xs,ys) ==> ((ref_field a (n,x) && 3w = 0w) = ~(n = 0))``,
  STRIP_TAC \\ REVERSE (Cases_on `n = 0`) \\ ASM_SIMP_TAC bool_ss [ref_field_def]
  THEN1 METIS_TAC [ref_field_def,ref_cheney_ALIGNED,GSYM ALIGNED_def]
  \\ Cases_on `x` \\ Cases_on `r` \\ REWRITE_TAC [ref_field_def]
  \\ SIMP_TAC std_ss [ALIGNED_add_3_and_3,ALIGNED_add_2_and_3,ALIGNED_ADDR32]
  \\ EVAL_TAC \\ REWRITE_TAC []);

val ref_field_and_3_EQ_1 = prove(
  ``!x a y. ALIGNED a ==> ~(ref_field a (x,y) && 3w = 1w)``,
  STRIP_TAC \\ Cases_on `x = 0` \\ ASM_SIMP_TAC bool_ss [ref_field_def] THENL [
    Cases_on `y` \\ Cases_on `r` \\ REWRITE_TAC [FST,SND]
    \\ METIS_TAC [ALIGNED_add_2_and_3,ALIGNED_add_3_and_3,
         ALIGNED_ADDR32,EVAL ``~(2w = 1w:word32) /\ ~(3w = 1w:word32)``],
    METIS_TAC [ALIGNED_ref_addr,ALIGNED_def,EVAL ``0w = 1w:word32``]]);

val ref_cheney_move_lemma = prove(
  ``ref_cheney (m,e) (a,d,xs,ys) /\ (~(x = 0) ==> ~(m x = EMP)) /\ (!x. ~(m x = REF 0)) /\
    (move(x,j,m) = (x1,j1,m1)) /\ ~(j = 0) /\ j <= e /\ x <= e /\
    (arm_move(ref_addr a j,ref_field a (x,xx),r7,r8,d,xs) = (j2,x2,r7_2,r8_2,d2,xs2)) ==>
    ref_cheney (m1,e) (a,d,xs2,ys) /\ (x2 = ref_field a (x1,xx)) /\ (j2 = ref_addr a j1) /\ (d2 = d) /\
    arm_move_pre(ref_addr a j,ref_field a (x,xx),r7,r8, d, xs)``,
  SIMP_TAC std_ss [def1,GSYM AND_IMP_INTRO]
  \\ STRIP_TAC \\ IMP_RES_TAC ref_field_and_3
  \\ ASM_SIMP_TAC bool_ss []
  \\ Q.PAT_X_ASSUM `!xnn.nnn` (K ALL_TAC)
  \\ REWRITE_TAC [move_def] \\ Cases_on `x = 0`
  THEN1 (Cases_on `xx` \\ ASM_SIMP_TAC std_ss [] \\ METIS_TAC [])
  \\ Cases_on `x <= e` \\ ASM_SIMP_TAC bool_ss []
  \\ SIMP_TAC std_ss [GSYM AND_IMP_INTRO] \\ STRIP_TAC
  \\ Cases_on `m x` \\ FULL_SIMP_TAC bool_ss [isREF_def,heap_type_11,getREF_def]
  THEN1 (
      ONCE_REWRITE_TAC [EQ_SYM_EQ] \\ SIMP_TAC std_ss []
      \\ SIMP_TAC std_ss [LET_DEF,GSYM AND_IMP_INTRO] \\ NTAC 2 STRIP_TAC
      \\ IMP_RES_TAC ref_cheney_d \\ IMP_RES_TAC ref_cheney_ALIGNED
      \\ FULL_SIMP_TAC bool_ss [ref_cheney_def,ref_mem_def]
      \\ `ref_mem x (REF n) (a,xs)` by METIS_TAC []
      \\ FULL_SIMP_TAC bool_ss [ref_cheney_def,ref_mem_def,ref_field_def]
      \\ `ref_addr a n + 1w && 3w = 1w` by METIS_TAC [ALIGNED_add_1_and_3,ALIGNED_ref_addr,ALIGNED_def]
      \\ ASM_SIMP_TAC bool_ss [PAIR_EQ,WORD_ADD_SUB]
      \\ ASM_SIMP_TAC bool_ss [INSERT_SUBSET,EMPTY_SUBSET,ALIGNED_def]
      \\ ONCE_REWRITE_TAC [WORD_AND_COMM]
      \\ ASM_SIMP_TAC bool_ss [] \\ METIS_TAC [])
  \\ SIMP_TAC std_ss [heap_type_distinct]
  \\ ONCE_REWRITE_TAC [EQ_SYM_EQ] \\ SIMP_TAC std_ss []
  \\ SIMP_TAC std_ss [LET_DEF]
  \\ `~(m x = EMP)` by METIS_TAC [heap_type_distinct]
  \\ `valid_address a x` by METIS_TAC [ref_cheney_def,va_IMP]
  \\ ASM_SIMP_TAC std_ss [word_arith_lemma1,WORD_ADD_SUB]
  \\ IMP_RES_TAC (GEN_ALL ref_cheney_ALIGNED)
  \\ ASM_SIMP_TAC std_ss [ref_field_def]
  \\ `~(xs (ref_addr a x) && 3w = 1w)` by
       (FULL_SIMP_TAC bool_ss [ref_cheney_def]
        \\ Cases_on `p` \\ Cases_on `r` \\ Cases_on `r'`
        \\ `ref_mem x (DATA (q,q',q'',r)) (a,xs)` by METIS_TAC []
        \\ CCONTR_TAC \\ FULL_SIMP_TAC bool_ss [ref_mem_def]
        \\ `ref_field a (q,q'') && 3w = 1w` by METIS_TAC []
        \\ METIS_TAC [ALIGNED_def,ref_field_and_3_EQ_1])
  \\ FULL_SIMP_TAC std_ss [PAIR_EQ,WORD_ADD_0,word_arith_lemma4]
  \\ REVERSE (NTAC 6 STRIP_TAC) THEN1
    (`~(j = 0)` by METIS_TAC []
     \\ IMP_RES_TAC ref_cheney_d \\ IMP_RES_TAC ref_cheney_ALIGNED
     \\ ASM_SIMP_TAC std_ss [INSERT_SUBSET,EMPTY_SUBSET,ALIGNED_def,LET_DEF,WORD_ADD_0,LENGTH]
     \\ ONCE_REWRITE_TAC [EQ_SYM_EQ]
     \\ ASM_REWRITE_TAC [RW [ALIGNED_def] ALIGNED_CLAUSES]
     \\ SIMP_TAC std_ss [ref_addr_def,LEFT_ADD_DISTRIB,GSYM word_add_n2w,WORD_ADD_ASSOC])
  \\ MATCH_MP_TAC ref_cheney_update_REF
  \\ ASM_SIMP_TAC bool_ss []
  \\ Cases_on `p` \\ Cases_on `r` \\ Cases_on `r'` \\ FULL_SIMP_TAC std_ss [ref_cheney_def]
  \\ REVERSE (REPEAT STRIP_TAC) THENL [ALL_TAC,ASM_SIMP_TAC std_ss [UPDATE_def],ALL_TAC]
  THEN1 (`valid_address a j` by METIS_TAC [va_IMP,UPDATE_ref_addr4,UPDATE_ref_addr]
         \\ MATCH_MP_TAC UPDATE_ref_addr4 \\ ASM_SIMP_TAC bool_ss []
         \\ MATCH_MP_TAC UPDATE_ref_addr \\ ASM_SIMP_TAC bool_ss [])
  \\ `ref_mem x (DATA (q,q',q'',r)) (a,xs)` by METIS_TAC []
  \\ Cases_on `i = j`
  THEN1 (FULL_SIMP_TAC bool_ss [UPDATE_def,ref_mem_def,WORD_EQ_ADD_LCANCEL,
           RW[WORD_ADD_0](Q.SPECL[`x`,`y`,`0w`]WORD_EQ_ADD_LCANCEL)]
         \\ SIMP_TAC (std_ss++SIZES_ss) [n2w_11])
  \\ `ref_mem i (m i) (a,xs)` by METIS_TAC []
  \\ CONV_TAC (RATOR_CONV (SIMP_CONV std_ss [UPDATE_def]))
  \\ ASM_SIMP_TAC bool_ss []
  \\ Cases_on `m i` \\ FULL_SIMP_TAC bool_ss [ref_mem_def,UPDATE_def]
  \\ `~(ref_addr a j = ref_addr a i)` by METIS_TAC [va_IMP,ref_addr_NEQ]
  \\ `valid_address a i /\ valid_address a j` by METIS_TAC [va_IMP]
  THEN1 ASM_SIMP_TAC bool_ss [ref_addr_ADD_NEQ]
  \\ Cases_on `p` \\ Cases_on `r` \\ Cases_on `r'` \\ Cases_on `r`
  \\ FULL_SIMP_TAC bool_ss [ref_mem_def,UPDATE_def,ref_addr_ADD_NEQ,WORD_EQ_ADD_RCANCEL]);

val ref_cheney_move = prove(
  ``!a b b' i j j2 j3 e m m2 w ww r x xj2 xx2 xs xs2 d x2 xx  r7 r8 r7_2 r8_2 d2.
    cheney_inv (b,b',i,j,j3,e,f,m,w,ww,r) /\ {x} SUBSET0 DR0(ICUT(b,e)m) /\
    ref_cheney (m,f) (a,d,xs,ys) /\ (move(x,j,m) = (x2,j2,m2)) /\
    (arm_move(ref_addr a j,ref_field a (x,xx),r7,r8, d, xs) = (xj2,xx2,r7_2,r8_2,d2,xs2)) ==>
    cheney_inv(b,b',i,j2,j3,e,f,m2,w,ww,r) /\ {x2} SUBSET0 RANGE(b,j2) /\ j <= j2 /\
    (CUT(b,j)m = CUT(b,j)m2) /\ (DR0 (ICUT(b,e)m) = DR0 (ICUT(b,e)m2)) /\
    ref_cheney (m2,f) (a,d,xs2,ys) /\
    (ref_field a (x2,xx) = xx2) /\ (ref_addr a j2 = xj2) /\ (d = d2) /\
    arm_move_pre(ref_addr a j,ref_field a (x,xx), r7,r8, d, xs)``,
  NTAC 28 STRIP_TAC \\ `~(x = 0) ==> ~(m x = EMP)` by (STRIP_TAC
    \\ FULL_SIMP_TAC bool_ss [SUBSET0_DEF,SUBSET_DEF,IN_INSERT,NOT_IN_EMPTY]
    \\ FULL_SIMP_TAC bool_ss [IN_DEF,DR0_def,D0_def,R0_def,ICUT_def]
    \\ METIS_TAC [heap_type_distinct])
  \\ `~(j = 0) /\ j <= f` by (FULL_SIMP_TAC bool_ss [cheney_inv_def] \\ DECIDE_TAC)
  \\ IMP_RES_TAC move_lemma
  \\ ASM_SIMP_TAC bool_ss [] \\ ONCE_REWRITE_TAC [EQ_SYM_EQ]
  \\ `!x. ~(m x = REF 0)` by
   (CCONTR_TAC \\ FULL_SIMP_TAC bool_ss [cheney_inv_def,cheney_gcTheory.R1_def]
    \\ `RANGE(b,j) 0` by METIS_TAC [cheney_gcTheory.R1_def]
    \\ FULL_SIMP_TAC bool_ss [RANGE_def] \\ DECIDE_TAC)
  \\ MATCH_MP_TAC ref_cheney_move_lemma
  \\ ASM_SIMP_TAC bool_ss [PAIR_EQ] \\ METIS_TAC []);

val arm_move2_thm = prove(
  ``(arm_move2 = arm_move) /\ (arm_move2_pre = arm_move_pre)``,
  TAILREC_TAC \\ SIMP_TAC std_ss [LET_DEF]);

val ref_cheney_inv_def = Define `
  ref_cheney_inv (b,i,j,k,e,f,m,w,ww,r) (a,r3,r4,d,xs,ys) =
    cheney_inv (b,b,i,j,k,e,f,m,w,ww,r) /\ ref_cheney (m,f) (a,d,xs,ys) /\
    valid_address a e /\ (r4 = ref_addr a j) /\ (r3 = ref_addr a i)`;

val ref_cheney_step_thm = prove(
  ``ref_cheney_inv (b,i,j,j,e,f,m,x,xx,r) (a,r3,r4,d,xs,ys) /\ ~(i = j) /\
    (cheney_step (i,j,e,m) = (i',j',e',m')) /\
    (arm_cheney_step (r3,r4,r7,r8,d,xs) = (r3',r4',r5',r6',r7',r8',d',xs')) ==>
    ref_cheney_inv (b,i',j',j',e',f,m',x,xx,r) (a,r3',r4',d,xs',ys) /\ (d = d') /\
    arm_cheney_step_pre (r3,r4,r7,r8,d,xs)``,
  REWRITE_TAC [ref_cheney_inv_def] \\ STRIP_TAC
  \\ `cheney_inv (b,b,i',j',j',e',f,m',x,xx,r)` by METIS_TAC [cheney_inv_step]
  \\ ASM_SIMP_TAC bool_ss []
  \\ Q.UNDISCH_TAC `cheney_step (i,j,e,m) = (i',j',e',m')`
  \\ Q.UNDISCH_TAC `arm_cheney_step (r3,r4,r7,r8,d,xs) = (r3',r4',r5',r6',r7',r8',d',xs')`
  \\ REWRITE_TAC [cheney_step_def]
  \\ SIMP_TAC bool_ss [def3]
  \\ `?r51. xs r3 = r51` by METIS_TAC []
  \\ `?r61. xs (r3+4w) = r61` by METIS_TAC []
  \\ `?r41 r52 r71 r81 d1 xs1. arm_move (ref_addr a j,r51,r7,r8,d,xs) = (r41,r52,r71,r81,d1,xs1)` by METIS_TAC [PAIR]
  \\ `?r42 r62 r72 r82 d2 xs2. arm_move (r41,r61,r71,r81,d1,xs1) = (r42,r62,r72,r82,d2,xs2)` by METIS_TAC [PAIR]
  \\ `?x1 y1 d1 d1a. getDATA (m i) = (x1,y1,d1,d1a)` by METIS_TAC [PAIR]
  \\ `?x2 j2 m2. move(x1,j,m) = (x2,j2,m2)` by METIS_TAC [PAIR]
  \\ `?y3 j3 m3. move(y1,j2,m2) = (y3,j3,m3)` by METIS_TAC [PAIR]
  \\ `(xs (ref_addr a i) = r51) /\ (xs (ref_addr a i + 4w) = r61)` by METIS_TAC []
  \\ ASM_SIMP_TAC std_ss [LET_DEF,arm_move2_thm,GSYM AND_IMP_INTRO]
  \\ ONCE_REWRITE_TAC [EQ_SYM_EQ] \\ SIMP_TAC bool_ss []
  \\ REPEAT (MATCH_MP_TAC (METIS_PROVE [] ``P ==> (Q ==> P)``))
  \\ `~(i = 0) /\ ~(j = 0) /\ (j <= e)` by
       (FULL_SIMP_TAC bool_ss [cheney_inv_def] \\ DECIDE_TAC)
  \\ `ref_addr a (i + 1) = ref_addr a i + 8w` by
   (ASM_SIMP_TAC std_ss [ref_addr_def,GSYM ADD1,MULT_CLAUSES,GSYM word_add_n2w]
    \\ SIMP_TAC bool_ss [AC WORD_ADD_ASSOC WORD_ADD_COMM])
  \\ ASM_SIMP_TAC bool_ss []
  \\ `?ax ay ad ad1. m i = DATA(ax,ay,ad,ad1)` by METIS_TAC [m_DATA,PAIR]
  \\ `(x1,y1,d1',d1a) = (ax,ay,ad,ad1)` by METIS_TAC [getDATA_def]
  \\ FULL_SIMP_TAC bool_ss [PAIR_EQ]
  \\ Q.PAT_X_ASSUM `getDATA (DATA (ax,ay,ad,ad1)) = (ax,ay,ad,ad1)` (K ALL_TAC)
  \\ `{ax} SUBSET0 DR0 (ICUT (b,e) m) /\ {ay} SUBSET0 DR0 (ICUT (b,e) m)` by
   (sg `{ax;ay} SUBSET0 D1(CUT(i,j)m)` THENL [
      FULL_SIMP_TAC bool_ss [SUBSET0_DEF,IN_INSERT,SUBSET_DEF,NOT_IN_EMPTY]
      \\ FULL_SIMP_TAC bool_ss [IN_DEF,D1_def,CUT_def,cheney_inv_def]
      \\ `RANGE(i,j)i` by (REWRITE_TAC [RANGE_def] \\ DECIDE_TAC)
      \\ METIS_TAC [],
      `{ax;ay} SUBSET0 DR0 (ICUT (b,e) m)` by
        METIS_TAC [cheney_inv_def,SUBSET0_TRANS]
      \\ FULL_SIMP_TAC bool_ss [SUBSET0_DEF,SUBSET_DEF,IN_INSERT,NOT_IN_EMPTY]])
  \\ `i <= e /\ i <= f /\ j <= f /\ RANGE(b,j)i` by
        (FULL_SIMP_TAC bool_ss [cheney_inv_def,RANGE_def] \\ DECIDE_TAC)
  \\ `ref_mem i (DATA (ax,ay,ad,ad1)) (a,xs)` by METIS_TAC [ref_cheney_def]
  \\ FULL_SIMP_TAC bool_ss [ref_mem_def]
  \\ `(r51 = ref_field a (ax,ad)) /\ (r61 = ref_field a (ay,ad1))` by METIS_TAC []
  \\ FULL_SIMP_TAC bool_ss []
  \\ (STRIP_ASSUME_TAC o UNDISCH_ALL o RW [GSYM AND_IMP_INTRO] o
       Q.SPECL [`a`,`b`,`b`,`i`,`j`,`j2`,`j`,`e`,`m`,`m2`,`x`,`xx`,`r`,`ax`,`r41`,`r52`,`xs`,`xs1`,`d`,`x2`,`ad`,`r7`,`r8`,`r71`,`r81`,`d1`]) ref_cheney_move
  \\ Q.PAT_X_ASSUM `ref_addr a j2 = r41` (ASSUME_TAC o GSYM)
  \\ FULL_SIMP_TAC bool_ss []
  \\ (STRIP_ASSUME_TAC o UNDISCH_ALL o RW [GSYM AND_IMP_INTRO] o
       Q.SPECL [`a`,`b`,`b`,`i`,`j2`,`j3`,`j`,`e`,`m2`,`m3`,`x`,`xx`,`r`,`ay`,`r42`,`r62`,`xs1`,`xs2`,`d1`,`y3`,`ad1`,`r71`,`r81`,`r72`,`r82`,`d2`]) ref_cheney_move
  \\ IMP_RES_TAC ref_cheney_d
  \\ REPEAT (Q.PAT_X_ASSUM `!xx.bb` (K ALL_TAC))
  \\ REPEAT (Q.PAT_X_ASSUM `ccc ==> !xx.bb` (K ALL_TAC))
  \\ IMP_RES_TAC ref_cheney_ALIGNED
  \\ ASM_SIMP_TAC std_ss [INSERT_SUBSET,EMPTY_SUBSET,ALIGNED_def,LET_DEF,WORD_ADD_0,LENGTH]
  \\ ONCE_REWRITE_TAC [EQ_SYM_EQ]
  \\ ASM_SIMP_TAC std_ss [RW [ALIGNED_def] ALIGNED_CLAUSES,word_arith_lemma1]
  \\ Q.PAT_X_ASSUM `ref_cheney (m3,f) (a,d1,xs2,ys)` (STRIP_ASSUME_TAC o RW [ref_cheney_def])
  \\ REVERSE STRIP_TAC THEN1 METIS_TAC []
  \\ ASM_SIMP_TAC bool_ss [ref_cheney_def,APPLY_UPDATE_THM]
  \\ ASM_SIMP_TAC bool_ss [ref_addr_ADD_NEQ]
  \\ `m3 i = m i` by
       (`RANGE(b,j2)i` by (FULL_SIMP_TAC bool_ss [RANGE_def] \\ DECIDE_TAC)
        \\ FULL_SIMP_TAC bool_ss [CUT_def,FUN_EQ_THM]
        \\ METIS_TAC [heap_type_distinct])
  \\ REVERSE (REPEAT STRIP_TAC) \\ `~(j3 = 0)` by DECIDE_TAC
  THEN1 (REWRITE_TAC [GSYM APPLY_UPDATE_THM]
    \\ `valid_address a i` by METIS_TAC [va_IMP]
    \\ MATCH_MP_TAC UPDATE_ref_addr4 \\ ASM_SIMP_TAC bool_ss []
    \\ MATCH_MP_TAC UPDATE_ref_addr \\ ASM_SIMP_TAC bool_ss [] \\ METIS_TAC [])
  \\ Cases_on `i'' = i` \\ ASM_SIMP_TAC bool_ss [ref_mem_def,UPDATE_def] THENL [
    `valid_address a i` by METIS_TAC [va_IMP]
    \\ `ref_mem i (DATA (ax,ay,ad,ad1)) (a,xs2)` by METIS_TAC []
    \\ FULL_SIMP_TAC bool_ss [ref_mem_def,ref_addr_ADD_NEQ],
    Cases_on `m3 i''` \\ ASM_SIMP_TAC bool_ss [ref_mem_def]
    THENL [ALL_TAC,Cases_on`p` \\ Cases_on`r'` \\ Cases_on`r''`]
    \\ `valid_address a i /\ valid_address a i'' /\ ref_mem i'' (m3 i'') (a,xs2)` by
      METIS_TAC [ref_cheney_def,heap_type_distinct,va_IMP]
    \\ Q.PAT_X_ASSUM `m3 i'' = xxxxx` (ASSUME_TAC)
    \\ FULL_SIMP_TAC bool_ss [ref_mem_def,ref_addr_NEQ,ref_addr_ADD_NEQ,WORD_EQ_ADD_RCANCEL]]);

val ref_cheney_loop_th = prove(
  ``!b i j e m x y r r3 r4 r5 r6 r7 r8 d xs i' m' r3' r4' r5' r6' r7' r8' d2 xs'.
      ref_cheney_inv (b,i,j,j,e,f,m,x,xx,r) (a,r3,r4,d,xs,ys) /\
      (cheney (i,j,e,m) = (i',m')) /\
      (arm_cheney_loop (r3,r4,r5,r6,r7,r8,d,xs) = (r3',r4',r5',r6',r7',r8',d2,xs')) ==>
      ref_cheney_inv (b,i',i',i',e,f,m',x,xx,r) (a,r3',r4',d,xs',ys) /\ (d2 = d) /\
      arm_cheney_loop_pre (r3,r4,r5,r6,r7,r8,d,xs)``,
  completeInduct_on `e - i:num` \\ NTAC 2 (ONCE_REWRITE_TAC [cheney_def])
  \\ ASM_REWRITE_TAC [GSYM AND_IMP_INTRO] \\ NTAC 28 STRIP_TAC
  \\ ONCE_REWRITE_TAC [def4]
  \\ SIMP_TAC std_ss []
  \\ Cases_on `i = j` THEN1
    (Q.PAT_X_ASSUM `!m.bb` (K ALL_TAC)
     \\ FULL_SIMP_TAC std_ss [ref_cheney_inv_def] \\ ONCE_REWRITE_TAC [EQ_SYM_EQ]
     \\ ASM_SIMP_TAC std_ss [] \\ METIS_TAC [])
  \\ Q.PAT_X_ASSUM `ref_cheney_inv (b,i,j,j,e,f,m,x,xx,r) (a,r3,r4,d,xs,ys)`
      (fn th => STRIP_ASSUME_TAC (RW [ref_cheney_inv_def] th) \\ ASSUME_TAC th)
  \\ `i <= j /\ j <= e` by METIS_TAC [cheney_inv_def]
  \\ Cases_on `v = 0` THEN1 `F` by DECIDE_TAC
  \\ `valid_address a i /\ valid_address a j /\ ~(e < i)` by
    (FULL_SIMP_TAC bool_ss [valid_address_def] \\ DECIDE_TAC)
  \\ ASM_REWRITE_TAC [] \\ SIMP_TAC (std_ss++pbeta_ss) [LET_DEF]
  \\ `?i2 j2 e2 m2. cheney_step (i,j,e,m) = (i2,j2,e2,m2)` by METIS_TAC [PAIR]
  \\ `?r31 r41 r51 r61 r71 r81 d1 xs1. arm_cheney_step (ref_addr a i,ref_addr a j,r7,r8,d,xs) =
                      (r31,r41,r51,r61,r71,r81,d1,xs1)` by METIS_TAC [PAIR]
  \\ `~(ref_addr a i = ref_addr a j)` by METIS_TAC [ref_addr_NEQ]
  \\ ASM_REWRITE_TAC []
  \\ STRIP_TAC
  \\ `e - (i + 1) < v` by DECIDE_TAC
  \\ Q.PAT_X_ASSUM `!m. m < v ==> !e i. bbb`
    (ASSUME_TAC o RW [] o Q.SPECL [`e`,`i+1`] o UNDISCH o Q.SPEC `e - (i + 1)`)
  \\ `ref_cheney_inv (b,i2,j2,j2,e2,f,m2,x,xx,r) (a,r31,r41,d,xs1,ys) /\ (d = d1) /\
      arm_cheney_step_pre (r3,r4,r7,r8,d,xs)` by METIS_TAC [ref_cheney_step_thm]
  \\ `(i2 = i+1) /\ (e2 = e)` by FULL_SIMP_TAC (std_ss++pbeta_ss) [cheney_step_def,LET_DEF]
  \\ METIS_TAC []);

val SING_IN_SUBSET0 = prove(
  ``x IN t /\ t SUBSET0 s ==> {x} SUBSET0 s``,
  SIMP_TAC bool_ss [SUBSET0_DEF,SUBSET_DEF,IN_INSERT,NOT_IN_EMPTY]);

val roots_in_mem_def = Define `
  (roots_in_mem [] (a,r12,m) = T) /\
  (roots_in_mem (x::xs) (a,r12,m) =
      (m r12 = ref_field a x) /\ r12 <+ ref_addr a 1 /\ r12 <+ r12 + 4w /\
      roots_in_mem xs (a,r12+4w,m))`;

val NOT_ref_addr = prove(
  ``!x a. valid_address a i /\ x <+ ref_addr a 1 /\ ~(i = 0) ==>
          ~(x = ref_addr a i) /\ ~(x = ref_addr a i + 4w)``,
  Cases_word \\ Cases_word \\ ASM_SIMP_TAC (std_ss++SIZES_ss)
       [ref_addr_def,word_add_n2w,n2w_11,WORD_LO,w2n_n2w,valid_address_def,LESS_MOD]
  \\ REPEAT STRIP_TAC
  \\ `n' + 8 * i < 4294967296 /\ n' + 8 < 4294967296` by DECIDE_TAC
  \\ `n' + 8 * i + 4 < 4294967296` by DECIDE_TAC
  \\ FULL_SIMP_TAC std_ss [LESS_MOD] \\ DECIDE_TAC);

val lemma = prove(
  ``ref_cheney (m1,f) (a,d,xs1,xs) /\ r12 <+ ref_addr a 1 ==>
    ref_cheney (m1,f) (a,d,(r12 =+ r51) xs1,(r12 =+ r51) xs1)``,
  SIMP_TAC bool_ss [ref_cheney_def] \\ REPEAT STRIP_TAC
  \\ Cases_on `m1 i` \\ ASM_REWRITE_TAC [ref_mem_def] THENL [
    `ref_addr a n + 1w = xs1 (ref_addr a i)` by METIS_TAC [ref_mem_def]
    \\ ASM_SIMP_TAC bool_ss [APPLY_UPDATE_THM]
    \\ METIS_TAC [NOT_ref_addr,va_IMP,heap_type_distinct],
    Cases_on `p` \\ Cases_on `r` \\ Cases_on `r'` \\ ASM_REWRITE_TAC [ref_mem_def]
    \\ ASM_SIMP_TAC bool_ss [APPLY_UPDATE_THM]
    \\ METIS_TAC [NOT_ref_addr,va_IMP,heap_type_distinct,ref_mem_def]]);

val roots_lemma = prove(
  ``!rs b k.
      roots_in_mem rs (a,b + k,xs) ==> b <+ b + k ==>
      ref_cheney (m,f) (a,d,xs1,xs) ==>
      roots_in_mem rs (a,b + k,(b =+ r51) xs1)``,
  Induct \\ REWRITE_TAC [roots_in_mem_def]
  \\ SIMP_TAC std_ss [APPLY_UPDATE_THM,WORD_LOWER_NOT_EQ,GSYM WORD_ADD_ASSOC]
  \\ REPEAT STRIP_TAC \\ METIS_TAC [ref_cheney_def,WORD_LOWER_TRANS]);

val root_address_ok_def = Define `
  (root_address_ok a 0 x = T) /\
  (root_address_ok a (SUC n) x = ALIGNED a /\ a IN x /\ root_address_ok (a+4w) n x)`;

val ref_cheney_move_roots = prove(
  ``!rs zs ds j m r4 r5 r7 r8 xs r12 ys jn mn.
      LENGTH rs < 2**32 /\ (LENGTH ds = LENGTH rs + LENGTH zs) /\
      root_address_ok r12 (LENGTH rs) x /\
      roots_in_mem (ZIP (rs++zs,ds)) (a,r12,xs) /\
      (!x. MEM x rs ==> {x} SUBSET0 DR0 (ICUT (b,e) m)) /\
      ref_cheney_inv (b,i,j,j',e,f,m,(w:num->((bool[30] # bool) # bool[30] # bool) heap_type),ww,r) (a,r3,r4,x,xs,xs) ==>
      (arm_move_roots(r4,r5,n2w (LENGTH rs),r7,r8,r12,x,xs) = (r4n,r5n,r6n,r7n,r8n,r12n,xn,xsn)) /\
      (move_roots(rs,j,m) = (ys,jn,mn)) ==>
      arm_move_roots_pre(r4,r5,n2w (LENGTH rs),r7,r8,r12,x,xs) /\
      ref_cheney_inv (b,i,jn,j',e,f,mn,w,ww,r) (a,r3,r4n,x,xsn,xsn) /\
      roots_in_mem (ZIP (ys++zs,ds)) (a,r12,xsn) /\
      (LENGTH ys = LENGTH rs) /\ (r12n = r12 + n2w (4 * LENGTH rs)) /\
      (!i. i <+ r12 ==> (xs i = xsn i)) /\ (xn = x)``,
  STRIP_TAC \\ STRIP_TAC \\ Induct_on `rs` THEN1
   (ONCE_REWRITE_TAC [def5] \\ SIMP_TAC std_ss [LET_DEF]
    \\ Cases_on `ys` \\ REWRITE_TAC [move_roots_def,PAIR_EQ,LENGTH,MAP,NOT_NIL_CONS]
    \\ ONCE_REWRITE_TAC [EQ_SYM_EQ] \\ SIMP_TAC std_ss [LENGTH,WORD_MULT_CLAUSES,WORD_ADD_0])
  \\ POP_ASSUM (ASSUME_TAC o RW1 [GSYM CONTAINER_def])
  \\ ONCE_REWRITE_TAC [def5] \\ SIMP_TAC std_ss [LET_DEF]
  \\ Cases_on `ds`
  \\ SIMP_TAC std_ss [LENGTH,ADD1,DECIDE ``(k + 1 = m + 1 + n) = (k = m + n:num)``,ZIP,APPEND]
  \\ SIMP_TAC (std_ss++SIZES_ss) [n2w_11,LESS_MOD,LENGTH,DECIDE ``~(SUC n = 0)``]
  \\ SIMP_TAC std_ss [ADD1,GSYM word_add_n2w,WORD_ADD_SUB]
  \\ NTAC 12 STRIP_TAC
  \\ `?r41 r51 r71 r81 x1 xs1. arm_move (r4,xs r12,r7,r8,x,xs) = (r41,r51,r71,r81,x1,xs1)` by METIS_TAC [PAIR]
  \\ ASM_REWRITE_TAC [LET_DEF,PAIR_EQ,move_roots_def,APPEND,MAP]
  \\ `?y1 j1 m1. move (h',j,m) = (y1,j1,m1)` by METIS_TAC [PAIR]
  \\ `?ys j2 m2. move_roots (rs,j1,m1) = (ys,j2,m2)` by METIS_TAC [PAIR]
  \\ FULL_SIMP_TAC std_ss [LET_DEF,PAIR_EQ,move_roots_def,GSYM AND_IMP_INTRO,MAP] \\ STRIP_TAC
  \\ ONCE_REWRITE_TAC [EQ_SYM_EQ] \\ SIMP_TAC bool_ss []
  \\ FULL_SIMP_TAC bool_ss [MAP,CONS_11,NOT_NIL_CONS,NOT_CONS_NIL,ZIP,APPEND,ADD1,EQ_ADD_RCANCEL,LENGTH]
  \\ REPEAT (MATCH_MP_TAC (METIS_PROVE [] ``P ==> (Q ==> P)``))
  \\ `LENGTH rs < 4294967296` by DECIDE_TAC
  \\ FULL_SIMP_TAC bool_ss [roots_in_mem_def,MEM,ref_cheney_inv_def,APPEND]
  \\ `{h'} SUBSET0 DR0 (ICUT(b,e)m)` by METIS_TAC [SING_IN_SUBSET0,IN_INSERT]
  \\ `arm_move (ref_addr a j,ref_field a (h',h),r7,r8,x,xs) = (r41,r51,r71,r81,x1,xs1)` by METIS_TAC [WORD_ADD_0]
  \\ FULL_SIMP_TAC bool_ss [FST,SND]
  \\ (STRIP_ASSUME_TAC o GSYM o UNDISCH_ALL o RW [GSYM AND_IMP_INTRO] o
   Q.SPECL [`a`,`b`,`b`,`i`,`j`,`j1`,`j'`,`e`,`m`,`m1`,
    `w`,`ww`,`r`,`h'`,`r41`,`r51`,`xs`,`xs1`,`x`,`y1`,`h`,`r7`,`r8`,`r71`,`r81`,`x1`] o Q.INST [`ys`|->`xs`]) (INST_TYPE [``:'a``|->``:((bool[30] # bool) # bool[30] # bool)``] ref_cheney_move)
  \\ ASM_SIMP_TAC bool_ss [WORD_ADD_0]
  \\ `!x. MEM x rs ==> {x} SUBSET0 DR0 (ICUT (b,e) m1)` by METIS_TAC []
  \\ `ref_cheney (m1,f) (a,x,(r12 =+ r51) xs1,(r12 =+ r51) xs1)` by METIS_TAC [lemma]
  \\ `roots_in_mem (ZIP (rs++zs,t)) (a,r12 + 4w,(r12 =+ r51) xs1)` by METIS_TAC [roots_lemma]
  \\ Q.PAT_X_ASSUM `r51 = ref_field a (y1,h)` ASSUME_TAC \\ FULL_SIMP_TAC bool_ss []
  \\ FULL_SIMP_TAC std_ss [root_address_ok_def,ALIGNED_def,GSYM ADD1,move_roots_def]
  \\ Q.PAT_X_ASSUM `CONTAINER (!j m xs r12. bbb)`
    (STRIP_ASSUME_TAC o UNDISCH_ALL o RW [GSYM AND_IMP_INTRO] o
     Q.SPECL [`t`,`j1`,`m1`,`ref_field a (y1,h)`,`r71`,`r81`,`(r12 =+ ref_field a (y1,h)) xs1`,`r12+4w`,`ys'`,`j2`,`m2`] o
     RW [CONTAINER_def])
  \\ FULL_SIMP_TAC std_ss [LENGTH,ADD1,word_add_n2w,word_mul_n2w,
       GSYM WORD_ADD_ASSOC,LEFT_ADD_DISTRIB,AC ADD_ASSOC ADD_COMM,FST]
  \\ METIS_TAC [APPLY_UPDATE_THM,WORD_LOWER_TRANS,WORD_LOWER_NOT_EQ,ref_cheney_def]);

val ref_cheney_move_roots6 =
  SIMP_RULE std_ss [LENGTH,ADD1,AND_IMP_INTRO,GSYM CONJ_ASSOC]
  (Q.SPEC `[x1;x2;x3;x4;x5;x6]` ref_cheney_move_roots);

val arm_c_init_lemma = prove(
  ``(arm_c_init(if u then 0w else 1w,r6,r9) =
     (r9 + 8w + if u then 0w else r6, if u then 1w else 0w,r6,r9))``,
  Cases_on `u` \\ SIMP_TAC std_ss [SIMP_RULE std_ss [LET_DEF] def6,
    WORD_ADD_0,PAIR_EQ,WORD_XOR_CLAUSES,EVAL ``0w = 1w:word32``]);

val arm_coll_inv_def = Define `
  arm_coll_inv (a,x,xs) (i,e,rs,rs',l,u,m) =
    ?x1 x2 x3 x4 x5 x6 y1 y2 y3 y4 y5 y6.
      roots_in_mem (ZIP (rs,rs') ++ [(i,(0w,F));(e,(0w,F))]) (a,a-24w,xs) /\
      (rs = [x1;x2;x3;x4;x5;x6]) /\ (rs' = [y1;y2;y3;y4;y5;y6]) /\
      valid_address a (l + l + 1) /\
      ref_cheney (m,l+l+1) (a,x,xs,xs) /\
      (xs (a-28w) = if u then 0w else 1w) /\ a - 28w <+ ref_addr a 1 /\ a - 28w <+ a - 24w /\
      (xs (a-32w) = n2w (8 * l)) /\ a - 32w <+ ref_addr a 1 /\ a - 32w <+ a - 24w`;

val roots_in_mem_carry_over = prove(
  ``!p r xs ys. ref_cheney (m,f) (a,x,xs,ys) /\ roots_in_mem p (a,r,ys) ==> roots_in_mem p (a,r,xs)``,
  Induct \\ FULL_SIMP_TAC bool_ss [roots_in_mem_def,ref_cheney_def] \\ METIS_TAC []);

val arm_coll_inv_pre_lemma = prove(
  ``arm_coll_inv (a,x,xs) (q,e,rs,rs',l,u,m) ==>
    {a+4w;a-32w;a-28w;a-24w;a-20w;a-16w;a-12w;a-8w;a-4w;a} SUBSET x /\
    !i. i IN {a+4w;a-32w;a-28w;a-24w;a-20w;a-16w;a-12w;a-8w;a-4w;a} ==> ALIGNED i``,
  REWRITE_TAC [arm_coll_inv_def,ref_cheney_def] \\ REPEAT STRIP_TAC THENL [
    Q.PAT_X_ASSUM `ref_set a (l + l + 1) = x` (ASSUME_TAC o GSYM)
    \\ ASM_SIMP_TAC bool_ss [INSERT_SUBSET,EMPTY_SUBSET,ref_set_def,IN_UNION]
    \\ REPEAT STRIP_TAC
    THEN1 (DISJ1_TAC \\ SIMP_TAC std_ss [GSPECIFICATION]
           \\ Q.EXISTS_TAC `1` \\ SIMP_TAC std_ss [] \\ DECIDE_TAC)
    \\ DISJ2_TAC \\ SIMP_TAC std_ss [GSPECIFICATION]
    THEN1 (Q.EXISTS_TAC `8` \\ SIMP_TAC std_ss [])
    THEN1 (Q.EXISTS_TAC `7` \\ SIMP_TAC std_ss [])
    THEN1 (Q.EXISTS_TAC `6` \\ SIMP_TAC std_ss [])
    THEN1 (Q.EXISTS_TAC `5` \\ SIMP_TAC std_ss [])
    THEN1 (Q.EXISTS_TAC `4` \\ SIMP_TAC std_ss [])
    THEN1 (Q.EXISTS_TAC `3` \\ SIMP_TAC std_ss [])
    THEN1 (Q.EXISTS_TAC `2` \\ SIMP_TAC std_ss [])
    THEN1 (Q.EXISTS_TAC `1` \\ SIMP_TAC std_ss [])
    THEN1 (Q.EXISTS_TAC `0` \\ SIMP_TAC (std_ss++WORD_ss) []),
    FULL_SIMP_TAC bool_ss [IN_INSERT,NOT_IN_EMPTY]
    \\ FULL_SIMP_TAC std_ss [INSERT_SUBSET,word_arith_lemma1,word_arith_lemma2]
    \\ FULL_SIMP_TAC std_ss [word_arith_lemma3,word_arith_lemma4,GSYM ALIGNED_def]
    \\ REWRITE_TAC [word_sub_def] \\ REPEAT STRIP_TAC
    \\ MATCH_MP_TAC ALIGNED_ADD \\ ASM_SIMP_TAC bool_ss [] \\ EVAL_TAC]);

val arm_collect_lemma = prove(
  ``ok_state (i,e,rs,l,u,m) ==>
    arm_coll_inv (a,x,xs) (i,e,rs,rs2,l,u,m) ==>
    (cheney_collector (i,e,rs,l,u,m) = (i',e',rs',l',u',m')) ==>
    (arm_collect (r7,r8,a,x,xs) = (r3',r4',r5',r6',r7',r8',a',x',xs')) ==>
    arm_collect_pre (r7,r8,a,x,xs) /\
    arm_coll_inv (a,x,xs') (i,e',rs',rs2,l',u',m') /\ (x = x') /\
    (r3' = ref_addr a i') /\ (r4' = ref_addr a e') /\ (a = a') /\ (l = l')``,
  STRIP_TAC \\ STRIP_TAC \\ IMP_RES_TAC arm_coll_inv_pre_lemma
  \\ ONCE_REWRITE_TAC [def7]
  \\ FULL_SIMP_TAC bool_ss [GSYM AND_IMP_INTRO,arm_coll_inv_def]
  \\ POP_ASSUM (STRIP_ASSUME_TAC o RW [arm_coll_inv_def])
  \\ ASM_SIMP_TAC bool_ss [LET_DEF]
  \\ ASM_SIMP_TAC std_ss [arm_c_init_lemma]
  \\ Q.ABBREV_TAC `xs1 = (a - 28w =+ (if u then 1w else 0w)) xs`
  \\ Q.ABBREV_TAC `r4l = a + 8w + (if u then 0w else n2w (8 * l))`
  \\ Q.ABBREV_TAC `xs2 = (a + 4w =+ r4l + n2w (8 * l)) xs1`
  \\ `?r43 r53 r63 r73 r83 a3 x3 xs3.
        arm_move_roots (r4l,r4l + n2w (8 * l),6w,r7,r8,a - 24w,x,xs2) =
         (r43,r53,r63,r73,r83,a3,x3,xs3)` by METIS_TAC [PAIR]
  \\ `?r34 r44 r54 r64 r74 r84 x4 xs4. arm_cheney_loop (r4l,r43,r53,r63,r73,r83,x3',xs3) =
                    (r34,r44,r54,r64,r74,r84,x4,xs4)` by METIS_TAC [PAIR]
  \\ ASM_SIMP_TAC std_ss [LET_DEF,cheney_collector_def]
  \\ Q.ABBREV_TAC `b = if ~u then 1 + l else 1`
  \\ `?ys j2 m2. move_roots ([x1; x2; x3; x4; x5; x6],b,m) = (ys,j2,m2)` by METIS_TAC [PAIR]
  \\ `?i3 m3. cheney (b,j2,b + l,m2) = (i3,m3)` by METIS_TAC [PAIR]
  \\ ASM_SIMP_TAC std_ss []
  \\ ASM_SIMP_TAC std_ss [LET_DEF]
  \\ ONCE_REWRITE_TAC [EQ_SYM_EQ] \\ SIMP_TAC std_ss [GSYM AND_IMP_INTRO]
  \\ REPEAT (MATCH_MP_TAC (METIS_PROVE [] ``P ==> (Q ==> P)``))
  \\ `roots_in_mem (ZIP (rs,rs2) ++ [(i,0w,F); (e,0w,F)]) (a,a - 24w,xs1)` by
   (Q.UNABBREV_TAC `xs1`
    \\ FULL_SIMP_TAC bool_ss [APPEND,roots_in_mem_def,APPLY_UPDATE_THM,ZIP]
    \\ SIMP_TAC (std_ss++WORD_ss) [WORD_EQ_ADD_LCANCEL,n2w_11,
      RW [WORD_ADD_0] (Q.SPECL [`v`,`w`,`0w`] WORD_EQ_ADD_LCANCEL)])
  \\ Q.PAT_X_ASSUM `roots_in_mem ppp (aaa,bbb,xs)` (K ALL_TAC)
  \\ Q.PAT_X_ASSUM `rs = ppppp` ASSUME_TAC
  \\ Q.PAT_X_ASSUM `rs2 = ppppp` ASSUME_TAC
  \\ `roots_in_mem (ZIP (rs,rs2) ++ [(i,0w,F); (b+l,0w,F)]) (a,a - 24w,xs2) /\ a + 4w <+ ref_addr a 1` by
   (Q.UNABBREV_TAC `xs2` \\ Q.UNABBREV_TAC `b`
    \\ FULL_SIMP_TAC bool_ss [APPEND,roots_in_mem_def,APPLY_UPDATE_THM,ZIP]
    \\ FULL_SIMP_TAC (std_ss++WORD_ss) [WORD_EQ_ADD_LCANCEL,n2w_11,
      RW [WORD_ADD_0] (Q.SPECL [`v`,`w`,`0w`] WORD_EQ_ADD_LCANCEL)]
    \\ Q.UNABBREV_TAC `r4l` \\ Cases_on `u`
    \\ SIMP_TAC std_ss [ref_addr_def,DECIDE ``~(m+1 = 0)``,GSYM WORD_ADD_ASSOC,
         word_add_n2w,LEFT_ADD_DISTRIB,AC ADD_COMM ADD_ASSOC,ref_field_def])
  \\ IMP_RES_TAC (SIMP_RULE std_ss [LET_DEF] ok_state_IMP_cheney_inv)
  \\ Q.UNABBREV_TAC `b`
  \\ Q.ABBREV_TAC `b = if ~u then 1 + l else 1`
  \\ Q.PAT_X_ASSUM `rs = [x1; x2; x3; x4; x5; x6]` ASSUME_TAC
  \\ FULL_SIMP_TAC bool_ss []
  \\ `ref_cheney_inv (b,b,b,b,b+l,l+l+1,m,m,m,{}) (a,ref_addr a b,r4l,x,xs2,xs2)` by
   (ASM_REWRITE_TAC [ref_cheney_inv_def,CONJ_ASSOC]
    \\ Q.UNABBREV_TAC `r4l` \\ Q.UNABBREV_TAC `b`  \\ REVERSE STRIP_TAC
    THEN1 (Cases_on `u` \\ SIMP_TAC std_ss [ref_addr_def,WORD_ADD_0,
      LEFT_ADD_DISTRIB,GSYM word_add_n2w,WORD_ADD_ASSOC])
    \\ REVERSE STRIP_TAC
    THEN1 (Cases_on `u` \\ FULL_SIMP_TAC bool_ss [valid_address_def] \\ DECIDE_TAC)
    \\ Q.UNABBREV_TAC `xs2`
    \\ Q.UNABBREV_TAC `xs1`
    \\ MATCH_MP_TAC (Q.GEN `xs` lemma) \\ ASM_SIMP_TAC bool_ss []
    \\ Q.EXISTS_TAC `(a - 28w =+ (if u then 1w else 0w)) xs`
    \\ MATCH_MP_TAC lemma \\ ASM_SIMP_TAC bool_ss [])
  \\ FULL_SIMP_TAC bool_ss [APPEND]
  \\ `root_address_ok (a - 24w) 6 x /\ a - 28w IN x /\ a - 32w IN x /\ a + 4w IN x /\
      ALIGNED (a-32w) /\ ALIGNED (a-28w) /\ ALIGNED (a+4w)` by
   (REWRITE_TAC [GSYM (EVAL ``(SUC(SUC(SUC(SUC(SUC(SUC 0))))))``),root_address_ok_def]
    \\ FULL_SIMP_TAC bool_ss [ref_cheney_def,IN_INSERT]
    \\ FULL_SIMP_TAC std_ss [INSERT_SUBSET,word_arith_lemma1,word_arith_lemma2]
    \\ FULL_SIMP_TAC std_ss [word_arith_lemma3,word_arith_lemma4] \\ METIS_TAC [])
  \\ `!x1 x2 x3 x4 x5 x6 x7.
        ZIP ([x1; x2; x3; x4; x5; x6],[y1; y2; y3; y4; y5; y6]) ++ [(i,0w,F); (b+l,0w,F)] =
        ZIP ([x1; x2; x3; x4; x5; x6; i; b+l],[y1; y2; y3; y4; y5; y6; (0w,F); (0w,F)])` by
         SIMP_TAC std_ss [ZIP,APPEND]
  \\ Q.PAT_X_ASSUM `rs2 = ppppp` ASSUME_TAC
  \\ FULL_SIMP_TAC bool_ss []
  \\ STRIP_ASSUME_TAC
    ((UNDISCH_ALL o Q.INST [`f`|->`l+l+1`])
    (Q.INST [`r5n`|->`r53`,`r6n`|->`r63`,`r7n`|->`r73`,`r8n`|->`r83`,`xn`|->`x3'`]
    (Q.SPECL [`b`,`m`,`r4l`,`r4l + n2w (8 * l)`,`r7`,`r8`,`xs2`,`a - 24w`,`ys`,`j2`,`m2`]
    (Q.INST [`e`|->`b+l`,`j'`|->`b`,`w`|->`m`,`ww`|->`m`,`r`|->`{}`,`i`|->`b`,`r3`|->`ref_addr a b`,`r4n`|->`r43`,`r12n`|->`a3`,`xsn`|->`xs3`,`ii`|->`i`]
    (SIMP_RULE std_ss [APPEND,GSYM AND_IMP_INTRO,LENGTH,ADD1] (Q.SPECL [`[ii;e]`,`[y1;y2;y3;y4;y5;y6;(0w,F);(0w,F)]`] ref_cheney_move_roots6))))))
  \\ `ref_cheney_inv (b,b,j2,j2,b + l,l+l+1,m2,m2,m,RANGE (b,j2)) (a,r4l,r43,x,xs3,xs3)` by
   (REWRITE_TAC [ref_cheney_inv_def] \\ REPEAT STRIP_TAC THENL [
      FULL_SIMP_TAC bool_ss [ref_cheney_inv_def] \\ IMP_RES_TAC cheney_inv_setup
      \\ FULL_SIMP_TAC bool_ss [cheney_inv_def] \\ METIS_TAC [],
      FULL_SIMP_TAC bool_ss [ref_cheney_inv_def],
      MATCH_MP_TAC va_IMP \\ Q.EXISTS_TAC `l+l+1` \\ ASM_SIMP_TAC bool_ss []
      \\ Q.UNABBREV_TAC `b` \\ Cases_on `u` \\ REWRITE_TAC [] \\ DECIDE_TAC,
      FULL_SIMP_TAC bool_ss [ref_cheney_inv_def],
      FULL_SIMP_TAC bool_ss [ref_cheney_inv_def]])
  \\ `ref_cheney_inv (b,b,j2,j2,b + l,l + l + 1,m2,m2,m,RANGE (b,j2))
        (a,r4l,r43,x3',xs3,xs3)` by METIS_TAC []
  \\ (STRIP_ASSUME_TAC o
      UNDISCH_ALL o RW [GSYM AND_IMP_INTRO] o
      Q.SPECL [`b`,`b`,`j2`,`b+l`,`m2`,`m2`,`x`,`RANGE(b,j2)`,`r4l`,`r43`,`r53`,`r63`,`r73`,`r83`,`x3'`,`xs3`,`i3`,`m3`,`r34`,`r44`,`r54`,`r64`,`r74`,`r84`,`x4'`,`xs4`] o
      Q.INST [`xx`|->`m`,`ys`|->`xs3`,`f`|->`l+l+1`,`d`|->`x`])
      (INST_TYPE [``:'a``|->``:((bool[30] # bool) # bool[30] # bool)``] ref_cheney_loop_th)
  \\ Q.PAT_X_ASSUM `ref_cheney_inv ppppp (a,r34,r44,x3',xs4,xs3)` (STRIP_ASSUME_TAC o RW [ref_cheney_inv_def])
  \\ ONCE_REWRITE_TAC [EQ_SYM_EQ]
  \\ ASM_SIMP_TAC bool_ss [WORD_SUB_ADD,GSYM ALIGNED_def]
  \\ SIMP_TAC std_ss [def6,LET_DEF]
  \\ `?x1' x2' x3' x4' x5' x6'. ys = [x1'; x2'; x3'; x4'; x5'; x6']` by
   (Cases_on `ys`    \\ FULL_SIMP_TAC std_ss [LENGTH]
    \\ Cases_on `t`  \\ FULL_SIMP_TAC std_ss [LENGTH]
    \\ Cases_on `t'` \\ FULL_SIMP_TAC std_ss [LENGTH]
    \\ Cases_on `t`  \\ FULL_SIMP_TAC std_ss [LENGTH]
    \\ Cases_on `t'` \\ FULL_SIMP_TAC std_ss [LENGTH]
    \\ Cases_on `t`  \\ FULL_SIMP_TAC std_ss [LENGTH]
    \\ Cases_on `t'`  \\ FULL_SIMP_TAC std_ss [LENGTH,CONS_11,ADD1,GSYM ADD_ASSOC]
    \\ FULL_SIMP_TAC bool_ss [DECIDE ``~(n + 7 = 6)``])
  \\ FULL_SIMP_TAC bool_ss [CONS_11,APPEND]
  \\ `xs4 (a-28w) = xs2 (a-28w)` by METIS_TAC [ref_cheney_def]
  \\ `xs4 (a-32w) = xs2 (a-32w)` by METIS_TAC [ref_cheney_def]
  \\ Q.PAT_X_ASSUM ` !i. i <+ a - 24w ==> (xs2 i = xs3 i)` (ASSUME_TAC o GSYM)
  \\ `~(b = 0) /\ ~(b + l = 0)` by
    (Q.UNABBREV_TAC `b` \\ Cases_on `u` \\ FULL_SIMP_TAC std_ss [LET_DEF,ok_state_def] \\ DECIDE_TAC)
  \\ `(a + 4w <+ ref_addr a 1) /\ (xs3 (a+4w) = ref_addr a (b + l))` by FULL_SIMP_TAC (std_ss++WORD_ss) [roots_in_mem_def,ZIP,ref_field_def]
  \\ REWRITE_TAC [GSYM CONJ_ASSOC]
  \\ STRIP_TAC THEN1 METIS_TAC [roots_in_mem_carry_over]
  \\ REVERSE STRIP_TAC THENL [
    `(xs4 (a - 32w) = xs3 (a - 32w)) /\ (xs4 (a + 4w) = xs3 (a + 4w)) /\
     (xs4 (a - 28w) = xs3 (a - 28w))` by METIS_TAC [ref_cheney_def]
    \\ ASM_SIMP_TAC bool_ss []
    \\ Q.UNABBREV_TAC `xs2` \\ Q.UNABBREV_TAC `xs1` \\ Cases_on `u`
    \\ FULL_SIMP_TAC (std_ss++WORD_ss) [APPLY_UPDATE_THM,WORD_EQ_ADD_LCANCEL,n2w_11,
        RW [WORD_ADD_0] (Q.SPECL [`v`,`w`,`0w`] WORD_EQ_ADD_LCANCEL)],
    FULL_SIMP_TAC bool_ss [ref_cheney_def,CUT_def]
    \\ FULL_SIMP_TAC bool_ss [ref_cheney_def,GSYM CUT_def]
    \\ METIS_TAC [ref_mem_def]]);

val arm_alloc_aux_lemma = prove(
  ``ok_state (i,e,rs,l,u,m) ==>
    arm_coll_inv (a,x,xs) (i,e,rs,rs2,l,u,m) ==>
    (cheney_alloc_gc (i,e,rs,l,u,m) = (i',e',rs',l',u',m')) ==>
    (arm_alloc_aux (ref_addr a i,ref_addr a e,r5,r6,r7,r8,a,x,xs) =
                   (r3',r4',r5',r6',r7',r8',a',x',xs')) ==>
    arm_coll_inv (a,x,xs') (i,e',rs',rs2,l',u',m') /\ (a = a') /\ (l = l') /\
    (r3' = ref_addr a i') /\ (r4' = ref_addr a e') /\ (x = x') /\
    arm_alloc_aux_pre (ref_addr a i,ref_addr a e,r5,r6,r7,r8,a,x,xs)``,
  REWRITE_TAC [def8,cheney_alloc_gc_def]
  \\ STRIP_TAC \\ STRIP_TAC
  \\ `valid_address a i /\ valid_address a e /\ i <= e` by (Cases_on `u` \\
    FULL_SIMP_TAC bool_ss [ok_state_def,LET_DEF,arm_coll_inv_def,valid_address_def] \\ DECIDE_TAC)
  \\ `(ref_addr a i = ref_addr a e) = (i = e)` by METIS_TAC [ref_addr_NEQ]
  \\ `(i = e) = ~(i < e)` by DECIDE_TAC
  \\ Cases_on `i < e` \\ ASM_SIMP_TAC bool_ss []
  THEN1 (ONCE_REWRITE_TAC [EQ_SYM_EQ] \\ ASM_SIMP_TAC bool_ss [PAIR_EQ] \\ METIS_TAC [])
  \\ `?r3i r4i r5i r6i r7i r8i r9i xi xsi. arm_collect (r7,r8,a,x,xs) =
                         (r3i,r4i,r5i,r6i,r7i,r8i,r9i,xi,xsi)` by METIS_TAC [PAIR]
  \\ ASM_SIMP_TAC std_ss [LET_DEF] \\ STRIP_TAC
  \\ ONCE_REWRITE_TAC [EQ_SYM_EQ] \\ SIMP_TAC bool_ss [GSYM AND_IMP_INTRO]
  \\ REPEAT (MATCH_MP_TAC (METIS_PROVE [] ``P ==> (Q ==> P)``))
  \\ IMP_RES_TAC arm_collect_lemma
  \\ FULL_SIMP_TAC bool_ss []
  \\ METIS_TAC []);

val LO_IMP_ref_addr = prove(
  ``!b a. b <+ ref_addr a 1 /\ valid_address a i /\ ~(i = 0) ==>
          ~(ref_addr a i = b) /\ ~(ref_addr a i + 4w = b)``,
  Cases_word \\ Cases_word
  \\ ASM_SIMP_TAC (std_ss++SIZES_ss) [ref_addr_def,WORD_LO,w2n_n2w,valid_address_def,word_add_n2w,n2w_11]
  \\ REPEAT STRIP_TAC
  \\ `n' + 8 * i + 4 < 4294967296 /\ n' + 8 * i < 4294967296` by DECIDE_TAC
  \\ `n' + 8 < 4294967296` by DECIDE_TAC
  \\ FULL_SIMP_TAC std_ss [LESS_MOD] \\ DECIDE_TAC);

val roots_in_mem_UPDATE = prove(
  ``!p b. valid_address a i /\ ~(i = 0) /\ roots_in_mem p (a,b,xs) ==>
          roots_in_mem p (a,b,(ref_addr a i =+ y) xs)``,
  Induct \\ ASM_SIMP_TAC std_ss [roots_in_mem_def,APPLY_UPDATE_THM]
  \\ REPEAT STRIP_TAC \\ IMP_RES_TAC WORD_LOWER_NOT_EQ \\ IMP_RES_TAC LO_IMP_ref_addr
  \\ ASM_SIMP_TAC bool_ss []);

val roots_in_mem_UPDATE4 = prove(
  ``!p b. valid_address a i /\ ~(i = 0) /\ roots_in_mem p (a,b,xs) ==>
          roots_in_mem p (a,b,(ref_addr a i +4w  =+ y) xs)``,
  Induct \\ ASM_SIMP_TAC std_ss [roots_in_mem_def,APPLY_UPDATE_THM]
  \\ REPEAT STRIP_TAC \\ IMP_RES_TAC WORD_LOWER_NOT_EQ \\ IMP_RES_TAC LO_IMP_ref_addr
  \\ ASM_SIMP_TAC bool_ss []);

val arm_alloc_aux2_lemma = prove(
  ``ok_state (i,e,rs,l,u,m) /\ ~(i = e) ==>
    arm_coll_inv (a,x,xs) (q,e,rs,rs2,l,u,m) ==>
    (cheney_alloc_aux (i,e,rs,l,u,m) (HD rs2,HD (TL rs2)) = (i',e',rs',l',u',m')) ==>
    (arm_alloc_aux2 (ref_addr a i,ref_addr a e,a,x,xs) = (r3',r4',r8',r9',r10',x',xs')) ==>
    arm_coll_inv (a,x,xs') (i',e',rs',rs2,l',u',m') /\ (l = l') /\ (x = x') /\ (a = r10') /\
    arm_alloc_aux2_pre (ref_addr a i,ref_addr a e,a,x,xs)``,
  STRIP_TAC \\ REWRITE_TAC [def9,cheney_alloc_aux_def]
  \\ STRIP_TAC \\ ASM_SIMP_TAC std_ss []
  \\ IMP_RES_TAC arm_coll_inv_pre_lemma
  \\ `valid_address a i /\ valid_address a e /\ ~(i = 0) /\ ~(e = 0)` by
      (Cases_on `u` \\ FULL_SIMP_TAC std_ss [valid_address_def,
         arm_coll_inv_def,ok_state_def,LET_DEF] \\ DECIDE_TAC)
  \\ ASM_SIMP_TAC bool_ss [ref_addr_NEQ]
  \\ ONCE_REWRITE_TAC [EQ_SYM_EQ]
  \\ SIMP_TAC std_ss [LET_DEF,WORD_ADD_0,GSYM AND_IMP_INTRO]
  \\ REPEAT (MATCH_MP_TAC (METIS_PROVE [] ``P ==> (Q ==> P)``))
  \\ FULL_SIMP_TAC bool_ss [CONS_11,arm_coll_inv_def,APPEND,HD,TL]
  \\ Q.ABBREV_TAC `xs2 = (a - 24w =+ ref_addr a i) xs`
  \\ Q.ABBREV_TAC `xs1 = (((ref_addr a i + 4w =+ xs (a - 20w))
             ((ref_addr a i =+ xs (a - 24w)) xs2)))`
  \\ SIMP_TAC std_ss [word_arith_lemma1]
  \\ `ref_addr a i + 8w = ref_addr a (i+1)` by
      FULL_SIMP_TAC std_ss [ref_addr_def,MULT_CLAUSES,GSYM ADD1,
        GSYM WORD_ADD_ASSOC,word_add_n2w,AC ADD_ASSOC ADD_COMM]
  \\ ASM_SIMP_TAC std_ss []
  \\ `a <+ ref_addr a 1 /\ a - 24w <+ ref_addr a 1` by (FULL_SIMP_TAC std_ss [roots_in_mem_def,APPEND,word_arith_lemma1,word_arith_lemma2,ZIP]
    \\ FULL_SIMP_TAC std_ss [word_arith_lemma3,word_arith_lemma4,WORD_ADD_0])
  \\ `ref_cheney (m,l+l+1) (a,x,xs2,xs2)` by METIS_TAC [lemma]
  \\ `ref_cheney ((i =+ DATA (x1,x2,y1,y2)) m,l+l+1) (a,x,xs1,xs1)` by
     (FULL_SIMP_TAC std_ss [ref_cheney_def,APPLY_UPDATE_THM] \\ REPEAT STRIP_TAC
      \\ Cases_on `i' = i` \\ ASM_SIMP_TAC bool_ss [ref_mem_def,UPDATE_def] THENL [
          Q.UNABBREV_TAC `xs1`
          \\ FULL_SIMP_TAC std_ss [roots_in_mem_def,APPLY_UPDATE_THM,word_arith_lemma1,word_arith_lemma2,APPEND,ZIP]
          \\ FULL_SIMP_TAC std_ss [word_arith_lemma3,word_arith_lemma4,WORD_ADD_0]
          \\ SIMP_TAC (std_ss++WORD_ss) [RW [WORD_ADD_0] (Q.SPECL [`v`,`x`,`0w`] WORD_EQ_ADD_LCANCEL),
               RW [WORD_ADD_0] (Q.SPECL [`v`,`0w`] WORD_EQ_ADD_LCANCEL),n2w_11,WORD_EQ_ADD_LCANCEL],
          Q.UNABBREV_TAC `xs1` \\ Cases_on `m i'` \\ ASM_SIMP_TAC bool_ss [ref_mem_def]
          \\ `valid_address a i'` by METIS_TAC [va_IMP]
          THENL [ALL_TAC,Cases_on `p` \\ Cases_on `r` \\ Cases_on `r'`]
          \\ ASM_SIMP_TAC bool_ss [ref_addr_ADD_NEQ,ref_addr_NEQ,UPDATE_def,ref_mem_def,WORD_EQ_ADD_RCANCEL]
          \\ METIS_TAC [ref_mem_def]])
  \\ `ref_cheney ((i =+ DATA (x1,x2,y1,y2)) m,l+l+1)
      (a,x,(a =+ ref_addr a (i + 1)) xs1,(a =+ ref_addr a (i + 1)) xs1)` by METIS_TAC [lemma]
  \\ ASM_SIMP_TAC std_ss []
  \\ Q.ABBREV_TAC `xxx = ZIP ([i; x2; x3; x4; x5; x6],[y1; y2; y3; y4; y5; y6]) ++
       [(q,0w,F); (e,0w,F)]`
  \\ SIMP_TAC std_ss [GSYM CONJ_ASSOC]
  \\ `roots_in_mem xxx (a,a - 24w,xs2)` by
     (Q.UNABBREV_TAC `xxx` \\ Q.UNABBREV_TAC `xs2`
      \\ FULL_SIMP_TAC std_ss [roots_in_mem_def,APPLY_UPDATE_THM,word_arith_lemma1,word_arith_lemma2,APPEND,ZIP]
      \\ FULL_SIMP_TAC std_ss [word_arith_lemma3,word_arith_lemma4,WORD_ADD_0]
      \\ SIMP_TAC (std_ss++WORD_ss) [RW [WORD_ADD_0] (Q.SPECL [`v`,`0w`] WORD_EQ_ADD_LCANCEL),n2w_11]
      \\ SIMP_TAC (std_ss++WORD_ss) [RW [WORD_ADD_0] (Q.SPECL [`v`,`x`,`0w`] WORD_EQ_ADD_LCANCEL),
           RW [WORD_ADD_0] (Q.SPECL [`v`,`0w`] WORD_EQ_ADD_LCANCEL),n2w_11,WORD_EQ_ADD_LCANCEL]
      \\ `~(i = 0)` by (FULL_SIMP_TAC std_ss [ok_state_def,LET_DEF] \\ Cases_on `u` \\ DECIDE_TAC)
      \\ ASM_SIMP_TAC std_ss [ref_field_def])
  \\ `roots_in_mem xxx (a,a - 24w,xs1)` by
     (Q.UNABBREV_TAC `xxx` \\ Q.UNABBREV_TAC `xs1`
      \\ FULL_SIMP_TAC std_ss [roots_in_mem_def,APPLY_UPDATE_THM,word_arith_lemma1,word_arith_lemma2,APPEND,ZIP]
      \\ IMP_RES_TAC LO_IMP_ref_addr
      \\ FULL_SIMP_TAC std_ss [roots_in_mem_def,APPLY_UPDATE_THM,word_arith_lemma1,word_arith_lemma2,APPEND,ZIP]
      \\ FULL_SIMP_TAC std_ss [word_arith_lemma3,WORD_ADD_0]
      \\ FULL_SIMP_TAC std_ss [word_arith_lemma3,word_arith_lemma4,WORD_ADD_0,WORD_EQ_SUB_LADD]
      \\ FULL_SIMP_TAC std_ss [WORD_EQ_ADD_CANCEL]
      \\ SIMP_TAC (std_ss++SIZES_ss) [n2w_11])
  \\ SIMP_TAC std_ss [GSYM CONJ_ASSOC]
  \\ STRIP_TAC THEN1
    (Q.UNABBREV_TAC `xxx`
     \\ FULL_SIMP_TAC std_ss [roots_in_mem_def,APPLY_UPDATE_THM,word_arith_lemma1,word_arith_lemma2,APPEND,ZIP]
     \\ FULL_SIMP_TAC std_ss [WORD_EQ_SUB_RADD,WORD_EQ_SUB_LADD,word_arith_lemma3]
     \\ SIMP_TAC (std_ss++SIZES_ss) [n2w_11,WORD_EQ_ADD_CANCEL]
     \\ ASM_SIMP_TAC std_ss [ref_field_def])
  \\ NTAC 2 (STRIP_TAC THEN1
   (ASM_SIMP_TAC std_ss [word_arith_lemma1]
    \\ Q.UNABBREV_TAC `xs1` \\ Q.UNABBREV_TAC `xs2`
    \\ IMP_RES_TAC LO_IMP_ref_addr
    \\ SIMP_TAC bool_ss [UPDATE_def]
    \\ ASM_SIMP_TAC std_ss [word_arith_lemma1]
    \\ SIMP_TAC (std_ss++WORD_ss) [RW [WORD_ADD_0] (Q.SPECL [`v`,`0w`] WORD_EQ_ADD_LCANCEL),n2w_11]
    \\ SIMP_TAC (std_ss++WORD_ss) [RW [WORD_ADD_0] (Q.SPECL [`v`,`x`,`0w`] WORD_EQ_ADD_LCANCEL),
         RW [WORD_ADD_0] (Q.SPECL [`v`,`0w`] WORD_EQ_ADD_LCANCEL),n2w_11,WORD_EQ_ADD_LCANCEL]))
  \\ `i <= l+l+1` by (Cases_on `u` \\ FULL_SIMP_TAC bool_ss [ok_state_def,LET_DEF] \\ DECIDE_TAC)
  \\ IMP_RES_TAC ref_cheney_d
  \\ ONCE_REWRITE_TAC [EQ_SYM_EQ]
  \\ FULL_SIMP_TAC std_ss [ref_cheney_def,GSYM ALIGNED_def,INSERT_SUBSET,LENGTH,ALIGNED_ref_addr]
  \\ REPEAT STRIP_TAC \\ REWRITE_TAC [word_sub_def]
  \\ REPEAT (MATCH_MP_TAC ALIGNED_ADD) \\ ASM_SIMP_TAC bool_ss [] \\ REPEAT STRIP_TAC
  \\ REPEAT (MATCH_MP_TAC ALIGNED_ref_addr) \\ ASM_SIMP_TAC bool_ss [] \\ EVAL_TAC);

val not_full_heap_def = Define `
  not_full_heap (i,e,root,l,u,m) =
    ~(FST (cheney_alloc_gc (i,e,root,l,u,m)) =
      FST (SND (cheney_alloc_gc (i,e,root,l,u,m))))`;

val arm_alloc_lemma = prove(
  ``ok_state (i,e,rs,l,u,m) ==>
    not_full_heap (i,e,rs,l,u,m) ==>
    arm_coll_inv (a,x,xs) (i,e,rs,rs3,l,u,m) ==>
    (cheney_alloc (i,e,rs,l,u,m) (HD rs3,HD (TL rs3)) = (i',e',rs',l',u',m')) ==>
    (arm_alloc_mem (r5,r6,r7,r8,a,x,xs) = (r3',r4',r5',r6',r7',r8',a',x',xs')) ==>
    arm_coll_inv (a',x,xs') (i',e',rs',rs3,l',u',m') /\ (a' = a) /\ (l' = l) /\ (x = x') /\
    arm_alloc_mem_pre (r5,r6,r7,r8,a,x,xs)``,
  REWRITE_TAC [cheney_alloc_def,def10] \\ STRIP_TAC \\ STRIP_TAC \\ STRIP_TAC
  \\ `~(i = 0) /\ ~(e = 0)` by
         (Cases_on `u` \\ FULL_SIMP_TAC bool_ss [ok_state_def,LET_DEF] \\ DECIDE_TAC)
  \\ `(xs a = ref_addr a i) /\ (xs (a+4w) = ref_addr a e)` by
   (FULL_SIMP_TAC std_ss [arm_coll_inv_def,APPEND,roots_in_mem_def,ZIP]
    \\ FULL_SIMP_TAC std_ss [arm_coll_inv_def,APPEND,roots_in_mem_def,ZIP]
    \\ FULL_SIMP_TAC std_ss [roots_in_mem_def,APPLY_UPDATE_THM,word_arith_lemma1,word_arith_lemma2,APPEND]
    \\ FULL_SIMP_TAC std_ss [word_arith_lemma3,word_arith_lemma4,WORD_ADD_0]
    \\ SIMP_TAC (std_ss++WORD_ss) [RW [WORD_ADD_0] (Q.SPECL [`v`,`0w`] WORD_EQ_ADD_LCANCEL),n2w_11]
    \\ ASM_SIMP_TAC std_ss [ref_field_def])
  \\ `?r3i r4i r5i r6i r7i r8i r9i xi xsi.
        arm_alloc_aux (ref_addr a i,ref_addr a e,r5,r6,r7,r8,a,x,xs) =
                      (r3i,r4i,r5i,r6i,r7i,r8i,r9i,xi,xsi)` by METIS_TAC [PAIR]
  \\ `?r3j r4j r7j r8j r9j xj xsj.
        arm_alloc_aux2 (r3i,r4i,r9i,xi,xsi) = (r3j,r4j,r7j,r8j,r9j,xj,xsj)` by METIS_TAC [PAIR]
  \\ `?i2 e2 rs2 l2 u2 m2. cheney_alloc_gc (i,e,rs,l,u,m) = (i2,e2,rs2,l2,u2,m2)` by METIS_TAC [PAIR]
  \\ ASM_SIMP_TAC std_ss [LET_DEF] \\ STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [not_full_heap_def]
  \\ ONCE_REWRITE_TAC [EQ_SYM_EQ] \\ ASM_SIMP_TAC std_ss [GSYM CONJ_ASSOC]
  \\ ONCE_REWRITE_TAC [EQ_SYM_EQ] \\ ASM_SIMP_TAC std_ss [GSYM ALIGNED_def]
  \\ IMP_RES_TAC arm_alloc_aux_lemma
  \\ `ok_state (i2,e2,rs2,l2,u2,m2)` by METIS_TAC [cheney_collector_spec,cheney_alloc_gc_def]
  \\ IMP_RES_TAC arm_coll_inv_pre_lemma
  \\ ONCE_REWRITE_TAC [EQ_SYM_EQ] \\ ASM_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC std_ss [INSERT_SUBSET,NOT_IN_EMPTY,IN_INSERT,EMPTY_SUBSET]
  \\ ONCE_REWRITE_TAC [EQ_SYM_EQ] \\ STRIP_TAC \\ FULL_SIMP_TAC bool_ss []
  \\ REPEAT (Q.PAT_X_ASSUM `~(i = 0)` ((K ALL_TAC)))
  \\ IMP_RES_TAC arm_alloc_aux2_lemma \\ ASM_SIMP_TAC std_ss []
  \\ REVERSE (REPEAT STRIP_TAC) \\ METIS_TAC []);

val field_list_def = Define `
  (field_list [] (a,r12,m) = T) /\
  (field_list (x::xs) (a,r12,m) = (m r12 = ref_field a x) /\ field_list xs (a,r12 + 4w,m))`;

val roots_in_mem_IMP_addr_list = prove(
  ``!p a b xs. roots_in_mem p (a,b,xs) ==> field_list p (a,b,xs)``,
  Induct \\ ASM_SIMP_TAC std_ss [field_list_def,roots_in_mem_def]);

val ch_mem_def = Define `
  ch_mem (i,e,rs,rs',l,u,m) (a,x,xs) =
    ?x1 x2 x3 x4 x5 x6:num y1 y2 y3 y4 y5 y6:(word30 # bool).
      32 <= w2n a /\ w2n a + 2 * 8 * l + 20 < 2**32 /\
      ok_state(i,e,rs,l,u,m) /\
      field_list (ZIP (rs,rs') ++ [(i,(0w,F));(e,(0w,F))]) (a,a-24w,xs) /\
      (rs = [x1;x2;x3;x4;x5;x6]) /\ (rs' = [y1;y2;y3;y4;y5;y6]) /\
      ref_cheney (m,l+l+1) (a,x,xs,xs) /\
      (xs (a-28w) = if u then 0w else 1w) /\
      (xs (a-32w) = n2w (8 * l)) /\ ~(l = 0)`;

val ch_word_def = Define `
  ch_word (i,e,rs,rs',l,u,m) (v1,v2,v3,v4,v5,v6,a,x,xs) =
    ?x1 x2 x3 x4 x5 x6:num y1 y2 y3 y4 y5 y6:(word30 # bool).
      32 <= w2n a /\ w2n a + 2 * 8 * l + 20 < 2**32 /\
      ok_state(i,e,rs,l,u,m) /\ ref_cheney (m,l+l+1) (a,x,xs,xs) /\
      (rs = [x1;x2;x3;x4;x5;x6]) /\ (rs' = [y1;y2;y3;y4;y5;y6]) /\
      (v1 = ref_field a (x1,y1)) /\ (v2 = ref_field a (x2,y2)) /\ (v3 = ref_field a (x3,y3)) /\
      (v4 = ref_field a (x4,y4)) /\ (v5 = ref_field a (x5,y5)) /\ (v6 = ref_field a (x6,y6)) /\
      (xs a = ref_addr a i) /\ (xs (a+4w) = ref_addr a e) /\
      (xs (a-28w) = if u then 0w else 1w) /\ (xs (a-32w) = n2w (8 * l)) /\ ~(l = 0)`;

val ch_mem_lemma1 = prove(
  ``!a. n < 2**32 /\ k < 2**32 /\ n <= w2n a /\
        w2n a + k < 2**32 /\ ~(a = 0w) /\ ~(k = 0) ==> (a:word32 - n2w n <+ a + n2w k)``,
  Cases_word
  \\ ASM_SIMP_TAC (std_ss++SIZES_ss) [word_arith_lemma2,WORD_LO,WORD_LS,w2n_n2w,
      LESS_MOD,GSYM AND_IMP_INTRO,word_add_n2w,DECIDE ``n <= n' = ~(n' < n:num)``,n2w_11]
  \\ REPEAT STRIP_TAC \\ `(n' - n) < 4294967296` by DECIDE_TAC
  \\ ASM_SIMP_TAC bool_ss [LESS_MOD] \\ DECIDE_TAC);

val ch_mem_lemma2 = prove(
  ``!a. n < 2**32 /\ k < 2**32 /\ n <= w2n a /\ k < w2n a /\
        ~(a = 0w) /\ (k < n) ==> (a:word32 - n2w n <+ a - n2w k)``,
  Cases_word
  \\ FULL_SIMP_TAC (std_ss++SIZES_ss) [word_arith_lemma2,WORD_LO,WORD_LS,w2n_n2w,
      LESS_MOD,GSYM AND_IMP_INTRO,word_add_n2w,DECIDE ``n < n' ==> ~(n' < n:num)``,n2w_11,
      DECIDE ``n <= n' ==> ~(n' < n:num)``]
  \\ REPEAT STRIP_TAC
  \\ `(n' - n) < 4294967296` by DECIDE_TAC
  \\ `(n' - k) < 4294967296` by DECIDE_TAC
  \\ ASM_SIMP_TAC bool_ss [LESS_MOD] \\ DECIDE_TAC);

val ch_mem_lemma3 = prove(
  ``!a. n < 2**32 /\ k < 2**32 /\ w2n a + n < 2**32 /\ w2n a + k < 2**32 /\
        ~(a = 0w) /\ ~(k = 0) /\ (n < k) ==> ((a:word32) + n2w n <+ a + n2w k)``,
  Cases_word
  \\ FULL_SIMP_TAC (std_ss++SIZES_ss) [word_arith_lemma2,WORD_LO,WORD_LS,w2n_n2w,
      LESS_MOD,GSYM AND_IMP_INTRO,word_add_n2w,DECIDE ``n < n' ==> ~(n' < n:num)``,n2w_11,
      DECIDE ``n <= n' ==> ~(n' < n:num)``]
  \\ REPEAT STRIP_TAC \\ DECIDE_TAC);

val ch_mem_lemma4 = RW [WORD_ADD_0] (Q.INST [`n`|->`0`] ch_mem_lemma3)

val ch_mem_lemma5 = prove(
  ``!a. n < 2**32 /\ n <= w2n a /\ ~(a = 0w) /\ ~(n = 0) ==> (a:word32 - n2w n <+ a)``,
  Cases_word
  \\ FULL_SIMP_TAC (std_ss++SIZES_ss) [word_arith_lemma2,WORD_LO,WORD_LS,w2n_n2w,
      LESS_MOD,GSYM AND_IMP_INTRO,word_add_n2w,DECIDE ``n <= n' = ~(n' < n:num)``,n2w_11]
  \\ REPEAT STRIP_TAC \\ `(n' - n) < 4294967296` by DECIDE_TAC
  \\ ASM_SIMP_TAC bool_ss [LESS_MOD] \\ DECIDE_TAC);

val ch_mem_IMP_arm_coll_inv = prove(
  ``ch_mem (i,e,rs,rs',l,u,m) (a,x,xs) ==>
    ok_state (i,e,rs,l,u,m) /\ arm_coll_inv (a,x,xs) (i,e,rs,rs',l,u,m)``,
  REWRITE_TAC [ch_mem_def,arm_coll_inv_def] \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [CONS_11,APPEND,roots_in_mem_def,field_list_def,valid_address_def,ZIP]
  \\ FULL_SIMP_TAC std_ss [word_arith_lemma1,word_arith_lemma2,APPEND]
  \\ FULL_SIMP_TAC std_ss [word_arith_lemma3,word_arith_lemma4,WORD_ADD_0]
  \\ FULL_SIMP_TAC bool_ss [GSYM TIMES2]
  \\ FULL_SIMP_TAC bool_ss [GSYM ADD_ASSOC,LEFT_ADD_DISTRIB,MULT_ASSOC]
  \\ FULL_SIMP_TAC std_ss [ref_addr_def]
  \\ `~(a = 0w)` by (STRIP_TAC \\ FULL_SIMP_TAC (std_ss++WORD_ss) [])
  \\ REPEAT STRIP_TAC
  \\ REPEAT (MATCH_MP_TAC ch_mem_lemma1 \\ ASM_SIMP_TAC std_ss [] \\ DECIDE_TAC)
  \\ REPEAT (MATCH_MP_TAC ch_mem_lemma2 \\ ASM_SIMP_TAC std_ss [] \\ DECIDE_TAC)
  \\ REPEAT (MATCH_MP_TAC ch_mem_lemma3 \\ ASM_SIMP_TAC std_ss [] \\ DECIDE_TAC)
  \\ REPEAT (MATCH_MP_TAC ch_mem_lemma4 \\ ASM_SIMP_TAC std_ss [] \\ DECIDE_TAC)
  \\ REPEAT (MATCH_MP_TAC ch_mem_lemma5 \\ ASM_SIMP_TAC std_ss [] \\ DECIDE_TAC)
  \\ DECIDE_TAC);

val ch_mem_cheney_alloc_lemma = prove(
  ``ch_mem (i,e,rs,rs2,l,u,m) (a,x,xs) ==>
    not_full_heap (i,e,rs,l,u,m) ==>
    (cheney_alloc (i,e,rs,l,u,m) (HD rs2, HD (TL rs2)) = (i',e',rs',l',u',m')) ==>
    (arm_alloc_mem (r5,r6,r7,r8,a,x,xs) = (r3',r4',r5',r6',r7',r8',a',x',xs')) ==>
    ch_mem (i',e',rs',rs2,l',u',m') (a',x,xs') /\ (a = a') /\ (l = l') /\ (x = x') /\
    arm_alloc_mem_pre (r5,r6,r7,r8,a,x,xs) /\ arm_coll_inv (a,x,xs) (i,e,rs,rs2,l,u,m)``,
  NTAC 4 STRIP_TAC \\ IMP_RES_TAC ch_mem_IMP_arm_coll_inv
  \\ IMP_RES_TAC arm_alloc_lemma
  \\ FULL_SIMP_TAC bool_ss [ch_mem_def,APPEND,ZIP]
  \\ `ok_state (i',e',rs',l',u',m')` by METIS_TAC [cheney_alloc_ok]
  \\ FULL_SIMP_TAC std_ss [arm_coll_inv_def,CONS_11,ZIP,APPEND]
  \\ Q.PAT_X_ASSUM `rs' = xxxxx` (fn th => FULL_SIMP_TAC std_ss [th])
  \\ Q.PAT_X_ASSUM `rs2 = xxxxx` (fn th => FULL_SIMP_TAC std_ss [th])
  \\ FULL_SIMP_TAC bool_ss [APPEND,roots_in_mem_def,field_list_def,ZIP,CONS_11,HD]
  \\ Q.PAT_X_ASSUM `ok_state (i',e',[x1''; x2''; x3''; x4''; x5''; x6''],l',u',m')` MP_TAC
  \\ ASM_SIMP_TAC std_ss []);

val ch_word_alloc = prove(
  ``ch_word (i,e,rs,rs2,l,u,m) (v1,v2,v3,v4,v5,v6,a,x,xs) ==>
    not_full_heap (i,e,rs,l,u,m) ==>
    (cheney_alloc (i,e,rs,l,u,m) (HD rs2, HD (TL rs2)) = (i',e',rs',l',u',m')) ==>
    (arm_alloc (v1,v2,v3,v4,v5,v6,a,x,xs) = (w1,w2,w3,w4,w5,w6,a',x',xs')) ==>
    ch_word (i',e',rs',rs2,l',u',m') (w1,w2,w3,w4,w5,w6,a',x',xs') /\ (a = a') /\ (l = l') /\ (x = x') /\
    arm_alloc_pre (v1,v2,v3,v4,v5,v6,a,x,xs)``,
  SIMP_TAC std_ss [def11,LET_DEF]
  \\ Q.ABBREV_TAC `xs1 = (a - 4w =+ v6)
      ((a - 8w =+ v5) ((a - 12w =+ v4) ((a - 16w =+ v3)
      ((a - 20w =+ v2) ((a - 24w =+ v1) (xs))))))`
  \\ `?r3i r4i r5i r6i r7i r8i r9i xi xsi.
        arm_alloc_mem (v3,v4,v5,v6,a,x,xs1) = (r3i,r4i,r5i,r6i,r7i,r8i,r9i,xi,xsi)` by METIS_TAC [PAIR]
  \\ ASM_SIMP_TAC std_ss [LET_DEF] \\ STRIP_TAC \\ STRIP_TAC \\ STRIP_TAC
  \\ REWRITE_TAC [GSYM ALIGNED_def]
  \\ ONCE_REWRITE_TAC [EQ_SYM_EQ] \\ ASM_SIMP_TAC std_ss []
  \\ MATCH_MP_TAC (METIS_PROVE [] ``Q ==> (P ==> Q)``)
  \\ sg `ch_mem (i,e,rs,rs2,l,u,m) (a,x,xs1)` THENL [
    FULL_SIMP_TAC bool_ss [ch_mem_def,ch_word_def,CONS_11]
    \\ `ref_cheney (m,l+l+1) (a,x,xs1,xs1)` by (Q.UNABBREV_TAC `xs1`
        \\ Cases_on `a = 0w` THEN1 FULL_SIMP_TAC (std_ss++WORD_ss) [w2n_n2w]
        \\ REPEAT (MATCH_MP_TAC (Q.INST [`xs`|->`xs1`] lemma)
          \\ REVERSE STRIP_TAC THEN1
            (SIMP_TAC std_ss [ref_addr_def] \\ MATCH_MP_TAC ch_mem_lemma1
             \\ ASM_SIMP_TAC bool_ss [] \\ DECIDE_TAC))
        \\ METIS_TAC [])
    \\ ASM_SIMP_TAC bool_ss []
    \\ ASM_SIMP_TAC std_ss [field_list_def,ZIP,APPEND,word_arith_lemma1,word_arith_lemma2]
    \\ ASM_SIMP_TAC std_ss [field_list_def,ZIP,APPEND,word_arith_lemma3,word_arith_lemma4]
    \\ REPEAT STRIP_TAC \\ Q.UNABBREV_TAC `xs1`
    \\ ASM_SIMP_TAC (std_ss++WORD_ss) [APPLY_UPDATE_THM,WORD_EQ_ADD_LCANCEL,n2w_11,
         RW [WORD_ADD_0] (Q.SPECL [`v`,`x`,`0w`] WORD_EQ_ADD_LCANCEL),
         RW [WORD_ADD_0] (Q.SPECL [`v`,`0w`] WORD_EQ_ADD_LCANCEL)]
    \\ `~(i = 0) /\ ~(e = 0)` by
          (Cases_on `u` \\ FULL_SIMP_TAC bool_ss [ok_state_def,LET_DEF] \\ DECIDE_TAC)
    \\ ASM_SIMP_TAC bool_ss [ref_field_def],
    IMP_RES_TAC ch_mem_cheney_alloc_lemma
    \\ Q.PAT_X_ASSUM `ch_mem (i,e,rs,rs2,l,u,m) (a,x,xs1)` (K ALL_TAC)
    \\ FULL_SIMP_TAC bool_ss [APPEND,ZIP,ch_word_def,ch_mem_def,field_list_def,CONS_11]
    \\ FULL_SIMP_TAC bool_ss [APPEND,ZIP,ch_word_def,ch_mem_def,field_list_def,CONS_11]
    \\ FULL_SIMP_TAC std_ss [field_list_def,ZIP,APPEND,word_arith_lemma1,word_arith_lemma2]
    \\ FULL_SIMP_TAC std_ss [field_list_def,ZIP,APPEND,word_arith_lemma3,word_arith_lemma4]
    \\ IMP_RES_TAC arm_coll_inv_pre_lemma
    \\ FULL_SIMP_TAC std_ss [WORD_ADD_0,LENGTH,IN_INSERT,NOT_IN_EMPTY,INSERT_SUBSET,ALIGNED_def]
    \\ `~(i' = 0) /\ ~(e' = 0)` by
          (Cases_on `u'` \\ FULL_SIMP_TAC bool_ss [ok_state_def,LET_DEF] \\ DECIDE_TAC)
    \\ ASM_SIMP_TAC bool_ss [ref_field_def]
    \\ METIS_TAC []]);

val ch_arm_def = Define `
  ch_arm (r,h,l) c =
    ?i e rs l' u m. ch_inv (MAP FST r,h,l) (i,e,rs,l',u,m) /\ ch_word (i,e,rs,MAP SND r,l',u,m) c`;

val ch_arm_alloc = store_thm("ch_arm_alloc",
  ``(arm_alloc (v1,v2,v3,v4,v5,v6,a,x,xs) = (w1,w2,w3,w4,w5,w6,a',x',xs')) ==>
    CARD (reachables (MAP FST (t1::t2::ts)) (ch_set h)) < l ==>
    ch_arm (t1::t2::ts,h,l) (v1,v2,v3,v4,v5,v6,a,x,xs) ==>
    ch_arm ((fresh h,SND t1)::t2::ts,h |+ (fresh h,FST t1,FST t2,SND t1, SND t2),l) (w1,w2,w3,w4,w5,w6,a',x,xs') /\
    (a' = a) /\ (x' = x) /\ arm_alloc_pre (v1,v2,v3,v4,v5,v6,a,x,xs)``,
  REWRITE_TAC [ch_arm_def] \\ STRIP_TAC \\ STRIP_TAC \\ STRIP_TAC
  \\ `?i' e' rs' l'' u' m'. cheney_alloc (i,e,rs,l,u,m) (SND t1, SND t2) = (i',e',rs',l'',u',m')` by METIS_TAC [PAIR]
  \\ `l' = l` by METIS_TAC [ch_inv_def] \\ FULL_SIMP_TAC bool_ss []
  \\ FULL_SIMP_TAC bool_ss [MAP,FST,SND]
  \\ `not_full_heap (i,e,rs,l,u,m)` by
   (`?i5 e5 c5 l5 u5 m5. cheney_alloc_gc (i,e,rs,l,u,m) = (i5,e5,c5,l5,u5,m5)` by METIS_TAC [PAIR]
    \\ IMP_RES_TAC cheney_alloc_gc_spec
    \\ FULL_SIMP_TAC std_ss [not_full_heap_def] \\ DECIDE_TAC)
  \\ IMP_RES_TAC (REWRITE_RULE [MAP,HD,TL]
       (Q.INST [`rs2`|->`MAP SND ((t1:(num#word30#bool))::t2::ts)`] ch_word_alloc))
  \\ RES_TAC \\ ASM_SIMP_TAC bool_ss []
  \\ Q.EXISTS_TAC `i'` \\ Q.EXISTS_TAC `e'` \\ Q.EXISTS_TAC `rs'` \\ Q.EXISTS_TAC `l''`
  \\ Q.EXISTS_TAC `u'` \\ Q.EXISTS_TAC `m'` \\ ASM_SIMP_TAC bool_ss [cheney_alloc_spec,FST]
  \\ MATCH_MP_TAC (GEN_ALL (RW [AND_IMP_INTRO] cheney_alloc_spec))
  \\ FULL_SIMP_TAC bool_ss [] \\ METIS_TAC []);


(* prove tree like representation *)

val _ = Hol_datatype `XExp = XDot of XExp => XExp | XVal of word30 | XSym of word30`;
val XExp_11 = fetch "-" "XExp_11";
val XExp_distinct = fetch "-" "XExp_distinct";

val word_tree_def = Define `
  (word_tree (XVal w) (a,m) d = (a = ADDR32 w + 2w)) /\
  (word_tree (XSym w) (a,m) d = (a = ADDR32 w + 3w)) /\
  (word_tree (XDot x y) (a,m) d = a IN d /\ ALIGNED a /\
     word_tree x (m a,m) d /\ word_tree y (m (a + 4w),m) d)`;

val ch_active_set_def = Define `
  ch_active_set (a:word32,i,e) = { a + 8w * n2w j | i <= j /\ j < e }`;

val ok_data_def = Define `
  ok_data w d = if ALIGNED w then w IN d else ~(ALIGNED (w - 1w))`;

val ch_tree_def = Define `
  ch_tree (t1,t2,t3,t4,t5,t6,l) (w1,w2,w3,w4,w5,w6,a,dm,m,b,k) =
    ?i u.
      let v = (if u then 1 + l else 1) in
      let d = ch_active_set (a,v,i) in
        (b = a + n2w (8 * v)) /\ (k = i - v) /\
        32 <= w2n a /\ w2n a + 2 * 8 * l + 20 < 2 ** 32 /\ l <> 0 /\
        (m a = a + n2w (8 * i)) /\ ALIGNED a /\ v <= i /\ i <= v + l /\
        (m (a + 0x4w) = a + n2w (8 * (v + l))) /\
        (m (a - 0x1Cw) = (if u then 0x0w else 0x1w)) /\
        (m (a - 0x20w) = n2w (8 * l)) /\
        (dm = ref_set a (l + l + 1)) /\
        word_tree t1 (w1,m) d /\
        word_tree t2 (w2,m) d /\
        word_tree t3 (w3,m) d /\
        word_tree t4 (w4,m) d /\
        word_tree t5 (w5,m) d /\
        word_tree t6 (w6,m) d /\
        !w. w IN d ==> ok_data (m w) d /\ ok_data (m (w + 4w)) d`;

val heap_el_def = Define `
  heap_el a w =
    if ALIGNED w then (w2n (w - a) DIV 8, (0w, F)) else
      (0, (ADDR30 w, ALIGNED (w - 3w)))`;

val build_heap_def = Define `
  (build_heap (0,i,a,m) = FEMPTY) /\
  (build_heap (SUC n,i,a,m) =
     let (x1,x2) = heap_el a (m i) in
     let (y1,y2) = heap_el a (m (i + 4w)) in
       build_heap (n,i + 8w,a,m) |+ (w2n (i - a) DIV 8,x1,y1,x2,y2))`;

val build_map_def = Define `
  (build_map (0,i,a,m) = \x. EMP) /\
  (build_map (SUC n,i,a,m) =
     let (x1,x2) = heap_el a (m i) in
     let (y1,y2) = heap_el a (m (i + 4w)) in
       ((w2n (i - a) DIV 8) =+ DATA (x1,y1,(x2,y2)))
       (build_map (n,i + 8w,a,m)))`;

val abstract_build_heap = prove(
  ``!k a b m.
      abstract (I,build_map (k,b,a,m)) =
      ch_set (build_heap (k,b,a,m))``,
  Induct THENL [
     SIMP_TAC std_ss [abstract_def, ch_set_def, build_heap_def,
       build_map_def, heap_type_distinct, ch_set_def]
     \\ SIMP_TAC std_ss [EXTENSION,GSPECIFICATION, EXISTS_PROD]
     \\ SIMP_TAC std_ss [FORALL_PROD,IN_DEF,ch_set_def, FDOM_FEMPTY,
          EMPTY_DEF],
     FULL_SIMP_TAC std_ss [abstract_def, ch_set_def, build_heap_def,
       build_map_def, heap_type_distinct, ch_set_def]
     \\ REPEAT STRIP_TAC
     \\ Cases_on `heap_el a (m b)`
     \\ Cases_on `heap_el a (m (b + 0x4w))`
     \\ SIMP_TAC std_ss [LET_DEF]
     \\ FULL_SIMP_TAC std_ss [EXTENSION,GSPECIFICATION, EXISTS_PROD]
     \\ FULL_SIMP_TAC std_ss [FORALL_PROD,IN_DEF,FDOM_FEMPTY,EMPTY_DEF]
     \\ FULL_SIMP_TAC std_ss [ch_set_def,FDOM_FUPDATE,IN_INSERT,
          FAPPLY_FUPDATE_THM,APPLY_UPDATE_THM]
     \\ REPEAT STRIP_TAC
     \\ Cases_on `p_1 = w2n (b - a) DIV 8`
     \\ ASM_SIMP_TAC std_ss [heap_type_11]])

val FDOM_build_heap = prove(
  ``!k a v m. 8 * (v + k) < 2 ** 32 ==>
              (FDOM (build_heap (k,a + n2w (8 * v),a,m)) = RANGE (v,v + k))``,
  Induct
  \\ REWRITE_TAC [build_heap_def,FDOM_FEMPTY,NOT_IN_EMPTY,EXTENSION]
  THEN1 (SIMP_TAC std_ss [IN_DEF,RANGE_def] \\ DECIDE_TAC)
  \\ REPEAT STRIP_TAC
  \\ Cases_on `heap_el a (m (a + n2w (8 * v)))`
  \\ Cases_on `heap_el a (m ((a + n2w (8 * v)) + 0x4w))`
  \\ SIMP_TAC std_ss [LET_DEF,FDOM_FUPDATE,IN_INSERT,WORD_ADD_SUB2]
  \\ FULL_SIMP_TAC (std_ss++SIZES_ss) [w2n_n2w]
  \\ `8 * v < 4294967296` by DECIDE_TAC
  \\ FULL_SIMP_TAC (std_ss++SIZES_ss) [w2n_n2w]
  \\ ONCE_REWRITE_TAC [MULT_COMM]
  \\ SIMP_TAC std_ss [MULT_DIV]
  \\ Cases_on `x = v` \\ ASM_SIMP_TAC std_ss []
  THEN1 SIMP_TAC std_ss [IN_DEF,RANGE_def]
  \\ REWRITE_TAC [GSYM WORD_ADD_ASSOC,word_add_n2w,GSYM MULT]
  \\ `8 * (SUC v + k) < 4294967296` by DECIDE_TAC
  \\ RES_TAC \\ FULL_SIMP_TAC std_ss [AC MULT_ASSOC MULT_COMM]
  \\ SIMP_TAC std_ss [IN_DEF,RANGE_def] \\ DECIDE_TAC);

val IN_ch_active_set = prove(
  ``v1 IN ch_active_set (a,v,i) /\ 8 * i < 2 ** 32 ==>
    w2n (v1 - a) DIV 8 IN RANGE (v,i)``,
  SIMP_TAC std_ss [ch_active_set_def,GSPECIFICATION]
  \\ STRIP_TAC
  \\ ASM_SIMP_TAC std_ss [WORD_ADD_SUB2,word_mul_n2w]
  \\ `8 * j < 4294967296` by DECIDE_TAC
  \\ ASM_SIMP_TAC (std_ss++SIZES_ss) [w2n_n2w]
  \\ ONCE_REWRITE_TAC [MULT_COMM]
  \\ SIMP_TAC std_ss [MULT_DIV,IN_DEF,RANGE_def]
  \\ DECIDE_TAC);

val FEVERY_FUPDATE_IMP = prove(
  ``!f P x y. P (x,y) /\ FEVERY P f ==> FEVERY P (f |+ (x,y))``,
  recInduct fmap_INDUCT
  \\ SIMP_TAC std_ss [FEVERY_DEF,FDOM_FUPDATE,IN_INSERT,
       FDOM_FEMPTY,NOT_IN_EMPTY, FAPPLY_FUPDATE_THM]
  \\ METIS_TAC []);

val build_map_EMP = prove(
  ``!k v j. 8 * (v + k) < 2 ** 32 /\ j NOTIN RANGE (v,v + k) ==>
            (build_map (k,a + n2w (8 * v),a,m) j = EMP)``,
  Induct \\ REWRITE_TAC [build_map_def]
  \\ REPEAT STRIP_TAC
  \\ Cases_on `heap_el a (m (a + n2w (8 * v)))`
  \\ Cases_on `heap_el a (m ((a + n2w (8 * v)) + 0x4w))`
  \\ SIMP_TAC std_ss [LET_DEF,FDOM_FUPDATE,IN_INSERT,WORD_ADD_SUB2]
  \\ `8 * v < 2**32` by DECIDE_TAC
  \\ FULL_SIMP_TAC (std_ss++SIZES_ss) [w2n_n2w]
  \\ ONCE_REWRITE_TAC [MULT_COMM]
  \\ SIMP_TAC std_ss [MULT_DIV,APPLY_UPDATE_THM]
  \\ Cases_on `v = j`
  THEN1 (FULL_SIMP_TAC std_ss [IN_DEF,RANGE_def] \\ DECIDE_TAC)
  \\ ASM_SIMP_TAC std_ss []
  \\ SIMP_TAC std_ss [GSYM WORD_ADD_ASSOC,word_add_n2w,GSYM MULT]
  \\ ONCE_REWRITE_TAC [MULT_COMM]
  \\ Q.PAT_X_ASSUM `!v. bbb` MATCH_MP_TAC
  \\ FULL_SIMP_TAC std_ss [IN_DEF,RANGE_def,MULT_CLAUSES]
  \\ DECIDE_TAC);

val build_map_DATA = prove(
  ``!k i a m j v.
      8 * (v + k) < 2 ** 32 /\ j IN RANGE (v,v + k) ==>
      (build_map (k,a + n2w (8 * v),a,m) j =
        let (x1,x2) = heap_el a (m (a + n2w (8 * j))) in
        let (y1,y2) = heap_el a (m (a + n2w (8 * j) + 0x4w)) in
          DATA (x1,y1,x2,y2))``,
  Induct \\ REWRITE_TAC [build_map_def]
  \\ REPEAT STRIP_TAC
  THEN1 (FULL_SIMP_TAC std_ss [IN_DEF,RANGE_def] \\ `F` by DECIDE_TAC)
  \\ Cases_on `heap_el a (m (a + n2w (8 * v)))`
  \\ Cases_on `heap_el a (m (a + n2w (8 * v) + 4w))`
  \\ FULL_SIMP_TAC std_ss [LET_DEF,heap_type_distinct]
  \\ `8 * v < 4294967296` by DECIDE_TAC
  \\ ASM_SIMP_TAC (std_ss++SIZES_ss) [w2n_n2w,WORD_ADD_SUB2]
  \\ Cases_on `v = j`
  \\ FULL_SIMP_TAC std_ss [RW1 [MULT_COMM] MULT_DIV,APPLY_UPDATE_THM]
  \\ REWRITE_TAC [GSYM WORD_ADD_ASSOC,word_add_n2w, RW1 [MULT_COMM] (GSYM MULT)]
  \\ REWRITE_TAC [WORD_ADD_ASSOC,GSYM word_add_n2w]
  \\ Q.PAT_X_ASSUM `!bb. bbb` MATCH_MP_TAC
  \\ FULL_SIMP_TAC std_ss [IN_DEF,RANGE_def] \\ DECIDE_TAC);

val build_heap_DATA = prove(
  ``!k i a m j v.
      8 * (v + k) < 2 ** 32 /\ j IN RANGE (v,v + k) ==>
      j IN FDOM (build_heap (k,a + n2w (8 * v),a,m)) /\
      (build_heap (k,a + n2w (8 * v),a,m) ' j =
        let (x1,x2) = heap_el a (m (a + n2w (8 * j))) in
        let (y1,y2) = heap_el a (m (a + n2w (8 * j) + 0x4w)) in
          (x1,y1,x2,y2))``,
  Induct \\ REWRITE_TAC [build_heap_def]
  THEN1 (REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [IN_DEF,RANGE_def] \\ `F` by DECIDE_TAC)
  \\ NTAC 5 STRIP_TAC
  \\ Cases_on `heap_el a (m (a + n2w (8 * v)))`
  \\ Cases_on `heap_el a (m (a + n2w (8 * v) + 4w))`
  \\ FULL_SIMP_TAC std_ss [LET_DEF,heap_type_distinct]
  \\ `8 * v < 4294967296` by DECIDE_TAC
  \\ ASM_SIMP_TAC (std_ss++SIZES_ss) [w2n_n2w,WORD_ADD_SUB2]
  \\ Cases_on `v = j`
  \\ FULL_SIMP_TAC std_ss [RW1 [MULT_COMM] MULT_DIV,
       FAPPLY_FUPDATE_THM,FDOM_FUPDATE,IN_INSERT]
  \\ REWRITE_TAC [GSYM WORD_ADD_ASSOC,word_add_n2w, RW1 [MULT_COMM] (GSYM MULT)]
  \\ REWRITE_TAC [WORD_ADD_ASSOC,GSYM word_add_n2w]
  \\ Q.PAT_X_ASSUM `!bb. bbb` MATCH_MP_TAC
  \\ FULL_SIMP_TAC std_ss [IN_DEF,RANGE_def] \\ DECIDE_TAC);

val NOT_ALIGNED_LEMMA = prove(
  ``!c. ~ALIGNED (ADDR32 c + 0x1w) /\ ~ALIGNED (ADDR32 c + 0x2w) /\
        ~ALIGNED (ADDR32 c + 0x3w) /\ ~ALIGNED (ADDR32 c - 0x1w) /\
        ~ALIGNED (ADDR32 c - 0x2w) /\ ~ALIGNED (ADDR32 c - 0x3w)``,
  METIS_TAC [ALIGNED_ADDR32,NOT_ALIGNED,WORD_ADD_SUB,WORD_SUB_ADD]);

val IN_ch_active_set2 = prove(
  ``!v a. v IN ch_active_set (a,b,j) /\ 8 * j < 2 ** 32 /\ b <> 0 ==>
          ?i. i <> 0 /\ 8 * i < 2 ** 32 /\ (8w * n2w i = v - a)``,
  Cases_word \\ Cases_word
  \\ SIMP_TAC std_ss [ch_active_set_def,GSPECIFICATION,
       WORD_EQ_SUB_LADD,word_mul_n2w,word_add_n2w]
  \\ REPEAT STRIP_TAC
  \\ ASM_SIMP_TAC std_ss [] \\ Q.EXISTS_TAC `j'`
  \\ SIMP_TAC std_ss [AC ADD_COMM ADD_ASSOC]
  \\ DECIDE_TAC);

val ok_data_IMP_ref_field_heap_el = prove(
  ``!j b a. 8 * j < 2 ** 32 /\ b <> 0 /\
            ok_data v (ch_active_set (a,b,j)) ==>
            (ref_field a (heap_el a v) = v)``,
  Cases_on `ALIGNED v`
  \\ ASM_SIMP_TAC std_ss [ok_data_def,ref_field_def,heap_el_def]
  \\ REWRITE_TAC [GSYM (EVAL ``(2**32):num``)]
  \\ REPEAT STRIP_TAC
  \\ IMP_RES_TAC (IN_ch_active_set2)
  \\ REPEAT (Q.PAT_X_ASSUM `!v.bbb` (K ALL_TAC)) THENL [
    Q.PAT_X_ASSUM `0x8w * n2w i = v - a` (ASSUME_TAC o GSYM)
    \\ FULL_SIMP_TAC (std_ss++SIZES_ss) [word_mul_n2w,w2n_n2w]
    \\ ASM_SIMP_TAC std_ss [RW1 [MULT_COMM] MULT_DIV]
    \\ FULL_SIMP_TAC std_ss [WORD_EQ_SUB_RADD]
    \\ SIMP_TAC std_ss [AC WORD_ADD_COMM WORD_ADD_ASSOC,ref_addr_def],
    STRIP_ASSUME_TAC (Q.SPEC `v` EXISTS_ADDR32)
    \\ FULL_SIMP_TAC std_ss [WORD_ADD_0,ALIGNED_ADDR32,WORD_ADD_SUB,
          ADDR30_ADDR32,word_arith_lemma4,NOT_ALIGNED_LEMMA]]);

val ref_field_heap_el = prove(
  ``!t j b a. 8 * j < 2 ** 32 /\ b <> 0 /\
              word_tree t (v,m) (ch_active_set (a,b,j)) ==>
              (ref_field a (heap_el a v) = v)``,
  REVERSE Cases
  \\ ASM_SIMP_TAC std_ss [word_tree_def,heap_el_def,NOT_ALIGNED_LEMMA,
       ref_field_def,ADDR30_ADDR32,word_arith_lemma4,WORD_ADD_0,
       ALIGNED_ADDR32,ref_addr_def]
  \\ REWRITE_TAC [GSYM (EVAL ``(2**32):num``)]
  \\ REPEAT STRIP_TAC
  \\ IMP_RES_TAC (IN_ch_active_set2)
  \\ REPEAT (Q.PAT_X_ASSUM `!v.bbb` (K ALL_TAC))
  \\ Q.PAT_X_ASSUM `0x8w * n2w i = v - a` (ASSUME_TAC o GSYM)
  \\ FULL_SIMP_TAC (std_ss++SIZES_ss) [word_mul_n2w,w2n_n2w]
  \\ ASM_SIMP_TAC std_ss [RW1 [MULT_COMM] MULT_DIV]
  \\ FULL_SIMP_TAC std_ss [WORD_EQ_SUB_RADD]
  \\ SIMP_TAC std_ss [AC WORD_ADD_COMM WORD_ADD_ASSOC]);

val IN_RANGE_IMP = prove(
  ``!i j v a. j IN RANGE (v,i) ==> a + 8w * n2w j IN ch_active_set (a,v,i)``,
  SIMP_TAC std_ss [ch_active_set_def,GSPECIFICATION]
  \\ SIMP_TAC std_ss [IN_DEF,RANGE_def] \\ METIS_TAC []);

val ZERO_OR_IN_RANGE = prove(
  ``!q r w a v i. 8 * i < 4294967296 /\
    ok_data w (ch_active_set (a,v,i)) /\
    (heap_el a w = (q,r)) ==>
    (q = 0) \/ q IN RANGE (v,i)``,
  STRIP_TAC
  \\ Cases_on `q = 0` \\ ASM_SIMP_TAC std_ss []
  \\ REPEAT STRIP_TAC
  \\ Cases_on `ALIGNED w`
  \\ FULL_SIMP_TAC std_ss [word_tree_def, heap_el_def, word_mul_n2w, ok_data_def]
  \\ Q.PAT_X_ASSUM `xxx = q` (ASSUME_TAC o GSYM)
  \\ FULL_SIMP_TAC std_ss []
  \\ MATCH_MP_TAC IN_ch_active_set
  \\ FULL_SIMP_TAC std_ss []);

val ch_tree_IMP_ch_arm = prove(
  ``ch_tree (t1,t2,t3,t4,t5,t6,l) (v1,v2,v3,v4,v5,v6,a,dm,m,b,k) ==>
    ch_arm ([heap_el a v1; heap_el a v2; heap_el a v3;
             heap_el a v4; heap_el a v5; heap_el a v6],
            build_heap (k,b,a,m),l)
           (v1,v2,v3,v4,v5,v6,a,dm,m)``,
  REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [ch_arm_def,ch_tree_def,LET_DEF]
  \\ Q.ABBREV_TAC `v = if u then 1 + l else 1`
  \\ Q.EXISTS_TAC `i`
  \\ Q.EXISTS_TAC `v + l`
  \\ Q.EXISTS_TAC `(MAP FST [heap_el a v1; heap_el a v2; heap_el a v3;
             heap_el a v4; heap_el a v5; heap_el a v6])`
  \\ Q.EXISTS_TAC `l`
  \\ Q.EXISTS_TAC `u`
  \\ Q.EXISTS_TAC `build_map (k, b, a, m)`
  \\ REWRITE_TAC [ch_inv_def]
  \\ `ok_state (i,v + l,
       [FST (heap_el a v1); FST (heap_el a v2); FST (heap_el a v3);
        FST (heap_el a v4); FST (heap_el a v5); FST (heap_el a v6)],l,u,
          build_map (k,b,a,m))` by
   (SIMP_TAC std_ss [ok_state_def,LET_DEF]
    \\ Q.UNABBREV_TAC `v`
    \\ Q.ABBREV_TAC `v = if u then 1 + l else 1`
    \\ ASM_SIMP_TAC std_ss [MAP,MEM]
    \\ STRIP_TAC THEN1
     (`!c. ~ALIGNED (ADDR32 c + 0x3w) /\ ~ALIGNED (ADDR32 c + 0x2w)` by
            METIS_TAC [ALIGNED_ADDR32,NOT_ALIGNED]
      \\ `8 * i < 4294967296` by
        (Cases_on `u` \\ FULL_SIMP_TAC std_ss [IN_DEF,RANGE_def]
         \\ Q.UNABBREV_TAC `v` \\ DECIDE_TAC)
      \\ REPEAT STRIP_TAC \\ POP_ASSUM MP_TAC
      \\ FULL_SIMP_TAC std_ss []
      THENL [
        Cases_on `t1`,
        Cases_on `t2`,
        Cases_on `t3`,
        Cases_on `t4`,
        Cases_on `t5`,
        Cases_on `t6`]
      \\ FULL_SIMP_TAC std_ss [word_tree_def,heap_el_def]
      \\ REPEAT STRIP_TAC
      \\ MATCH_MP_TAC IN_ch_active_set
      \\ ASM_SIMP_TAC std_ss [])
    \\ STRIP_TAC THEN1
     (REPEAT STRIP_TAC
      \\ MATCH_MP_TAC build_map_EMP
      \\ `v + (i - v) = i` by DECIDE_TAC
      \\ FULL_SIMP_TAC std_ss [IN_DEF,RANGE_def]
      \\ Cases_on `u` \\ FULL_SIMP_TAC std_ss [IN_DEF,RANGE_def]
      \\ Q.UNABBREV_TAC `v` \\ DECIDE_TAC)
    \\ REPEAT STRIP_TAC
    \\ IMP_RES_TAC IN_RANGE_IMP
    \\ POP_ASSUM (ASSUME_TAC o Q.SPEC `a`)
    \\ `8 * (v + (i - v)) < 2 ** 32 /\ k' IN RANGE (v,v + (i - v))` by
     (`v + (i - v) = i` by DECIDE_TAC
      \\ Q.UNABBREV_TAC `v` \\ Cases_on `u` \\ FULL_SIMP_TAC std_ss []
      \\ DECIDE_TAC)
    \\ IMP_RES_TAC build_map_DATA
    \\ ASM_SIMP_TAC std_ss [EXISTS_PROD]
    \\ POP_ASSUM (K ALL_TAC)
    \\ Cases_on `heap_el a (m (a + n2w (8 * k')))`
    \\ Cases_on `heap_el a (m (a + n2w (8 * k') + 4w))`
    \\ ASM_SIMP_TAC std_ss [LET_DEF,heap_type_11]
    \\ Q.EXISTS_TAC `FST r`
    \\ Q.EXISTS_TAC `SND r`
    \\ Q.EXISTS_TAC `FST r'`
    \\ Q.EXISTS_TAC `SND r'`
    \\ SIMP_TAC std_ss [INSERT_SUBSET,EMPTY_SUBSET,SUBSET0_DEF,IN_INSERT]
    \\ RES_TAC
    \\ `v + (i - v) = i` by DECIDE_TAC
    \\ FULL_SIMP_TAC std_ss [word_tree_def,word_mul_n2w]
    \\ STRIP_TAC \\ MATCH_MP_TAC ZERO_OR_IN_RANGE \\ METIS_TAC [])
  \\ REPEAT STRIP_TAC THEN1 (POP_ASSUM MP_TAC  \\ ASM_REWRITE_TAC [MAP])
  THEN1
   (SIMP_TAC std_ss [ok_abs_def]
    \\ `v + (i - v) = i` by DECIDE_TAC
    \\ `FDOM (build_heap (i - v,a + n2w (8 * v),a,m)) = RANGE (v,v + (i - v))` by
     (MATCH_MP_TAC FDOM_build_heap
      \\ ASM_SIMP_TAC std_ss []
      \\ Cases_on `u` \\ Q.UNABBREV_TAC `v`
      \\ FULL_SIMP_TAC std_ss []
      \\ DECIDE_TAC)
    \\ ASM_SIMP_TAC std_ss []
    \\ STRIP_TAC THEN1
     (Cases_on `u` \\ FULL_SIMP_TAC std_ss [IN_DEF,RANGE_def]
      \\ Q.UNABBREV_TAC `v` \\ DECIDE_TAC)
    \\ REVERSE STRIP_TAC THEN1
     (SIMP_TAC std_ss [MAP,MEM]
      \\ `!c. ~ALIGNED (ADDR32 c + 0x3w) /\ ~ALIGNED (ADDR32 c + 0x2w)` by
            METIS_TAC [ALIGNED_ADDR32,NOT_ALIGNED]
      \\ `8 * i < 4294967296` by
        (Cases_on `u` \\ FULL_SIMP_TAC std_ss [IN_DEF,RANGE_def]
         \\ Q.UNABBREV_TAC `v` \\ DECIDE_TAC)
      \\ REPEAT STRIP_TAC \\ POP_ASSUM MP_TAC
      \\ FULL_SIMP_TAC std_ss []
      THENL [
        Cases_on `t1`,
        Cases_on `t2`,
        Cases_on `t3`,
        Cases_on `t4`,
        Cases_on `t5`,
        Cases_on `t6`]
      \\ FULL_SIMP_TAC std_ss [word_tree_def,heap_el_def]
      \\ REPEAT STRIP_TAC
      \\ MATCH_MP_TAC IN_ch_active_set
      \\ ASM_SIMP_TAC std_ss [])
    \\ ASM_SIMP_TAC std_ss [FEVERY_DEF]
    \\ REPEAT STRIP_TAC
    \\ IMP_RES_TAC IN_RANGE_IMP
    \\ POP_ASSUM (ASSUME_TAC o Q.SPEC `a`)
    \\ `8 * (v + (i - v)) < 2 ** 32 /\ x IN RANGE (v,v + (i - v))` by
     (Q.UNABBREV_TAC `v` \\ Cases_on `u`
      \\ FULL_SIMP_TAC std_ss [] \\ DECIDE_TAC)
    \\ IMP_RES_TAC build_heap_DATA
    \\ ASM_SIMP_TAC std_ss []
    \\ POP_ASSUM (K ALL_TAC)
    \\ Cases_on `heap_el a (m (a + n2w (8 * x)))`
    \\ Cases_on `heap_el a (m (a + n2w (8 * x) + 4w))`
    \\ ASM_SIMP_TAC std_ss [LET_DEF,heap_type_11]
    \\ SIMP_TAC std_ss [INSERT_SUBSET,EMPTY_SUBSET,SUBSET0_DEF,IN_INSERT]
    \\ FULL_SIMP_TAC std_ss [word_tree_def,word_mul_n2w]
    \\ RES_TAC \\ STRIP_TAC \\ MATCH_MP_TAC ZERO_OR_IN_RANGE
    \\ Q.PAT_X_ASSUM `v + (i - v) = i` ASSUME_TAC
    \\ FULL_SIMP_TAC std_ss []
    \\ METIS_TAC [])
  THEN1
   (Q.EXISTS_TAC `I`
    \\ SIMP_TAC std_ss [MAP,bijection_def,ONE_ONE_DEF,ONTO_DEF]
    \\ ASM_SIMP_TAC std_ss [abstract_build_heap,SUBSET_REFL]
    \\ SIMP_TAC std_ss [SUBSET_DEF,IN_DEF,reachables_def,FORALL_PROD])
  THEN
   (ASM_SIMP_TAC std_ss [ch_word_def,MAP,CONS_11,ref_addr_def]
    \\ POP_ASSUM MP_TAC \\ ASM_SIMP_TAC std_ss [MAP]
    \\ STRIP_TAC \\ POP_ASSUM (K ALL_TAC)
    \\ REVERSE STRIP_TAC THEN1
     (`8 * i < 2 ** 32 /\ v <> 0` by
        (Cases_on `u` \\ Q.UNABBREV_TAC `v`
         \\ FULL_SIMP_TAC std_ss [] \\ DECIDE_TAC)
      \\ ONCE_REWRITE_TAC [EQ_SYM_EQ] \\ REPEAT STRIP_TAC
      \\ MATCH_MP_TAC ref_field_heap_el
      THENL [Q.EXISTS_TAC `t1`,
             Q.EXISTS_TAC `t2`,
             Q.EXISTS_TAC `t3`,
             Q.EXISTS_TAC `t4`,
             Q.EXISTS_TAC `t5`,
             Q.EXISTS_TAC `t6`]
      \\ Q.EXISTS_TAC `i`
      \\ Q.EXISTS_TAC `v`
      \\ ASM_SIMP_TAC bool_ss [])
    \\ ASM_SIMP_TAC std_ss [ref_cheney_def,ALIGNED_INTRO]
    \\ STRIP_TAC THEN1
       (REPEAT (POP_ASSUM MP_TAC)
        \\ Q.SPEC_TAC (`a`,`a`)
        \\ Cases_word
        \\ FULL_SIMP_TAC (std_ss++SIZES_ss) [w2n_n2w,n2w_11]
        \\ REPEAT STRIP_TAC
        \\ DECIDE_TAC)
    \\ REVERSE (REPEAT STRIP_TAC)
    THEN1 (FULL_SIMP_TAC std_ss [valid_address_def] \\ DECIDE_TAC)
    THEN1 (MATCH_MP_TAC build_map_EMP
           \\ Cases_on `u` \\ Q.UNABBREV_TAC `v`
           \\ FULL_SIMP_TAC std_ss [IN_DEF,RANGE_def] \\ DECIDE_TAC)
    \\ `~(v = 0) /\ 8 * (v + (i - v)) < 2 ** 32 /\ 8 * i < 2 ** 32` by
     (Cases_on `u` \\ Q.UNABBREV_TAC `v`
      \\ FULL_SIMP_TAC std_ss [IN_DEF,RANGE_def] \\ DECIDE_TAC)
    \\ REVERSE (Cases_on `i' IN RANGE (v,v + (i - v))`)
    THEN1 (IMP_RES_TAC build_map_EMP \\ ASM_SIMP_TAC std_ss [ref_mem_def])
    \\ IMP_RES_TAC build_map_DATA
    \\ POP_ASSUM (ASSUME_TAC o Q.SPECL [`m`,`a`])
    \\ Cases_on `heap_el a (m (a + n2w (8 * i')))`
    \\ Cases_on `heap_el a (m (a + n2w (8 * i') + 4w))`
    \\ FULL_SIMP_TAC std_ss [LET_DEF,ref_mem_def]
    \\ POP_ASSUM (fn th => REWRITE_TAC [GSYM th])
    \\ POP_ASSUM (fn th => REWRITE_TAC [GSYM th])
    \\ IMP_RES_TAC IN_RANGE_IMP
    \\ POP_ASSUM (ASSUME_TAC o Q.SPEC `a`)
    \\ `v + (i - v) = i` by DECIDE_TAC
    \\ FULL_SIMP_TAC std_ss [ref_addr_def,word_mul_n2w]
    \\ RES_TAC \\ FULL_SIMP_TAC std_ss [word_tree_def]
    \\ ONCE_REWRITE_TAC [EQ_SYM_EQ] \\ STRIP_TAC
    \\ SIMP_TAC std_ss [ref_addr_def]
    \\ MATCH_MP_TAC ok_data_IMP_ref_field_heap_el
    \\ SIMP_TAC std_ss [] \\ METIS_TAC []));

val XSIZE_def = Define `
  (XSIZE (XDot x y) = SUC (XSIZE x + XSIZE y)) /\
  (XSIZE (XVal w) = 0) /\
  (XSIZE (XSym s) = 0)`;

val XDEPTH_def = Define `
  (XDEPTH (XDot x y) = SUC (MAX (XDEPTH x) (XDEPTH y))) /\
  (XDEPTH (XVal w) = 0) /\
  (XDEPTH (XSym s) = 0)`;

val CARD_LESS_EQ_XSIZE = prove(
  ``!t1 v1 a m. ch_tree (t1,t2,t3,t4,t5,t6,l) (v1,v2,v3,v4,v5,v6,a,dm,m,b,k) ==>
                CARD (reachables [FST (heap_el a v1)] (ch_set (build_heap (k,b,a,m)))) <= XSIZE t1``,
  Induct THEN1
   (SIMP_TAC std_ss [word_tree_def,XSIZE_def,ADD1]
    \\ REPEAT STRIP_TAC \\ RES_TAC
    \\ Cases_on `heap_el a (m v1)`
    \\ Cases_on `heap_el a (m (v1+4w))`
    \\ `(build_heap (k,b,a,m)) ' (FST (heap_el a v1)) = (q,q',r,r')` by
     (REPEAT (Q.PAT_X_ASSUM `!xx.yy` (K ALL_TAC))
      \\ FULL_SIMP_TAC std_ss [ch_tree_def,LET_DEF]
      \\ Q.ABBREV_TAC `v = if u then 1 + l else 1`
      \\ `8 * (v + (i - v)) < 2 ** 32 /\ v <> 0` by
       (Cases_on `u` \\ Q.UNABBREV_TAC `v`
        \\ FULL_SIMP_TAC std_ss [] \\ DECIDE_TAC)
      \\ `v + (i - v) = i` by DECIDE_TAC
      \\ FULL_SIMP_TAC bool_ss [word_tree_def]
      \\ ASM_SIMP_TAC std_ss [heap_el_def]
      \\ IMP_RES_TAC IN_ch_active_set
      \\ `8 * (v + (i - v)) < 2 ** 32 /\
          w2n (v1 - a) DIV 8 IN RANGE (v,v + (i - v))` by
            FULL_SIMP_TAC std_ss []
      \\ IMP_RES_TAC build_heap_DATA
      \\ ASM_SIMP_TAC std_ss []
      \\ POP_ASSUM (K ALL_TAC)
      \\ IMP_RES_TAC (RW [WORD_EQ_SUB_LADD] IN_ch_active_set2)
      \\ REPEAT (Q.PAT_X_ASSUM `!xx.yy` (K ALL_TAC))
      \\ Q.PAT_X_ASSUM `0x8w * n2w i' + a = v1` (ASSUME_TAC o GSYM)
      \\ FULL_SIMP_TAC std_ss [word_mul_n2w,WORD_ADD_SUB]
      \\ ASM_SIMP_TAC (std_ss++SIZES_ss) [w2n_n2w]
      \\ ASM_SIMP_TAC std_ss [RW1 [MULT_COMM] MULT_DIV]
      \\ FULL_SIMP_TAC std_ss [LET_DEF,AC WORD_ADD_ASSOC WORD_ADD_COMM])
    \\ `(FST (heap_el a v1)) IN FDOM (build_heap (k,b,a,m))` by
     (REPEAT (Q.PAT_X_ASSUM `!xx.yy` (K ALL_TAC))
      \\ FULL_SIMP_TAC std_ss [ch_tree_def,LET_DEF]
      \\ Q.ABBREV_TAC `v = if u then 1 + l else 1`
      \\ `8 * (v + (i - v)) < 2 ** 32 /\ v <> 0` by
       (Cases_on `u` \\ Q.UNABBREV_TAC `v`
        \\ FULL_SIMP_TAC std_ss [] \\ DECIDE_TAC)
      \\ IMP_RES_TAC FDOM_build_heap
      \\ FULL_SIMP_TAC std_ss [word_tree_def,heap_el_def]
      \\ MATCH_MP_TAC IN_ch_active_set
      \\ `v + (i - v) = i` by DECIDE_TAC \\ ASM_SIMP_TAC std_ss []
      \\ Cases_on `u` \\ Q.UNABBREV_TAC `v`
      \\ FULL_SIMP_TAC std_ss [] \\ DECIDE_TAC)
    \\ IMP_RES_TAC reachables_NEXT \\ RES_TAC
    \\ ASM_SIMP_TAC std_ss []
    \\ `ch_tree (t1,t2,t3,t4,t5,t6,l) (m v1,v2,v3,v4,v5,v6,a,dm,m,b,k) /\
        ch_tree (t1',t2,t3,t4,t5,t6,l) (m (v1 + 4w),v2,v3,v4,v5,v6,a,dm,m,b,k)` by
     (REPEAT (Q.PAT_X_ASSUM `!xx.yy` (K ALL_TAC))
      \\ FULL_SIMP_TAC std_ss [LET_DEF,ch_tree_def,word_tree_def]
      \\ STRIP_TAC \\ Q.EXISTS_TAC `i` \\ Q.EXISTS_TAC `u`
      \\ Q.ABBREV_TAC `v = if u then 1 + l else 1`
      \\ ASM_SIMP_TAC std_ss [])
    \\ RES_TAC
    \\ REPEAT (Q.PAT_X_ASSUM `!xx.yy` (K ALL_TAC))
    \\ Q.PAT_X_ASSUM `ch_tree (t1,t2,t3,t4,t5,t6,l) (m v1,v2,v3,v4,v5,v6,a,dm,m,b,k)` (K ALL_TAC)
    \\ Q.PAT_X_ASSUM `ch_tree (t1',t2,t3,t4,t5,t6,l) (m (v1 + 4w),v2,v3,v4,v5,v6,a,dm,m,b,k)` (K ALL_TAC)
    \\ Q.PAT_X_ASSUM `heap_el a (m v1) = (q,r)` (fn th => FULL_SIMP_TAC std_ss [th])
    \\ Q.PAT_X_ASSUM `heap_el a (m (v1+4w)) = bbb` (fn th => FULL_SIMP_TAC std_ss [th])
    \\ MATCH_MP_TAC LESS_EQ_TRANS
    \\ Q.EXISTS_TAC `CARD (reachables [q] (ch_set (build_heap (k,b,a,m)))) +
                     CARD (reachables [q'] (ch_set (build_heap (k,b,a,m)))) + 1`
    \\ REVERSE STRIP_TAC THEN1 DECIDE_TAC
    \\ MATCH_MP_TAC LESS_EQ_TRANS
    \\ Q.EXISTS_TAC `CARD (reachables [q] (ch_set (build_heap (k,b,a,m))) UNION
                           reachables [q'] (ch_set (build_heap (k,b,a,m)))) + 1`
    \\ ASM_SIMP_TAC std_ss [GSYM CARD_UNION,FINITE_reachables]
    \\ `1 = CARD {(FST (heap_el a v1),q,q',r,r')}` by METIS_TAC [CARD_SING]
    \\ ASM_SIMP_TAC std_ss [GSYM CARD_UNION,FINITE_reachables,FINITE_INSERT,FINITE_UNION,FINITE_EMPTY]
    \\ SIMP_TAC std_ss [AC UNION_ASSOC UNION_COMM])
  \\ FULL_SIMP_TAC std_ss [ch_tree_def,LET_DEF]
  \\ SIMP_TAC bool_ss [XSIZE_def,DECIDE ``n <= 0 = (n = 0)``,CARD_EQ_0,FINITE_reachables]
  \\ SIMP_TAC std_ss [EXTENSION,IN_DEF,EMPTY_DEF]
  \\ REPEAT STRIP_TAC \\ Cases_on `x` \\ Cases_on `r` \\ Cases_on `r'`
  \\ FULL_SIMP_TAC std_ss [reachables_def,reachable_def,IN_DEF,ch_set_def,MEM]
  \\ REPEAT (Cases_on `p`)
  \\ POP_ASSUM MP_TAC
  \\ FULL_SIMP_TAC std_ss [APPEND,PATH_def,ch_set_def,IN_DEF,word_tree_def,
       heap_el_def,NOT_ALIGNED_LEMMA]
  \\ `~(FDOM (build_heap (k,b,a,m)) 0)` by
   (ASM_SIMP_TAC std_ss []
    \\ Q.ABBREV_TAC `v = if u then 1 + l else 1`
    \\ `8 * (v + (i - v)) < 2 ** 32 /\ v <> 0` by
     (Cases_on `u` \\ Q.UNABBREV_TAC `v`
      \\ FULL_SIMP_TAC std_ss [] \\ DECIDE_TAC)
    \\ IMP_RES_TAC FDOM_build_heap
    \\ ASM_SIMP_TAC std_ss [RANGE_def])
  \\ METIS_TAC []);

val CARD_UNION_IMP = prove(
  ``!s t m n. FINITE s /\ FINITE t /\ CARD s <= m /\ CARD t <= n ==>
              CARD (s UNION t) <= m + n``,
  REPEAT STRIP_TAC \\ IMP_RES_TAC CARD_UNION \\ DECIDE_TAC);

val ch_tree_swap = prove(
  ``ch_tree (t1,t2,t3,t4,t5,t6,l) (v1,v2,v3,v4,v5,v6,a,dm,m,b,k) ==>
    ch_tree (t2,t2,t3,t4,t5,t6,l) (v2,v2,v3,v4,v5,v6,a,dm,m,b,k) /\
    ch_tree (t3,t2,t3,t4,t5,t6,l) (v3,v2,v3,v4,v5,v6,a,dm,m,b,k) /\
    ch_tree (t4,t2,t3,t4,t5,t6,l) (v4,v2,v3,v4,v5,v6,a,dm,m,b,k) /\
    ch_tree (t5,t2,t3,t4,t5,t6,l) (v5,v2,v3,v4,v5,v6,a,dm,m,b,k) /\
    ch_tree (t6,t2,t3,t4,t5,t6,l) (v6,v2,v3,v4,v5,v6,a,dm,m,b,k)``,
  REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [ch_tree_def,LET_DEF]
  \\ Q.EXISTS_TAC `i` \\ Q.EXISTS_TAC `u`
  \\ FULL_SIMP_TAC std_ss [ch_tree_def,LET_DEF]);

val CARD_LESS_EQ_SUM_XSIZE = prove(
  ``ch_tree (t1,t2,t3,t4,t5,t6,l) (v1,v2,v3,v4,v5,v6,a,dm,m,b,k) ==>
        CARD (reachables [FST (heap_el a v1) ;FST (heap_el a v2); FST (heap_el a v3);
                          FST (heap_el a v4) ;FST (heap_el a v5); FST (heap_el a v6)]
                (ch_set (build_heap (k,b,a,m))))
        <= XSIZE t1 + XSIZE t2 + XSIZE t3 + XSIZE t4 + XSIZE t5 + XSIZE t6``,
  NTAC 8 (ONCE_REWRITE_TAC [reachables_THM])
  \\ REWRITE_TAC [(hd o CONJUNCTS o SPEC_ALL) reachables_THM,UNION_EMPTY]
  \\ REPEAT STRIP_TAC
  \\ REWRITE_TAC [GSYM ADD_ASSOC]
  \\ STRIP_ASSUME_TAC (UNDISCH ch_tree_swap)
  \\ IMP_RES_TAC CARD_LESS_EQ_XSIZE
  \\ MATCH_MP_TAC CARD_UNION_IMP
  \\ ASM_REWRITE_TAC [FINITE_UNION,FINITE_reachables]
  \\ MATCH_MP_TAC CARD_UNION_IMP
  \\ ASM_REWRITE_TAC [FINITE_UNION,FINITE_reachables]
  \\ MATCH_MP_TAC CARD_UNION_IMP
  \\ ASM_REWRITE_TAC [FINITE_UNION,FINITE_reachables]
  \\ MATCH_MP_TAC CARD_UNION_IMP
  \\ ASM_REWRITE_TAC [FINITE_UNION,FINITE_reachables]
  \\ MATCH_MP_TAC CARD_UNION_IMP
  \\ ASM_REWRITE_TAC [FINITE_UNION,FINITE_reachables]);

val LIMIT_LEMMA = prove(
  ``(p ==> m <= n) ==> (p ==> q ==> m < l ==> r) ==>
    (p ==> q ==> n < (l:num) ==> r)``,
  REPEAT STRIP_TAC \\ RES_TAC \\ `m < l` by DECIDE_TAC \\ METIS_TAC []);

val ch_arm_setup = let
  val th = RW [GSYM AND_IMP_INTRO] (RW1 [CONJ_COMM] (RW [AND_IMP_INTRO] ch_arm_alloc))
  val th = DISCH_ALL (MATCH_MP th (UNDISCH ch_tree_IMP_ch_arm))
  val imp = MATCH_MP LIMIT_LEMMA CARD_LESS_EQ_SUM_XSIZE
  val th = MATCH_MP imp (RW [MAP] th)
  in th end

val ch_arm2_def = Define `
  ch_arm2 (r,h,l,i,u) c =
    ?e rs m. ch_inv (MAP FST r,h,l) (i,e,rs,l,u,m) /\ ch_word (i,e,rs,MAP SND r,l,u,m) c`;

val ch_arm_IMP_ch_arm2 = prove(
  ``ch_arm (r,h,l) c ==> ?i u. ch_arm2 (r,h,l,i,u) c``,
  SIMP_TAC std_ss [ch_arm_def,ch_arm2_def,ch_inv_def] \\ METIS_TAC []);

(*
set_trace "Goalstack.print_goal_at_top" 0
*)


val ok_data_ref_field = prove(
  ``{x} SUBSET0 RANGE (v,i) /\ 8 * i < 2 ** 32 /\ ALIGNED a ==>
    ok_data (ref_field a (x,q)) (ch_active_set (a,v,i))``,
  SIMP_TAC std_ss [SUBSET0_DEF,INSERT_SUBSET,IN_INSERT,EMPTY_SUBSET]
  \\ Cases_on `x = 0` \\ ASM_SIMP_TAC std_ss []
  \\ REPEAT STRIP_TAC THEN1
   (FULL_SIMP_TAC std_ss [ref_field_def,ok_data_def]
    \\ Cases_on `SND q`
    \\ ASM_SIMP_TAC std_ss [NOT_ALIGNED_LEMMA,word_arith_lemma4])
  \\ ASM_SIMP_TAC std_ss [ref_field_def,ref_addr_def,ok_data_def]
  \\ ASM_SIMP_TAC std_ss [ALIGNED_ADD_EQ,ALIGNED_n2w]
  \\ REWRITE_TAC [GSYM (EVAL ``4*2``),GSYM MULT_ASSOC]
  \\ REWRITE_TAC [RW1 [MULT_COMM] (MATCH_MP MOD_EQ_0 (DECIDE ``0<4``))]
  \\ SIMP_TAC std_ss [MULT_ASSOC,ch_active_set_def,GSPECIFICATION]
  \\ Q.EXISTS_TAC `x` \\ FULL_SIMP_TAC std_ss [IN_DEF,RANGE_def,word_mul_n2w]);

val REV_STRIP_TAC =
  REWRITE_TAC [CONJ_ASSOC] \\ REVERSE STRIP_TAC \\ REWRITE_TAC [GSYM CONJ_ASSOC]

val ch_tree_CAR_CDR = prove(
  ``ch_tree (XDot t1 t7,t2,t3,t4,t5,t6,l) (v1,v2,v3,v4,v5,v6,a,dm,m,b,k) ==>
    ch_tree (t1,t2,t3,t4,t5,t6,l) (m v1,v2,v3,v4,v5,v6,a,dm,m,b,k) /\
    ch_tree (t7,t2,t3,t4,t5,t6,l) (m (v1 + 4w),v2,v3,v4,v5,v6,a,dm,m,b,k)``,
  SIMP_TAC std_ss [ch_tree_def,LET_DEF] \\ REPEAT STRIP_TAC
  \\ Q.EXISTS_TAC `i` \\ Q.EXISTS_TAC `u`
  \\ FULL_SIMP_TAC std_ss [word_tree_def]);

val IN_ch_active_set3 = prove(
  ``!v a.
       v IN ch_active_set (a,b,j) /\ 8 * j < 2 ** 32 /\ b <> 0 /\ ALIGNED a ==>
       ?i. i <> 0 /\ 8 * i < 2 ** 32 /\ (v = n2w (8 * i) + a) /\
           (heap_el a v = (i,0w,F))``,
  REPEAT STRIP_TAC
  \\ IMP_RES_TAC IN_ch_active_set
  \\ IMP_RES_TAC IN_ch_active_set2
  \\ Q.EXISTS_TAC `i`
  \\ Q.PAT_X_ASSUM `0x8w * n2w i = v - a` (ASSUME_TAC o GSYM o RW [WORD_EQ_SUB_LADD])
  \\ ASM_SIMP_TAC std_ss [word_mul_n2w]
  \\ ASM_SIMP_TAC std_ss [heap_el_def,ALIGNED_ADD_EQ,WORD_ADD_SUB]
  \\ SIMP_TAC std_ss [ALIGNED_n2w]
  \\ REWRITE_TAC [GSYM (EVAL ``4 * 2``), GSYM MULT_ASSOC,
       RW1 [MULT_COMM] (MATCH_MP MOD_EQ_0 (DECIDE ``0<4``))]
  \\ FULL_SIMP_TAC (std_ss++SIZES_ss) [MULT_ASSOC,w2n_n2w]
  \\ REWRITE_TAC [RW1 [MULT_COMM] (MATCH_MP MULT_DIV (DECIDE ``0<8``))]);

val MEM_fix = prove(``set l x = MEM x l``, SIMP_TAC bool_ss [IN_DEF])
val IN_reachables =
    ``(a,b,c,d) IN reachables rs h``
        |> SIMP_CONV bool_ss [reachables_def, IN_DEF]
        |> REWRITE_RULE [MEM_fix]

val ch_arm2_CAR = prove(
  ``(FST q1) IN FDOM h /\
    (h ' (FST q1) = (z1,y1,z2,y2)) /\
    ch_arm2 ([q1; q2; q3; q4; q5; q6],h,l,i,u) (w1,w2,w3,w4,w5,w6,a,dm,xs) ==>
    ch_arm2 ([(z1,z2); q2; q3; q4; q5; q6],h,l,i,u) (xs w1,w2,w3,w4,w5,w6,a,dm,xs)``,
  SIMP_TAC std_ss [ch_arm2_def,ch_inv_def] \\ REPEAT STRIP_TAC
  \\ `(FST q1,z1,y1,z2,y2) IN reachables (MAP FST [q1; q2; q3; q4; q5; q6]) (ch_set h)` by
   (FULL_SIMP_TAC std_ss [IN_reachables,ch_set_def]
    \\ Q.EXISTS_TAC `FST q1` \\ SIMP_TAC std_ss [MEM,MAP,reachable_def])
  \\ `(FST q1,z1,y1,z2,y2) IN abstract (b,m)` by METIS_TAC [SUBSET_DEF]
  \\ FULL_SIMP_TAC std_ss [abstract_def,GSPECIFICATION]
  \\ `?a1 a2 a3 a4 a5. x = (a1,a2,a3,a4,a5)` by METIS_TAC [PAIR]
  \\ FULL_SIMP_TAC std_ss [abstract_def,GSPECIFICATION]
  \\ Q.EXISTS_TAC `e`
  \\ Q.EXISTS_TAC `a2 :: TL rs` \\ Q.EXISTS_TAC `m`
  \\ `ok_state (i,e,a2::TL rs,l,u,m) /\ a1 IN RANGE (if u then 1 + l else 1,i)` by
   (FULL_SIMP_TAC std_ss [ok_state_def,LET_DEF,MEM]
    \\ Cases_on `rs`
    \\ FULL_SIMP_TAC std_ss [MAP,CONS_11,NOT_NIL_CONS,MEM,ok_abs_def,TL]
    \\ `(h' = a1) /\ (b a1 <> 0)` by METIS_TAC [ONE_ONE_DEF,ONTO_DEF,bijection_def]
    \\ `(a1 <> 0)` by METIS_TAC [ONE_ONE_DEF,ONTO_DEF,bijection_def]
    \\ `a1 IN RANGE (if u then 1 + l else 1,i)` by METIS_TAC []
    \\ RES_TAC
    \\ FULL_SIMP_TAC std_ss [SUBSET0_DEF,INSERT_SUBSET,IN_INSERT,heap_type_11]
    \\ METIS_TAC [])
  \\ FULL_SIMP_TAC std_ss [GSYM abstract_def]
  \\ STRIP_TAC THEN1
   (FULL_SIMP_TAC std_ss [ok_abs_def,MEM,MAP,FEVERY_DEF]
    \\ RES_TAC \\ POP_ASSUM MP_TAC \\ ASM_REWRITE_TAC []
    \\ SIMP_TAC std_ss [] \\ STRIP_TAC \\ STRIP_TAC THEN1
      (FULL_SIMP_TAC std_ss [SUBSET0_DEF,INSERT_SUBSET,IN_INSERT]
      \\ METIS_TAC [])
    \\ Q.EXISTS_TAC `b` \\ Cases_on `rs`
    \\ FULL_SIMP_TAC std_ss [MAP,CONS_11,NOT_NIL_CONS,MEM,ok_abs_def,TL]
    \\ MATCH_MP_TAC SUBSET_TRANS
    \\ Q.EXISTS_TAC `reachables [b a1; FST q2; FST q3; FST q4; FST q5; FST q6] (ch_set h)`
    \\ ASM_SIMP_TAC std_ss []
    \\ ASM_SIMP_TAC std_ss [SUBSET_DEF,IN_DEF,reachables_def,FORALL_PROD,MEM]
    \\ REPEAT STRIP_TAC THEN1
     (Q.EXISTS_TAC `b a1` \\ FULL_SIMP_TAC std_ss [reachable_def] THENL [
        DISJ2_TAC \\ Q.EXISTS_TAC `[]`
        \\ ASM_SIMP_TAC std_ss [APPEND,PATH_def,IN_DEF,ch_set_def]
        \\ METIS_TAC [],
        DISJ2_TAC \\ Q.EXISTS_TAC `b a2::p`
        \\ ASM_SIMP_TAC std_ss [APPEND,PATH_def,IN_DEF,ch_set_def]
        \\ METIS_TAC []])
    \\ METIS_TAC [])
  \\ FULL_SIMP_TAC std_ss [ch_word_def,MAP,CONS_11,TL]
  \\ FULL_SIMP_TAC std_ss [ref_cheney_def]
  \\ `a1 <= l+l+1` by (Cases_on `u`
    \\ FULL_SIMP_TAC std_ss [IN_DEF,RANGE_def,ok_state_def,LET_DEF]
    \\ DECIDE_TAC)
  \\ RES_TAC \\ POP_ASSUM MP_TAC
  \\ `a1 <> 0` by (CCONTR_TAC \\ FULL_SIMP_TAC std_ss [ok_abs_def])
  \\ `x1 <> 0` by (CCONTR_TAC \\ FULL_SIMP_TAC std_ss [ok_abs_def,MAP,CONS_11])
  \\ `ref_field a (x1,SND q1) = ref_addr a x1` by
       ASM_SIMP_TAC bool_ss [ref_mem_def,ref_field_def]
  \\ ASM_REWRITE_TAC []
  \\ ASM_SIMP_TAC std_ss [ref_mem_def]
  \\ FULL_SIMP_TAC std_ss [MAP,CONS_11,bijection_def,ONE_ONE_DEF]
  \\ METIS_TAC []);

val ch_arm2_swap2 = prove(
  ``ch_arm2 ([q1; q2; q3; q4; q5; q6],h,l,i,u) (w1,w2,w3,w4,w5,w6,a,dm,xs) ==>
    ch_arm2 ([q2; q1; q3; q4; q5; q6],h,l,i,u) (w2,w1,w3,w4,w5,w6,a,dm,xs)``,
  SIMP_TAC std_ss [ch_arm2_def,ch_word_def,ch_inv_def,ok_state_def,
    ok_abs_def,LET_DEF] \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [MAP,MEM,CONS_11]
  \\ Q.EXISTS_TAC `[x2; x1; x3; x4; x5; x6]` \\ Q.EXISTS_TAC `m`
  \\ FULL_SIMP_TAC std_ss [MAP,MEM,CONS_11,SUBSET_DEF,IN_DEF,
       reachables_def,FORALL_PROD]
  \\ FULL_SIMP_TAC std_ss [AC DISJ_COMM DISJ_ASSOC]
  \\ REPEAT STRIP_TAC \\ REPEAT (Q.EXISTS_TAC `b`) \\ METIS_TAC []);

val ch_arm2_swap3 = prove(
  ``ch_arm2 ([q1; q2; q3; q4; q5; q6],h,l,i,u) (w1,w2,w3,w4,w5,w6,a,dm,xs) ==>
    ch_arm2 ([q3; q2; q1; q4; q5; q6],h,l,i,u) (w3,w2,w1,w4,w5,w6,a,dm,xs)``,
  SIMP_TAC std_ss [ch_arm2_def,ch_word_def,ch_inv_def,ok_state_def,
    ok_abs_def,LET_DEF] \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [MAP,MEM,CONS_11]
  \\ Q.EXISTS_TAC `[x3; x2; x1; x4; x5; x6]` \\ Q.EXISTS_TAC `m`
  \\ FULL_SIMP_TAC std_ss [MAP,MEM,CONS_11,SUBSET_DEF,IN_DEF,
       reachables_def,FORALL_PROD]
  \\ FULL_SIMP_TAC std_ss [AC DISJ_COMM DISJ_ASSOC]
  \\ REPEAT STRIP_TAC \\ REPEAT (Q.EXISTS_TAC `b`) \\ METIS_TAC []);

val ch_arm2_swap4 = prove(
  ``ch_arm2 ([q1; q2; q3; q4; q5; q6],h,l,i,u) (w1,w2,w3,w4,w5,w6,a,dm,xs) ==>
    ch_arm2 ([q4; q2; q3; q1; q5; q6],h,l,i,u) (w4,w2,w3,w1,w5,w6,a,dm,xs)``,
  SIMP_TAC std_ss [ch_arm2_def,ch_word_def,ch_inv_def,ok_state_def,
    ok_abs_def,LET_DEF] \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [MAP,MEM,CONS_11]
  \\ Q.EXISTS_TAC `[x4; x2; x3; x1; x5; x6]` \\ Q.EXISTS_TAC `m`
  \\ FULL_SIMP_TAC std_ss [MAP,MEM,CONS_11,SUBSET_DEF,IN_DEF,
       reachables_def,FORALL_PROD]
  \\ FULL_SIMP_TAC std_ss [AC DISJ_COMM DISJ_ASSOC]
  \\ REPEAT STRIP_TAC \\ REPEAT (Q.EXISTS_TAC `b`) \\ METIS_TAC []);

val ch_arm2_swap5 = prove(
  ``ch_arm2 ([q1; q2; q3; q4; q5; q6],h,l,i,u) (w1,w2,w3,w4,w5,w6,a,dm,xs) ==>
    ch_arm2 ([q5; q2; q3; q4; q1; q6],h,l,i,u) (w5,w2,w3,w4,w1,w6,a,dm,xs)``,
  SIMP_TAC std_ss [ch_arm2_def,ch_word_def,ch_inv_def,ok_state_def,
    ok_abs_def,LET_DEF] \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [MAP,MEM,CONS_11]
  \\ Q.EXISTS_TAC `[x5; x2; x3; x4; x1; x6]` \\ Q.EXISTS_TAC `m`
  \\ FULL_SIMP_TAC std_ss [MAP,MEM,CONS_11,SUBSET_DEF,IN_DEF,
       reachables_def,FORALL_PROD]
  \\ FULL_SIMP_TAC std_ss [AC DISJ_COMM DISJ_ASSOC]
  \\ REPEAT STRIP_TAC \\ REPEAT (Q.EXISTS_TAC `b`) \\ METIS_TAC []);

val ch_arm2_swap6 = prove(
  ``ch_arm2 ([q1; q2; q3; q4; q5; q6],h,l,i,u) (w1,w2,w3,w4,w5,w6,a,dm,xs) ==>
    ch_arm2 ([q6; q2; q3; q4; q5; q1],h,l,i,u) (w6,w2,w3,w4,w5,w1,a,dm,xs)``,
  SIMP_TAC std_ss [ch_arm2_def,ch_word_def,ch_inv_def,ok_state_def,
    ok_abs_def,LET_DEF] \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [MAP,MEM,CONS_11]
  \\ Q.EXISTS_TAC `[x6; x2; x3; x4; x5; x1]` \\ Q.EXISTS_TAC `m`
  \\ FULL_SIMP_TAC std_ss [MAP,MEM,CONS_11,SUBSET_DEF,IN_DEF,
       reachables_def,FORALL_PROD]
  \\ FULL_SIMP_TAC std_ss [AC DISJ_COMM DISJ_ASSOC]
  \\ REPEAT STRIP_TAC \\ REPEAT (Q.EXISTS_TAC `b`) \\ METIS_TAC []);

val ch_arm2_CDR = prove(
  ``(FST q1) IN FDOM h /\
    (h ' (FST q1) = (z1,y1,z2,y2)) /\
    ch_arm2 ([q1; q2; q3; q4; q5; q6],h,l,i,u) (w1,w2,w3,w4,w5,w6,a,dm,xs) ==>
    ch_arm2 ([(y1,y2); q2; q3; q4; q5; q6],h,l,i,u) (xs (w1+4w),w2,w3,w4,w5,w6,a,dm,xs) /\
    w1 IN ch_active_set (a,if u then 1 + l else 1,i) /\ ALIGNED w1``,
  SIMP_TAC std_ss [ch_arm2_def,ch_inv_def] \\ STRIP_TAC
  \\ `(FST q1,z1,y1,z2,y2) IN reachables (MAP FST [q1; q2; q3; q4; q5; q6]) (ch_set h)` by
   (FULL_SIMP_TAC std_ss [IN_reachables,ch_set_def]
    \\ Q.EXISTS_TAC `FST q1` \\ SIMP_TAC std_ss [MEM,MAP,reachable_def])
  \\ `(FST q1,z1,y1,z2,y2) IN abstract (b,m)` by METIS_TAC [SUBSET_DEF]
  \\ FULL_SIMP_TAC std_ss [abstract_def,GSPECIFICATION]
  \\ `?a1 a2 a3 a4 a5. x = (a1,a3,a2,a5,a4)` by METIS_TAC [PAIR]
  \\ FULL_SIMP_TAC std_ss [abstract_def,GSPECIFICATION]
  \\ SIMP_TAC std_ss [METIS_PROVE [] ``(?x. P x) /\ Q = ?x. P x /\ Q``]
  \\ Q.EXISTS_TAC `e`
  \\ Q.EXISTS_TAC `a2 :: TL rs` \\ Q.EXISTS_TAC `m`
  \\ `ok_state (i,e,a2::TL rs,l,u,m) /\ a1 IN RANGE (if u then 1 + l else 1,i)` by
   (FULL_SIMP_TAC std_ss [ok_state_def,LET_DEF,MEM]
    \\ Cases_on `rs`
    \\ FULL_SIMP_TAC std_ss [MAP,CONS_11,NOT_NIL_CONS,MEM,ok_abs_def,TL]
    \\ `(h' = a1) /\ (b a1 <> 0)` by METIS_TAC [ONE_ONE_DEF,ONTO_DEF,bijection_def]
    \\ `(a1 <> 0)` by METIS_TAC [ONE_ONE_DEF,ONTO_DEF,bijection_def]
    \\ `a1 IN RANGE (if u then 1 + l else 1,i)` by METIS_TAC []
    \\ RES_TAC
    \\ FULL_SIMP_TAC std_ss [SUBSET0_DEF,INSERT_SUBSET,IN_INSERT,heap_type_11]
    \\ METIS_TAC [])
  \\ FULL_SIMP_TAC std_ss [GSYM abstract_def]
  \\ REWRITE_TAC [GSYM CONJ_ASSOC]
  \\ ONCE_REWRITE_TAC [CONJ_ASSOC]
  \\ STRIP_TAC THEN1
   (FULL_SIMP_TAC std_ss [ok_abs_def,MEM,MAP,FEVERY_DEF]
    \\ RES_TAC \\ POP_ASSUM MP_TAC \\ ASM_REWRITE_TAC []
    \\ SIMP_TAC std_ss [] \\ STRIP_TAC \\ STRIP_TAC THEN1
      (FULL_SIMP_TAC std_ss [SUBSET0_DEF,INSERT_SUBSET,IN_INSERT]
      \\ METIS_TAC [])
    \\ Q.EXISTS_TAC `b` \\ Cases_on `rs`
    \\ FULL_SIMP_TAC std_ss [MAP,CONS_11,NOT_NIL_CONS,MEM,ok_abs_def,TL]
    \\ MATCH_MP_TAC SUBSET_TRANS
    \\ Q.EXISTS_TAC `reachables [b a1; FST q2; FST q3; FST q4; FST q5; FST q6] (ch_set h)`
    \\ ASM_SIMP_TAC std_ss []
    \\ ASM_SIMP_TAC std_ss [SUBSET_DEF,IN_DEF,reachables_def,FORALL_PROD,MEM]
    \\ REPEAT STRIP_TAC THEN1
     (Q.EXISTS_TAC `b a1` \\ FULL_SIMP_TAC std_ss [reachable_def] THENL [
        DISJ2_TAC \\ Q.EXISTS_TAC `[]`
        \\ ASM_SIMP_TAC std_ss [APPEND,PATH_def,IN_DEF,ch_set_def]
        \\ METIS_TAC [],
        DISJ2_TAC \\ Q.EXISTS_TAC `b a2::p`
        \\ ASM_SIMP_TAC std_ss [APPEND,PATH_def,IN_DEF,ch_set_def]
        \\ METIS_TAC []])
    \\ METIS_TAC [])
  \\ FULL_SIMP_TAC std_ss [ch_word_def,MAP,CONS_11,TL]
  \\ FULL_SIMP_TAC std_ss [ref_cheney_def]
  \\ `a1 <= l+l+1` by (Cases_on `u`
    \\ FULL_SIMP_TAC std_ss [IN_DEF,RANGE_def,ok_state_def,LET_DEF]
    \\ DECIDE_TAC)
  \\ RES_TAC \\ POP_ASSUM MP_TAC
  \\ `a1 <> 0` by (CCONTR_TAC \\ FULL_SIMP_TAC std_ss [ok_abs_def])
  \\ `x1 <> 0` by (CCONTR_TAC \\ FULL_SIMP_TAC std_ss [ok_abs_def,MAP,CONS_11])
  \\ `ref_field a (x1,SND q1) = ref_addr a x1` by
       ASM_SIMP_TAC bool_ss [ref_mem_def,ref_field_def]
  \\ ASM_REWRITE_TAC []
  \\ ASM_SIMP_TAC std_ss [ref_mem_def]
  \\ FULL_SIMP_TAC std_ss [MAP,CONS_11,bijection_def,ONE_ONE_DEF]
  \\ `a1 = x1` by METIS_TAC []
  \\ FULL_SIMP_TAC std_ss []
  \\ STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [ref_addr_def,ch_active_set_def,
       GSPECIFICATION,word_mul_n2w,ALIGNED_ADD_EQ,ALIGNED_INTRO]
  \\ SIMP_TAC bool_ss [ALIGNED_n2w,GSYM (EVAL ``4*2``),GSYM MULT_ASSOC]
  \\ REWRITE_TAC [RW1 [MULT_COMM] (MATCH_MP MOD_EQ_0 (DECIDE ``0<4``))]
  \\ Q.EXISTS_TAC `x1` \\ REWRITE_TAC []
  \\ FULL_SIMP_TAC std_ss [LET_DEF,ok_state_def,MEM]
  \\ `x1 IN RANGE (if u then 1 + l else 1,i)` by METIS_TAC []
  \\ Cases_on `u` \\ FULL_SIMP_TAC std_ss [IN_DEF,RANGE_def]
  \\ DECIDE_TAC);

val ch_tree_XDot = prove(
  ``ch_tree (XDot tx ty,t2,t3,t4,t5,t6,l) (v1,v2,v3,v4,v5,v6,a,dm,m,b,k) ==>
    (FST (heap_el a v1)) IN FDOM (build_heap (k,b,a,m)) /\
    (build_heap (k,b,a,m) ' (FST (heap_el a v1)) =
      (FST (heap_el a (m v1)),
       FST (heap_el a (m (v1 + 4w))),
       SND (heap_el a (m v1)),
       SND (heap_el a (m (v1 + 4w)))))``,
  SIMP_TAC std_ss [ch_tree_def,LET_DEF,word_tree_def] \\ STRIP_TAC
  \\ Q.ABBREV_TAC `v = if u then 1 + l else 1`
  \\ `v <> 0 /\ 8 * i < 2 ** 32` by
   (Cases_on `u` \\ Q.UNABBREV_TAC `v`
    \\ FULL_SIMP_TAC std_ss [] \\ DECIDE_TAC)
  \\ `?j. j <> 0 /\ 8 * j < 2 ** 32 /\ (v1 = n2w (8 * j) + a) /\
          (heap_el a v1 = (j,0x0w,F))` by
              METIS_TAC [IN_ch_active_set3]
  \\ `j IN RANGE (v,i)` by
   (IMP_RES_TAC IN_ch_active_set
    \\ Q.PAT_X_ASSUM `w2n (v1 - a) DIV 8 IN RANGE (v,i)` MP_TAC
    \\ FULL_SIMP_TAC (std_ss++SIZES_ss) [WORD_ADD_SUB,w2n_n2w]
    \\ SIMP_TAC std_ss [RW1 [MULT_COMM] (MULT_DIV)])
  \\ ASM_SIMP_TAC std_ss []
  \\ `i = v + (i - v)` by DECIDE_TAC
  \\ `j IN FDOM (build_heap (i - v,a + n2w (8 * v),a,m)) /\
      (build_heap (i - v,a + n2w (8 * v),a,m) ' j =
      (let (x1,x2) = heap_el a (m (n2w (8 * j) + a)) in
       let (y1,y2) = heap_el a (m (n2w (8 * j) + a + 0x4w)) in
         (x1,y1,x2,y2)))` by METIS_TAC [build_heap_DATA,WORD_ADD_COMM]
  \\ ASM_SIMP_TAC std_ss []
  \\ Cases_on `(heap_el a (m (n2w (8 * j) + a)))`
  \\ Cases_on `(heap_el a (m (n2w (8 * j) + a + 4w)))`
  \\ SIMP_TAC std_ss [LET_DEF]);

val IMP_word_tree = prove(
  ``!t1 v1 w1.
      ch_tree (t1,t2,t3,t4,t5,t6,l) (v1,v2,v3,v4,v5,v6,a,dm,m,b,k) /\
      ch_arm2
        ([heap_el a v1; q2; q3; q4; q5; q6],
         build_heap (k,b,a,m) |+
         (fresh (build_heap (k,b,a,m)),qqq),l,i,u) (w1,w2,w3,w4,w5,w6,a,dm,xs) ==>
      word_tree t1 (w1,xs) (ch_active_set (a,if u then 1 + l else 1,i))``,
  REVERSE Induct THEN1
   (REPEAT STRIP_TAC
    \\ FULL_SIMP_TAC std_ss [ch_tree_def,LET_DEF,word_tree_def]
    \\ Q.PAT_X_ASSUM `v1 = ADDR32 c + 0x3w` (fn th => FULL_SIMP_TAC std_ss [th])
    \\ FULL_SIMP_TAC std_ss [heap_el_def,NOT_ALIGNED_LEMMA,WORD_ADD_SUB,
         ALIGNED_ADDR32,ADDR30_ADDR32,ch_arm2_def,ch_word_def,MAP,CONS_11]
    \\ FULL_SIMP_TAC std_ss [ch_inv_def,MAP,CONS_11,bijection_def]
    \\ `x1 = 0` by METIS_TAC [ONE_ONE_DEF]
    \\ ASM_SIMP_TAC std_ss [ref_field_def])
  THEN1
   (REPEAT STRIP_TAC
    \\ FULL_SIMP_TAC std_ss [ch_tree_def,LET_DEF,word_tree_def]
    \\ Q.PAT_X_ASSUM `v1 = ADDR32 c + 0x2w` (fn th => FULL_SIMP_TAC std_ss [th])
    \\ FULL_SIMP_TAC std_ss [heap_el_def,NOT_ALIGNED_LEMMA,WORD_ADD_SUB,
         ALIGNED_ADDR32,ADDR30_ADDR32,ch_arm2_def,ch_word_def,MAP,CONS_11,
         word_arith_lemma4]
    \\ FULL_SIMP_TAC std_ss [ch_inv_def,MAP,CONS_11,bijection_def]
    \\ `x1 = 0` by METIS_TAC [ONE_ONE_DEF]
    \\ ASM_SIMP_TAC std_ss [ref_field_def])
  \\ REPEAT STRIP_TAC
  \\ IMP_RES_TAC ch_tree_XDot
  \\ Q.ABBREV_TAC `hhh = build_heap (k,b,a,m) |+ (fresh (build_heap (k,b,a,m)),qqq)`
  \\ `FST (heap_el a v1) IN FDOM hhh /\
     (hhh ' (FST (heap_el a v1)) =
      (FST (heap_el a (m v1)),FST (heap_el a (m (v1 + 0x4w))),
       SND (heap_el a (m v1)),SND (heap_el a (m (v1 + 0x4w)))))` by
    (Q.UNABBREV_TAC `hhh`
    \\ ASM_SIMP_TAC std_ss [FAPPLY_FUPDATE_THM,FDOM_FUPDATE,IN_INSERT]
    \\ METIS_TAC [fresh_NOT_IN_FDOM])
  \\ IMP_RES_TAC ch_arm2_CAR
  \\ IMP_RES_TAC ch_arm2_CDR
  \\ REPEAT (Q.PAT_X_ASSUM `!xxx yyyy xzzz.bbb` (K ALL_TAC))
  \\ FULL_SIMP_TAC std_ss [word_tree_def]
  \\ IMP_RES_TAC ch_tree_CAR_CDR
  \\ RES_TAC \\ ASM_SIMP_TAC std_ss []
  \\ REPEAT (Q.PAT_X_ASSUM `xxx ==> yy` (K ALL_TAC))
  \\ REPEAT (Q.PAT_X_ASSUM `!xxx.bbb` (K ALL_TAC))
  \\ Q.UNABBREV_TAC `hhh`
  \\ NTAC 10 (POP_ASSUM (K ALL_TAC))
  \\ FULL_SIMP_TAC std_ss [ch_arm2_def]
  \\ `?j. j <> 0 /\ 8 * j < 2 ** 32 /\ (heap_el a v1 = (j,0x0w,F))` by
     (FULL_SIMP_TAC std_ss [ch_tree_def,LET_DEF,word_tree_def]
      \\ Q.ABBREV_TAC `vv = if u' then 1 + l else 1`
      \\ `8 * i' < 2**32 /\ vv <> 0` by
        (Cases_on `u'` \\ Q.UNABBREV_TAC `vv`
         \\ FULL_SIMP_TAC std_ss [IN_DEF,RANGE_def] \\ DECIDE_TAC)
      \\ FULL_SIMP_TAC std_ss []
      \\ METIS_TAC [SIMP_RULE std_ss [] IN_ch_active_set3])
  \\ FULL_SIMP_TAC std_ss [FST,MAP]);

val ch_tree_alloc_lemma = prove(
  ``ch_tree (t1,t2,t3,t4,t5,t6,l) (v1,v2,v3,v4,v5,v6,a,dm,m,b,k) ==>
    ch_arm2
     ([(fresh (build_heap (k,b,a,m)),SND (heap_el a v1)); heap_el a v2;
       heap_el a v3; heap_el a v4; heap_el a v5; heap_el a v6],
      build_heap (k,b,a,m) |+
      (fresh (build_heap (k,b,a,m)),FST (heap_el a v1),
       FST (heap_el a v2),SND (heap_el a v1),SND (heap_el a v2)),l,i,u)
     (w1,w2,w3,w4,w5,w6,a,dm,xs') ==>
    ?b k. ch_tree (XDot t1 t2,t2,t3,t4,t5,t6,l) (w1,w2,w3,w4,w5,w6,a,dm,xs',b,k)``,
  REPEAT STRIP_TAC
  \\ SIMP_TAC std_ss [ch_tree_def,LET_DEF]
  \\ Q.EXISTS_TAC `i` \\ Q.EXISTS_TAC `u`
  \\ REV_STRIP_TAC THEN1
   (FULL_SIMP_TAC std_ss [ch_arm2_def]
    \\ Q.PAT_X_ASSUM `ch_inv xxx yyy` (K ALL_TAC)
    \\ FULL_SIMP_TAC std_ss [ch_word_def]
    \\ REPEAT (Q.PAT_X_ASSUM `ww = ref_field a (xx,yy)` (K ALL_TAC))
    \\ POP_ASSUM MP_TAC
    \\ NTAC 6 (POP_ASSUM (K ALL_TAC))
    \\ NTAC 3 STRIP_TAC
    \\ FULL_SIMP_TAC std_ss [ok_state_def,LET_DEF]
    \\ Q.ABBREV_TAC `v = if u then 1 + l else 1`
    \\ `8 * i < 2 ** 32 /\ v <> 0` by
      (Cases_on `u` \\ Q.UNABBREV_TAC `v`
       \\ FULL_SIMP_TAC std_ss [] \\ DECIDE_TAC)
    \\ IMP_RES_TAC IN_ch_active_set
    \\ `?j. j <> 0 /\ 8 * j < 2 ** 32 /\ (w - a = 0x8w * n2w j)` by
         METIS_TAC [IN_ch_active_set2]
    \\ FULL_SIMP_TAC std_ss [WORD_EQ_SUB_LADD,word_mul_n2w]
    \\ FULL_SIMP_TAC (std_ss++SIZES_ss) [w2n_n2w, RW1 [MULT_COMM] MULT_DIV]
    \\ RES_TAC
    \\ FULL_SIMP_TAC std_ss [ref_cheney_def,ALIGNED_INTRO]
    \\ `j <= l + l + 1` by
      (Cases_on `u` \\ Q.UNABBREV_TAC `v`
       \\ FULL_SIMP_TAC std_ss [IN_DEF,RANGE_def] \\ DECIDE_TAC)
    \\ RES_TAC
    \\ Q.PAT_X_ASSUM `ref_mem j xxx (a,yyy)` MP_TAC
    \\ Cases_on `d'`
    \\ ASM_REWRITE_TAC [ref_mem_def]
    \\ FULL_SIMP_TAC std_ss [ref_addr_def,WORD_EQ_SUB_RADD]
    \\ SIMP_TAC std_ss [AC WORD_ADD_ASSOC WORD_ADD_COMM]
    \\ REPEAT STRIP_TAC
    \\ MATCH_MP_TAC ok_data_ref_field
    \\ FULL_SIMP_TAC std_ss [SUBSET0_DEF,INSERT_SUBSET,EMPTY_SUBSET])
  \\ REV_STRIP_TAC THEN1
   (MATCH_MP_TAC (GEN_ALL IMP_word_tree) \\ IMP_RES_TAC ch_arm2_swap6
    \\ IMP_RES_TAC ch_tree_swap \\ METIS_TAC [])
  \\ REV_STRIP_TAC THEN1
   (MATCH_MP_TAC (GEN_ALL IMP_word_tree) \\ IMP_RES_TAC ch_arm2_swap5
    \\ IMP_RES_TAC ch_tree_swap \\ METIS_TAC [])
  \\ REV_STRIP_TAC THEN1
   (MATCH_MP_TAC (GEN_ALL IMP_word_tree) \\ IMP_RES_TAC ch_arm2_swap4
    \\ IMP_RES_TAC ch_tree_swap \\ METIS_TAC [])
  \\ REV_STRIP_TAC THEN1
   (MATCH_MP_TAC (GEN_ALL IMP_word_tree) \\ IMP_RES_TAC ch_arm2_swap3
    \\ IMP_RES_TAC ch_tree_swap \\ METIS_TAC [])
  \\ REV_STRIP_TAC THEN1
   (MATCH_MP_TAC (GEN_ALL IMP_word_tree) \\ IMP_RES_TAC ch_arm2_swap2
    \\ IMP_RES_TAC ch_tree_swap \\ METIS_TAC [])
  \\ REVERSE REV_STRIP_TAC THEN1
   (FULL_SIMP_TAC std_ss [ch_arm2_def,ch_word_def,ref_addr_def,
      ALIGNED_INTRO,ch_tree_def,LET_DEF,ok_state_def]
    \\ Cases_on `u` \\ FULL_SIMP_TAC std_ss [] \\ DECIDE_TAC)
  \\ SIMP_TAC std_ss [word_tree_def]
  \\ Q.ABBREV_TAC `f = fresh (build_heap (k,b,a,m))`
  \\ Q.ABBREV_TAC `xx = (FST (heap_el a v1),FST (heap_el a v2),SND (heap_el a v1),
          SND (heap_el a v2))`
  \\ Q.ABBREV_TAC `hh = build_heap (k,b,a,m) |+ (f,xx)`
  \\ `(FST (f,SND (heap_el a v1))) IN FDOM hh /\
      (hh ' (FST (f,SND (heap_el a v1))) = xx)` by
   (Q.UNABBREV_TAC `hh`
    \\ ASM_SIMP_TAC std_ss [FDOM_FUPDATE,IN_INSERT,FAPPLY_FUPDATE_THM,FST])
  \\ Q.UNABBREV_TAC `xx`
  \\ IMP_RES_TAC ch_arm2_CDR
  \\ IMP_RES_TAC ch_arm2_CAR
  \\ FULL_SIMP_TAC std_ss []
  \\ REV_STRIP_TAC THEN1
   (MATCH_MP_TAC (GEN_ALL IMP_word_tree) \\ IMP_RES_TAC ch_arm2_swap2
    \\ IMP_RES_TAC ch_tree_swap \\ METIS_TAC [])
  \\ MATCH_MP_TAC (GEN_ALL IMP_word_tree) \\ METIS_TAC []);

val ch_tree_alloc = store_thm("ch_tree_alloc",
  ``ch_tree (t1,t2,t3,t4,t5,t6,l) (v1,v2,v3,v4,v5,v6,a,dm,m,b,k) ==>
    (arm_alloc (v1,v2,v3,v4,v5,v6,a,dm,m) = (w1,w2,w3,w4,w5,w6,a2,dm2,m2)) ==>
    XSIZE t1 + XSIZE t2 + XSIZE t3 + XSIZE t4 + XSIZE t5 + XSIZE t6 < l ==>
    (a2 = a) /\ (dm2 = dm) /\
    arm_alloc_pre (v1,v2,v3,v4,v5,v6,a,dm,m) /\
    ?b k. ch_tree (XDot t1 t2,t2,t3,t4,t5,t6,l) (w1,w2,w3,w4,w5,w6,a2,dm2,m2,b,k)``,
  REPEAT STRIP_TAC \\ IMP_RES_TAC ch_arm_setup
  \\ IMP_RES_TAC ch_arm_IMP_ch_arm2
  \\ Q.PAT_X_ASSUM `a2 = a` (fn th => FULL_SIMP_TAC std_ss [th])
  \\ Q.PAT_X_ASSUM `dm2 = dm` (fn th => FULL_SIMP_TAC std_ss [th])
  \\ IMP_RES_TAC ch_tree_alloc_lemma \\ METIS_TAC []);


(* --- PowerPC --- *)

val (th,def,pre) = compile "ppc" ``
  ppc_move (r4:word32,r5:word32,r7:word32,r8:word32,df:word32 set,f:word32->word32) =
    (if r5 && 3w = 0x0w then
       (let r7 = f r5 in
        let r8 = r7 && 3w in
          (if r8 = 0x1w then
             (let r5 = r7 - 0x1w in (r4,r5,r7,r8,df,f))
           else
             (let r8 = f (r5 + 0x4w) in
              let f = (r4 =+ r7) f in
              let r4 = r4 + 0x4w in
              let f = (r4 =+ r8) f in
              let r4 = r4 + 0x4w in
              let r7 = r4 - 0x7w in
              let f = (r5 =+ r7) f in
              let r5 = r7 - 0x1w in
                (r4,r5,r7,r8,df,f))))
     else
       (r4,r5,r7,r8,df,f))``

val (th,def,pre) = compile "ppc" ``
  ppc_move2 (r4:word32,r6:word32,r7:word32,r8:word32,df:word32 set,f:word32->word32) =
    (if r6 && 0x3w = 0x0w then
       (let r7 = f r6 in
        let r8 = 0x3w && r7 in
          (if r8 = 0x1w then
             (let r6 = r7 - 0x1w in (r4,r6,r7,r8,df,f))
           else
             (let r8 = f (r6 + 0x4w) in
              let f = (r4 =+ r7) f in
              let r4 = r4 + 0x4w in
              let f = (r4 =+ r8) f in
              let r4 = r4 + 0x4w in
              let r7 = r4 - 0x7w in
              let f = (r6 =+ r7) f in
              let r6 = r7 - 0x1w in
                (r4,r6,r7,r8,df,f))))
     else
       (r4,r6,r7,r8,df,f))``

val (th,def,pre) = compile "ppc" ``
  ppc_cheney_step (r3:word32,r4:word32,r7:word32,r8:word32,df:word32 set,f:word32->word32) =
    (let r5 = f r3 in
     let r6 = f (r3 + 0x4w) in
     let (r4,r5,r7,r8,df,f) = ppc_move (r4,r5,r7,r8,df,f) in
     let (r4,r6,r7,r8,df,f) = ppc_move2 (r4,r6,r7,r8,df,f) in
     let f = (r3 =+ r5) f in
     let r3 = r3 + 0x4w in
     let f = (r3 =+ r6) f in
     let r3 = r3 + 0x4w in
       (r3,r4,r5,r6,r7,r8,df,f))``;

val (th,def,pre) = compile "ppc" ``
  ppc_cheney_loop (r3,r4,r5,r6,r7,r8,df,f) =
    (if r3 = r4 then
       (r3,r4,r5,r6,r7,r8,df,f)
     else
       (let (r3,r4,r5,r6,r7,r8,df,f) = ppc_cheney_step (r3,r4,r7,r8,df,f) in
          ppc_cheney_loop (r3,r4,r5,r6,r7,r8,df,f)))``;

val (th,def,pre) = compile "ppc" ``
  ppc_move_roots (r4,r5,r6:word32,r7,r8,r9,df,f) =
    (if r6 = 0x0w then
       (r4,r5,r6,r7,r8,r9,df,f)
     else
       (let r5 = f r9 in
        let (r4,r5,r7,r8,df,f) = ppc_move (r4,r5,r7,r8,df,f) in
        let r6 = r6 - 0x1w in
        let f = (r9 =+ r5) f in
        let r9 = r9 + 0x4w in
          ppc_move_roots (r4,r5,r6,r7,r8,r9,df,f)))``

val (th,def,pre) = compile "ppc" ``
  ppc_c_init (r5:word32,r6:word32,r9:word32) =
    let r3 = r9 + 0x8w in
       if r5 = 0x1w then
          let r5 = r5 ?? 0x1w in
          let r3 = r3 + r6 in (r3,r5,r6,r9)
        else
          let r5 = r5 ?? 0x1w in (r3,r5,r6,r9)``

val (th,def,pre) = compile "ppc" ``
  ppc_collect (r7,r8,r9,df,f) =
    (let r5 = f (r9 - 0x1Cw) in
     let r6 = f (r9 - 0x20w) in
     let (r3,r5,r6,r9) = ppc_c_init (r5,r6,r9) in
     let f = (r9 - 0x1Cw =+ r5) f in
     let r5 = r3 + r6 in
     let r4 = r3 in
     let f = (r9 + 0x4w =+ r5) f in
     let r6 = 0x6w in
     let r9 = r9 - 0x18w in
     let (r4,r5,r6,r7,r8,r9,df,f) = ppc_move_roots (r4,r5,r6,r7,r8,r9,df,f) in
     let (r3,r4,r5,r6,r7,r8,df,f) = ppc_cheney_loop (r3,r4,r5,r6,r7,r8,df,f) in
     let r4 = f (r9 + 0x4w) in
       (r3,r4,r5,r6,r7,r8,r9,df,f))``;

val (th,def,pre) = compile "ppc" ``
  ppc_alloc_aux (r3,r4,r5,r6,r7,r8,r9,df,f) =
    (if r3 = r4 then
       (let (r3,r4,r5,r6,r7,r8,r9,df,f) = ppc_collect (r7,r8,r9,df,f) in
          (r3,r4,r5,r6,r7,r8,r9,df,f))
     else
       (r3,r4,r5,r6,r7,r8,r9,df,f))``;

val (th,def,pre) = compile "ppc" ``
  ppc_alloc_aux2 (r3:word32,r4:word32,r9:word32,df:word32 set,f:word32->word32) =
    (let r7 = f (r9 - 0x18w) in
     let r8 = f (r9 - 0x14w) in
       (if r3 = r4 then
          (let r7 = 0x2w in
           let f = (r9 - 0x18w =+ r7) f in
           let f = (r9 =+ r3) f in (r3,r4,r7,r8,r9,df,f))
        else
          (let f = (r9 - 0x18w =+ r3) f in
           let f = (r3 =+ r7) f in
           let r3 = r3 + 0x4w in
           let f = (r3 =+ r8) f in
           let r3 = r3 + 0x4w in
           let f = (r9 =+ r3) f in
             (r3,r4,r7,r8,r9,df,f))))``;

val (th,def,pre) = compile "ppc" ``
  ppc_alloc_mem (r5,r6,r7,r8,r9,df,f) =
    (let r3 = f r9 in
     let r4 = f (r9 + 0x4w) in
     let (r3,r4,r5,r6,r7,r8,r9,df,f) = ppc_alloc_aux (r3,r4,r5,r6,r7,r8,r9,df,f) in
     let (r3,r4,r7,r8,r9,df,f) = ppc_alloc_aux2 (r3,r4,r9,df,f) in
       (r3,r4,r5,r6,r7,r8,r9,df,f))``;

val (th,def,pre) = compile "ppc" ``
  ppc_alloc (r3,r4,r5,r6,r7,r8,r9,df,f) =
     let f = (r9 - 0x18w =+ r3) f in
     let f = (r9 - 0x14w =+ r4) f in
     let f = (r9 - 0x10w =+ r5) f in
     let f = (r9 - 0xCw =+ r6) f in
     let f = (r9 - 0x8w =+ r7) f in
     let f = (r9 - 0x4w =+ r8) f in
     let (r3,r4,r5,r6,r7,r8,r9,df,f) = ppc_alloc_mem (r5,r6,r7,r8,r9,df,f) in
     let r3 = f (r9 - 0x18w) in
     let r4 = f (r9 - 0x14w) in
     let r5 = f (r9 - 0x10w) in
     let r6 = f (r9 - 0xCw) in
     let r7 = f (r9 - 0x8w) in
     let r8 = f (r9 - 0x4w) in
       (r3,r4,r5,r6,r7,r8,r9,df,f)``;

val ppc_alloc_thm = save_thm("ppc_alloc_thm",th)


(* --- x86 --- *)

val (th,def,pre) = compile "x86" ``
  x86_move (r1:word32,r2:word32,r4:word32,r5:word32,df:word32 set,f:word32->word32) =
    (if r2 && 3w = 0x0w then
       (let r4 = f r2 in
        let r5 = r4 && 3w in
          (if r5 = 0x1w then
             (let r2 = r4 - 0x1w in (r1,r2,r4,r5,df,f))
           else
             (let r5 = f (r2 + 0x4w) in
              let f = (r1 =+ r4) f in
              let r1 = r1 + 0x4w in
              let f = (r1 =+ r5) f in
              let r1 = r1 + 0x4w in
              let r4 = r1 - 0x7w in
              let f = (r2 =+ r4) f in
              let r2 = r4 - 0x1w in
                (r1,r2,r4,r5,df,f))))
     else
       (r1,r2,r4,r5,df,f))``

val (th,def,pre) = compile "x86" ``
  x86_move2 (r1:word32,r3:word32,r4:word32,r5:word32,df:word32 set,f:word32->word32) =
    (if r3 && 0x3w = 0x0w then
       (let r4 = f r3 in
        let r5 = 0x3w && r4 in
          (if r5 = 0x1w then
             (let r3 = r4 - 0x1w in (r1,r3,r4,r5,df,f))
           else
             (let r5 = f (r3 + 0x4w) in
              let f = (r1 =+ r4) f in
              let r1 = r1 + 0x4w in
              let f = (r1 =+ r5) f in
              let r1 = r1 + 0x4w in
              let r4 = r1 - 0x7w in
              let f = (r3 =+ r4) f in
              let r3 = r4 - 0x1w in
                (r1,r3,r4,r5,df,f))))
     else
       (r1,r3,r4,r5,df,f))``

val (th,def,pre) = compile "x86" ``
  x86_cheney_step (r0:word32,r1:word32,r4:word32,r5:word32,df:word32 set,f:word32->word32) =
    (let r2 = f r0 in
     let r3 = f (r0 + 0x4w) in
     let (r1,r2,r4,r5,df,f) = x86_move (r1,r2,r4,r5,df,f) in
     let (r1,r3,r4,r5,df,f) = x86_move2 (r1,r3,r4,r5,df,f) in
     let f = (r0 =+ r2) f in
     let r0 = r0 + 0x4w in
     let f = (r0 =+ r3) f in
     let r0 = r0 + 0x4w in
       (r0,r1,r2,r3,r4,r5,df,f))``;

val (th,def,pre) = compile "x86" ``
  x86_cheney_loop (r0,r1,r2,r3,r4,r5,df,f) =
    (if r0 = r1 then
       (r0,r1,r2,r3,r4,r5,df,f)
     else
       (let (r0,r1,r2,r3,r4,r5,df,f) = x86_cheney_step (r0,r1,r4,r5,df,f) in
          x86_cheney_loop (r0,r1,r2,r3,r4,r5,df,f)))``;

val (th,def,pre) = compile "x86" ``
  x86_move_roots (r1,r2,r3:word32,r4,r5,r6,df,f) =
    (if r3 = 0x0w then
       (r1,r2,r3,r4,r5,r6,df,f)
     else
       (let r2 = f r6 in
        let (r1,r2,r4,r5,df,f) = x86_move (r1,r2,r4,r5,df,f) in
        let r3 = r3 - 0x1w in
        let f = (r6 =+ r2) f in
        let r6 = r6 + 0x4w in
          x86_move_roots (r1,r2,r3,r4,r5,r6,df,f)))``

val (th,def,pre) = compile "x86" ``
  x86_c_init (r2:word32,r3:word32,r6:word32) =
    let r0 = r6 + 0x8w in
       if r2 = 0x1w then
          let r2 = r2 ?? 0x1w in
          let r0 = r0 + r3 in (r0,r2,r3,r6)
        else
          let r2 = r2 ?? 0x1w in (r0,r2,r3,r6)``

val (th,def,pre) = compile "x86" ``
  x86_collect (r4,r5,r6,df,f) =
    (let r2 = f (r6 - 0x1Cw) in
     let r3 = f (r6 - 0x20w) in
     let (r0,r2,r3,r6) = x86_c_init (r2,r3,r6) in
     let f = (r6 - 0x1Cw =+ r2) f in
     let r2 = r0 + r3 in
     let r1 = r0 in
     let f = (r6 + 0x4w =+ r2) f in
     let r3 = 0x6w in
     let r6 = r6 - 0x18w in
     let (r1,r2,r3,r4,r5,r6,df,f) = x86_move_roots (r1,r2,r3,r4,r5,r6,df,f) in
     let (r0,r1,r2,r3,r4,r5,df,f) = x86_cheney_loop (r0,r1,r2,r3,r4,r5,df,f) in
     let r1 = f (r6 + 0x4w) in
       (r0,r1,r2,r3,r4,r5,r6,df,f))``;

val (th,def,pre) = compile "x86" ``
  x86_alloc_aux (r0,r1,r2,r3,r4,r5,r6,df,f) =
    (if r0 = r1 then
       (let (r0,r1,r2,r3,r4,r5,r6,df,f) = x86_collect (r4,r5,r6,df,f) in
          (r0,r1,r2,r3,r4,r5,r6,df,f))
     else
       (r0,r1,r2,r3,r4,r5,r6,df,f))``;

val (th,def,pre) = compile "x86" ``
  x86_alloc_aux2 (r0:word32,r1:word32,r6:word32,df:word32 set,f:word32->word32) =
    (let r4 = f (r6 - 0x18w) in
     let r5 = f (r6 - 0x14w) in
       (if r0 = r1 then
          (let r4 = 0x2w in
           let f = (r6 - 0x18w =+ r4) f in
           let f = (r6 =+ r0) f in (r0,r1,r4,r5,r6,df,f))
        else
          (let f = (r6 - 0x18w =+ r0) f in
           let f = (r0 =+ r4) f in
           let r0 = r0 + 0x4w in
           let f = (r0 =+ r5) f in
           let r0 = r0 + 0x4w in
           let f = (r6 =+ r0) f in
             (r0,r1,r4,r5,r6,df,f))))``;

val (th,def,pre) = compile "x86" ``
  x86_alloc_mem (r2,r3,r4,r5,r6,df,f) =
    (let r0 = f r6 in
     let r1 = f (r6 + 0x4w) in
     let (r0,r1,r2,r3,r4,r5,r6,df,f) = x86_alloc_aux (r0,r1,r2,r3,r4,r5,r6,df,f) in
     let (r0,r1,r4,r5,r6,df,f) = x86_alloc_aux2 (r0,r1,r6,df,f) in
       (r0,r1,r2,r3,r4,r5,r6,df,f))``;

val (th,def,pre) = compile "x86" ``
  x86_alloc (r0,r1,r2,r3,r4,r5,r6,df,f) =
     let f = (r6 - 0x18w =+ r0) f in
     let f = (r6 - 0x14w =+ r1) f in
     let f = (r6 - 0x10w =+ r2) f in
     let f = (r6 - 0xCw =+ r3) f in
     let f = (r6 - 0x8w =+ r4) f in
     let f = (r6 - 0x4w =+ r5) f in
     let (r0,r1,r2,r3,r4,r5,r6,df,f) = x86_alloc_mem (r2,r3,r4,r5,r6,df,f) in
     let r0 = f (r6 - 0x18w) in
     let r1 = f (r6 - 0x14w) in
     let r2 = f (r6 - 0x10w) in
     let r3 = f (r6 - 0xCw) in
     let r4 = f (r6 - 0x8w) in
     let r5 = f (r6 - 0x4w) in
       (r0,r1,r2,r3,r4,r5,r6,df,f)``;

val x86_alloc_thm = save_thm("x86_alloc_thm",th)

fun prove_eq n1 n2 rw goal = prove(goal,
  STRIP_TAC \\ TAILREC_TAC \\ SIMP_TAC std_ss ([LET_DEF,word_arith_lemma1] @ rw)
  \\ SIMP_TAC std_ss [AC WORD_AND_ASSOC WORD_AND_COMM, AC WORD_ADD_ASSOC WORD_ADD_COMM]
  \\ COMPILER_TAC);

val l1 = prove_eq "x86_move" "arm_move" []
  ``(x86_move = arm_move) /\ (x86_move_pre = arm_move_pre)``;
val l2 = prove_eq "x86_move2" "arm_move2" []
  ``(x86_move2 = arm_move2) /\ (x86_move2_pre = arm_move2_pre)``;
val l3 = prove_eq "x86_cheney_step" "arm_cheney_step" [l1,l2]
  ``(x86_cheney_step = arm_cheney_step) /\ (x86_cheney_step_pre = arm_cheney_step_pre)``;
val l4 = prove_eq "x86_cheney_loop" "arm_cheney_loop" [l3]
  ``(x86_cheney_loop = arm_cheney_loop) /\ (x86_cheney_loop_pre = arm_cheney_loop_pre)``;
val l5 = prove_eq "x86_move_roots" "arm_move_roots" [l4,l1,l2,l3]
  ``(x86_move_roots = arm_move_roots) /\ (x86_move_roots_pre = arm_move_roots_pre)``;
val l6 = prove_eq "x86_c_init" "arm_c_init" [l4,l1,l2,l3]
  ``(x86_c_init = arm_c_init) /\ (x86_c_init_pre = arm_c_init_pre)``;
val l7 = prove_eq "x86_collect" "arm_collect" [l1,l2,l3,l4,l5,l6]
  ``(x86_collect = arm_collect) /\ (x86_collect_pre = arm_collect_pre)``;
val l8 = prove_eq "x86_alloc_aux" "arm_alloc_aux" [l1,l2,l3,l4,l5,l6,l7]
  ``(x86_alloc_aux = arm_alloc_aux) /\ (x86_alloc_aux_pre = arm_alloc_aux_pre)``;
val l9 = prove_eq "x86_alloc_aux2" "arm_alloc_aux2" [l1,l2,l3,l4,l5,l6,l7,l8]
  ``(x86_alloc_aux2 = arm_alloc_aux2) /\ (x86_alloc_aux2_pre = arm_alloc_aux2_pre)``;
val lA = prove_eq "x86_alloc_mem" "arm_alloc_mem" [l1,l2,l3,l4,l5,l6,l7,l8,l9]
  ``(x86_alloc_mem = arm_alloc_mem) /\ (x86_alloc_mem_pre = arm_alloc_mem_pre)``;
val lB = prove_eq "x86_alloc" "arm_alloc" [l1,l2,l3,l4,l5,l6,l7,l8,l9,lA]
  ``(x86_alloc = arm_alloc) /\ (x86_alloc_pre = arm_alloc_pre)``;

val x86_alloc_EQ = save_thm("x86_alloc_EQ",lB)

val l1 = prove_eq "ppc_move" "arm_move" []
  ``(ppc_move = arm_move) /\ (ppc_move_pre = arm_move_pre)``;
val l2 = prove_eq "ppc_move2" "arm_move2" []
  ``(ppc_move2 = arm_move2) /\ (ppc_move2_pre = arm_move2_pre)``;
val l3 = prove_eq "ppc_cheney_step" "arm_cheney_step" [l1,l2]
  ``(ppc_cheney_step = arm_cheney_step) /\ (ppc_cheney_step_pre = arm_cheney_step_pre)``;
val l4 = prove_eq "ppc_cheney_loop" "arm_cheney_loop" [l3]
  ``(ppc_cheney_loop = arm_cheney_loop) /\ (ppc_cheney_loop_pre = arm_cheney_loop_pre)``;
val l5 = prove_eq "ppc_move_roots" "arm_move_roots" [l4,l1,l2,l3]
  ``(ppc_move_roots = arm_move_roots) /\ (ppc_move_roots_pre = arm_move_roots_pre)``;
val l6 = prove_eq "ppc_c_init" "arm_c_init" [l4,l1,l2,l3]
  ``(ppc_c_init = arm_c_init) /\ (ppc_c_init_pre = arm_c_init_pre)``;
val l7 = prove_eq "ppc_collect" "arm_collect" [l1,l2,l3,l4,l5,l6]
  ``(ppc_collect = arm_collect) /\ (ppc_collect_pre = arm_collect_pre)``;
val l8 = prove_eq "ppc_alloc_aux" "arm_alloc_aux" [l1,l2,l3,l4,l5,l6,l7]
  ``(ppc_alloc_aux = arm_alloc_aux) /\ (ppc_alloc_aux_pre = arm_alloc_aux_pre)``;
val l9 = prove_eq "ppc_alloc_aux2" "arm_alloc_aux2" [l1,l2,l3,l4,l5,l6,l7,l8]
  ``(ppc_alloc_aux2 = arm_alloc_aux2) /\ (ppc_alloc_aux2_pre = arm_alloc_aux2_pre)``;
val lA = prove_eq "ppc_alloc_mem" "arm_alloc_mem" [l1,l2,l3,l4,l5,l6,l7,l8,l9]
  ``(ppc_alloc_mem = arm_alloc_mem) /\ (ppc_alloc_mem_pre = arm_alloc_mem_pre)``;
val lB = prove_eq "ppc_alloc" "arm_alloc" [l1,l2,l3,l4,l5,l6,l7,l8,l9,lA]
  ``(ppc_alloc = arm_alloc) /\ (ppc_alloc_pre = arm_alloc_pre)``;

val ppc_alloc_EQ = save_thm("ppc_alloc_EQ",lB)


val _ = export_theory();
