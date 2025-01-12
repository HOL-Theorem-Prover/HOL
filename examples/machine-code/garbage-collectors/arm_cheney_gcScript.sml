
open HolKernel boolLib bossLib Parse; val _ = new_theory "arm_cheney_gc";
val _ = ParseExtras.temp_loose_equality()

open decompilerLib prog_armLib;

open wordsTheory arithmeticTheory wordsLib listTheory pred_setTheory pairTheory;
open combinTheory finite_mapTheory addressTheory;
open mc_tailrecLib tailrecTheory;
open cheney_gcTheory; (* an abstract implementation is imported *)

val decompile_arm = decompile arm_tools;
val basic_decompile_arm = basic_decompile arm_tools;


val _ = map Parse.hide ["r0","r1","r2","r3","r4","r5","r6","r7","r8","r9","r10","r11","r12","r13"];
val RW = REWRITE_RULE;
val RW1 = ONCE_REWRITE_RULE;


val (th,def1) = decompile_arm "arm_move" `
  E3550000 (* cmp r5,#0 *)
  0A000009 (* beq L1 *)
  E5957000 (* ldr r7,[r5] *)
  E3170001 (* tst r7,#1 *)
  04847004 (* streq r7,[r4],#4 *)
  05958004 (* ldreq r8,[r5,#4] *)
  05957008 (* ldreq r7,[r5,#8] *)
  04848004 (* streq r8,[r4],#4 *)
  04847004 (* streq r7,[r4],#4 *)
  0244700B (* subeq r7,r4,#11 *)
  05857000 (* streq r7,[r5] *)
  E2475001 (* sub r5,r7,#1 *)`;

val (th,def2) = decompile_arm "arm_move2" `
  E3560000 (* cmp r6,#0 *)
  0A000009 (* beq L2 *)
  E5967000 (* ldr r7,[r6] *)
  E3170001 (* tst r7,#1 *)
  04847004 (* streq r7,[r4],#4 *)
  05968004 (* ldreq r8,[r6,#4] *)
  05967008 (* ldreq r7,[r6,#8] *)
  04848004 (* streq r8,[r4],#4 *)
  04847004 (* streq r7,[r4],#4 *)
  0244700B (* subeq r7,r4,#11 *)
  05867000 (* streq r7,[r6] *)
  E2476001 (* sub r6,r7,#1 *)`;

val (th,def3) = decompile_arm "arm_cheney_step" `
  E5935000 (* ldr r5,[r3] *)
  E5936004 (* ldr r6,[r3,#4] *)
  insert: arm_move
  insert: arm_move2
  E4835004 (* L2:str r5,[r3],#4 *)
  E4836004 (* str r6,[r3],#4 *)
  E2833004 (* add r3,r3,#4 *)`;

val (th,def4) = basic_decompile_arm "arm_cheney_loop"NONE `
  E1530004 (* CHENEY:cmp r3,r4 *)
  0A00001D (* beq EXIT *)
  insert: arm_cheney_step
  EAFFFFDF (* b CHENEY *)`;

val (th,def5) = basic_decompile_arm "arm_move_roots" NONE `
  E3560000 (* ROOTS:cmp r6,#0 *)
  0A00000F (* beq CHENEY *)
  E5995000 (* ldr r5,[r9] *)
  insert: arm_move
  E2466001 (* RL:sub r6,r6,#1 *)
  E4895004 (* str r5,[r9],#4 *)
  EAFFFFED (* b ROOTS *)`;

val (th,def6) = decompile_arm "arm_c_init" `
  E2355001 (* eors r5,r5,#1 *)    (* calc u *)
  E289300C (* add r3,r9,#12 *)    (* set i *)
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

val (th,def8) = decompile_arm "arm_alloc_gc" `
  E1530004 (* cmp r3,r4 *)
  1A00003D (* bne NO_GC *)
  insert: arm_collect`;

val (th,def9) = decompile_arm "arm_alloc_aux" `
  E5197018 (* NO_GC:ldr r7,[r9,#-24] *)
  E5198014 (* ldr r8,[r9,#-20] *)
  E3A06000 (* mov r6,#0 *)
  E1530004 (* cmp r3,r4 *)
  15093018 (* strne r3,[r9,#-24] *)
  14837004 (* strne r7,[r3],#4 *)
  14838004 (* strne r8,[r3],#4 *)
  14836004 (* strne r6,[r3],#4 *)
  03A07000 (* moveq r7,#0 *)
  05097018 (* streq r7,[r9,#-24] *)
  E5893000 (* str r3,[r9] *)`;

val (th,def10) = decompile_arm "arm_alloc_mem" `
  E5993000 (* ldr r3,[r9] *)
  E5994004 (* ldr r4,[r9,#4] *)
  insert: arm_alloc_gc
  insert: arm_alloc_aux`;

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
  (ref_addr a n = if n = 0 then 0w:word32 else a + n2w (12 * n))`;

val ref_mem_def = Define `
  (ref_mem i EMP (a,xs) = T) /\
  (ref_mem i (REF j) (a,xs) =
    (xs (ref_addr a i) = ref_addr a j + 1w)) /\
  (ref_mem i (DATA (x,y,z)) (a,xs) =
    (xs (ref_addr a i) = ref_addr a x) /\
    (xs (ref_addr a i + 4w) = ref_addr a y) /\
    (xs (ref_addr a i + 8w) = z))`;

val valid_address_def = Define `
  valid_address a i = w2n a + 12 * i + 8 < 2**32`;

val ref_set_def = Define `
  ref_set a f = { a + n2w (4 * i) | i <= 3 * f + 2 } UNION { a - n2w (4 * i) | i <= 9 }`;

val ref_cheney_def = Define `
  ref_cheney (m,e) (a,d,xs,ys) =
    ~(a = 0w) /\ (a && 3w = 0w) /\ (!i. i <= e ==> ref_mem i (m i) (a,xs)) /\
    (m 0 = EMP) /\ valid_address a e /\ (!i. i <+ ref_addr a 1 ==> (xs i = ys i)) /\
    (ref_set a e = d)`;

val ref_addr_NOT_ZERO = prove(
  ``!a. ref_cheney (m,e) (a,d,xs,ys) /\ x <= e /\ ~(x = 0) ==> ~(ref_addr a x = 0w)``,
  Cases_word \\ FULL_SIMP_TAC (std_ss++SIZES_ss) [ref_cheney_def,ref_addr_def,
    word_add_n2w,n2w_11,valid_address_def,w2n_n2w] \\ REPEAT STRIP_TAC
  \\ `(n + 12 * x) < 4294967296` by DECIDE_TAC
  \\ `n + 12 * x = 0` by METIS_TAC [LESS_MOD] \\ DECIDE_TAC);

val ref_addr_NEQ = store_thm("ref_addr_NEQ",
  ``!a i j. ~(i = j) /\ valid_address a i /\ valid_address a j ==>
            ~(ref_addr a i = ref_addr a j)``,
  Cases_word \\ Cases \\ Cases
  \\ SIMP_TAC std_ss [ref_addr_def,valid_address_def,word_add_n2w]
  \\ ASM_SIMP_TAC (std_ss++SIZES_ss) [w2n_n2w,LESS_MOD,n2w_11,DECIDE ``~(SUC n = 0)``]
  \\ STRIP_TAC \\ IMP_RES_TAC (DECIDE ``m + n + 8 < l ==> m + n + 4 < l /\ m + n < l``)
  \\ ASM_SIMP_TAC bool_ss [LESS_MOD] \\ DECIDE_TAC);

val ref_addr_ADD_NEQ = store_thm("ref_addr_ADD_NEQ",
  ``!a i j. valid_address a i /\ valid_address a j ==>
            ~(ref_addr a i + 4w = ref_addr a j) /\
            ~(ref_addr a i + 8w = ref_addr a j) /\
            ~(ref_addr a i + 4w = ref_addr a j + 8w)``,
  Cases_word \\ Cases \\ Cases
  \\ ASM_SIMP_TAC (std_ss++SIZES_ss) [ref_addr_def,word_add_n2w,n2w_11,LESS_MOD,valid_address_def,w2n_n2w,DECIDE ``~(SUC n = 0)``]
  \\ STRIP_TAC \\ IMP_RES_TAC (DECIDE ``m + n + 8 < l ==> m + n + 4 < l /\ m + n < l``)
  \\ ASM_SIMP_TAC bool_ss [LESS_MOD,MULT_CLAUSES]
  THEN1 DECIDE_TAC THEN1 DECIDE_TAC
  \\ FULL_SIMP_TAC std_ss [EQ_ADD_LCANCEL,GSYM ADD_ASSOC] \\ REPEAT STRIP_TAC
  \\ IMP_RES_TAC (METIS_PROVE [] ``(m = n) ==> (m MOD 12 = n MOD 12)``)
  \\ FULL_SIMP_TAC std_ss [RW1 [MULT_COMM] (CONJ MOD_TIMES MOD_EQ_0)]);

val ALIGNED_ref_addr = store_thm("ALIGNED_ref_addr",
  ``!n a. ALIGNED a ==> ALIGNED (ref_addr a n)``,
  Cases \\ REWRITE_TAC [ref_addr_def,ALIGNED_def] THEN1 (STRIP_TAC \\ EVAL_TAC)
  \\ REWRITE_TAC [GSYM ALIGNED_def,GSYM (EVAL ``4 * 3``),GSYM word_mul_n2w,DECIDE ``~(SUC n = 0)``]
  \\ SIMP_TAC bool_ss [ALIGNED_MULT,GSYM WORD_MULT_ASSOC]);

val ref_cheney_ALIGNED = prove(
  ``ref_cheney (m,f) (a,d,xs,ys) ==> (ref_addr a x && 3w = 0w)``,
  METIS_TAC [ALIGNED_def,ALIGNED_ref_addr,ref_cheney_def]);

val ref_cheney_d = store_thm("ref_cheney_d",
  ``ref_cheney (m,f) (a,d,xs,ys) /\ ~(x = 0) /\ x <= f ==>
    ref_addr a x IN d /\ ref_addr a x + 4w IN d /\ ref_addr a x + 8w IN d``,
  REWRITE_TAC [ref_cheney_def] \\ REPEAT STRIP_TAC
  \\ Q.PAT_X_ASSUM `ref_set a f = d` (ASSUME_TAC o GSYM)
  \\ ASM_SIMP_TAC bool_ss [ref_set_def,GSPECIFICATION,IN_UNION,ref_addr_def]
  \\ DISJ1_TAC
  THENL [Q.EXISTS_TAC `3*x`,Q.EXISTS_TAC `3*x+1`,Q.EXISTS_TAC `3*x+2`]
  \\ ASM_SIMP_TAC std_ss [MULT_ASSOC,LEFT_ADD_DISTRIB,
      GSYM word_add_n2w,WORD_ADD_ASSOC] \\ DECIDE_TAC);

fun UPDATE_ref_addr_prove (c,tm) = prove(tm,
  Cases \\ Cases_word \\ REPEAT STRIP_TAC
  \\ sg c \\ ASM_REWRITE_TAC [APPLY_UPDATE_THM]
  \\ FULL_SIMP_TAC std_ss [ref_addr_def,EVAL ``1=0``,word_add_n2w,valid_address_def,
      w2n_n2w,n2w_11,WORD_LO]
  \\ Q.PAT_X_ASSUM `n < dimword (:32)` ASSUME_TAC
  \\ Q.PAT_X_ASSUM `n' < dimword (:32)` ASSUME_TAC
  \\ FULL_SIMP_TAC (std_ss++SIZES_ss) [LESS_MOD]
  \\ `n' + 12 * x < 4294967296` by DECIDE_TAC
  \\ `n' + 12 * x + 4 < 4294967296` by DECIDE_TAC
  \\ `n' + 12 < 4294967296` by DECIDE_TAC
  \\ FULL_SIMP_TAC (std_ss++SIZES_ss) [LESS_MOD] \\ DECIDE_TAC);

val UPDATE_ref_addr = UPDATE_ref_addr_prove(`~(ref_addr (n2w n') x = (n2w n))`,
  ``!i a. valid_address a x /\
          ~(x=0) /\ i <+ ref_addr a 1 /\ (xs i = ys i) ==> ((ref_addr a x =+ y) xs i = ys i)``);

val UPDATE_ref_addr4 = UPDATE_ref_addr_prove(`~(ref_addr (n2w n') x + 4w = (n2w n))`,
  ``!i a. valid_address a x /\
          ~(x=0) /\ i <+ ref_addr a 1 /\ (xs i = ys i) ==> ((ref_addr a x + 4w =+ y) xs i = ys i)``);

val UPDATE_ref_addr8 = UPDATE_ref_addr_prove(`~(ref_addr (n2w n') x + 8w = (n2w n))`,
  ``!i a. valid_address a x /\
          ~(x=0) /\ i <+ ref_addr a 1 /\ (xs i = ys i) ==> ((ref_addr a x + 8w =+ y) xs i = ys i)``);

val va_IMP = store_thm("va_IMP",
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
  \\ ASM_SIMP_TAC bool_ss [] \\ Cases_on `p` \\ Cases_on `r`
  \\ FULL_SIMP_TAC std_ss [ref_mem_def] \\ METIS_TAC [ref_addr_ADD_NEQ]);

val ref_cheney_move_lemma = prove(
  ``ref_cheney (m,e) (a,d,xs,ys) /\ (~(x = 0) ==> ~(m x = EMP)) /\ (!x. ~(m x = REF 0)) /\
    (move(x,j,m) = (x1,j1,m1)) /\ ~(j = 0) /\ j <= e /\ x <= e /\
    (arm_move(ref_addr a j,ref_addr a x,r7,r8,d,xs) = (j2,x2,r7_2,r8_2,d2,xs2)) ==>
    ref_cheney (m1,e) (a,d,xs2,ys) /\ (x2 = ref_addr a x1) /\ (j2 = ref_addr a j1) /\ (d2 = d) /\
    arm_move_pre(ref_addr a j,ref_addr a x,r7,r8, d, xs)``,
  REWRITE_TAC [move_def] \\ Cases_on `x = 0` THEN1
   (ASM_SIMP_TAC std_ss [ref_addr_def] \\ REWRITE_TAC [def1]
    \\ SIMP_TAC std_ss [] \\ ONCE_REWRITE_TAC [EQ_SYM_EQ]
    \\ SIMP_TAC std_ss [ref_addr_def])
  \\ Cases_on `x <= e` \\ ASM_SIMP_TAC bool_ss []
  \\ SIMP_TAC std_ss [GSYM AND_IMP_INTRO] \\ STRIP_TAC
  \\ `~(ref_addr a x = 0w)` by METIS_TAC [ref_addr_NOT_ZERO]
  \\ Cases_on `m x` \\ ASM_SIMP_TAC bool_ss [isREF_def,heap_type_11] THEN1
     (REWRITE_TAC [getREF_def]
      \\ ONCE_REWRITE_TAC [EQ_SYM_EQ] \\ SIMP_TAC std_ss []
      \\ REWRITE_TAC [def1]
      \\ SIMP_TAC std_ss [LET_DEF,GSYM AND_IMP_INTRO] \\ NTAC 2 STRIP_TAC
      \\ ASM_SIMP_TAC std_ss []
      \\ `~(xs (ref_addr a x) && 1w = 0w)` by (
        FULL_SIMP_TAC bool_ss [ref_cheney_def,ref_mem_def]
        \\ `ref_mem x (REF n) (a,xs)` by METIS_TAC []
        \\ FULL_SIMP_TAC bool_ss [ref_cheney_def,ref_mem_def]
        \\ MATCH_MP_TAC ALIGNED_add_1_and_1
        \\ MATCH_MP_TAC ALIGNED_ref_addr
        \\ ASM_REWRITE_TAC [ALIGNED_def])
      \\ ASM_SIMP_TAC std_ss []
      \\ `ref_mem x (REF n) (a,xs)` by METIS_TAC [ref_cheney_def]
      \\ FULL_SIMP_TAC std_ss [ref_mem_def,WORD_ADD_SUB]
      \\ IMP_RES_TAC ref_cheney_d \\ IMP_RES_TAC ref_cheney_ALIGNED
      \\ ASM_SIMP_TAC bool_ss [INSERT_SUBSET,EMPTY_SUBSET,ALIGNED_def])
  \\ SIMP_TAC std_ss [heap_type_distinct]
  \\ ONCE_REWRITE_TAC [EQ_SYM_EQ] \\ SIMP_TAC std_ss []
  \\ REWRITE_TAC [def1]
  \\ SIMP_TAC std_ss [LET_DEF]
  \\ `~(m x = EMP)` by METIS_TAC [heap_type_distinct]
  \\ `valid_address a x` by METIS_TAC [ref_cheney_def,va_IMP]
  \\ ASM_SIMP_TAC std_ss [word_arith_lemma1,WORD_ADD_SUB]
  \\ `(xs (ref_addr a x) && 1w = 0w)` by
       (FULL_SIMP_TAC bool_ss [ref_cheney_def] \\ Cases_on `p` \\ Cases_on `r`
        \\ `ref_mem x (DATA (q,q',r')) (a,xs)` by METIS_TAC []
        \\ FULL_SIMP_TAC bool_ss [ref_mem_def]
        \\ MATCH_MP_TAC ALIGNED_and_1 \\ MATCH_MP_TAC ALIGNED_ref_addr
        \\ ASM_REWRITE_TAC [ALIGNED_def])
  \\ FULL_SIMP_TAC std_ss [PAIR_EQ,WORD_ADD_0,word_arith_lemma4]
  \\ NTAC 4 STRIP_TAC
  \\ `~(j = 0)` by METIS_TAC []
  \\ IMP_RES_TAC ref_cheney_d \\ IMP_RES_TAC ref_cheney_ALIGNED
  \\ ASM_SIMP_TAC bool_ss []
  \\ REVERSE (STRIP_TAC \\ STRIP_TAC) THEN1
   (FULL_SIMP_TAC std_ss [GSYM ALIGNED_def,ALIGNED_CLAUSES,
      SIMP_RULE std_ss [word_mul_n2w] (Q.SPEC `2w` ALIGNED_CLAUSES)]
    \\ ASM_SIMP_TAC std_ss [ref_addr_def,LEFT_ADD_DISTRIB,GSYM word_add_n2w,WORD_ADD_ASSOC])
  \\ MATCH_MP_TAC ref_cheney_update_REF \\ ASM_SIMP_TAC bool_ss []
  \\ Cases_on `p` \\ Cases_on `r` \\ FULL_SIMP_TAC std_ss [ref_cheney_def]
  \\ REVERSE (REPEAT STRIP_TAC)
  THEN1
    (`valid_address a j` by METIS_TAC [va_IMP]
     \\ MATCH_MP_TAC UPDATE_ref_addr8 \\ ASM_SIMP_TAC bool_ss []
     \\ MATCH_MP_TAC UPDATE_ref_addr4 \\ ASM_SIMP_TAC bool_ss []
     \\ MATCH_MP_TAC UPDATE_ref_addr \\ ASM_SIMP_TAC bool_ss [])
  THEN1 ASM_SIMP_TAC std_ss [UPDATE_def]
  \\ `ref_mem x (DATA (q,q',r')) (a,xs)` by METIS_TAC []
  \\ Cases_on `i = j`
  THEN1 (FULL_SIMP_TAC bool_ss [UPDATE_def,ref_mem_def,WORD_EQ_ADD_LCANCEL,
         RW[WORD_ADD_0](Q.SPECL[`x`,`y`,`0w`]WORD_EQ_ADD_LCANCEL)]
       \\ SIMP_TAC (std_ss++SIZES_ss) [n2w_11]
       \\ IMP_RES_TAC va_IMP
       \\ IMP_RES_TAC ref_addr_ADD_NEQ \\ ASM_SIMP_TAC std_ss []
       \\ METIS_TAC [])
  \\ `ref_mem i (m i) (a,xs)` by METIS_TAC []
  \\ CONV_TAC (RATOR_CONV (SIMP_CONV std_ss [UPDATE_def]))
  \\ ASM_SIMP_TAC bool_ss []
  \\ Cases_on `m i`
  \\ FULL_SIMP_TAC bool_ss [ref_mem_def,UPDATE_def]
  \\ `~(ref_addr a j = ref_addr a i)` by METIS_TAC [va_IMP,ref_addr_NEQ]
  \\ RES_TAC \\ `valid_address a i /\ valid_address a j` by METIS_TAC [va_IMP]
  \\ ASM_SIMP_TAC bool_ss [ref_addr_ADD_NEQ]
  \\ Cases_on `p` \\ Cases_on `r`
  \\ FULL_SIMP_TAC bool_ss [ref_mem_def,UPDATE_def,ref_addr_ADD_NEQ,WORD_EQ_ADD_RCANCEL]);

val ref_cheney_move = prove(
  ``!a b b' i j j2 j3 e m m2 w ww r x xj2 xx2 xs xs2 d x2 xx  r7 r8 r7_2 r8_2 d2.
    cheney_inv (b,b',i,j,j3,e,f,m,w,ww,r) /\ {x} SUBSET0 DR0(ICUT(b,e)m) /\
    ref_cheney (m,f) (a,d,xs,ys) /\ (move(x,j,m) = (x2,j2,m2)) /\
    (arm_move(ref_addr a j,ref_addr a x,r7,r8, d, xs) = (xj2,xx2,r7_2,r8_2,d2,xs2)) ==>
    cheney_inv(b,b',i,j2,j3,e,f,m2,w,ww,r) /\ {x2} SUBSET0 RANGE(b,j2) /\ j <= j2 /\
    (CUT(b,j)m = CUT(b,j)m2) /\ (DR0 (ICUT(b,e)m) = DR0 (ICUT(b,e)m2)) /\
    ref_cheney (m2,f) (a,d,xs2,ys) /\
    (ref_addr a x2 = xx2) /\ (ref_addr a j2 = xj2) /\ (d = d2) /\
    arm_move_pre(ref_addr a j,ref_addr a x, r7,r8, d, xs)``,
  NTAC 27 STRIP_TAC \\ `~(x = 0) ==> ~(m x = EMP)` by (STRIP_TAC
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
  \\ `?x1 y1 d1. getDATA (m i) = (x1,y1,d1)` by METIS_TAC [PAIR]
  \\ `?x2 j2 m2. move(x1,j,m) = (x2,j2,m2)` by METIS_TAC [PAIR]
  \\ `?y3 j3 m3. move(y1,j2,m2) = (y3,j3,m3)` by METIS_TAC [PAIR]
  \\ `(xs (ref_addr a i) = r51) /\ (xs (ref_addr a i + 4w) = r61)` by METIS_TAC []
  \\ ASM_SIMP_TAC std_ss [LET_DEF,arm_move2_thm,GSYM AND_IMP_INTRO]
  \\ ONCE_REWRITE_TAC [EQ_SYM_EQ] \\ SIMP_TAC bool_ss []
  \\ REPEAT (MATCH_MP_TAC (METIS_PROVE [] ``P ==> (Q ==> P)``))
  \\ `~(i = 0) /\ ~(j = 0) /\ (j <= e)` by
       (FULL_SIMP_TAC bool_ss [cheney_inv_def] \\ DECIDE_TAC)
  \\ `ref_addr a (i + 1) = ref_addr a i + 12w` by
   (ASM_SIMP_TAC std_ss [ref_addr_def,GSYM ADD1,MULT_CLAUSES,GSYM word_add_n2w]
    \\ SIMP_TAC bool_ss [AC WORD_ADD_ASSOC WORD_ADD_COMM])
  \\ ASM_SIMP_TAC bool_ss []
  \\ `?ax ay ad. m i = DATA(ax,ay,ad)` by METIS_TAC [m_DATA,PAIR]
  \\ `(x1,y1,d1') = (ax,ay,ad)` by METIS_TAC [getDATA_def]
  \\ FULL_SIMP_TAC bool_ss [PAIR_EQ]
  \\ Q.PAT_X_ASSUM `getDATA (DATA (ax,ay,ad)) = (ax,ay,ad)` (K ALL_TAC)
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
  \\ `ref_mem i (DATA (ax,ay,ad)) (a,xs)` by METIS_TAC [ref_cheney_def]
  \\ FULL_SIMP_TAC bool_ss [ref_mem_def]
  \\ `(r51 = ref_addr a ax) /\ (r61 = ref_addr a ay)` by METIS_TAC []
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
    \\ `ref_mem i (DATA (ax,ay,ad)) (a,xs2)` by METIS_TAC []
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
  \\ ASM_REWRITE_TAC [GSYM AND_IMP_INTRO] \\ NTAC 27 STRIP_TAC
  \\ ONCE_REWRITE_TAC [def4]
  \\ Cases_on `i = j` THEN1
    (Q.PAT_X_ASSUM `!m.bb` (K ALL_TAC)
     \\ FULL_SIMP_TAC std_ss [ref_cheney_inv_def] \\ ONCE_REWRITE_TAC [EQ_SYM_EQ]
     \\ METIS_TAC [])
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
      (m r12 = ref_addr a x) /\ r12 <+ ref_addr a 1 /\ r12 <+ r12 + 4w /\
      roots_in_mem xs (a,r12+4w,m))`;

val NOT_ref_addr = prove(
  ``!x a. valid_address a i /\ x <+ ref_addr a 1 /\ ~(i = 0) ==>
          ~(x = ref_addr a i) /\ ~(x = ref_addr a i + 4w) /\ ~(x = ref_addr a i + 8w)``,
  NTAC 2 Cases_word \\ ASM_SIMP_TAC (std_ss++SIZES_ss)
       [ref_addr_def,word_add_n2w,n2w_11,WORD_LO,w2n_n2w,valid_address_def,LESS_MOD]
  \\ REPEAT STRIP_TAC
  \\ `n' + 12 * i < 4294967296 /\ n' + 12 < 4294967296` by DECIDE_TAC
  \\ `n' + 12 * i + 4 < 4294967296` by DECIDE_TAC
  \\ FULL_SIMP_TAC std_ss [LESS_MOD] \\ DECIDE_TAC);

val lemma = store_thm("lemma",
  ``ref_cheney (m1,f) (a,d,xs1,xs) /\ r12 <+ ref_addr a 1 ==>
    ref_cheney (m1,f) (a,d,(r12 =+ r51) xs1,(r12 =+ r51) xs1)``,
  SIMP_TAC bool_ss [ref_cheney_def] \\ REPEAT STRIP_TAC
  \\ Cases_on `m1 i` \\ ASM_REWRITE_TAC [ref_mem_def] THENL [
    `ref_addr a n + 1w = xs1 (ref_addr a i)` by METIS_TAC [ref_mem_def]
    \\ ASM_SIMP_TAC bool_ss [APPLY_UPDATE_THM]
    \\ METIS_TAC [NOT_ref_addr,va_IMP,heap_type_distinct],
    Cases_on `p` \\ Cases_on `r` \\ ASM_REWRITE_TAC [ref_mem_def]
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
  ``!rs zs j m r4 r5 r7 r8 xs r12 ys jn mn.
      LENGTH rs < 2**32 /\
      root_address_ok r12 (LENGTH rs) x /\
      roots_in_mem (rs++zs) (a,r12,xs) /\
      (!x. MEM x rs ==> {x} SUBSET0 DR0 (ICUT (b,e) m)) /\
      ref_cheney_inv (b,i,j,j',e,f,m,(w:num->word32 heap_type),ww,r) (a,r3,r4,x,xs,xs) ==>
      (arm_move_roots(r4,r5,n2w (LENGTH rs),r7,r8,r12,x,xs) = (r4n,r5n,r6n,r7n,r8n,r12n,xn,xsn)) /\
      (move_roots(rs,j,m) = (ys,jn,mn)) ==>
      arm_move_roots_pre(r4,r5,n2w (LENGTH rs),r7,r8,r12,x,xs) /\
      ref_cheney_inv (b,i,jn,j',e,f,mn,w,ww,r) (a,r3,r4n,x,xsn,xsn) /\
      roots_in_mem (ys++zs) (a,r12,xsn) /\
      (LENGTH ys = LENGTH rs) /\ (r12n = r12 + n2w (4 * LENGTH rs)) /\
      (!i. i <+ r12 ==> (xs i = xsn i)) /\ (xn = x)``,
  STRIP_TAC \\ STRIP_TAC \\ Induct_on `rs`
  \\ ONCE_REWRITE_TAC [def5] \\ SIMP_TAC std_ss [LET_DEF]
  THEN1 (Cases_on `ys` \\ REWRITE_TAC [move_roots_def,PAIR_EQ,LENGTH,MAP,NOT_NIL_CONS]
         \\ ONCE_REWRITE_TAC [EQ_SYM_EQ] \\ SIMP_TAC std_ss [LENGTH,WORD_MULT_CLAUSES,WORD_ADD_0])
  \\ POP_ASSUM (ASSUME_TAC o RW1 [GSYM CONTAINER_def])
  \\ SIMP_TAC std_ss [LENGTH,ADD1,DECIDE ``(k + 1 = m + 1 + n) = (k = m + n:num)``,ZIP,APPEND]
  \\ SIMP_TAC (std_ss++SIZES_ss) [n2w_11,LESS_MOD,LENGTH,DECIDE ``~(SUC n = 0)``]
  \\ SIMP_TAC std_ss [ADD1,GSYM word_add_n2w,WORD_ADD_SUB]
  \\ NTAC 12 STRIP_TAC
  \\ `?r41 r51 r71 r81 x1 xs1. arm_move (r4,xs r12,r7,r8,x,xs) = (r41,r51,r71,r81,x1,xs1)` by METIS_TAC [PAIR]
  \\ ASM_REWRITE_TAC [LET_DEF,PAIR_EQ,move_roots_def,APPEND,MAP]
  \\ `?y1 j1 m1. move (h,j,m) = (y1,j1,m1)` by METIS_TAC [PAIR]
  \\ `?ys j2 m2. move_roots (rs,j1,m1) = (ys,j2,m2)` by METIS_TAC [PAIR]
  \\ FULL_SIMP_TAC std_ss [LET_DEF,PAIR_EQ,move_roots_def,GSYM AND_IMP_INTRO,MAP] \\ STRIP_TAC
  \\ ONCE_REWRITE_TAC [EQ_SYM_EQ] \\ SIMP_TAC bool_ss []
  \\ FULL_SIMP_TAC bool_ss [MAP,CONS_11,NOT_NIL_CONS,NOT_CONS_NIL,ZIP,APPEND,ADD1,EQ_ADD_RCANCEL,LENGTH]
  \\ REPEAT (MATCH_MP_TAC (METIS_PROVE [] ``P ==> (Q ==> P)``))
  \\ `LENGTH rs < 4294967296` by DECIDE_TAC
  \\ FULL_SIMP_TAC bool_ss [roots_in_mem_def,MEM,ref_cheney_inv_def,APPEND]
  \\ `{h} SUBSET0 DR0 (ICUT(b,e)m)` by METIS_TAC [SING_IN_SUBSET0,IN_INSERT]
  \\ `arm_move (ref_addr a j,ref_addr a h,r7,r8,x,xs) = (r41,r51,r71,r81,x1,xs1)` by METIS_TAC [WORD_ADD_0]
  \\ FULL_SIMP_TAC bool_ss [FST,SND]
  \\ (STRIP_ASSUME_TAC o GSYM o UNDISCH_ALL o RW [GSYM AND_IMP_INTRO] o
   Q.SPECL [`a`,`b`,`b`,`i`,`j`,`j1`,`j'`,`e`,`m`,`m1`,
    `w`,`ww`,`r`,`h`,`r41`,`r51`,`xs`,`xs1`,`x`,`y1`,`hx`,`r7`,`r8`,`r71`,`r81`,`x1`] o Q.INST [`ys`|->`xs`]) (INST_TYPE [``:'a``|->``:word32``] ref_cheney_move)
  \\ ASM_SIMP_TAC bool_ss [WORD_ADD_0]
  \\ `!x. MEM x rs ==> {x} SUBSET0 DR0 (ICUT (b,e) m1)` by METIS_TAC []
  \\ `ref_cheney (m1,f) (a,x,(r12 =+ r51) xs1,(r12 =+ r51) xs1)` by METIS_TAC [lemma]
  \\ `roots_in_mem (rs++zs) (a,r12 + 4w,(r12 =+ r51) xs1)` by METIS_TAC [roots_lemma]
  \\ Q.PAT_X_ASSUM `r51 = ref_addr a y1` ASSUME_TAC \\ FULL_SIMP_TAC bool_ss []
  \\ FULL_SIMP_TAC std_ss [root_address_ok_def,ALIGNED_def,GSYM ADD1,move_roots_def]
  \\ Q.PAT_X_ASSUM `CONTAINER (!j m xs r12. bbb)`
    (STRIP_ASSUME_TAC o UNDISCH_ALL o RW [GSYM AND_IMP_INTRO] o
     Q.SPECL [`j1`,`m1`,`ref_addr a y1`,`r71`,`r81`,`(r12 =+ ref_addr a y1) xs1`,`r12+4w`,`ys'`,`j2`,`m2`] o
     RW [CONTAINER_def])
  \\ FULL_SIMP_TAC std_ss [LENGTH,ADD1,word_add_n2w,word_mul_n2w,
       GSYM WORD_ADD_ASSOC,LEFT_ADD_DISTRIB,AC ADD_ASSOC ADD_COMM,FST]
  \\ METIS_TAC [APPLY_UPDATE_THM,WORD_LOWER_TRANS,WORD_LOWER_NOT_EQ,ref_cheney_def]);

val ref_cheney_move_roots6 =
  SIMP_RULE std_ss [LENGTH,ADD1,AND_IMP_INTRO,GSYM CONJ_ASSOC]
  (Q.SPEC `[x1;x2;x3;x4;x5;x6]` ref_cheney_move_roots);

val arm_c_init_lemma = prove(
  ``(arm_c_init(if u then 0w else 1w,r6,r10) =
     (r10 + 12w + if u then 0w else r6, if u then 1w else 0w,r6,r10))``,
  Cases_on `u` \\ SIMP_TAC std_ss [SIMP_RULE std_ss [LET_DEF] def6,
    WORD_ADD_0,PAIR_EQ,WORD_XOR_CLAUSES,EVAL ``0w = 1w:word32``]);

val arm_coll_inv_def = Define `
  arm_coll_inv (a,x,xs) (i,e,rs,l,u,m) =
    ?x1 x2 x3 x4 x5 x6.
      roots_in_mem (rs ++ [i;e]) (a,a-24w,xs) /\
      (rs = [x1;x2;x3;x4;x5;x6]) /\
      valid_address a (l + l + 1) /\
      ref_cheney (m,l+l+1) (a,x,xs,xs) /\
      (xs (a-28w) = if u then 0w else 1w) /\ a - 28w <+ ref_addr a 1 /\ a - 28w <+ a - 24w /\
      (xs (a-32w) = n2w (12 * l)) /\ a - 32w <+ ref_addr a 1 /\ a - 32w <+ a - 24w`;

val roots_in_mem_carry_over = prove(
  ``!p r xs ys. ref_cheney (m,f) (a,x,xs,ys) /\ roots_in_mem p (a,r,ys) ==> roots_in_mem p (a,r,xs)``,
  Induct \\ FULL_SIMP_TAC bool_ss [roots_in_mem_def,ref_cheney_def] \\ METIS_TAC []);

val arm_coll_inv_pre_lemma = store_thm("arm_coll_inv_pre_lemma",
  ``arm_coll_inv (a,x,xs) (q,e,rs,l,u,m) ==>
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

val arm_collect_lemma = store_thm("arm_collect_lemma",
  ``ok_state (i,e,rs,l,u,m) ==>
    arm_coll_inv (a,x,xs) (i,e,rs,l,u,m) ==>
    (cheney_collector (i,e,rs,l,u,m) = (i',e',rs',l',u',m')) ==>
    (arm_collect (r7,r8,a,x,xs) = (r3',r4',r5',r6',r7',r8',a',x',xs')) ==>
    arm_collect_pre (r7,r8,a,x,xs) /\
    arm_coll_inv (a,x,xs') (i,e',rs',l',u',m') /\ (x = x') /\
    (r3' = ref_addr a i') /\ (r4' = ref_addr a e') /\ (a = a') /\ (l = l')``,
  STRIP_TAC \\ STRIP_TAC \\ IMP_RES_TAC arm_coll_inv_pre_lemma
  \\ ONCE_REWRITE_TAC [def7]
  \\ FULL_SIMP_TAC bool_ss [GSYM AND_IMP_INTRO,arm_coll_inv_def]
  \\ POP_ASSUM (STRIP_ASSUME_TAC o RW [arm_coll_inv_def])
  \\ ASM_SIMP_TAC bool_ss [LET_DEF]
  \\ ASM_SIMP_TAC std_ss [arm_c_init_lemma]
  \\ Q.ABBREV_TAC `xs1 = (a - 28w =+ (if u then 1w else 0w)) xs`
  \\ Q.ABBREV_TAC `r4l = a + 12w + (if u then 0w else n2w (12 * l))`
  \\ Q.ABBREV_TAC `xs2 = (a + 4w =+ r4l + n2w (12 * l)) xs1`
  \\ `?r43 r53 r63 r73 r83 a3 x3 xs3.
        arm_move_roots (r4l,r4l + n2w (12 * l),6w,r7,r8,a - 24w,x,xs2) =
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
  \\ `roots_in_mem (rs ++ [i;e]) (a,a - 24w,xs1)` by
   (Q.UNABBREV_TAC `xs1`
    \\ FULL_SIMP_TAC bool_ss [APPEND,roots_in_mem_def,APPLY_UPDATE_THM,ZIP]
    \\ SIMP_TAC (std_ss++WORD_ss) [WORD_EQ_ADD_LCANCEL,n2w_11,
      RW [WORD_ADD_0] (Q.SPECL [`v`,`w`,`0w`] WORD_EQ_ADD_LCANCEL)])
  \\ Q.PAT_X_ASSUM `roots_in_mem ppp (aaa,bbb,xs)` (K ALL_TAC)
  \\ Q.PAT_X_ASSUM `rs = ppppp` ASSUME_TAC
  \\ Q.PAT_X_ASSUM `rs2 = ppppp` ASSUME_TAC
  \\ `roots_in_mem (rs ++ [i;b+l]) (a,a - 24w,xs2) /\ a + 4w <+ ref_addr a 1` by
   (Q.UNABBREV_TAC `xs2` \\ Q.UNABBREV_TAC `b`
    \\ FULL_SIMP_TAC bool_ss [APPEND,roots_in_mem_def,APPLY_UPDATE_THM,ZIP]
    \\ FULL_SIMP_TAC (std_ss++WORD_ss) [WORD_EQ_ADD_LCANCEL,n2w_11,
      RW [WORD_ADD_0] (Q.SPECL [`v`,`w`,`0w`] WORD_EQ_ADD_LCANCEL)]
    \\ Q.UNABBREV_TAC `r4l` \\ Cases_on `u`
    \\ SIMP_TAC std_ss [ref_addr_def,DECIDE ``~(m+1 = 0)``,GSYM WORD_ADD_ASSOC,
         word_add_n2w,LEFT_ADD_DISTRIB,AC ADD_COMM ADD_ASSOC])
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
  \\ FULL_SIMP_TAC bool_ss []
  \\ STRIP_ASSUME_TAC
    ((UNDISCH_ALL o Q.INST [`f`|->`l+l+1`])
    (Q.INST [`r5n`|->`r53`,`r6n`|->`r63`,`r7n`|->`r73`,`r8n`|->`r83`,`xn`|->`x3'`]
    (Q.SPECL [`b`,`m`,`r4l`,`r4l + n2w (12 * l)`,`r7`,`r8`,`xs2`,`a - 24w`,`ys`,`j2`,`m2`]
    (Q.INST [`e`|->`b+l`,`j'`|->`b`,`w`|->`m`,`ww`|->`m`,`r`|->`{}`,`i`|->`b`,`r3`|->`ref_addr a b`,`r4n`|->`r43`,`r12n`|->`a3`,`xsn`|->`xs3`,`ii`|->`i`]
    (SIMP_RULE std_ss [APPEND,GSYM AND_IMP_INTRO,LENGTH,ADD1] (Q.SPEC `[ii;e]` ref_cheney_move_roots6))))))
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
      (INST_TYPE [``:'a``|->``:word32``] ref_cheney_loop_th)
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
  \\ `(a + 4w <+ ref_addr a 1) /\ (xs3 (a+4w) = ref_addr a (b + l))` by FULL_SIMP_TAC (std_ss++WORD_ss) [roots_in_mem_def]
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


val _ = export_theory();
