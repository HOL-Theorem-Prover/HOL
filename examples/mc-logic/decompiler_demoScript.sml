(*
  fun load_path_add x = loadPath := !loadPath @ [concat Globals.HOLDIR x];
  load_path_add "/examples/mc-logic";
  load_path_add "/examples/ARM/v4";
  load_path_add "/tools/mlyacc/mlyacclib";
*)

open HolKernel boolLib bossLib Parse;

open wordsTheory arithmeticTheory wordsLib listTheory pred_setTheory pairTheory combinTheory systemTheory arm_evalTheory addressTheory;
open arm_compilerLib;

val _ = new_theory "decompiler_demo";

infix \\ << >>

val op \\ = op THEN;
val op << = op THENL;
val op >> = op THEN1;

val _ = Parse.hide "set";

val RW = REWRITE_RULE;
val RW1 = ONCE_REWRITE_RULE;

(* 

INTRODUCTION

This file illustrates how the decompiler from arm_compilerLib 
can be used in verification of ARM code.

*)


(* example: factorial function --------- *)

val (arm_fac_def,_,th) = arm_decompiler "arm_fac" `T` NONE ["r1"] `
  cmp   r1,#0
  mulne r2,r1,r2  
  subne r1,r1,#1
  bne   -12`


(* example: mod 10 --------- *)

val termination_tac = SOME
 (WF_REL_TAC `measure w2n` \\ Cases
  \\ FULL_SIMP_TAC (std_ss++SIZES_ss) [WORD_LO,n2w_11,w2n_n2w,
       LESS_MOD,ZERO_LT_dimword,addressTheory.word_arith_lemma2]
  \\ REPEAT STRIP_TAC \\ `n - 10 < 4294967296` by DECIDE_TAC
  \\ ASM_SIMP_TAC bool_ss [LESS_MOD] \\ DECIDE_TAC)

val (arm_mod10_def,_,th) = arm_decompiler "arm_mod10" `T` termination_tac [] `
  cmp   r1,#10
  subcs r1,r1,#10
  bcs   -8`


(* example: simple division --------- *)

val termination_tac = SOME
 (WF_REL_TAC `measure (w2n o FST o SND)` \\ NTAC 2 Cases
  \\ ASM_SIMP_TAC bool_ss [WORD_LO,n2w_11,w2n_n2w,LESS_MOD,ZERO_LT_dimword]
  \\ `n - n' < dimword (:32)` by DECIDE_TAC
  \\ ASM_SIMP_TAC bool_ss [addressTheory.word_arith_lemma2,w2n_n2w,LESS_MOD] 
  \\ DECIDE_TAC)

val (arm_div_def,_,th) = arm_decompiler "arm_div" `~(r2 = 0w)` termination_tac [] `
  cmp   r1,r2
  addcs r0,r0,#1
  subcs r1,r1,r2
  bcs   -12`


(* example: length of linked-list --------- *)

val llist_def = Define `
  (llist [] (a:word32,m:word32->word32) = (a = 0w)) /\
  (llist (x::xs) (a,m) = ~(a = 0w) /\ 
     ?a'. (m a = a') /\ (m (a+4w) = x) /\ llist xs (a',m))`;

val llist_SELECT = prove(
  ``!xs a m. llist xs (a,m) ==> 
      ((@n. ?xs. llist xs (a,m) /\ (LENGTH xs = n)) = LENGTH xs)``,
  REPEAT STRIP_TAC
  \\ MATCH_MP_TAC SELECT_UNIQUE \\ SIMP_TAC std_ss []
  \\ STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC
  THENL [ALL_TAC,METIS_TAC []]
  \\ Q.PAT_ASSUM `LENGTH xs' = y` (fn th => REWRITE_TAC [GSYM th])    
  \\ Q.UNDISCH_TAC `llist xs (a,m)` \\ Q.UNDISCH_TAC `llist xs' (a,m)`
  \\ Q.SPEC_TAC (`a`,`a`) \\ Q.SPEC_TAC (`xs'`,`ys`)
  \\ Induct_on `xs` THEN1 (Cases \\ SIMP_TAC bool_ss [llist_def])
  \\ STRIP_TAC \\ Cases \\ ASM_SIMP_TAC bool_ss [llist_def,LENGTH] \\ METIS_TAC []);

val termination_tac = SOME
 (WF_REL_TAC `measure (\(r0,r1,x,xs). @n. ?ys. llist ys (r1,xs) /\ (LENGTH ys = n))`
  \\ REPEAT STRIP_TAC \\ IMP_RES_TAC llist_SELECT
  \\ Cases_on `ys` \\ FULL_SIMP_TAC bool_ss [llist_def]
  \\ IMP_RES_TAC llist_SELECT
  \\ FULL_SIMP_TAC bool_ss [LENGTH,WORD_ADD_0] \\ DECIDE_TAC);

val (arm_len_def,_,th) = arm_decompiler "arm_len" `?ys. llist ys (r1,xs)` 
  termination_tac [] `
  cmp   r1,#0
  ldrne r1,[r1]
  addne r0,r0,#1
  bne   -12`

val arm_len_spec = prove(
  ``!ys r0 r1 x xs. 
      llist ys (r1,xs) ==> (arm_len(r0,r1,x,xs) = (r0 + n2w (LENGTH ys),0w))``,
  Induct \\ ONCE_REWRITE_TAC [arm_len_def] \\ REPEAT STRIP_TAC
  \\ `(?ys. llist ys (r1,xs)) = T` by METIS_TAC [] \\ ASM_REWRITE_TAC []
  \\ FULL_SIMP_TAC std_ss [llist_def,WORD_ADD_0,LET_DEF,LENGTH]
  \\ REWRITE_TAC [RW1 [ADD_COMM] ADD1,GSYM word_add_n2w,WORD_ADD_ASSOC]);


(* example: addition ------------ *)

val (addition_def,addition_pre_def,th) = arm_decompiler_status "addition" 
  `T` NONE ["r0","r4","r5","sN","sZ","sC","sV"] `
  teq r0,#0
  beq 28
  ldr r4,[r1],#4
  ldr r5,[r2],#4
  adcs r4,r4,r5
  str r4,[r3],#4 | y 
  sub r0,r0,#1
  b -28` 

val (add4_def,add4_pre_def,th) = arm_decompiler "add4" 
  `T` NONE ["r4","r5","r6","r7","r8","r9","r10","r11"] `
  ldmia r1!,{r4,r5,r6,r7}   
  ldmia r2!,{r8,r9,r10,r11}
  adds  r4,r4,r8 
  adcs  r5,r5,r9 
  adcs  r6,r6,r10 
  adcs  r7,r7,r11
  stmia r3!,{r4,r5,r6,r7} | y` 

val add4_thm = prove(
  ``addition(4w,r1,r2,r3,x,xs,y,ys,z1,z2,F,z3) = add4(r1,r2,r3,x,xs,y,ys)``,
  NTAC 5 (ONCE_REWRITE_TAC [addition_def])
  \\ SIMP_TAC (std_ss++WORD_ss++WORD_ARITH_EQ_ss) [add4_def,LET_DEF]);
 



(* example: Cheney garbage collector --------- *)

open cheneyTheory; (* an abstract implementation is imported *)

val (arm_move_def,arm_move_pre_def,th) = arm_decompiler "arm_move" 
  `T` NONE ["r7","r8","r9"] `
  cmp r5,#0 
  beq 28
  ldmia r5,{r7,r8,r9}
  tst r7,#1
  stmeqia r4!,{r7,r8,r9}
  subeq r7,r4,#11
  streq r7,[r5]
  sub r5,r7,#1`  

val (arm_move2_def,arm_move2_pre_def,th) = arm_decompiler "arm_move2" 
  `T` NONE ["r7","r8","r9"] `
  cmp r6,#0
  beq 28
  ldmia r6,{r7,r8,r9}
  tst r7,#1
  stmeqia r4!,{r7,r8,r9}
  subeq r7,r4,#11
  streq r7,[r6]
  sub r6,r7,#1` 

val (arm_cheney_step_def,arm_cheney_step_pre_def,th) = arm_decompiler "arm_cheney_step" 
  `T` NONE ["r5","r6","r7","r8","r9"] `
  ldmia r3,{r5,r6}     
  insert: arm_move       
  insert: arm_move2      
  stmia r3,{r5,r6}     
  add r3,r3,#12` 

val FST_arm_cheney_step = prove(
  ``FST(arm_cheney_step(r3,r4,x,xs)) = r3 + 12w``,
  SIMP_TAC std_ss [arm_cheney_step_def,LET_DEF]
  \\ CONV_TAC (DEPTH_CONV arm_progLib.FORCE_PBETA_CONV) \\ SIMP_TAC std_ss [FST]);

val termination_tac = SOME
 (WF_REL_TAC `measure (\x. 2**32 - w2n (FST x))`
  \\ ONCE_REWRITE_TAC [GSYM PAIR] \\ PURE_REWRITE_TAC [FST_arm_cheney_step]
  \\ SIMP_TAC bool_ss [PAIR_EQ,FST]
  \\ REPEAT STRIP_TAC \\ ASM_SIMP_TAC bool_ss [] 
  \\ `w2n (r3:word32) < dimword(:32)` by METIS_TAC [w2n_lt]
  \\ FULL_SIMP_TAC (std_ss++SIZES_ss) [] \\ DECIDE_TAC)

val (arm_cheney_loop_def,arm_cheney_loop_pre_def,arm_cheney_loop_thm) = 
  arm_decompiler "arm_cheney_loop" `(r3 = r4) \/ (w2n (r3 + 12w) = w2n r3 + 12)`
  termination_tac ["r7","r8","r9","r5","r6"] `
  cmp r3,r4            
  beq 84                 
  insert: arm_cheney_step
  b -84`

val (arm_move_roots_def,arm_move_roots_pre_def,th) = 
  arm_decompiler "arm_move_roots" `T` NONE ["r7","r8","r9","r5","r6"] `
  cmp r6,#0            
  beq 52               
  ldr r5,[r10]         
  insert: arm_move       
  sub r6,r6,#1         
  str r5,[r10],#4      
  b -52`  

val (arm_c_init_def,_,th) = arm_decompiler "arm_c_init" `T` NONE [] `
  eors r5,r5,#1          (* calc u *)
  add r3,r10,#12         (* set i *)
  addeq r3,r3,r6` 

val (arm_collector_def,arm_collector_pre_def,th) = 
  arm_decompiler "arm_collect" `T` NONE ["r5","r6"] `
  ldr r5,[r10,#-32]      (* load u *)
  ldr r6,[r10,#-36]      (* load l *)
  insert: arm_c_init       (* ... *)
  str r5,[r10,#-32]      (* store u *)
  add r5,r3,r6           (* calc e *)     
  mov r4,r3              (* init j *)
  str r5,[r10,#4]        (* store e *)
  mov r6,#7            
  sub r10,r10,#28      
  insert: arm_move_roots   
  insert: arm_cheney_loop  (* main loop *)
  ldr r4,[r10,#4]`       (* load e *)
   
val (arm_alloc_aux_def,arm_alloc_aux_pre_def,arm_alloc_aux_thm) = 
  arm_decompiler "arm_alloc_aux" `T` NONE [] `
  cmp r3,r4              (* compare i and e *)
  bne 196               
  insert: arm_collect` 

val (arm_alloc_aux2_def,arm_alloc_aux2_pre_def,arm_alloc_aux2_thm) = 
  arm_decompiler "arm_alloc_aux2" `T` NONE ["r8","r9"] `
  ldr r8,[r10,#-28]      (* load root 1 *)
  ldr r9,[r10,#-24]      (* load root 2 *)
  cmp r3,r4            
  strne r3,[r10,#-28]  
  stmneia r3!, {r8,r9}   (* store new data element *)
  strne r0,[r3],#4     
  str r3,[r10]`          (* store i *)

val (arm_alloc_mem_def,arm_alloc_mem_pre_def,arm_alloc_mem_thm) =
  arm_decompiler "arm_alloc_mem" `T` NONE ["r3","r4","r5","r6","r7","r8","r9"] `
  ldmia r10,{r3,r4}      (* load i and e *)
  insert: arm_alloc_aux   
  insert: arm_alloc_aux2` 

val (arm_alloc_def,arm_alloc_pre_def,arm_alloc_thm) =
  arm_decompiler "arm_alloc" `T` NONE [] `
  stmdb r10,{r3,r4,r5,r6,r7,r8,r9}  (* store roots *)
  insert: arm_alloc_mem              
  ldmdb r10,{r3,r4,r5,r6,r7,r8,r9}` (* load roots *)
    
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

val ref_addr_NEQ = prove(
  ``!a i j. ~(i = j) /\ valid_address a i /\ valid_address a j ==> 
            ~(ref_addr a i = ref_addr a j)``,
  Cases_word \\ Cases \\ Cases
  \\ SIMP_TAC std_ss [ref_addr_def,valid_address_def,word_add_n2w]
  \\ ASM_SIMP_TAC (std_ss++SIZES_ss) [w2n_n2w,LESS_MOD,n2w_11,DECIDE ``~(SUC n = 0)``]
  \\ STRIP_TAC \\ IMP_RES_TAC (DECIDE ``m + n + 8 < l ==> m + n + 4 < l /\ m + n < l``)
  \\ ASM_SIMP_TAC bool_ss [LESS_MOD] \\ DECIDE_TAC);

val ref_addr_ADD_NEQ = prove(
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

val aligned_ref_addr = prove(
  ``!n a. aligned a ==> aligned (ref_addr a n)``,
  Cases \\ REWRITE_TAC [ref_addr_def,aligned_def] THEN1 (STRIP_TAC \\ EVAL_TAC)
  \\ REWRITE_TAC [GSYM aligned_def,GSYM (EVAL ``4 * 3``),GSYM word_mul_n2w,DECIDE ``~(SUC n = 0)``]
  \\ SIMP_TAC bool_ss [aligned_MULT,GSYM WORD_MULT_ASSOC]);  

val ref_cheney_aligned = prove(
  ``ref_cheney (m,f) (a,d,xs,ys) ==> (ref_addr a x && 3w = 0w)``,
  METIS_TAC [aligned_def,aligned_ref_addr,ref_cheney_def]);

val ref_cheney_d = prove(
  ``ref_cheney (m,f) (a,d,xs,ys) /\ ~(x = 0) /\ x <= f ==>
    ref_addr a x IN d /\ ref_addr a x + 4w IN d /\ ref_addr a x + 8w IN d``,
  REWRITE_TAC [ref_cheney_def] \\ REPEAT STRIP_TAC
  \\ Q.PAT_ASSUM `ref_set a f = d` (ASSUME_TAC o GSYM)
  \\ ASM_SIMP_TAC bool_ss [ref_set_def,GSPECIFICATION,IN_UNION,ref_addr_def] 
  \\ DISJ1_TAC 
  THENL [Q.EXISTS_TAC `3*x`,Q.EXISTS_TAC `3*x+1`,Q.EXISTS_TAC `3*x+2`]
  \\ ASM_SIMP_TAC std_ss [MULT_ASSOC,LEFT_ADD_DISTRIB,
      GSYM word_add_n2w,WORD_ADD_ASSOC] \\ DECIDE_TAC);

fun UPDATE_ref_addr_prove (c,tm) = prove(tm,
  Cases \\ Cases_word \\ REPEAT STRIP_TAC
  \\ c by ALL_TAC \\ ASM_REWRITE_TAC [APPLY_UPDATE_THM]
  \\ FULL_SIMP_TAC std_ss [ref_addr_def,EVAL ``1=0``,word_add_n2w,valid_address_def,
      w2n_n2w,n2w_11,WORD_LO]
  \\ Q.PAT_ASSUM `n < dimword (:32)` ASSUME_TAC
  \\ Q.PAT_ASSUM `n' < dimword (:32)` ASSUME_TAC
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
  \\ ASM_SIMP_TAC bool_ss [] \\ Cases_on `p` \\ Cases_on `r` 
  \\ FULL_SIMP_TAC std_ss [ref_mem_def] \\ METIS_TAC [ref_addr_ADD_NEQ]);

val ref_cheney_move_lemma = prove(    
  ``ref_cheney (m,e) (a,d,xs,ys) /\ (~(x = 0) ==> ~(m x = EMP)) /\
    (move(x,j,m) = (x1,j1,m1)) /\ ~(j = 0) /\ j <= e /\ x <= e /\
    (arm_move(ref_addr a j,ref_addr a x, d, xs) = (j2,x2,xs2)) ==>
    ref_cheney (m1,e) (a,d,xs2,ys) /\ (x2 = ref_addr a x1) /\ (j2 = ref_addr a j1) /\
    arm_move_pre(ref_addr a j,ref_addr a x, d, xs)``,
  REWRITE_TAC [move_def] \\ Cases_on `x = 0` THEN1   
   (ASM_SIMP_TAC std_ss [ref_addr_def] \\ REWRITE_TAC [arm_move_def,arm_move_pre_def]
    \\ SIMP_TAC std_ss [] \\ ONCE_REWRITE_TAC [EQ_SYM_EQ]
    \\ SIMP_TAC std_ss [ref_addr_def])
  \\ Cases_on `x <= e` \\ ASM_SIMP_TAC bool_ss []
  \\ SIMP_TAC std_ss [GSYM AND_IMP_INTRO] \\ STRIP_TAC      
  \\ `~(ref_addr a x = 0w)` by METIS_TAC [ref_addr_NOT_ZERO]
  \\ Cases_on `m x` \\ ASM_SIMP_TAC bool_ss [isREF_def,heap_type_11] THEN1 
     (REWRITE_TAC [getREF_def]    
      \\ ONCE_REWRITE_TAC [EQ_SYM_EQ] \\ SIMP_TAC std_ss []
      \\ REWRITE_TAC [arm_move_def,arm_move_pre_def]
      \\ SIMP_TAC std_ss [LET_DEF,GSYM AND_IMP_INTRO] \\ NTAC 2 STRIP_TAC 
      \\ ASM_SIMP_TAC std_ss []
      \\ `~(xs (ref_addr a x) && 1w = 0w)` by ALL_TAC << [
        FULL_SIMP_TAC bool_ss [ref_cheney_def,ref_mem_def]
        \\ `ref_mem x (REF n) (a,xs)` by METIS_TAC []
        \\ FULL_SIMP_TAC bool_ss [ref_cheney_def,ref_mem_def]
        \\ MATCH_MP_TAC aligned_add_1_and_1
        \\ MATCH_MP_TAC aligned_ref_addr
        \\ ASM_REWRITE_TAC [aligned_def],
        ASM_SIMP_TAC std_ss []
        \\ `ref_mem x (REF n) (a,xs)` by METIS_TAC [ref_cheney_def]
        \\ FULL_SIMP_TAC std_ss [ref_mem_def,WORD_ADD_SUB]
        \\ IMP_RES_TAC ref_cheney_d \\ IMP_RES_TAC ref_cheney_aligned
        \\ ASM_SIMP_TAC bool_ss [INSERT_SUBSET,EMPTY_SUBSET,aligned_def]])
  \\ SIMP_TAC std_ss [heap_type_distinct]        
  \\ ONCE_REWRITE_TAC [EQ_SYM_EQ] \\ SIMP_TAC std_ss []
  \\ REWRITE_TAC [arm_move_def]
  \\ SIMP_TAC std_ss [LET_DEF]
  \\ `~(m x = EMP)` by METIS_TAC [heap_type_distinct]
  \\ `valid_address a x` by METIS_TAC [ref_cheney_def,va_IMP]
  \\ ASM_SIMP_TAC std_ss [word_arith_lemma1,WORD_ADD_SUB]
  \\ `(xs (ref_addr a x) && 1w = 0w)` by 
       (FULL_SIMP_TAC bool_ss [ref_cheney_def] \\ Cases_on `p` \\ Cases_on `r`
        \\ `ref_mem x (DATA (q,q',r')) (a,xs)` by METIS_TAC []
        \\ FULL_SIMP_TAC bool_ss [ref_mem_def]
        \\ MATCH_MP_TAC aligned_and_1 \\ MATCH_MP_TAC aligned_ref_addr
        \\ ASM_REWRITE_TAC [aligned_def])
  \\ FULL_SIMP_TAC std_ss [PAIR_EQ,WORD_ADD_0,word_arith_lemma4] 
  \\ NTAC 3 STRIP_TAC
  \\ `arm_move_pre (ref_addr a j,ref_addr a x,d,xs)` by 
    (`~(j = 0)` by METIS_TAC []
     \\ IMP_RES_TAC ref_cheney_d \\ IMP_RES_TAC ref_cheney_aligned
     \\ ASM_SIMP_TAC std_ss [INSERT_SUBSET,EMPTY_SUBSET,aligned_def,
         arm_move_pre_def,LET_DEF,WORD_ADD_0,LENGTH])
  \\ ASM_SIMP_TAC bool_ss []
  \\ REVERSE (REPEAT STRIP_TAC)
  THEN1 ASM_SIMP_TAC std_ss 
    [ref_addr_def,LEFT_ADD_DISTRIB,GSYM word_add_n2w,WORD_ADD_ASSOC]
  \\ MATCH_MP_TAC ref_cheney_update_REF \\ ASM_SIMP_TAC bool_ss []        
  \\ Cases_on `p` \\ Cases_on `r` \\ FULL_SIMP_TAC std_ss [ref_cheney_def]
  \\ REPEAT STRIP_TAC << [
     `ref_mem x (DATA (q,q',r')) (a,xs)` by METIS_TAC []
     \\ Cases_on `i = j`
     THEN1 (FULL_SIMP_TAC bool_ss [UPDATE_def,ref_mem_def,WORD_EQ_ADD_LCANCEL,
         RW[WORD_ADD_0](Q.SPECL[`x`,`y`,`0w`]WORD_EQ_ADD_LCANCEL)]
       \\ SIMP_TAC (std_ss++SIZES_ss) [n2w_11])
     \\ `ref_mem i (m i) (a,xs)` by METIS_TAC []
     \\ CONV_TAC (RATOR_CONV (SIMP_CONV std_ss [UPDATE_def]))
     \\ ASM_SIMP_TAC bool_ss []
     \\ Cases_on `m i` 
     \\ FULL_SIMP_TAC bool_ss [ref_mem_def,UPDATE_def]
     \\ `~(ref_addr a j = ref_addr a i)` by METIS_TAC [va_IMP,ref_addr_NEQ]
     \\ RES_TAC \\ `valid_address a i /\ valid_address a j` by METIS_TAC [va_IMP]
     \\ ASM_SIMP_TAC bool_ss [ref_addr_ADD_NEQ]
     \\ Cases_on `p` \\ Cases_on `r`
     \\ FULL_SIMP_TAC bool_ss [ref_mem_def,UPDATE_def,ref_addr_ADD_NEQ,WORD_EQ_ADD_RCANCEL],
     ASM_SIMP_TAC std_ss [UPDATE_def],
     `valid_address a j` by METIS_TAC [va_IMP]
     \\ MATCH_MP_TAC UPDATE_ref_addr8 \\ ASM_SIMP_TAC bool_ss []
     \\ MATCH_MP_TAC UPDATE_ref_addr4 \\ ASM_SIMP_TAC bool_ss []
     \\ MATCH_MP_TAC UPDATE_ref_addr \\ ASM_SIMP_TAC bool_ss []]);

val ref_cheney_move = prove(    
  ``!a b b' i j j2 j3 e m m2 w ww r x xj2 xx2 xs xs2 d x2.
    cheney_inv (b,b',i,j,j3,e,f,m,w,ww,r) /\ {x} SUBSET0 dr0(icut(b,e)m) /\
    ref_cheney (m,f) (a,d,xs,ys) /\ (move(x,j,m) = (x2,j2,m2)) /\  
    (arm_move(ref_addr a j,ref_addr a x, d, xs) = (xj2,xx2,xs2)) ==>
    cheney_inv(b,b',i,j2,j3,e,f,m2,w,ww,r) /\ {x2} SUBSET0 range(b,j2) /\ j <= j2 /\
    (cut(b,j)m = cut(b,j)m2) /\ ref_cheney (m2,f) (a,d,xs2,ys) /\
    (ref_addr a x2 = xx2) /\ (ref_addr a j2 = xj2) /\ (dr0 (icut(b,e)m) = dr0 (icut(b,e)m2)) /\ 
    arm_move_pre(ref_addr a j,ref_addr a x, d, xs)``,
  NTAC 21 STRIP_TAC \\ `~(x = 0) ==> ~(m x = EMP)` by (STRIP_TAC
    \\ FULL_SIMP_TAC bool_ss [SUBSET0_DEF,SUBSET_DEF,IN_INSERT,NOT_IN_EMPTY]
    \\ FULL_SIMP_TAC bool_ss [IN_DEF,dr0_def,d0_def,r0_def,icut_def]
    \\ METIS_TAC [heap_type_distinct])
  \\ `~(j = 0) /\ j <= f` by (FULL_SIMP_TAC bool_ss [cheney_inv_def] \\ DECIDE_TAC)
  \\ IMP_RES_TAC move_lemma 
  \\ ASM_SIMP_TAC bool_ss [] \\ ONCE_REWRITE_TAC [EQ_SYM_EQ]
  \\ MATCH_MP_TAC ref_cheney_move_lemma
  \\ ASM_SIMP_TAC bool_ss [PAIR_EQ] \\ METIS_TAC []); 

val arm_move2_thm = prove(
  ``(arm_move2 = arm_move) /\ (arm_move2_pre = arm_move_pre)``,
  STRIP_TAC \\ REWRITE_TAC [FUN_EQ_THM] \\ Cases \\ Cases_on `r` \\ Cases_on `r'`
  \\ REWRITE_TAC [arm_move_def,arm_move2_def,arm_move_pre_def,arm_move2_pre_def]);  

val ref_cheney_inv_def = Define `
  ref_cheney_inv (b,i,j,k,e,f,m,w,ww,r) (a,r3,r4,d,xs,ys) =
    cheney_inv (b,b,i,j,k,e,f,m,w,ww,r) /\ ref_cheney (m,f) (a,d,xs,ys) /\ 
    valid_address a e /\ (r4 = ref_addr a j) /\ (r3 = ref_addr a i)`;

val ref_cheney_step_thm = prove(
  ``ref_cheney_inv (b,i,j,j,e,f,m,x,xx,r) (a,r3,r4,d,xs,ys) /\ ~(i = j) /\
    (cheney_step (i,j,e,m) = (i',j',e',m')) /\
    (arm_cheney_step (r3,r4,d,xs) = (r3',r4',xs')) ==>
    ref_cheney_inv (b,i',j',j',e',f,m',x,xx,r) (a,r3',r4',d,xs',ys) /\
    arm_cheney_step_pre (r3,r4,d,xs)``,
  REWRITE_TAC [ref_cheney_inv_def] \\ STRIP_TAC
  \\ `cheney_inv (b,b,i',j',j',e',f,m',x,xx,r)` by METIS_TAC [cheney_inv_step]  
  \\ ASM_SIMP_TAC bool_ss []
  \\ Q.UNDISCH_TAC `cheney_step (i,j,e,m) = (i',j',e',m')`
  \\ Q.UNDISCH_TAC `arm_cheney_step (r3,r4,d,xs) = (r3',r4',xs')`
  \\ REWRITE_TAC [cheney_step_def,arm_cheney_step_def,arm_cheney_step_pre_def]
  \\ `?r51. xs r3 = r51` by METIS_TAC []
  \\ `?r61. xs (r3+4w) = r61` by METIS_TAC []
  \\ `?r41 r52 xs1. arm_move (ref_addr a j,r51,d,xs) = (r41,r52,xs1)` by METIS_TAC [PAIR]
  \\ `?r42 r62 xs2. arm_move (r41,r61,d,xs1) = (r42,r62,xs2)` by METIS_TAC [PAIR]
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
  \\ `?ax ay ad. m i = DATA(ax,ay,ad)` by METIS_TAC [m_DATA]    
  \\ `(x1,y1,d1') = (ax,ay,ad)` by METIS_TAC [getDATA_def]
  \\ FULL_SIMP_TAC bool_ss [PAIR_EQ]
  \\ Q.PAT_ASSUM `getDATA (DATA (ax,ay,ad)) = (ax,ay,ad)` (K ALL_TAC)
  \\ `{ax} SUBSET0 dr0 (icut (b,e) m) /\ {ay} SUBSET0 dr0 (icut (b,e) m)` by  
   (`{ax;ay} SUBSET0 d1(cut(i,j)m)` by ALL_TAC << [      
      FULL_SIMP_TAC bool_ss [SUBSET0_DEF,IN_INSERT,SUBSET_DEF,NOT_IN_EMPTY]
      \\ FULL_SIMP_TAC bool_ss [IN_DEF,d1_def,cut_def,cheney_inv_def]
      \\ `range(i,j)i` by (REWRITE_TAC [range_def] \\ DECIDE_TAC)
      \\ METIS_TAC [],
      `{ax;ay} SUBSET0 dr0 (icut (b,e) m)` by 
        METIS_TAC [cheney_inv_def,SUBSET0_TRANS]
      \\ FULL_SIMP_TAC bool_ss [SUBSET0_DEF,SUBSET_DEF,IN_INSERT,NOT_IN_EMPTY]])
  \\ `i <= e /\ i <= f /\ j <= f /\ range(b,j)i` by 
        (FULL_SIMP_TAC bool_ss [cheney_inv_def,range_def] \\ DECIDE_TAC)
  \\ `ref_mem i (DATA (ax,ay,ad)) (a,xs)` by METIS_TAC [ref_cheney_def]  
  \\ FULL_SIMP_TAC bool_ss [ref_mem_def]
  \\ `(r51 = ref_addr a ax) /\ (r61 = ref_addr a ay)` by METIS_TAC []
  \\ FULL_SIMP_TAC bool_ss []
  \\ (STRIP_ASSUME_TAC o UNDISCH_ALL o RW [GSYM AND_IMP_INTRO] o 
      Q.SPECL [`a`,`b`,`b`,`i`,`j`,`j2`,`j`,`e`,`m`,`m2`,`x`,`xx`,`r`,`ax`,`r41`,`r52`,`xs`,`xs1`,`d`,`x2`]) ref_cheney_move
  \\ Q.PAT_ASSUM `ref_addr a j2 = r41` (ASSUME_TAC o GSYM)
  \\ FULL_SIMP_TAC bool_ss []
  \\ (STRIP_ASSUME_TAC o UNDISCH_ALL o RW [GSYM AND_IMP_INTRO] o 
      Q.SPECL [`a`,`b`,`b`,`i`,`j2`,`j3`,`j`,`e`,`m2`,`m3`,`x`,`xx`,`r`,`ay`,`r42`,`r62`,`xs1`,`xs2`,`d`,`y3`]) ref_cheney_move  
  \\ IMP_RES_TAC ref_cheney_d 
  \\ REPEAT (Q.PAT_ASSUM `!xx.bb` (K ALL_TAC))
  \\ REPEAT (Q.PAT_ASSUM `ccc ==> !xx.bb` (K ALL_TAC))
  \\ IMP_RES_TAC ref_cheney_aligned
  \\ ASM_SIMP_TAC std_ss [INSERT_SUBSET,EMPTY_SUBSET,aligned_def,
       arm_move_pre_def,LET_DEF,WORD_ADD_0,LENGTH]
  \\ Q.PAT_ASSUM `ref_cheney (m3,f) (a,d,xs2,ys)` (STRIP_ASSUME_TAC o RW [ref_cheney_def])  
  \\ ASM_SIMP_TAC bool_ss [ref_cheney_def,APPLY_UPDATE_THM]
  \\ ASM_SIMP_TAC bool_ss [ref_addr_ADD_NEQ] 
  \\ `m3 i = m i` by 
       (`range(b,j2)i` by (FULL_SIMP_TAC bool_ss [range_def] \\ DECIDE_TAC)
        \\ FULL_SIMP_TAC bool_ss [cut_def,FUN_EQ_THM] 
        \\ METIS_TAC [heap_type_distinct])
  \\ REPEAT STRIP_TAC << [
    Cases_on `i'' = i` \\ ASM_SIMP_TAC bool_ss [ref_mem_def,UPDATE_def] << [
      `valid_address a i` by METIS_TAC [va_IMP] 
      \\ `ref_mem i (DATA (ax,ay,ad)) (a,xs2)` by METIS_TAC []
      \\ FULL_SIMP_TAC bool_ss [ref_mem_def,ref_addr_ADD_NEQ],
      Cases_on `m3 i''` \\ ASM_SIMP_TAC bool_ss [ref_mem_def]
      THENL [ALL_TAC,Cases_on`p` \\ Cases_on`r'`]
      \\ `valid_address a i /\ valid_address a i'' /\ ref_mem i'' (m3 i'') (a,xs2)` by 
        METIS_TAC [ref_cheney_def,heap_type_distinct,va_IMP]
      \\ Q.PAT_ASSUM `m3 i'' = xxxxx` (ASSUME_TAC)
      \\ FULL_SIMP_TAC bool_ss [ref_mem_def,ref_addr_NEQ,ref_addr_ADD_NEQ,WORD_EQ_ADD_RCANCEL]],
    REWRITE_TAC [GSYM APPLY_UPDATE_THM]
    \\ `valid_address a i` by METIS_TAC [va_IMP]
    \\ MATCH_MP_TAC UPDATE_ref_addr4 \\ ASM_SIMP_TAC bool_ss []
    \\ MATCH_MP_TAC UPDATE_ref_addr \\ ASM_SIMP_TAC bool_ss [] \\ METIS_TAC []]);
        
val w2n_ADD_w2n = prove(
  ``!x:'a word y. w2n x + w2n y < dimword(:'a) ==> (w2n (x + y) = w2n x + w2n y)``,
  NTAC 2 Cases_word \\ ASM_SIMP_TAC bool_ss [LESS_MOD,w2n_n2w,word_add_n2w]);

val ref_cheney_loop_lemma = prove(
  ``valid_address a j /\ i < j ==>
    (w2n (ref_addr a i + 12w) = w2n (ref_addr a i) + w2n (12w:word32))``,
  Cases_on `i = 0`
  THEN1 ASM_SIMP_TAC (std_ss++SIZES_ss) [ref_addr_def,word_add_n2w,w2n_n2w]
  \\ REPEAT STRIP_TAC \\ MATCH_MP_TAC w2n_ADD_w2n  
  \\ ASSUME_TAC (Q.ISPECL [`a:word32`,`n2w(12*i):word32`] w2n_ADD_w2n)
  \\ FULL_SIMP_TAC (std_ss++SIZES_ss) [ref_addr_def,w2n_n2w,valid_address_def]
  \\ `12 * i < 4294967296 /\ w2n a + 12 * i < 4294967296` by DECIDE_TAC
  \\ FULL_SIMP_TAC std_ss [LESS_MOD] \\ DECIDE_TAC);

val ref_cheney_loop_th = prove(
  ``!b i j e m x y r r3 r4 xs i' m' r3' r4' xs'.
      ref_cheney_inv (b,i,j,j,e,f,m,x,xx,r) (a,r3,r4,d,xs,ys) /\
      (cheney (i,j,e,m) = (i',m')) /\
      (arm_cheney_loop (r3,r4,d,xs) = (r3',r4',xs')) ==>
      ref_cheney_inv (b,i',i',i',e,f,m',x,xx,r) (a,r3',r4',d,xs',ys) /\
      arm_cheney_loop_pre (r3,r4,d,xs) /\
      (~(r3 = r4) ==> (w2n (r3 + 12w) = w2n r3 + 12))``,
  completeInduct_on `e - i:num`
  \\ NTAC 2 (ONCE_REWRITE_TAC [cheney_def,arm_cheney_loop_def,arm_cheney_loop_pre_def])
  \\ ASM_REWRITE_TAC [GSYM AND_IMP_INTRO] 
  \\ NTAC 18 STRIP_TAC \\ Cases_on `i = j` THEN1
   (FULL_SIMP_TAC bool_ss [ref_cheney_inv_def] \\ ONCE_REWRITE_TAC [EQ_SYM_EQ]
    \\ FULL_SIMP_TAC bool_ss [PAIR_EQ] \\ METIS_TAC [])
  \\ Q.PAT_ASSUM `ref_cheney_inv (b,i,j,j,e,f,m,x,r) (a,r3,r4,d,xs,ys)`
      (fn th => STRIP_ASSUME_TAC (RW [ref_cheney_inv_def] th) \\ ASSUME_TAC th)
  \\ `i <= j /\ j <= e` by METIS_TAC [cheney_inv_def]
  \\ Cases_on `v = 0` THEN1 `F` by DECIDE_TAC
  \\ `valid_address a i /\ valid_address a j /\ ~(e < i)` by 
    (FULL_SIMP_TAC bool_ss [valid_address_def] \\ DECIDE_TAC)
  \\ `i < j` by DECIDE_TAC
  \\ IMP_RES_TAC ref_cheney_loop_lemma
  \\ ASM_SIMP_TAC bool_ss [ref_addr_NEQ,ref_cheney_loop_lemma]
  \\ REWRITE_TAC [EVAL ``w2n(12w:word32)``]
  \\ `?i2 j2 e2 m2. cheney_step (i,j,e,m) = (i2,j2,e2,m2)` by METIS_TAC [PAIR]
  \\ `?r31 r41 xs1. arm_cheney_step (ref_addr a i,ref_addr a j,d,xs) = (r31,r41,xs1)` by METIS_TAC [PAIR]
  \\ ASM_SIMP_TAC std_ss [LET_DEF] \\ STRIP_TAC
  \\ `e - (i + 1) < v` by DECIDE_TAC
  \\ Q.PAT_ASSUM `!m. m < v ==> !e i. bbb` 
    (ASSUME_TAC o RW [] o Q.SPECL [`e`,`i+1`] o UNDISCH o Q.SPEC `e - (i + 1)`)
  \\ `ref_cheney_inv (b,i2,j2,j2,e2,f,m2,x,xx,r) (a,r31,r41,d,xs1,ys) /\
      arm_cheney_step_pre (r3,r4,d,xs)` by METIS_TAC [ref_cheney_step_thm]
  \\ Q.PAT_ASSUM `r4 = ref_addr a j` (ASSUME_TAC o GSYM)       
  \\ Q.PAT_ASSUM `r3 = ref_addr a i` (ASSUME_TAC o GSYM)       
  \\ ASM_SIMP_TAC bool_ss []
  \\ `~(r31 = r41) ==> (w2n (r31 + 12w) = w2n r31 + 12)` by 
   (FULL_SIMP_TAC bool_ss [ref_cheney_inv_def]
    \\ REPEAT (Q.PAT_ASSUM `!xx.bb` (K ALL_TAC))  
    \\ `i2 <= f /\ j2 <= f /\ ~(i2 = 0) /\ ~(j2 = 0) /\ i2 <= j2` by 
      (FULL_SIMP_TAC bool_ss [cheney_inv_def] \\ DECIDE_TAC)
    \\ `valid_address a i2 /\ valid_address a j2` by METIS_TAC [va_IMP,ref_cheney_def]
    \\ Cases_on `i2 = j2` \\ ASM_SIMP_TAC bool_ss []   
    \\ STRIP_TAC \\ Q.UNDISCH_TAC `valid_address (a:word32) j2`
    \\ `i2 < j2` by DECIDE_TAC \\ Q.UNDISCH_TAC `i2 < j2`
    \\ ASM_SIMP_TAC std_ss [ref_addr_def]
    \\ REPEAT (POP_ASSUM (K ALL_TAC))
    \\ Q.SPEC_TAC (`a:word32`,`a:word32`) \\ Cases_word
    \\ ASM_SIMP_TAC (std_ss++SIZES_ss) [word_add_n2w,w2n_n2w,valid_address_def]
    \\ REPEAT STRIP_TAC
    \\ `n + 12 * i2 + 12 < 4294967296 /\ n + 12 * i2 < 4294967296` by DECIDE_TAC
    \\ ASM_SIMP_TAC bool_ss [LESS_MOD])
  \\ REWRITE_TAC [METIS_PROVE [] ``b\/c = ~b ==> c``]  
  \\ Q.PAT_ASSUM `!b' j'. bbbb` MATCH_MP_TAC
  \\ Q.EXISTS_TAC `j2` \\ Q.EXISTS_TAC `m2`
  \\ REVERSE (`(i + 1 = i2) /\ (e = e2)` by ALL_TAC) THEN1 METIS_TAC []
  \\ ASM_SIMP_TAC bool_ss []
  \\ Q.UNDISCH_TAC `cheney_step (i,j,e,m) = (i2,j2,e2,m2)`
  \\ ONCE_REWRITE_TAC [EQ_SYM_EQ]
  \\ SIMP_TAC std_ss [cheney_step_def,LET_DEF] 
  \\ CONV_TAC (DEPTH_CONV (arm_progLib.FORCE_PBETA_CONV))
  \\ SIMP_TAC bool_ss [PAIR_EQ] \\ METIS_TAC []);

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

val lemma = prove(
  ``ref_cheney (m1,f) (a,d,xs1,xs) /\ r12 <+ ref_addr a 1 ==>
    ref_cheney (m1,f) (a,d,(r12 =+ r51) xs1,(r12 =+ r51) xs1)``,
  SIMP_TAC bool_ss [ref_cheney_def] \\ REPEAT STRIP_TAC
  \\ Cases_on `m1 i` \\ ASM_REWRITE_TAC [ref_mem_def] << [
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
  (root_address_ok a (SUC n) x = aligned a /\ a IN x /\ root_address_ok (a+4w) n x)`;

val ref_cheney_move_roots = prove(
  ``!rs zs j m r4 xs r12 ys jn mn.
      LENGTH rs < 2**32 /\
      root_address_ok r12 (LENGTH rs) x /\
      roots_in_mem (rs++zs) (a,r12,xs) /\
      (!x. MEM x rs ==> {x} SUBSET0 dr0 (icut (b,e) m)) /\
      ref_cheney_inv (b,i,j,j',e,f,m,w:num->word32 heap_type,ww,r) (a,r3,r4,x,xs,xs) ==>
      (arm_move_roots(r4,n2w (LENGTH rs),r12,x,xs) = (r4n,r12n,xsn)) /\
      (move_roots(rs,j,m) = (ys,jn,mn)) ==>
      arm_move_roots_pre(r4,n2w (LENGTH rs),r12,x,xs) /\
      ref_cheney_inv (b,i,jn,j',e,f,mn,w,ww,r) (a,r3,r4n,x,xsn,xsn) /\
      roots_in_mem (ys++zs) (a,r12,xsn) /\
      (LENGTH ys = LENGTH rs) /\ (r12n = r12 + n2w (4 * LENGTH rs)) /\
      !i. i <+ r12 ==> (xs i = xsn i)``,  
  STRIP_TAC \\ STRIP_TAC \\ Induct_on `rs` THEN1
   (NTAC 2 (ONCE_REWRITE_TAC [arm_move_roots_pre_def,arm_move_roots_def])
    \\ REWRITE_TAC [move_roots_def,PAIR_EQ,LENGTH]
    \\ ONCE_REWRITE_TAC [EQ_SYM_EQ] \\ SIMP_TAC std_ss [LENGTH,WORD_MULT_CLAUSES,WORD_ADD_0])  
  \\ ONCE_REWRITE_TAC [arm_move_roots_def,LENGTH]   
  \\ ONCE_REWRITE_TAC [arm_move_roots_pre_def,LENGTH]   
  \\ FULL_SIMP_TAC (std_ss++SIZES_ss) [n2w_11,LESS_MOD,LENGTH,DECIDE ``~(SUC n = 0)``]                
  \\ SIMP_TAC std_ss [ADD1,GSYM word_add_n2w,WORD_ADD_SUB]    
  \\ NTAC 10 STRIP_TAC
  \\ `?r41 r51 xs1. arm_move (r4,xs(r12+0w),x,xs) = (r41,r51,xs1)` by METIS_TAC [PAIR]
  \\ ASM_SIMP_TAC std_ss [LET_DEF,PAIR_EQ,move_roots_def,APPEND]
  \\ `?y1 j1 m1. move (h,j,m) = (y1,j1,m1)` by METIS_TAC [PAIR]
  \\ `?ys j2 m2. move_roots (rs,j1,m1) = (ys,j2,m2)` by METIS_TAC [PAIR]
  \\ ASM_SIMP_TAC std_ss [LET_DEF,PAIR_EQ,move_roots_def,GSYM AND_IMP_INTRO] \\ STRIP_TAC
  \\ ONCE_REWRITE_TAC [EQ_SYM_EQ] \\ SIMP_TAC bool_ss []
  \\ REPEAT (MATCH_MP_TAC (METIS_PROVE [] ``P ==> (Q ==> P)``))
  \\ `LENGTH rs < 4294967296` by DECIDE_TAC           
  \\ FULL_SIMP_TAC bool_ss [roots_in_mem_def,MEM,ref_cheney_inv_def,APPEND]  
  \\ `{h} SUBSET0 dr0 (icut(b,e)m)` by METIS_TAC [SING_IN_SUBSET0,IN_INSERT]
  \\ `arm_move (ref_addr a j,ref_addr a h,x,xs) = (r41,r51,xs1)` by METIS_TAC [WORD_ADD_0]
  \\ (STRIP_ASSUME_TAC o GSYM o UNDISCH_ALL o RW [GSYM AND_IMP_INTRO] o
   Q.SPECL [`a`,`b`,`b`,`i`,`j`,`j1`,`j'`,`e`,`m`,`m1`,
    `w`,`ww`,`r`,`h`,`r41`,`r51`,`xs`,`xs1`,`x`,`y1`] o Q.INST [`ys`|->`xs`]) (INST_TYPE [``:'a``|->``:word32``] ref_cheney_move)
  \\ ASM_SIMP_TAC bool_ss [WORD_ADD_0]
  \\ `!x. MEM x rs ==> {x} SUBSET0 dr0 (icut (b,e) m1)` by METIS_TAC []
  \\ `ref_cheney (m1,f) (a,x,(r12 =+ r51) xs1,(r12 =+ r51) xs1)` by METIS_TAC [lemma]
  \\ `roots_in_mem (rs++zs) (a,r12 + 4w,(r12 =+ r51) xs1)` by METIS_TAC [roots_lemma]
  \\ Q.PAT_ASSUM `r51 = ref_addr a y1` ASSUME_TAC \\ FULL_SIMP_TAC bool_ss []   
  \\ FULL_SIMP_TAC bool_ss [root_address_ok_def,aligned_def,GSYM ADD1]
  \\ Q.PAT_ASSUM `!j m xs r12. bbb` 
    (STRIP_ASSUME_TAC o UNDISCH_ALL o RW [GSYM AND_IMP_INTRO] o 
     Q.SPECL [`j1`,`m1`,`(r12 =+ ref_addr a y1) xs1`,`r12+4w`,`ys'`,`j2`,`m2`])
  \\ ASM_SIMP_TAC std_ss [LENGTH,ADD1,word_add_n2w,word_mul_n2w,
       GSYM WORD_ADD_ASSOC,LEFT_ADD_DISTRIB,AC ADD_ASSOC ADD_COMM]
  \\ METIS_TAC [APPLY_UPDATE_THM,WORD_LOWER_TRANS,WORD_LOWER_NOT_EQ,ref_cheney_def]);

val ref_cheney_move_roots7 = 
  SIMP_RULE std_ss [LENGTH,ADD1,AND_IMP_INTRO,GSYM CONJ_ASSOC] 
  (Q.SPEC `[x1;x2;x3;x4;x5;x6;x7]` ref_cheney_move_roots)

val arm_c_init_lemma = prove(
  ``(arm_c_init(if u then 0w else 1w,r6,r10) = 
     (r10 + 12w + if u then 0w else r6, if u then 1w else 0w))``,
  Cases_on `u` \\ SIMP_TAC std_ss [SIMP_RULE std_ss [LET_DEF] arm_c_init_def,
    WORD_ADD_0,PAIR_EQ,WORD_XOR_CLAUSES,EVAL ``0w = 1w:word32``]);

val arm_coll_inv_def = Define `
  arm_coll_inv (a,x,xs) (i,e,rs,l,u,m) =
    ?x1 x2 x3 x4 x5 x6 x7. 
      roots_in_mem (rs ++ [i;e]) (a,a-28w,xs) /\
      (rs = [x1;x2;x3;x4;x5;x6;x7]) /\
      valid_address a (l + l + 1) /\
      ref_cheney (m,l+l+1) (a,x,xs,xs) /\
      (xs (a-32w) = if u then 0w else 1w) /\ a - 32w <+ ref_addr a 1 /\ a - 32w <+ a - 28w /\
      (xs (a-36w) = n2w (12 * l)) /\  a - 36w <+ ref_addr a 1 /\ a - 36w <+ a - 28w`;

val roots_in_mem_carry_over = prove(
  ``!p r xs ys. ref_cheney (m,f) (a,x,xs,ys) /\ roots_in_mem p (a,r,ys) ==> roots_in_mem p (a,r,xs)``,
  Induct \\ FULL_SIMP_TAC bool_ss [roots_in_mem_def,ref_cheney_def] \\ METIS_TAC []);

val arm_coll_inv_pre_lemma = prove(
  ``arm_coll_inv (a,x,xs) (q,e,rs,l,u,m) ==>
    {a+4w;a-36w;a-32w;a-28w;a-24w;a-20w;a-16w;a-12w;a-8w;a-4w;a} SUBSET x /\
    !i. i IN {a+4w;a-36w;a-32w;a-28w;a-24w;a-20w;a-16w;a-12w;a-8w;a-4w;a} ==> aligned i``,
  REWRITE_TAC [arm_coll_inv_def,ref_cheney_def] \\ REPEAT STRIP_TAC << [
    Q.PAT_ASSUM `ref_set a (l + l + 1) = x` (ASSUME_TAC o GSYM)
    \\ ASM_SIMP_TAC bool_ss [INSERT_SUBSET,EMPTY_SUBSET,ref_set_def,IN_UNION]
    \\ REPEAT STRIP_TAC
    THEN1 (DISJ1_TAC \\ SIMP_TAC std_ss [GSPECIFICATION] 
           \\ Q.EXISTS_TAC `1` \\ SIMP_TAC std_ss [] \\ DECIDE_TAC)
    \\ DISJ2_TAC \\ SIMP_TAC std_ss [GSPECIFICATION]   
    THEN1 (Q.EXISTS_TAC `9` \\ SIMP_TAC std_ss [])
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
    \\ FULL_SIMP_TAC std_ss [word_arith_lemma3,word_arith_lemma4,GSYM aligned_def]
    \\ REWRITE_TAC [word_sub_def] \\ REPEAT STRIP_TAC
    \\ MATCH_MP_TAC aligned_ADD \\ ASM_SIMP_TAC bool_ss [] \\ EVAL_TAC]);

val arm_collect_lemma = prove(
  ``ok_state (i,e,rs,l,u,m) ==>
    arm_coll_inv (a,x,xs) (i,e,rs,l,u,m) ==>
    (cheney_collector (i,e,rs,l,u,m) = (i',e',rs',l',u',m')) ==>
    (arm_collect (a,x,xs) = (r3',r4',a',xs')) ==>
    arm_collect_pre (a,x,xs) /\
    arm_coll_inv (a,x,xs') (i,e',rs',l',u',m') /\
    (r3' = ref_addr a i') /\ (r4' = ref_addr a e') /\ (a = a') /\ (l = l')``,
  STRIP_TAC \\ STRIP_TAC \\ IMP_RES_TAC arm_coll_inv_pre_lemma
  \\ FULL_SIMP_TAC bool_ss[arm_collector_def,arm_collector_pre_def,GSYM AND_IMP_INTRO,arm_coll_inv_def]
  \\ POP_ASSUM (STRIP_ASSUME_TAC o RW [arm_coll_inv_def])
  \\ ASM_SIMP_TAC bool_ss [LET_DEF]
  \\ ASM_SIMP_TAC std_ss [arm_c_init_lemma]
  \\ Q.ABBREV_TAC `xs1 = (a - 32w =+ (if u then 1w else 0w)) xs`
  \\ Q.ABBREV_TAC `r4l = a + 12w + (if u then 0w else n2w (12 * l))`
  \\ Q.ABBREV_TAC `xs2 = (a + 4w =+ r4l + n2w (12 * l)) xs1`
  \\ `?r43 a3 xs3. arm_move_roots (r4l,7w,a - 28w,x,xs2) = (r43,a3,xs3)` by METIS_TAC [PAIR]
  \\ `?r34 r44 xs4. arm_cheney_loop (r4l,r43,x,xs3) = (r34,r44,xs4)` by METIS_TAC [PAIR]
  \\ ASM_SIMP_TAC std_ss [LET_DEF,cheney_collector_def]   
  \\ Q.ABBREV_TAC `b = if ~u then 1 + l else 1`
  \\ `?ys j2 m2. move_roots ([x1; x2; x3; x4; x5; x6; x7],b,m) = (ys,j2,m2)` by METIS_TAC [PAIR]
  \\ `?i3 m3. cheney (b,j2,b + l,m2) = (i3,m3)` by METIS_TAC [PAIR]
  \\ ASM_SIMP_TAC std_ss []
  \\ ASM_SIMP_TAC std_ss [LET_DEF]
  \\ ONCE_REWRITE_TAC [EQ_SYM_EQ] \\ SIMP_TAC std_ss [GSYM AND_IMP_INTRO]
  \\ REPEAT (MATCH_MP_TAC (METIS_PROVE [] ``P ==> (Q ==> P)``))
  \\ `roots_in_mem (rs ++ [i; e]) (a,a - 28w,xs1)` by 
   (Q.UNABBREV_TAC `xs1`
    \\ FULL_SIMP_TAC bool_ss [APPEND,roots_in_mem_def,APPLY_UPDATE_THM]
    \\ SIMP_TAC (std_ss++WORD_ss) [WORD_EQ_ADD_LCANCEL,n2w_11,
      RW [WORD_ADD_0] (Q.SPECL [`v`,`w`,`0w`] WORD_EQ_ADD_LCANCEL)])
  \\ Q.PAT_ASSUM `roots_in_mem ppp (aaa,bbb,xs)` (K ALL_TAC)
  \\ Q.PAT_ASSUM `rs = ppppp` ASSUME_TAC
  \\ `roots_in_mem (rs ++ [i; b + l]) (a,a - 28w,xs2) /\ a + 4w <+ ref_addr a 1` by 
   (Q.UNABBREV_TAC `xs2` \\ Q.UNABBREV_TAC `b`
    \\ FULL_SIMP_TAC bool_ss [APPEND,roots_in_mem_def,APPLY_UPDATE_THM]
    \\ FULL_SIMP_TAC (std_ss++WORD_ss) [WORD_EQ_ADD_LCANCEL,n2w_11,
      RW [WORD_ADD_0] (Q.SPECL [`v`,`w`,`0w`] WORD_EQ_ADD_LCANCEL)]
    \\ Q.UNABBREV_TAC `r4l` \\ Cases_on `u`
    \\ SIMP_TAC std_ss [ref_addr_def,DECIDE ``~(m+1 = 0)``,GSYM WORD_ADD_ASSOC,
         word_add_n2w,LEFT_ADD_DISTRIB,AC ADD_COMM ADD_ASSOC])
  \\ IMP_RES_TAC (SIMP_RULE std_ss [LET_DEF] ok_state_IMP_cheney_inv)
  \\ Q.UNABBREV_TAC `b`
  \\ Q.ABBREV_TAC `b = if ~u then 1 + l else 1`
  \\ Q.PAT_ASSUM `rs = [x1; x2; x3; x4; x5; x6; x7]` ASSUME_TAC 
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
    \\ Q.EXISTS_TAC `(a - 32w =+ (if u then 1w else 0w)) xs`
    \\ MATCH_MP_TAC lemma \\ ASM_SIMP_TAC bool_ss [])
  \\ FULL_SIMP_TAC bool_ss [APPEND]
  \\ `root_address_ok (a - 28w) 7 x /\ a - 32w IN x /\ a - 36w IN x /\ a + 4w IN x /\
      aligned (a-36w) /\ aligned (a-32w) /\ aligned (a+4w)` by 
   (REWRITE_TAC [GSYM (EVAL ``SUC(SUC(SUC(SUC(SUC(SUC(SUC 0))))))``),root_address_ok_def]
    \\ FULL_SIMP_TAC bool_ss [ref_cheney_def,IN_INSERT]
    \\ FULL_SIMP_TAC std_ss [INSERT_SUBSET,word_arith_lemma1,word_arith_lemma2]
    \\ FULL_SIMP_TAC std_ss [word_arith_lemma3,word_arith_lemma4] \\ METIS_TAC [])
  \\ STRIP_ASSUME_TAC 
    ((UNDISCH_ALL o Q.INST [`f`|->`l+l+1`])
    (Q.SPECL [`b`,`m`,`r4l`,`xs2`,`a-28w`,`ys`,`j2`,`m2`] 
    (Q.INST [`e`|->`b+l`,`j'`|->`b`,`w`|->`m`,`ww`|->`m`,`r`|->`{}`,`i`|->`b`,`r3`|->`ref_addr a b`,`r4n`|->`r43`,`r12n`|->`a3`,`xsn`|->`xs3`,`ii`|->`i`]
    (RW [APPEND,GSYM AND_IMP_INTRO] (Q.SPEC `[ii;e]` ref_cheney_move_roots7)))))    
  \\ `ref_cheney_inv (b,b,j2,j2,b + l,l+l+1,m2,m2,m,range (b,j2)) (a,r4l,r43,x,xs3,xs3)` by 
   (REWRITE_TAC [ref_cheney_inv_def] \\ REPEAT STRIP_TAC << [
      FULL_SIMP_TAC bool_ss [ref_cheney_inv_def] \\ IMP_RES_TAC cheney_inv_setup
      \\ FULL_SIMP_TAC bool_ss [cheney_inv_def] \\ METIS_TAC [], 
      FULL_SIMP_TAC bool_ss [ref_cheney_inv_def],
      MATCH_MP_TAC va_IMP \\ Q.EXISTS_TAC `l+l+1` \\ ASM_SIMP_TAC bool_ss []
      \\ Q.UNABBREV_TAC `b` \\ Cases_on `u` \\ REWRITE_TAC [] \\ DECIDE_TAC,
      FULL_SIMP_TAC bool_ss [ref_cheney_inv_def],
      FULL_SIMP_TAC bool_ss [ref_cheney_inv_def]])
  \\ (STRIP_ASSUME_TAC o UNDISCH_ALL o RW [GSYM AND_IMP_INTRO]) (Q.SPECL [`b`,`b`,`j2`,`b+l`,`m2`,`m2`,`x`,`range(b,j2)`,`r4l`,`r43`,`xs3`,`i3`,`m3`,`r34`,`r44`,`xs4`] (Q.INST [`xx`|->`m`,`ys`|->`xs3`,`f`|->`l+l+1`,`d`|->`x`] (INST_TYPE [``:'a``|->``:word32``] ref_cheney_loop_th)))
  \\ Q.PAT_ASSUM `ref_cheney_inv ppppp (a,r34,r44,x,xs4,xs3)` (STRIP_ASSUME_TAC o RW [ref_cheney_inv_def])
  \\ ONCE_REWRITE_TAC [EQ_SYM_EQ]
  \\ ASM_SIMP_TAC bool_ss [WORD_SUB_ADD,GSYM aligned_def]
  \\ STRIP_TAC THEN1 METIS_TAC []  
  \\ `?x1' x2' x3' x4' x5' x6' x7'. ys = [x1'; x2'; x3'; x4'; x5'; x6'; x7']` by
   (Cases_on `ys` \\ FULL_SIMP_TAC std_ss [LENGTH]
    \\ Cases_on `t` \\ FULL_SIMP_TAC std_ss [LENGTH]
    \\ Cases_on `t'` \\ FULL_SIMP_TAC std_ss [LENGTH]
    \\ Cases_on `t` \\ FULL_SIMP_TAC std_ss [LENGTH]
    \\ Cases_on `t'` \\ FULL_SIMP_TAC std_ss [LENGTH]
    \\ Cases_on `t` \\ FULL_SIMP_TAC std_ss [LENGTH]
    \\ Cases_on `t'` \\ FULL_SIMP_TAC std_ss [LENGTH]
    \\ Cases_on `t` \\ FULL_SIMP_TAC std_ss [LENGTH,CONS_11,ADD1,GSYM ADD_ASSOC] 
    \\ FULL_SIMP_TAC bool_ss [DECIDE ``~(n + 8 = 7)``])
  \\ FULL_SIMP_TAC bool_ss [CONS_11,APPEND]  
  \\ `xs4 (a-32w) = xs2 (a-32w)` by METIS_TAC [ref_cheney_def]
  \\ `xs4 (a-36w) = xs2 (a-36w)` by METIS_TAC [ref_cheney_def]
  \\ Q.PAT_ASSUM ` !i. i <+ a - 28w ==> (xs2 i = xs3 i)` (ASSUME_TAC o GSYM)
  \\ `(a + 4w <+ ref_addr a 1) /\ (xs3 (a+4w) = ref_addr a (b + l))` by ALL_TAC
  THEN1 FULL_SIMP_TAC (std_ss++WORD_ss) [roots_in_mem_def]
  \\ REWRITE_TAC [GSYM CONJ_ASSOC]
  \\ STRIP_TAC THEN1 METIS_TAC [roots_in_mem_carry_over]  
  \\ REVERSE STRIP_TAC << [  
    `(xs4 (a - 36w) = xs3 (a - 36w)) /\ (xs4 (a + 4w) = xs3 (a + 4w)) /\ 
     (xs4 (a - 32w) = xs3 (a - 32w))` by METIS_TAC [ref_cheney_def]
    \\ ASM_SIMP_TAC bool_ss []
    \\ Q.UNABBREV_TAC `xs2` \\ Q.UNABBREV_TAC `xs1` \\ Cases_on `u`
    \\ FULL_SIMP_TAC (std_ss++WORD_ss) [APPLY_UPDATE_THM,WORD_EQ_ADD_LCANCEL,n2w_11,
        RW [WORD_ADD_0] (Q.SPECL [`v`,`w`,`0w`] WORD_EQ_ADD_LCANCEL)],    
    FULL_SIMP_TAC bool_ss [ref_cheney_def,cut_def]
    \\ FULL_SIMP_TAC bool_ss [ref_cheney_def,GSYM cut_def]
    \\ METIS_TAC [ref_mem_def]]);

val arm_alloc_aux_lemma = prove(
  ``ok_state (i,e,rs,l,u,m) ==>
    arm_coll_inv (a,x,xs) (i,e,rs,l,u,m) ==>
    (cheney_alloc_aux (i,e,rs,l,u,m) = (i',e',rs',l',u',m')) ==>
    (arm_alloc_aux (ref_addr a i,ref_addr a e,a,x,xs) = (r3',r4',a',xs')) ==>
    arm_coll_inv (a,x,xs') (i,e',rs',l',u',m') /\ (a = a') /\ (l = l') /\
    (r3' = ref_addr a i') /\ (r4' = ref_addr a e') /\
    arm_alloc_aux_pre (ref_addr a i,ref_addr a e,a,x,xs)``,
  REWRITE_TAC [arm_alloc_aux_def,arm_alloc_aux_pre_def,cheney_alloc_aux_def] 
  \\ STRIP_TAC \\ STRIP_TAC
  \\ `valid_address a i /\ valid_address a e /\ i <= e` by (Cases_on `u` \\ 
    FULL_SIMP_TAC bool_ss [ok_state_def,LET_DEF,arm_coll_inv_def,valid_address_def] \\ DECIDE_TAC)
  \\ `(ref_addr a i = ref_addr a e) = (i = e)` by METIS_TAC [ref_addr_NEQ]
  \\ `(i = e) = ~(i < e)` by DECIDE_TAC
  \\ Cases_on `i < e` \\ ASM_SIMP_TAC bool_ss []
  THEN1 (ONCE_REWRITE_TAC [EQ_SYM_EQ] \\ ASM_SIMP_TAC bool_ss [PAIR_EQ] \\ METIS_TAC [])
  \\ `?r3i r4i r10i xsi. arm_collect (a,x,xs) = (r3i,r4i,r10i,xsi)` by METIS_TAC [PAIR]
  \\ ASM_SIMP_TAC std_ss [LET_DEF] \\ STRIP_TAC
  \\ ONCE_REWRITE_TAC [EQ_SYM_EQ] \\ SIMP_TAC bool_ss [GSYM AND_IMP_INTRO]
  \\ REPEAT (MATCH_MP_TAC (METIS_PROVE [] ``P ==> (Q ==> P)``))
  \\ METIS_TAC [arm_collect_lemma]);

val LO_IMP_ref_addr = prove(
  ``!b a. b <+ ref_addr a 1 /\ valid_address a i /\ ~(i = 0) ==> 
          ~(ref_addr a i = b) /\ ~(ref_addr a i + 4w = b) /\ ~(ref_addr a i + 8w = b)``,
  NTAC 2 Cases_word
  \\ ASM_SIMP_TAC (std_ss++SIZES_ss) [ref_addr_def,WORD_LO,w2n_n2w,valid_address_def,word_add_n2w,n2w_11]
  \\ REPEAT STRIP_TAC
  \\ `n' + 12 * i + 4 < 4294967296 /\ n' + 12 * i < 4294967296` by DECIDE_TAC
  \\ `n' + 12 < 4294967296` by DECIDE_TAC
  \\ FULL_SIMP_TAC std_ss [LESS_MOD] \\ DECIDE_TAC);

val roots_in_mem_UPDATE = prove(
  ``!p b. valid_address a i /\ ~(i = 0) /\ roots_in_mem p (a,b,xs) ==> 
          roots_in_mem p (a,b,(ref_addr a i      =+ y) xs)``,
  Induct \\ ASM_SIMP_TAC std_ss [roots_in_mem_def,APPLY_UPDATE_THM]
  \\ REPEAT STRIP_TAC \\ IMP_RES_TAC WORD_LOWER_NOT_EQ \\ IMP_RES_TAC LO_IMP_ref_addr
  \\ ASM_SIMP_TAC bool_ss []);

val roots_in_mem_UPDATE4 = prove(
  ``!p b. valid_address a i /\ ~(i = 0) /\ roots_in_mem p (a,b,xs) ==> 
          roots_in_mem p (a,b,(ref_addr a i +4w  =+ y) xs)``,
  Induct \\ ASM_SIMP_TAC std_ss [roots_in_mem_def,APPLY_UPDATE_THM]
  \\ REPEAT STRIP_TAC \\ IMP_RES_TAC WORD_LOWER_NOT_EQ \\ IMP_RES_TAC LO_IMP_ref_addr
  \\ ASM_SIMP_TAC bool_ss []);

val roots_in_mem_UPDATE8 = prove(
  ``!p b. valid_address a i /\ ~(i = 0) /\ roots_in_mem p (a,b,xs) ==>   
          roots_in_mem p (a,b,(ref_addr a i + 8w =+ y) xs)``,
  Induct \\ ASM_SIMP_TAC std_ss [roots_in_mem_def,APPLY_UPDATE_THM]
  \\ REPEAT STRIP_TAC \\ IMP_RES_TAC WORD_LOWER_NOT_EQ \\ IMP_RES_TAC LO_IMP_ref_addr
  \\ ASM_SIMP_TAC bool_ss []);

val arm_alloc_aux2_lemma = prove(
  ``ok_state (i,e,rs,l,u,m) ==>
    arm_coll_inv (a,x,xs) (q,e,rs,l,u,m) ==>
    (cheney_alloc_aux2 (i,e,rs,l,u,m) y = (i',e',rs',l',u',m')) ==>
    (arm_alloc_aux2 (y,ref_addr a i,ref_addr a e,a,x,xs) = (r3',xs')) ==>
    arm_coll_inv (a,x,xs') (i',e',rs',l',u',m') /\ (l = l') /\
    arm_alloc_aux2_pre (y,ref_addr a i,ref_addr a e,a,x,xs)``,
  STRIP_TAC \\ REWRITE_TAC [cheney_alloc_aux2_def,arm_alloc_aux2_def,arm_alloc_aux2_pre_def] 
  \\ STRIP_TAC \\ Cases_on `i = e` \\ ASM_SIMP_TAC std_ss [] THEN1
   (ONCE_REWRITE_TAC [EQ_SYM_EQ] 
    \\ SIMP_TAC std_ss [LET_DEF,WORD_ADD_0,GSYM AND_IMP_INTRO]  
    \\ REPEAT (MATCH_MP_TAC (METIS_PROVE [] ``P ==> (Q ==> P)``))
    \\ IMP_RES_TAC arm_coll_inv_pre_lemma 
    \\ REVERSE STRIP_TAC THEN1 METIS_TAC [IN_INSERT,aligned_def,INSERT_SUBSET]
    \\ FULL_SIMP_TAC bool_ss [CONS_11,arm_coll_inv_def,APPLY_UPDATE_THM,APPEND]    
    \\ `roots_in_mem [x1; x2; x3; x4; x5; x6; x7; e; e] (a,a - 28w,(a =+ ref_addr a e) xs) /\
        a <+ ref_addr a 1` by   
     (FULL_SIMP_TAC std_ss [roots_in_mem_def,APPLY_UPDATE_THM,word_arith_lemma1,word_arith_lemma2,APPEND]
      \\ FULL_SIMP_TAC std_ss [word_arith_lemma3,word_arith_lemma4,WORD_ADD_0]
      \\ SIMP_TAC (std_ss++WORD_ss) [RW [WORD_ADD_0] (Q.SPECL [`v`,`0w`] WORD_EQ_ADD_LCANCEL),n2w_11])       
    \\ ASM_SIMP_TAC std_ss [GSYM CONJ_ASSOC]
    \\ STRIP_TAC THEN1 METIS_TAC [lemma]
    \\ SIMP_TAC (std_ss++WORD_ss) [RW [WORD_ADD_0] (Q.SPECL [`v`,`0w`] WORD_EQ_ADD_LCANCEL),n2w_11])
  \\ IMP_RES_TAC arm_coll_inv_pre_lemma 
  \\ `valid_address a i /\ valid_address a e /\ ~(i = 0) /\ ~(e = 0)` by
      (Cases_on `u` \\ FULL_SIMP_TAC std_ss [valid_address_def,arm_coll_inv_def,ok_state_def,LET_DEF]
       \\ DECIDE_TAC)       
  \\ ASM_SIMP_TAC bool_ss [ref_addr_NEQ]
  \\ ONCE_REWRITE_TAC [EQ_SYM_EQ] 
  \\ SIMP_TAC std_ss [LET_DEF,WORD_ADD_0,GSYM AND_IMP_INTRO]  
  \\ REPEAT (MATCH_MP_TAC (METIS_PROVE [] ``P ==> (Q ==> P)``))
  \\ FULL_SIMP_TAC bool_ss [CONS_11,arm_coll_inv_def,APPEND,HD,TL]    
  \\ Q.ABBREV_TAC `xs2 = (a - 28w =+ ref_addr a i) xs`
  \\ Q.ABBREV_TAC `xs1 = ((ref_addr a i + 8w =+ y) ((ref_addr a i + 4w =+ xs (a - 24w))
             ((ref_addr a i =+ xs (a - 28w)) xs2)))`
  \\ `ref_addr a i + 8w + 4w = ref_addr a (i+1)` by 
      FULL_SIMP_TAC std_ss [ref_addr_def,MULT_CLAUSES,GSYM ADD1,
        GSYM WORD_ADD_ASSOC,word_add_n2w,AC ADD_ASSOC ADD_COMM]    
  \\ ASM_SIMP_TAC std_ss []
  \\ `a <+ ref_addr a 1 /\ a - 28w <+ ref_addr a 1` by 
   (FULL_SIMP_TAC std_ss [roots_in_mem_def,APPEND,word_arith_lemma1,word_arith_lemma2]
    \\ FULL_SIMP_TAC std_ss [word_arith_lemma3,word_arith_lemma4,WORD_ADD_0])
  \\ `ref_cheney (m,l+l+1) (a,x,xs2,xs2)` by METIS_TAC [lemma]
  \\ `ref_cheney ((i =+ DATA (x1,x2,y)) m,l+l+1) (a,x,xs1,xs1)` by 
     (FULL_SIMP_TAC std_ss [ref_cheney_def,APPLY_UPDATE_THM] \\ REPEAT STRIP_TAC
      \\ Cases_on `i' = i` \\ ASM_SIMP_TAC bool_ss [ref_mem_def,UPDATE_def] << [
          Q.UNABBREV_TAC `xs1`
          \\ FULL_SIMP_TAC std_ss [roots_in_mem_def,APPLY_UPDATE_THM,word_arith_lemma1,word_arith_lemma2,APPEND]
          \\ FULL_SIMP_TAC std_ss [word_arith_lemma3,word_arith_lemma4,WORD_ADD_0]
          \\ SIMP_TAC (std_ss++WORD_ss) [RW [WORD_ADD_0] (Q.SPECL [`v`,`x`,`0w`] WORD_EQ_ADD_LCANCEL),
               RW [WORD_ADD_0] (Q.SPECL [`v`,`0w`] WORD_EQ_ADD_LCANCEL),n2w_11,WORD_EQ_ADD_LCANCEL],
          Q.UNABBREV_TAC `xs1` \\ Cases_on `m i'` \\ ASM_SIMP_TAC bool_ss [ref_mem_def]
          \\ `valid_address a i'` by METIS_TAC [va_IMP]
          THENL [ALL_TAC,Cases_on `p` \\ Cases_on `r`]
          \\ ASM_SIMP_TAC bool_ss [ref_addr_ADD_NEQ,ref_addr_NEQ,UPDATE_def,ref_mem_def,WORD_EQ_ADD_RCANCEL] 
          \\ METIS_TAC [ref_mem_def]])
  \\ `ref_cheney ((i =+ DATA (x1,x2,y)) m,l+l+1)
      (a,x,(a =+ ref_addr a (i + 1)) xs1,(a =+ ref_addr a (i + 1)) xs1)` by METIS_TAC [lemma]
  \\ ASM_SIMP_TAC std_ss []
  \\ `roots_in_mem [i; x2; x3; x4; x5; x6; x7; q; e] (a,a - 28w,xs2)` by 
     (Q.UNABBREV_TAC `xs2`
      \\ FULL_SIMP_TAC std_ss [roots_in_mem_def,APPLY_UPDATE_THM,word_arith_lemma1,word_arith_lemma2,APPEND]
      \\ FULL_SIMP_TAC std_ss [word_arith_lemma3,word_arith_lemma4,WORD_ADD_0]
      \\ SIMP_TAC (std_ss++WORD_ss) [RW [WORD_ADD_0] (Q.SPECL [`v`,`0w`] WORD_EQ_ADD_LCANCEL),n2w_11]       
      \\ SIMP_TAC (std_ss++WORD_ss) [RW [WORD_ADD_0] (Q.SPECL [`v`,`x`,`0w`] WORD_EQ_ADD_LCANCEL),
           RW [WORD_ADD_0] (Q.SPECL [`v`,`0w`] WORD_EQ_ADD_LCANCEL),n2w_11,WORD_EQ_ADD_LCANCEL])
  \\ `roots_in_mem [i; x2; x3; x4; x5; x6; x7; q; e] (a,a - 28w,xs1)` by 
          METIS_TAC [roots_in_mem_UPDATE,roots_in_mem_UPDATE4,roots_in_mem_UPDATE8]
  \\ REVERSE STRIP_TAC THEN1
   (`i <= l+l+1` by (Cases_on `u` \\ FULL_SIMP_TAC bool_ss [ok_state_def,LET_DEF] \\ DECIDE_TAC)
    \\ IMP_RES_TAC ref_cheney_d    
    \\ ONCE_REWRITE_TAC [EQ_SYM_EQ]
    \\ FULL_SIMP_TAC std_ss [ref_cheney_def,GSYM aligned_def,INSERT_SUBSET,LENGTH,aligned_ref_addr]
    \\ REPEAT STRIP_TAC \\ REWRITE_TAC [word_sub_def]
    \\ REPEAT (MATCH_MP_TAC aligned_ADD) \\ ASM_SIMP_TAC bool_ss [] \\ REPEAT STRIP_TAC
    \\ REPEAT (MATCH_MP_TAC aligned_ref_addr) \\ ASM_SIMP_TAC bool_ss [] \\ EVAL_TAC)
  \\ STRIP_TAC THEN1 
     (FULL_SIMP_TAC std_ss [roots_in_mem_def,APPLY_UPDATE_THM,word_arith_lemma1,word_arith_lemma2,APPEND]
      \\ FULL_SIMP_TAC std_ss [word_arith_lemma3,word_arith_lemma4,WORD_ADD_0]
      \\ SIMP_TAC (std_ss++WORD_ss) [RW [WORD_ADD_0] (Q.SPECL [`v`,`0w`] WORD_EQ_ADD_LCANCEL),n2w_11]       
      \\ SIMP_TAC (std_ss++WORD_ss) [RW [WORD_ADD_0] (Q.SPECL [`v`,`x`,`0w`] WORD_EQ_ADD_LCANCEL),
           RW [WORD_ADD_0] (Q.SPECL [`v`,`0w`] WORD_EQ_ADD_LCANCEL),n2w_11,WORD_EQ_ADD_LCANCEL])
  \\ Q.UNABBREV_TAC `xs1` \\ Q.UNABBREV_TAC `xs2`
  \\ IMP_RES_TAC LO_IMP_ref_addr
  \\ SIMP_TAC bool_ss [UPDATE_def]
  \\ ASM_SIMP_TAC bool_ss []
  \\ SIMP_TAC (std_ss++WORD_ss) [RW [WORD_ADD_0] (Q.SPECL [`v`,`0w`] WORD_EQ_ADD_LCANCEL),n2w_11]       
  \\ SIMP_TAC (std_ss++WORD_ss) [RW [WORD_ADD_0] (Q.SPECL [`v`,`x`,`0w`] WORD_EQ_ADD_LCANCEL),
         RW [WORD_ADD_0] (Q.SPECL [`v`,`0w`] WORD_EQ_ADD_LCANCEL),n2w_11,WORD_EQ_ADD_LCANCEL]);

val arm_alloc_lemma = prove(
  ``ok_state (i,e,rs,l,u,m) ==>
    arm_coll_inv (a,x,xs) (i,e,rs,l,u,m) ==>
    (cheney_alloc (i,e,rs,l,u,m) y = (i',e',rs',l',u',m')) ==>
    (arm_alloc_mem (y,a,x,xs) = (a',xs')) ==>
    arm_coll_inv (a',x,xs') (i',e',rs',l',u',m') /\ (a' = a) /\ (l' = l) /\ 
    arm_alloc_mem_pre (y,a,x,xs)``,
  REWRITE_TAC [cheney_alloc_def,arm_alloc_mem_def,arm_alloc_mem_pre_def] \\ STRIP_TAC \\ STRIP_TAC
  \\ `(xs a = ref_addr a i) /\ (xs (a+4w) = ref_addr a e)` by 
   (FULL_SIMP_TAC std_ss [arm_coll_inv_def,APPEND,roots_in_mem_def]
    \\ FULL_SIMP_TAC std_ss [arm_coll_inv_def,APPEND,roots_in_mem_def]
    \\ FULL_SIMP_TAC std_ss [roots_in_mem_def,APPLY_UPDATE_THM,word_arith_lemma1,word_arith_lemma2,APPEND]
    \\ FULL_SIMP_TAC std_ss [word_arith_lemma3,word_arith_lemma4,WORD_ADD_0]
    \\ SIMP_TAC (std_ss++WORD_ss) [RW [WORD_ADD_0] (Q.SPECL [`v`,`0w`] WORD_EQ_ADD_LCANCEL),n2w_11]       
    \\ SIMP_TAC (std_ss++WORD_ss) [RW [WORD_ADD_0] (Q.SPECL [`v`,`x`,`0w`] WORD_EQ_ADD_LCANCEL),
         RW [WORD_ADD_0] (Q.SPECL [`v`,`0w`] WORD_EQ_ADD_LCANCEL),n2w_11,WORD_EQ_ADD_LCANCEL])
  \\ `?r3i r4i r10i xsi. arm_alloc_aux (ref_addr a i,ref_addr a e,a,x,xs) = (r3i,r4i,r10i,xsi)` by METIS_TAC [PAIR]
  \\ `?r3j xsj. arm_alloc_aux2 (y,r3i,r4i,r10i,x,xsi) = (r3j,xsj)` by METIS_TAC [PAIR]
  \\ `?i2 e2 rs2 l2 u2 m2. cheney_alloc_aux (i,e,rs,l,u,m) = (i2,e2,rs2,l2,u2,m2)` by METIS_TAC [PAIR]
  \\ ASM_SIMP_TAC std_ss [LET_DEF] \\ STRIP_TAC
  \\ ONCE_REWRITE_TAC [EQ_SYM_EQ] \\ ASM_SIMP_TAC std_ss []
  \\ ONCE_REWRITE_TAC [EQ_SYM_EQ] \\ ASM_SIMP_TAC std_ss [GSYM aligned_def]
  \\ IMP_RES_TAC arm_alloc_aux_lemma
  \\ `ok_state (i2,e2,rs2,l2,u2,m2)` by METIS_TAC [cheney_collector_spec,cheney_alloc_aux_def]
  \\ IMP_RES_TAC arm_coll_inv_pre_lemma 
  \\ ONCE_REWRITE_TAC [EQ_SYM_EQ] \\ ASM_SIMP_TAC std_ss []
  \\ METIS_TAC [arm_alloc_aux2_lemma,aligned_def,INSERT_SUBSET,arm_coll_inv_def,ref_cheney_def]);

val addr_list_def = Define `
  (addr_list [] (a,r12,m) = T) /\
  (addr_list (x::xs) (a,r12,m) = (m r12 = ref_addr a x) /\ addr_list xs (a,r12 + 4w,m))`;

val roots_in_mem_IMP_addr_list = prove(
  ``!p a b xs. roots_in_mem p (a,b,xs) ==> addr_list p (a,b,xs)``,
  Induct \\ ASM_SIMP_TAC std_ss [addr_list_def,roots_in_mem_def]);



val ch_mem_def = Define `
  ch_mem (i,e,rs,l,u,m) (a,x,xs) =
    ?x1 x2 x3 x4 x5 x6 x7. 
      36 <= w2n a /\ w2n a + 2 * 12 * l + 20 < 2**32 /\
      ok_state(i,e,rs,l,u,m) /\
      addr_list (rs ++ [i;e]) (a,a-28w,xs) /\
      (rs = [x1;x2;x3;x4;x5;x6;x7]) /\
      ref_cheney (m,l+l+1) (a,x,xs,xs) /\
      (xs (a-32w) = if u then 0w else 1w) /\ 
      (xs (a-36w) = n2w (12 * l)) /\ ~(l = 0)`;

val ch_word_def = Define `
  ch_word (i,e,rs,l,u,m) (v1,v2,v3,v4,v5,v6,v7,a,x,xs) =
    ?x1 x2 x3 x4 x5 x6 x7. 
      36 <= w2n a /\ w2n a + 2 * 12 * l + 20 < 2**32 /\
      ok_state(i,e,rs,l,u,m) /\ ref_cheney (m,l+l+1) (a,x,xs,xs) /\ 
      (rs = [x1;x2;x3;x4;x5;x6;x7]) /\
      (v1 = ref_addr a x1) /\ (v2 = ref_addr a x2) /\ (v3 = ref_addr a x3) /\ 
      (v4 = ref_addr a x4) /\ (v5 = ref_addr a x5) /\ (v6 = ref_addr a x6) /\ 
      (v7 = ref_addr a x7) /\ (xs a = ref_addr a i) /\ (xs (a+4w) = ref_addr a e) /\
      (xs (a-32w) = if u then 0w else 1w) /\ (xs (a-36w) = n2w (12 * l)) /\ ~(l = 0)`;

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
  ``ch_mem (i,e,rs,l,u,m) (a,x,xs) ==>
    ok_state (i,e,rs,l,u,m) /\ arm_coll_inv (a,x,xs) (i,e,rs,l,u,m)``,
  REWRITE_TAC [ch_mem_def,arm_coll_inv_def] \\ REPEAT STRIP_TAC 
  \\ FULL_SIMP_TAC std_ss [CONS_11,APPEND,roots_in_mem_def,addr_list_def,valid_address_def]
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
  \\ REPEAT (MATCH_MP_TAC ch_mem_lemma5 \\ ASM_SIMP_TAC std_ss [] \\ DECIDE_TAC));
        
val ch_mem_cheney_alloc_lemma = prove(
  ``ch_mem (i,e,rs,l,u,m) (a,x,xs) ==> 
    (cheney_alloc (i,e,rs,l,u,m) d = (i',e',rs',l',u',m')) ==>
    (arm_alloc_mem (d,a,x,xs) = (a',xs')) ==>
    ch_mem (i',e',rs',l',u',m') (a',x,xs') /\ (a = a') /\ (l = l') /\
    arm_alloc_mem_pre (d,a,x,xs) /\ arm_coll_inv (a,x,xs) (i,e,rs,l,u,m)``,
  NTAC 3 STRIP_TAC \\ IMP_RES_TAC ch_mem_IMP_arm_coll_inv
  \\ IMP_RES_TAC arm_alloc_lemma 
  \\ FULL_SIMP_TAC bool_ss [ch_mem_def,APPEND]
  \\ `ok_state (i',e',rs',l',u',m')` by METIS_TAC [cheney_alloc_ok]
  \\ FULL_SIMP_TAC std_ss [arm_coll_inv_def,CONS_11]
  \\ STRIP_TAC THEN1 METIS_TAC []
  \\ Q.PAT_ASSUM `rs' = xxxxx` (fn th => FULL_SIMP_TAC std_ss [th])
  \\ FULL_SIMP_TAC bool_ss [APPEND,roots_in_mem_def,addr_list_def]);    

val ch_word_alloc = store_thm("ch_word_alloc",
  ``ch_word (i,e,rs,l,u,m) (v1,v2,v3,v4,v5,v6,v7,a,x,xs) ==> 
    (cheney_alloc (i,e,rs,l,u,m) d = (i',e',rs',l',u',m')) ==>
    (arm_alloc (d,v1,v2,v3,v4,v5,v6,v7,a,x,xs) = (w1,w2,w3,w4,w5,w6,w7,a',xs')) ==>
    ch_word (i',e',rs',l',u',m') (w1,w2,w3,w4,w5,w6,w7,a',x,xs') /\ (a = a') /\ (l = l') /\
    arm_alloc_pre (d,v1,v2,v3,v4,v5,v6,v7,a,x,xs)``,
  REWRITE_TAC [arm_alloc_def,arm_alloc_pre_def]
  \\ Q.ABBREV_TAC `xs1 = (a - 4w =+ v7)
      ((a - 8w =+ v6) ((a - 12w =+ v5) ((a - 16w =+ v4)
      ((a - 20w =+ v3) ((a - 24w =+ v2) ((a - 28w =+ v1) xs))))))`
  \\ `?r10i xsi. arm_alloc_mem (d,a,x,xs1) = (r10i,xsi)` by METIS_TAC [PAIR]
  \\ ASM_SIMP_TAC std_ss [LET_DEF] \\ STRIP_TAC \\ STRIP_TAC
  \\ ONCE_REWRITE_TAC [EQ_SYM_EQ] \\ ASM_SIMP_TAC std_ss []
  \\ MATCH_MP_TAC (METIS_PROVE [] ``Q ==> (P ==> Q)``)  
  \\ `ch_mem (i,e,rs,l,u,m) (a,x,xs1)` by ALL_TAC << [
    FULL_SIMP_TAC bool_ss [ch_mem_def,ch_word_def,CONS_11]    
    \\ `ref_cheney (m,l+l+1) (a,x,xs1,xs1)` by (Q.UNABBREV_TAC `xs1`
        \\ Cases_on `a = 0w` THEN1 FULL_SIMP_TAC (std_ss++WORD_ss) [w2n_n2w]
        \\ REPEAT (MATCH_MP_TAC (Q.INST [`xs`|->`xs1`] lemma) 
          \\ REVERSE STRIP_TAC THEN1  
            (SIMP_TAC std_ss [ref_addr_def] \\ MATCH_MP_TAC ch_mem_lemma1
             \\ ASM_SIMP_TAC bool_ss [] \\ DECIDE_TAC))
        \\ METIS_TAC [])
    \\ ASM_SIMP_TAC bool_ss []
    \\ ASM_SIMP_TAC std_ss [addr_list_def,APPEND,word_arith_lemma1,word_arith_lemma2]
    \\ ASM_SIMP_TAC std_ss [addr_list_def,APPEND,word_arith_lemma3,word_arith_lemma4]
    \\ REPEAT STRIP_TAC \\ Q.UNABBREV_TAC `xs1`
    \\ ASM_SIMP_TAC (std_ss++WORD_ss) [APPLY_UPDATE_THM,WORD_EQ_ADD_LCANCEL,n2w_11,
         RW [WORD_ADD_0] (Q.SPECL [`v`,`x`,`0w`] WORD_EQ_ADD_LCANCEL),
         RW [WORD_ADD_0] (Q.SPECL [`v`,`0w`] WORD_EQ_ADD_LCANCEL)],
    IMP_RES_TAC ch_mem_cheney_alloc_lemma
    \\ Q.PAT_ASSUM `ch_mem (i,e,rs,l,u,m) (a,x,xs1)` (K ALL_TAC)
    \\ FULL_SIMP_TAC bool_ss [APPEND,ch_word_def,ch_mem_def,addr_list_def,CONS_11]
    \\ FULL_SIMP_TAC bool_ss [APPEND,ch_word_def,ch_mem_def,addr_list_def,CONS_11]
    \\ FULL_SIMP_TAC std_ss [addr_list_def,APPEND,word_arith_lemma1,word_arith_lemma2]
    \\ FULL_SIMP_TAC std_ss [addr_list_def,APPEND,word_arith_lemma3,word_arith_lemma4]
    \\ IMP_RES_TAC arm_coll_inv_pre_lemma
    \\ FULL_SIMP_TAC std_ss [WORD_ADD_0,LENGTH,IN_INSERT,NOT_IN_EMPTY,INSERT_SUBSET,aligned_def]
    \\ METIS_TAC []]);

val ch_arm_def = Define `ch_arm s c = ?t. ch_inv s t /\ ch_word t c`;

val ch_arm_alloc = store_thm("ch_arm_alloc",
  ``(arm_alloc (d,v1,v2,v3,v4,v5,v6,v7,a,x,xs) = (w1,w2,w3,w4,w5,w6,w7,a',xs')) ==>
    CARD (reachables (t1::t2::ts) (ch_set h)) < l ==>
    ch_arm (t1::t2::ts,h,l) (v1,v2,v3,v4,v5,v6,v7,a,x,xs) ==> 
    ch_arm (fresh h::t2::ts,h |+ (fresh h,t1,t2,d),l) (w1,w2,w3,w4,w5,w6,w7,a',x,xs') /\
    (a' = a) /\ arm_alloc_pre (d,v1,v2,v3,v4,v5,v6,v7,a,x,xs)``,
  REWRITE_TAC [ch_arm_def] \\ STRIP_TAC \\ STRIP_TAC \\ STRIP_TAC
  \\ `?i e rs l u m. t = (i,e,rs,l,u,m)` by METIS_TAC [PAIR]
  \\ `?i' e' rs' l' u' m'. cheney_alloc (i,e,rs,l,u,m) d = (i',e',rs',l',u',m')` by METIS_TAC [PAIR]
  \\ `l' = l` by METIS_TAC [ch_inv_def] \\ FULL_SIMP_TAC bool_ss []
  \\ IMP_RES_TAC ch_word_alloc \\ ASM_SIMP_TAC bool_ss []  
  \\ Q.EXISTS_TAC `(i',e',rs',l'',u',m')` \\ ASM_SIMP_TAC bool_ss [cheney_alloc_spec]
  \\ METIS_TAC [cheney_alloc_spec]);

val HEAP_def = Define `
  HEAP (a,l) (v1,v2,v3,v4,v5,v6,v7,h) =
    SEP_EXISTS r3 r4 r5 r6 r7 r8 r9 x xs.
      R 3w r3 * R 4w r4 * R 5w r5 * R 6w r6 * R 7w r7 * R 8w r8 * R 9w r9 * R 10w a * MEMORY x xs * 
      cond (ch_arm ([v1;v2;v3;v4;v5;v6;v7],h,l) (r3,r4,r5,r6,r7,r8,r9,a,x,xs))`;   

open arm_progLib;
open set_sepLib;
open set_sepTheory

val _ = Parse.hide "r0";

val ARM_HEAP_alloc = save_thm("ARM_HEAP_alloc",let
val th = arm_alloc_thm
val th = APP_FRAME `cond (ch_arm ([v1;v2;v3;v4;v5;v6;v7],h,l) (r3,r4,r5,r6,r7,r8,r9,r10,x,xs) /\ 
                          CARD (reachables [v1;v2;v3;v4;v5;v6;v7] (ch_set h)) < l)` th
val th = APP_WEAKEN1 th `
    R 0w r0 * HEAP (r10,l) (fresh h,v2,v3,v4,v5,v6,v7,h |+ (fresh h,v1,v2,r0)) * ~S`
 (REWRITE_TAC [SEP_IMP_MOVE_COND] \\ REPEAT STRIP_TAC
  \\ `?w1 w2 w3 w4 w5 w6 w7 a' xs'.
        arm_alloc (r0,r3,r4,r5,r6,r7,r8,r9,r10,x,xs) = 
        (w1,w2,w3,w4,w5,w6,w7,a',xs')` by METIS_TAC [PAIR]
  \\ ASM_SIMP_TAC (bool_ss++sep2_ss) [FST,SND,HEAP_def] 
  \\ IMP_RES_TAC ch_arm_alloc
  \\ SIMP_TAC std_ss [SEP_IMP_def,SEP_EXISTS,cond_STAR] 
  \\ REPEAT STRIP_TAC  \\ Q.EXISTS_TAC `w1`
  \\ Q.EXISTS_TAC `w2` \\ Q.EXISTS_TAC `w3`
  \\ Q.EXISTS_TAC `w4` \\ Q.EXISTS_TAC `w5`
  \\ Q.EXISTS_TAC `w6` \\ Q.EXISTS_TAC `w7`
  \\ Q.EXISTS_TAC `x`  \\ Q.EXISTS_TAC `xs'`
  \\ Q.PAT_ASSUM `a' = r10` ASSUME_TAC
  \\ FULL_SIMP_TAC (bool_ss++star_ss) [])
val th = EXISTS_PRE `xs` th
val th = EXISTS_PRE `x` th
val th = EXISTS_PRE `r9` th
val th = EXISTS_PRE `r8` th
val th = EXISTS_PRE `r7` th
val th = EXISTS_PRE `r6` th
val th = EXISTS_PRE `r5` th
val th = EXISTS_PRE `r4` th
val th = EXISTS_PRE `r3` th
val th = APP_STRENGTHEN th `
    R 0w r0 * HEAP (r10,l) (v1,v2,v3,v4,v5,v6,v7,h) * ~S * 
    cond (CARD (reachables [v1;v2;v3;v4;v5;v6;v7] (ch_set h)) < l)`
 (REWRITE_TAC [SEP_IMP_MOVE_COND] \\ REPEAT STRIP_TAC
  \\ ASM_SIMP_TAC (bool_ss++sep2_ss) [FST,SND,HEAP_def] 
  \\ IMP_RES_TAC ch_arm_alloc
  \\ SIMP_TAC std_ss [SEP_IMP_def,SEP_EXISTS,cond_STAR] 
  \\ REPEAT STRIP_TAC 
  \\ Q.ABBREV_TAC `i3 = y` \\ Q.EXISTS_TAC `i3`
  \\ Q.ABBREV_TAC `i4 = y'` \\ Q.EXISTS_TAC `i4`
  \\ Q.ABBREV_TAC `i5 = y''` \\ Q.EXISTS_TAC `i5`
  \\ Q.ABBREV_TAC `i6 = y'''` \\ Q.EXISTS_TAC `i6`
  \\ Q.ABBREV_TAC `i7 = y''''` \\ Q.EXISTS_TAC `i7`
  \\ Q.ABBREV_TAC `i8 = y'''''` \\ Q.EXISTS_TAC `i8`
  \\ Q.ABBREV_TAC `i9 = y''''''` \\ Q.EXISTS_TAC `i9`
  \\ Q.ABBREV_TAC `z  = y'''''''` \\ Q.EXISTS_TAC `z`
  \\ Q.ABBREV_TAC `zs = y''''''''` \\ Q.EXISTS_TAC `zs`
  \\ SIMP_TAC (bool_ss++sep2_ss) [sidecond_def,cond_STAR]
  \\ `?w1 w2 w3 w4 w5 w6 w7 a' xs'.
        arm_alloc (r0,i3,i4,i5,i6,i7,i8,i9,r10,z,zs) = 
        (w1,w2,w3,w4,w5,w6,w7,a',xs')` by METIS_TAC [PAIR]
  \\ IMP_RES_TAC ch_arm_alloc
  \\ FULL_SIMP_TAC (bool_ss++star_ss) []) 
val th = append_ret th
in th end);

val _ = add_compiled "ACA" ARM_HEAP_alloc;

val (alloc_list_def,alloc_list_pre_def,th) = arm_decompiler "alloc_list" `T` NONE ["r0"] `
  cmp   r0,#0
  beq   16
  insert: ACA
  sub   r0,r0,#1
  b     -16`;

val fresh_NOT_IN_reachables = prove(
  ``!h v1 v2 x. ~((fresh h,v1,v2,x) IN reachables vs (ch_set h))``,
  SIMP_TAC bool_ss [IN_DEF,reachables_def]
  \\ SIMP_TAC bool_ss [ch_set_def,fresh_NOT_IN_FDOM]);

val reachables_lemma = prove(
  ``reachables [v1; v2; v2; v3; v4; v5; v6; v7] s = 
    reachables [v1; v2; v3; v4; v5; v6; v7] s``,
  REWRITE_TAC [METIS_PROVE [PAIR] ``(f = g) = !a x y d. f (a,x,y,d) = g (a,x,y,d)``]
  \\ SIMP_TAC std_ss [reachables_def,MEM] \\ METIS_TAC []);

val WORD_INDUCT = prove(
 ``!P. P 0w /\ (!n. SUC n < dimword(:'a) ==> P (n2w n) ==> P (n2w (SUC n))) ==>
       !x:'a word. P x``,
 STRIP_TAC \\ STRIP_TAC \\ Cases_word \\ Induct_on `n`
 \\ METIS_TAC [DECIDE ``SUC n < m ==> n < m``]);

val alloc_list_pre_thm = prove(
  ``!r0 h v1. alloc_list_pre (r0,h,l,v1,v2,v3,v4,v5,v6,v7) =
      CARD (reachables [v1; v2; v3; v4; v5; v6; v7] (ch_set h)) + w2n r0 <= l \/ (r0 = 0w)``,
  recInduct WORD_INDUCT \\ REPEAT STRIP_TAC
  THEN1 (ONCE_REWRITE_TAC [alloc_list_pre_def] \\ METIS_TAC [])
  \\ ONCE_REWRITE_TAC [alloc_list_pre_def]
  \\ ASM_SIMP_TAC std_ss [n2w_11,ZERO_LT_dimword,DECIDE ``~(SUC n = 0)``,LET_DEF]
  \\ Q.PAT_ASSUM `SUC n < dimword (:32)` ASSUME_TAC
  \\ `n < dimword (:32)` by DECIDE_TAC
  \\ FULL_SIMP_TAC std_ss [w2n_n2w,LESS_MOD]
  \\ ASM_SIMP_TAC std_ss [ADD1,GSYM word_add_n2w,WORD_ADD_SUB]
  \\ ASM_SIMP_TAC bool_ss [reachables_fresh,CARD_INSERT,FINITE_reachables,
       fresh_NOT_IN_reachables,reachables_lemma,n2w_11,LESS_MOD,ZERO_LT_dimword]  
  \\ DECIDE_TAC);



val _ = export_theory();

