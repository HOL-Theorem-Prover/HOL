open HolKernel boolLib bossLib Parse; val _ = new_theory "lisp_equal";
val _ = ParseExtras.temp_loose_equality()

open wordsTheory arithmeticTheory wordsLib listTheory pred_setTheory pairTheory;
open combinTheory finite_mapTheory addressTheory;

open decompilerLib compilerLib;
open mc_tailrecLib tailrecTheory cheney_gcTheory cheney_allocTheory;
open lisp_gcTheory lisp_typeTheory lisp_invTheory;


val _ = map Parse.hide ["r0","r1","r2","r3","r4","r5","r6","r7","r8","r9","r10","r11","r12","r13"];
val RW = REWRITE_RULE;
val RW1 = ONCE_REWRITE_RULE;

val bool_ss = bool_ss -* ["lift_disj_eq", "lift_imp_disj"]
val std_ss = std_ss -* ["lift_disj_eq", "lift_imp_disj"]


val _ = codegen_x86Lib.set_x86_regs
  [(3,"eax"),(4,"ecx"),(5,"edx"),(6,"ebx"),(7,"edi"),(8,"esi"),(9,"ebp")]

val (th1,arm_eq_loop_def,arm_eq_loop_pre_def) = compile_all ``
  arm_eq_loop (r3:word32,r4:word32,r5:word32,r6:word32,r7:word32,r8:word32,df:word32 set,f:word32->word32) =
    if r3 = r4 then
      if r8 = 0x0w then
        (r3,r4,r5,r6,r7,r8,df,f)
      else
        let r4 = f (r7 - 0x4w) in
        let r7 = r7 - 0x4w in
        let r3 = f (r7 - 0x4w) in
        let r7 = r7 - 0x4w in
        let r8 = r8 - 0x1w in
          arm_eq_loop (r3,r4,r5,r6,r7,r8,df,f)
   else
     let r5 = r3 || r4 in
       if r5 && 3w = 0x0w then
         let r5 = f (r3 + 0x4w) in
         let r3 = f r3 in
         let r6 = f (r4 + 0x4w) in
         let r4 = f r4 in
         let f = (r7 =+ r5) f in
         let r7 = r7 + 0x4w in
         let f = (r7 =+ r6) f in
         let r7 = r7 + 0x4w in
         let r8 = r8 + 0x1w in
           arm_eq_loop (r3,r4,r5,r6,r7,r8,df,f)
       else
         (r3,r4,r5,r6,r7,r8,df,f)``;

val (th1,arm_eq_init_def,arm_eq_init_pre_def) = compile_all ``
  arm_eq_init (r5:word32,r6:word32,r9:word32) =
    let r7 = r9 + 0x8w in
      if r5 = 0x0w then
        (r5,r6,r7,r9)
      else
        let r7 = r7 + r6 in (r5,r6,r7,r9)``;

val (th1,arm_eq_assign_def,arm_eq_assign_pre_def) = compile_all ``
  arm_eq_assign (r3:word32,r4:word32) =
    if r3 = r4 then
      let r3 = 0xFw in (r3:word32,r4)
    else
      let r3 = 0x3w in (r3:word32,r4)``

val (arm_eq_thms,arm_eq_def,arm_eq_pre_def) = compile_all ``
  arm_eq (r3,r4,r5,r6,r7,r8,r9,df,f) =
    if r3 = r4 then
      let r3 = 0xFw in (r3,r4,r5,r6,r7,r8,r9,df,f)
    else
     let f = (r9 - 0x14w =+ r4) f in
      let f = (r9 - 0x10w =+ r5) f in
      let f = (r9 - 0xCw =+ r6) f in
      let f = (r9 - 0x8w =+ r7) f in
      let f = (r9 - 0x4w =+ r8) f in
      let r5 = f (r9 - 0x1Cw) in
      let r6 = f (r9 - 0x20w) in
      let (r5,r6,r7,r9) = arm_eq_init (r5,r6,r9) in
      let r8 = 0x0w in
      let (r3,r4,r5,r6,r7,r8,df,f) = arm_eq_loop (r3,r4,r5,r6,r7,r8,df,f) in
      let (r3,r4) = arm_eq_assign (r3,r4) in
      let r4 = f (r9 - 0x14w) in
      let r5 = f (r9 - 0x10w) in
      let r6 = f (r9 - 0xCw) in
      let r7 = f (r9 - 0x8w) in
      let r8 = f (r9 - 0x4w) in
        (r3,r4,r5,r6,r7,r8,r9,df,f)``;

fun save_all prefix postfix =
  map (fn (n,th) => save_thm(prefix ^ n ^ postfix,th));

val _ = save_all "" "_eq_thm" arm_eq_thms

val word_tree2_def = Define `
  (word_tree2 (XVal w) (a,m) d = (a = ADDR32 w + 0x2w)) /\
  (word_tree2 (XSym w) (a,m) d = (a = ADDR32 w + 0x3w)) /\
  (word_tree2 (XDot x y) (a,m) d = ALIGNED a /\
     a IN d /\ (a + 4w) IN d /\
     word_tree2 x (m a,m) d /\ word_tree2 y (m (a + 0x4w),m) d)`;

val lisp_stack_def = Define `
  (lisp_stack [] (a,m,d,e) = ALIGNED a) /\
  (lisp_stack ((x,y)::xs) (a,m,d,e) = (a - 4w) IN e /\ (a - 8w) IN e /\
     word_tree2 y (m (a - 4w),m) d /\ word_tree2 x (m (a - 8w),m) d /\
     lisp_stack xs (a-8w,m,d,e))`;

val word_tree2_11 = prove(
  ``!x y a m d. word_tree2 x (a,m) d /\ word_tree2 y (a,m) d ==> (x = y)``,
  Induct \\ Cases_on `y` \\ REWRITE_TAC [word_tree2_def,XExp_11]
  \\ METIS_TAC [NOT_ALIGNED,ALIGNED_ADDR32,ALIGNED_add_2_and_3,ALIGNED_add_3_and_3,
       EVAL ``2w = 3w:word32``,WORD_EQ_ADD_RCANCEL,ADDR32_11]);

val word_tree2_ALIGNED_LEMMA = prove(
  ``~ALIGNED r3 /\ word_tree2 x (r3,m) d /\ ~(r3 = r4) /\ word_tree2 y (r4,m) d ==>
    ~(x = y)``,
  REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [] \\ Cases_on `y`
  \\ FULL_SIMP_TAC std_ss [word_tree2_def]);

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

val word_tree2_IGNORE_WRITE = prove(
  ``!a d. ~(a IN d) ==>
          !x w v m. word_tree2 x (w,(a =+ v) m) d = word_tree2 x (w,m) d``,
  NTAC 3 STRIP_TAC \\ Induct
  \\ ASM_SIMP_TAC std_ss [word_tree2_def,APPLY_UPDATE_THM]
  \\ METIS_TAC []);

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
  \\ ASM_SIMP_TAC std_ss [word_tree2_IGNORE_WRITE,APPLY_UPDATE_THM]
  \\ `~(a = 0w) /\ ~(a - 4w = 0w) /\ ~(a - 8w = 0w)` by METIS_TAC []
  \\ `~(b = a - 4w) /\ ~(b = a - 8w) /\ a - 8w <=+ b` by METIS_TAC [LEMMA]
  \\ FULL_SIMP_TAC std_ss []
  \\ Q.PAT_X_ASSUM `!x.bbb` MATCH_MP_TAC
  \\ ASM_SIMP_TAC std_ss [word_sub_def]
  \\ MATCH_MP_TAC ALIGNED_ADD \\ ASM_SIMP_TAC std_ss [ALIGNED_NEG] \\ EVAL_TAC);

val arm_eq_loop_spec_lemma = prove(
  ``!ys:(XExp # XExp) list x y d e m r3 r4 r5 r6 r7 r8. (d INTER e = {}) /\
      (arm_eq_loop (r3,r4,r5,r6,r7,r8,df,m) = (u3,u4,u5,u6,u7,u8,udf,uf)) /\
      (r8 = n2w (LENGTH ys)) /\ (MAX_XDEPTH (x::MAP FST ys) < 2**32) /\
      (MAX_ADDRESSES r7 (x::MAP FST ys)) SUBSET e /\ ~(0w IN e) /\ e SUBSET df /\ d SUBSET df /\
      lisp_stack ys (r7,m,d,e) /\ word_tree2 x (r3,m) d /\ word_tree2 y (r4,m) d ==>
      arm_eq_loop_pre (r3,r4,r5,r6,r7,r8,df,m) /\
      ((u3 = u4) = (MAP FST ys = MAP SND ys) /\ (x = y)) /\
      (!x. ~(x IN e) ==> (m x = uf x)) /\ (df = udf)``,
  STRIP_TAC \\ STRIP_TAC \\ completeInduct_on `2 * (SUM_XSIZE (MAP FST ys) + XSIZE x) + LENGTH ys`
  \\ Q.PAT_X_ASSUM `!xxx. bbb` (ASSUME_TAC o RW1 [GSYM CONTAINER_def])
  \\ ONCE_REWRITE_TAC [arm_eq_loop_def]
  \\ ONCE_REWRITE_TAC [arm_eq_loop_pre_def]
  \\ NTAC 14 STRIP_TAC \\ Cases_on `r3 = r4`
  THENL [
    FULL_SIMP_TAC std_ss [] \\ IMP_RES_TAC word_tree2_11
    \\ FULL_SIMP_TAC std_ss []
    \\ `ALIGNED r7` by METIS_TAC [lisp_stack_LEMMA]
    \\ Cases_on `ys` THEN1
        (SIMP_TAC std_ss [] \\ FULL_SIMP_TAC std_ss [LENGTH,MAP] \\ METIS_TAC [])
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
    \\ Q.PAT_X_ASSUM `CONTAINER (!m. bbb)`
        (STRIP_ASSUME_TAC o RW [] o Q.SPEC `q` o Q.SPEC `t` o UNDISCH o
         Q.SPEC `2 * (SUM_XSIZE (MAP FST t) + XSIZE q) + LENGTH (t:(XExp # XExp) list)` o
         RW [CONTAINER_def])
    \\ Q.PAT_X_ASSUM `!x. bbb`
        (MP_TAC o Q.SPECL [`r`,`d`,`e`,`m`,`m (r7 - 8w:word32)`,`m (r7 - 4w:word32)`,`r5`,`r6`,`r7 - 8w`])
    \\ FULL_SIMP_TAC std_ss [GSYM WORD_SUB_PLUS,word_add_n2w,MAX_XDEPTH_def]
    \\ REVERSE (sg `MAX_ADDRESSES (r7 - 8w) (q::MAP FST t) SUBSET e`) THENL [
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
      \\ `MAX_XDEPTH (q::MAP FST t) <= MAX_XDEPTH (y::q::MAP FST t)` suffices_by DECIDE_TAC
      \\ CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [MAX_XDEPTH_def]))
      \\ SIMP_TAC std_ss [MAX_DEF]]
,
    FULL_SIMP_TAC std_ss [ALIGNED_INTRO,LET_DEF]
    \\ SIMP_TAC std_ss [GSYM ALIGNED_def,RW1 [WORD_AND_COMM] (GSYM ALIGNED_def)]
    \\ SIMP_TAC std_ss [ALIGNED_CLAUSES,ALIGNED_SUB_4]
    \\ REVERSE (Cases_on `ALIGNED (r3 || r4)`) \\ FULL_SIMP_TAC std_ss []
    THEN1 METIS_TAC [ALIGNED_OR,word_tree2_ALIGNED_LEMMA]
    \\ `ALIGNED r7` by METIS_TAC [lisp_stack_LEMMA]
    \\ FULL_SIMP_TAC std_ss [ALIGNED_OR,GSYM WORD_ADD_ASSOC,word_add_n2w]
    \\ `?x1 x2. x = XDot x1 x2` by
       (Cases_on `x` \\ FULL_SIMP_TAC std_ss [XExp_11,XExp_distinct,word_tree2_def]
        \\ METIS_TAC [ALIGNED_ADDR32,NOT_ALIGNED])
    \\ `?y1 y2. y = XDot y1 y2` by
       (Cases_on `y` \\ FULL_SIMP_TAC std_ss [XExp_11,XExp_distinct,word_tree2_def]
        \\ METIS_TAC [ALIGNED_ADDR32,NOT_ALIGNED])
    \\ FULL_SIMP_TAC std_ss [XExp_11,word_tree2_def]
    \\ `2 * (SUM_XSIZE (MAP FST ((x2,y2)::ys)) + XSIZE x1) +
        LENGTH ((x2,y2)::ys) <
        2 * (SUM_XSIZE (MAP FST ys) + XSIZE (XDot x1 x2)) + LENGTH ys` by
     (SIMP_TAC std_ss [SUM_XSIZE_def,XSIZE_def,LENGTH,MAP,ADD1] \\ DECIDE_TAC)
    \\ Q.PAT_X_ASSUM `CONTAINER (!x. bbb)`
        (STRIP_ASSUME_TAC o RW [MAP,CONS_11] o Q.SPECL [`(x2,y2)::ys`,`x1`] o UNDISCH o
         Q.SPEC `2 * (SUM_XSIZE (MAP FST ((x2,y2)::ys)) + XSIZE x1) + LENGTH (((x2,y2)::ys):(XExp # XExp) list)` o
         RW [CONTAINER_def])
    \\ Q.PAT_X_ASSUM `!x. bbb`
        (MP_TAC o Q.SPECL [`y1`,`d`,`e`,`(r7 + 4w =+ m (r4 + 4w:word32)) ((r7 =+ m (r3 + 4w:word32)) m)`,
          `m (r3:word32)`,`m (r4:word32)`,`m (r3 + 4w:word32)`,`m (r4 + 4w:word32)`,`r7 + 8w`])
    \\ ASM_SIMP_TAC std_ss [LENGTH,ADD1]
    \\ `MAX_XDEPTH (x1::x2::MAP FST ys) < 4294967296` by METIS_TAC [LESS_EQ_LESS_TRANS,MAX_XDEPTH_DOT]
    \\ ASM_SIMP_TAC std_ss []
    \\ sg `MAX_ADDRESSES (r7 + 8w) (x1::x2::MAP FST ys) SUBSET e`
    THENL [
      MATCH_MP_TAC SUBSET_TRANS
      \\ Q.EXISTS_TAC `MAX_ADDRESSES r7 (XDot x1 x2::MAP FST ys)`
      \\ ASM_SIMP_TAC std_ss []
      \\ SIMP_TAC std_ss [SUBSET_DEF,IN_DEF,MAX_ADDRESSES_def]
      \\ REPEAT STRIP_TAC
      \\ FULL_SIMP_TAC std_ss [WORD_MULT_CLAUSES,LENGTH,n2w_SUC,WORD_SUB_PLUS,WORD_ADD_SUB]
      \\ Q.EXISTS_TAC `i` \\ REWRITE_TAC []
      \\ `MAX_XDEPTH (x1::x2::MAP FST ys) <= MAX_XDEPTH (XDot x1 x2::MAP FST ys)` suffices_by DECIDE_TAC \\ METIS_TAC [MAX_XDEPTH_DOT],
      ASM_SIMP_TAC std_ss []
      \\ `r7 IN MAX_ADDRESSES r7 (XDot x1 x2::MAP FST ys)` by
       (SIMP_TAC std_ss [IN_DEF,MAX_ADDRESSES_def]
        \\ Q.EXISTS_TAC `2 * LENGTH (MAP FST ys)`
        \\ SIMP_TAC std_ss [LENGTH,n2w_SUC,WORD_MULT_CLAUSES,WORD_SUB_PLUS,WORD_ADD_SUB]
        \\ SIMP_TAC std_ss [MULT_ASSOC,word_mul_n2w,WORD_SUB_ADD]
        \\ `LENGTH (MAP FST ys) + 1 < MAX_XDEPTH (XDot x1 x2::MAP FST ys)` suffices_by DECIDE_TAC
        \\ SIMP_TAC std_ss [MAX_XDEPTH_def,XDEPTH_def,ADD1,LENGTH]
        \\ DISJ1_TAC \\ DECIDE_TAC)
      \\ `r7 + 4w IN MAX_ADDRESSES r7 (XDot x1 x2::MAP FST ys)` by
       (SIMP_TAC std_ss [IN_DEF,MAX_ADDRESSES_def]
        \\ Q.EXISTS_TAC `2 * LENGTH (MAP FST ys) + 1`
        \\ SIMP_TAC std_ss [LENGTH,n2w_SUC,WORD_MULT_CLAUSES,WORD_SUB_PLUS,WORD_ADD_SUB]
        \\ SIMP_TAC std_ss [MULT_ASSOC,word_mul_n2w,WORD_SUB_ADD,LEFT_ADD_DISTRIB,GSYM word_add_n2w]
        \\ SIMP_TAC std_ss [WORD_ADD_ASSOC,WORD_SUB_ADD]
        \\ `LENGTH (MAP FST ys) + 1 < MAX_XDEPTH (XDot x1 x2::MAP FST ys)` suffices_by DECIDE_TAC
        \\ SIMP_TAC std_ss [MAX_XDEPTH_def,XDEPTH_def,ADD1,LENGTH]
        \\ DISJ1_TAC \\ DECIDE_TAC)
      \\ `~(r7 IN d) /\ ~(r7 + 4w IN d)` by METIS_TAC [SUBSET_DEF,EXTENSION,IN_INTER,NOT_IN_EMPTY]
      \\ ASM_SIMP_TAC std_ss [word_tree2_IGNORE_WRITE]
      \\ `lisp_stack ((x2,y2)::ys)
         (r7 + 8w,(r7 + 4w =+ m (r4 + 4w)) ((r7 =+ m (r3 + 4w)) m),d,e)` suffices_by
      (STRIP_TAC THEN ASM_SIMP_TAC std_ss [APPLY_UPDATE_THM] \\ METIS_TAC [SUBSET_DEF])
      \\ ASM_SIMP_TAC std_ss [lisp_stack_def,word_arith_lemma1,word_arith_lemma2,word_arith_lemma3,word_arith_lemma4,word_arith_lemma5,WORD_ADD_0]
      \\ STRIP_TAC THEN1 METIS_TAC [SUBSET_DEF]
      \\ STRIP_TAC THEN1 METIS_TAC [SUBSET_DEF]
      \\ ASM_SIMP_TAC (std_ss++SIZES_ss) [APPLY_UPDATE_THM,word_tree2_IGNORE_WRITE,WORD_ADD_EQ,n2w_11]
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

val IN_heap_half = prove(
  ``lisp_inv (x1,x2,x3,x4,x5,x6,limit) (r1,r2,r3,r4,r5,r6,a,df,f,s,rest) /\ isDot x1 ==>
    ALIGNED r1 /\ r1 IN heap_half (a, f (a-28w) = 0w, limit) /\
    r1 + 4w IN heap_half (a, f (a-28w) = 0w, limit)``,
  STRIP_TAC \\ FULL_SIMP_TAC std_ss [isDot_thm,lisp_inv_def,LET_DEF]
  \\ FULL_SIMP_TAC std_ss [lisp_x_def]
  \\ Q.PAT_X_ASSUM `r1 IN ch_active_set (a,if u then 1 + limit else 1,i)` MP_TAC
  \\ `((if u then 0x0w else 0x1w) = 0x0w:word32) = u` by (Cases_on `u` \\ EVAL_TAC)
  \\ ASM_REWRITE_TAC [] \\ Q.PAT_X_ASSUM `!x. bbb` (K ALL_TAC)
  \\ SIMP_TAC std_ss [heap_half_def,ch_active_set_def,GSPECIFICATION]
  \\ STRIP_TAC \\ ASM_SIMP_TAC std_ss [word_mul_n2w] \\ STRIP_TAC THENL [
    Q.EXISTS_TAC `2 * (j - 1 - if u then limit else 0)`
    \\ Cases_on `u` \\ FULL_SIMP_TAC std_ss []
    \\ MATCH_MP_TAC (METIS_PROVE []
          ``(m = n) /\ b ==> ((a:word32) + n2w m = a + n2w n) /\ b``)
    \\ SIMP_TAC std_ss [LEFT_SUB_DISTRIB,MULT_ASSOC]
    \\ DECIDE_TAC,
    Q.EXISTS_TAC `2 * (j - 1 - if u then limit else 0) + 1`
    \\ Cases_on `u` \\ FULL_SIMP_TAC std_ss []
    \\ REWRITE_TAC [GSYM WORD_ADD_ASSOC,word_add_n2w]
    \\ MATCH_MP_TAC (METIS_PROVE []
          ``(m = n) /\ b ==> ((a:word32) + n2w m = a + n2w n) /\ b``)
    \\ SIMP_TAC std_ss [LEFT_SUB_DISTRIB,LEFT_ADD_DISTRIB,MULT_ASSOC]
    \\ DECIDE_TAC]);

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
  (SExp2XExp (Val n) sym = XVal (n2w n)) /\
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

val word_tree2_INTRO = prove(
  ``!r1. lisp_inv (x1,x2,x3,x4,x5,x6,limit) (r1,r2,r3,r4,r5,r6,a,df,f,s,rest) ==>
         word_tree2 (SExp2XExp x1 s) (r1,f) (heap_half(a,f(a-28w)=0w,limit)) /\
         (LDEPTH x1 = XDEPTH (SExp2XExp x1 s))``,
  REVERSE (Induct_on `x1`) THENL [
    FULL_SIMP_TAC std_ss [lisp_inv_def,LET_DEF,SExp2XExp_def,LDEPTH_def,
      XDEPTH_def,word_tree2_def,lisp_x_def,ALIGNED_INTRO]
    \\ REPEAT STRIP_TAC
    \\ STRIP_ASSUME_TAC (Q.SPEC `r1` EXISTS_ADDR32)
    \\ FULL_SIMP_TAC std_ss [ALIGNED_ADDR32,ALIGNED_ADD_EQ,
          word_arith_lemma4,ALIGNED_n2w,WORD_ADD_0]
    \\ METIS_TAC [lisp_symbol_table_11_Sym],
    FULL_SIMP_TAC std_ss [lisp_inv_def,LET_DEF,SExp2XExp_def,LDEPTH_def,
      XDEPTH_def,word_tree2_def,lisp_x_def,ALIGNED_INTRO]
    \\ REPEAT STRIP_TAC
    \\ ASM_SIMP_TAC std_ss [ADDR32_n2w,word_add_n2w]
    \\ SIMP_TAC std_ss [AC MULT_COMM MULT_ASSOC],
    REWRITE_TAC [SExp2XExp_def,word_tree2_def]
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
    STRIP_TAC \\ STRIP_ASSUME_TAC (Q.SPEC `x2` SExp_expand)
    \\ FULL_SIMP_TAC std_ss [SExp2XExp_def,XExp_11,SExp_11,XExp_distinct,SExp_distinct]
    \\ `isDot (Dot x1 x1') /\ isDot (Dot exp1 exp2)` by REWRITE_TAC [isDot_def]
    \\ STRIP_TAC \\ STRIP_TAC \\ STRIP_TAC
    \\ `lisp_inv (CAR (Dot x1 x1'),Dot exp1 exp2,x3,x4,x5,x6,limit) (f r1,r2,r3,r4,r5,r6,a,df,f,s,rest)` by METIS_TAC [lisp_inv_car]
    \\ `lisp_inv (CAR (Dot x1 x1'),CAR (Dot exp1 exp2),x3,x4,x5,x6,limit) (f r1,f r2,r3,r4,r5,r6,a,df,f,s,rest)` by METIS_TAC [lisp_inv_car]
    \\ FULL_SIMP_TAC std_ss [CAR_def]
    \\ `lisp_inv (CDR (Dot x1 x1'),Dot exp1 exp2,x3,x4,x5,x6,limit) (f (r1+4w),r2,r3,r4,r5,r6,a,df,f,s,rest)` by METIS_TAC [lisp_inv_cdr]
    \\ `lisp_inv (CDR (Dot x1 x1'),CDR (Dot exp1 exp2),x3,x4,x5,x6,limit) (f (r1+4w),f (r2+4w),r3,r4,r5,r6,a,df,f,s,rest)` by METIS_TAC [lisp_inv_cdr]
    \\ FULL_SIMP_TAC std_ss [CDR_def]
    \\ METIS_TAC [],
    Cases_on `x2`
    \\ SIMP_TAC std_ss [SExp2XExp_def,XExp_11,SExp_11,XExp_distinct,SExp_distinct]
    \\ SIMP_TAC std_ss [lisp_inv_def,LET_DEF,lisp_x_def]
    \\ REPEAT STRIP_TAC \\ ASM_SIMP_TAC (std_ss++SIZES_ss) [n2w_11],
    Cases_on `x2`
    \\ SIMP_TAC std_ss [SExp2XExp_def,XExp_11,SExp_11,XExp_distinct,SExp_distinct]
    \\ SIMP_TAC std_ss [lisp_inv_def,LET_DEF,lisp_x_def]
    \\ REPEAT STRIP_TAC
    \\ `?dm m dg g. rest = (dm,m,dg,g)` by METIS_TAC [PAIR]
    \\ Q.ABBREV_TAC `sa = a + 0x10w * n2w limit + 0x18w`
    \\ FULL_SIMP_TAC std_ss [lisp_symbol_table_def,ALIGNED_INTRO]
    \\ STRIP_ASSUME_TAC (Q.SPEC `r1` EXISTS_ADDR32)
    \\ FULL_SIMP_TAC std_ss [ALIGNED_ADDR32,ALIGNED_ADD_EQ,
          word_arith_lemma4,ALIGNED_n2w,WORD_ADD_0]
    \\ STRIP_ASSUME_TAC (Q.SPEC `r2` EXISTS_ADDR32)
    \\ FULL_SIMP_TAC std_ss [ALIGNED_ADDR32,ALIGNED_ADD_EQ,
          word_arith_lemma4,ALIGNED_n2w,WORD_ADD_0]
    \\ `(ADDR32 a' + sa,s'') IN (set_add sa s)` by
       FULL_SIMP_TAC std_ss [IN_DEF,set_add_def,WORD_ADD_SUB]
    \\ `(ADDR32 a'' + sa,s') IN (set_add sa s)` by
       FULL_SIMP_TAC std_ss [IN_DEF,set_add_def,WORD_ADD_SUB]
    \\ `!w s2. (ADDR32 w + sa,s2) IN (set_add sa s) = (ADDR32 w, s2) IN s` by
       FULL_SIMP_TAC std_ss [IN_DEF,set_add_def,WORD_ADD_SUB]
    \\ `(s'' = s') = (a'' = a')` by METIS_TAC [symbol_table_eq,WORD_EQ_ADD_RCANCEL,ADDR32_11]
    \\ FULL_SIMP_TAC std_ss []
   \\ `!w1 w2 s1 s2. (ADDR32 w1 + sa,s1) IN (set_add sa s) /\
        (ADDR32 w2 + sa,s2) IN (set_add sa s) ==>
        ((ADDR32 w1 + sa = ADDR32 w2 + sa) = (s1 = s2))` by METIS_TAC [symbol_table_eq]
    \\ POP_ASSUM MP_TAC
    \\ ASM_SIMP_TAC std_ss [WORD_EQ_ADD_RCANCEL,ADDR32_11]
    \\ METIS_TAC []]);

val word_tree2_THM = prove(
  ``lisp_inv (x1,x2,x3,x4,x5,x6,limit) (r1,r2,r3,r4,r5,r6,a,df,f,s,rest) ==>
    ?y1 y2. word_tree2 y1 (r1,f) (heap_half(a,f(a-28w)=0w,limit)) /\
            word_tree2 y2 (r2,f) (heap_half(a,f(a-28w)=0w,limit)) /\
            ((x1 = x2) = (y1 = y2)) /\ (XDEPTH y1 = LDEPTH x1) /\
            (XDEPTH y2 = LDEPTH x2)``,
  STRIP_TAC
  \\ Q.EXISTS_TAC `SExp2XExp x1 s` \\ Q.EXISTS_TAC `SExp2XExp x2 s`
  \\ IMP_RES_TAC word_tree2_INTRO
  \\ IMP_RES_TAC SExp2XExp_11
  \\ ASM_SIMP_TAC std_ss []
  \\ METIS_TAC [lisp_inv_swap2,word_tree2_INTRO]);

val lisp_inv_arm_eq_loop = prove(
  ``let w = a + if f (a - 28w) = 0w then 8w else 8w + n2w (8 * limit) in
    lisp_inv (x1,x2,x3,x4,x5,x6,limit) (r3,r4,z5,z6,z7,z8,a,df,f,s,rest) /\
    (arm_eq_loop (r3,r4,r5,r6,w,0w,df,f) = (u3,u4,u5,u6,u7,u8,udf,uf)) ==>
    arm_eq_loop_pre (r3,r4,r5,r6,w,0w,df,f) /\
    ((u3 = u4) = (x1 = x2)) /\
    (!x. ~(x IN heap_half (a, ~((f:word32->word32) (a - 28w) = 0w),limit)) ==> (f x = uf x)) /\ (df = udf)``,
  Q.ABBREV_TAC `w = a + if f (a - (28w:word32)) = (0w:word32) then 8w else 8w + n2w (8 * limit)`
  \\ SIMP_TAC std_ss [LET_DEF] \\ STRIP_TAC
  \\ IMP_RES_TAC word_tree2_THM \\ ASM_SIMP_TAC std_ss []
  \\ MATCH_MP_TAC arm_eq_loop_spec
  \\ Q.EXISTS_TAC `heap_half (a, (f (a - 28w) = 0w),limit)`
  \\ ASM_SIMP_TAC std_ss []
  \\ `LDEPTH x1 <= limit` by METIS_TAC [lisp_inv_LDEPTH]
  \\ ASM_SIMP_TAC std_ss []
  \\ `16 * limit < 2**32` by
       (FULL_SIMP_TAC std_ss [lisp_inv_def,LET_DEF] \\ DECIDE_TAC)
  \\ IMP_RES_TAC heap_half_DISJOINT
  \\ STRIP_TAC THEN1
   (Cases_on `f (a - 0x1Cw) = 0x0w` \\ ASM_SIMP_TAC std_ss []
    \\ METIS_TAC [INTER_COMM])
  \\ `ALIGNED w` by (Q.UNABBREV_TAC `w`
    \\ Cases_on `(f:word32->word32) (a - 28w) = 0w` \\ ASM_SIMP_TAC std_ss []
    \\ SIMP_TAC std_ss [GSYM (EVAL ``4w + 4w:word32``),WORD_ADD_ASSOC,ALIGNED_CLAUSES]
    \\ SIMP_TAC bool_ss [GSYM (EVAL ``4*2``),GSYM word_mul_n2w,WORD_MULT_ASSOC]
    \\ REWRITE_TAC [ALIGNED_CLAUSES,GSYM WORD_MULT_ASSOC]
    \\ FULL_SIMP_TAC std_ss [lisp_inv_def,LET_DEF,ALIGNED_def])
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
    \\ Q.PAT_X_ASSUM `w2n a + 16 * limit + 20 < 4294967296` MP_TAC
    \\ Q.SPEC_TAC (`a`,`a`) \\ Cases_word
    \\ ASM_SIMP_TAC std_ss [w2n_n2w,word_add_n2w,n2w_11,ZERO_LT_dimword]
    \\ Cases_on `k < 2 * limit` \\ ASM_SIMP_TAC (std_ss++SIZES_ss) [] \\ STRIP_TAC
    \\ `n + (8 * limit + 8 + 4 * k) < 4294967296` by DECIDE_TAC
    \\ `n + (8 + 4 * k) < 4294967296` by DECIDE_TAC
    \\ Cases_on `(f:word32->word32) (n2w n - 28w) = 0w` \\ ASM_SIMP_TAC std_ss [])
  \\ `df = ref_set a (limit + limit + 1)` by
    (FULL_SIMP_TAC std_ss [lisp_inv_def,LET_DEF] \\ METIS_TAC [])
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

val lisp_x_APPLY = prove(
  ``!x1 a. ~(xx IN b) /\ ~(xx - 4w IN b) ==>
           (lisp_x x1 (a,b,(xx =+ x) f) s = lisp_x x1 (a,b,f) s)``,
  Induct \\ SIMP_TAC std_ss [lisp_x_def] \\ REPEAT STRIP_TAC
  \\ Cases_on `a IN b` \\ ASM_SIMP_TAC std_ss []
  \\ `~(xx = a)` by METIS_TAC []
  \\ ASM_SIMP_TAC std_ss [APPLY_UPDATE_THM]
  \\ `~(a = xx - 4w)` by METIS_TAC []
  \\ FULL_SIMP_TAC std_ss [WORD_EQ_SUB_LADD]);

val tac =
  FULL_SIMP_TAC std_ss [lisp_inv_def,LET_DEF]
  \\ REPEAT STRIP_TAC \\ Q.EXISTS_TAC `i` \\ Q.EXISTS_TAC `u`
  \\ ASM_SIMP_TAC std_ss []
  \\ Q.ABBREV_TAC `bb = ch_active_set (a,if u then 1 + limit else 1,i)`
  \\ Q.PAT_ABBREV_TAC `xx = a - n2w n`
  \\ `~(xx IN bb) /\ ~(xx - 4w IN bb)` by
   (Q.UNABBREV_TAC `bb` \\ Q.UNABBREV_TAC `xx`
    \\ SIMP_TAC std_ss [ch_active_set_def,GSPECIFICATION]
    \\ SIMP_TAC std_ss [APPLY_UPDATE_THM,WORD_EQ_SUB_RADD]
    \\ SIMP_TAC std_ss [GSYM WORD_ADD_ASSOC,word_add_n2w,word_mul_n2w]
    \\ SIMP_TAC std_ss [WORD_EQ_ADD_CANCEL]
    \\ REPEAT STRIP_TAC
    \\ Cases_on `j < i` \\ ASM_SIMP_TAC std_ss []
    \\ Cases_on `(if u then 1 + limit else 1) <= j` \\ ASM_SIMP_TAC std_ss []
    \\ SIMP_TAC std_ss [n2w_11,ZERO_LT_dimword]
    \\ MATCH_MP_TAC (METIS_PROVE [LESS_MOD] ``(n < k) /\ (n <> 0) ==> (n MOD k <> 0)``)
    \\ Cases_on `u` \\ FULL_SIMP_TAC (std_ss++SIZES_ss) []
    \\ DECIDE_TAC)
  \\ ASM_SIMP_TAC std_ss [lisp_x_APPLY]
  \\ NTAC 4 (STRIP_TAC THEN1
    (Q.UNABBREV_TAC `xx`
     \\ SIMP_TAC std_ss [APPLY_UPDATE_THM,WORD_EQ_SUB_RADD]
     \\ SIMP_TAC std_ss [word_arith_lemma1,word_arith_lemma2]
     \\ SIMP_TAC std_ss [word_arith_lemma3,word_arith_lemma4]
     \\ ASM_SIMP_TAC (std_ss++SIZES_ss) [WORD_EQ_ADD_CANCEL,WORD_EQ_SUB_LADD,n2w_11]))
  \\ SIMP_TAC std_ss [APPLY_UPDATE_THM,GSYM WORD_EQ_SUB_RADD]
  \\ METIS_TAC []

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

val lisp_x_or = prove(
  ``(!x. x IN bb \/ x - 4w IN bb ==> (f5 x = ft x)) ==>
    !t a s. (lisp_x t (a,bb,ft) s = lisp_x t (a,bb,f5) s)``,
  STRIP_TAC \\ Induct \\ SIMP_TAC std_ss [lisp_x_def] \\ REPEAT STRIP_TAC
  \\ METIS_TAC [WORD_ADD_SUB,WORD_SUB_ADD]);

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
  \\ REWRITE_TAC [arm_eq_def,arm_eq_pre_def,GSYM ALIGNED_def]
  \\ ONCE_REWRITE_TAC [ALIGNED_MOD_4]
  \\ SIMP_TAC std_ss [WORD_SUB_RZERO]
  \\ Cases_on `r3 = r4` THEN1
   (ASM_SIMP_TAC std_ss [LET_DEF] \\ ONCE_REWRITE_TAC [EQ_SYM_EQ]
    \\ SIMP_TAC std_ss []
    \\ STRIP_TAC \\ IMP_RES_TAC word_tree2_THM
    \\ IMP_RES_TAC word_tree2_11
    \\ FULL_SIMP_TAC std_ss [LISP_EQUAL_def,LISP_TEST_def]
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
      FULL_SIMP_TAC std_ss [lisp_inv_def,LET_DEF,ALIGNED_INTRO]
  \\ ASM_SIMP_TAC std_ss [WORD_SUB_PLUS,ALIGNED_SUB_4]
  \\ SIMP_TAC std_ss [arm_eq_init_def,LET_DEF,arm_eq_assign_def]
  \\ `lisp_inv (x1,x2,x3,x4,x5,x6,limit) (r3,r4,r5,r6,r7,r8,a,df,f5,s,rest)` by
         METIS_TAC [lemma20,lemma16,lemma12,lemma8,lemma4]
  \\ Q.UNABBREV_TAC `ww` \\ Q.UNABBREV_TAC `wi` \\ Q.UNABBREV_TAC `wl`
  \\ `f5 (a - 32w) = n2w (8 * limit)` by
       FULL_SIMP_TAC std_ss [LET_DEF,lisp_inv_def,ch_arm_def,ch_word_def,ch_inv_def]
  \\ FULL_SIMP_TAC std_ss []
  \\ IMP_RES_TAC (SIMP_RULE std_ss [LET_DEF] lisp_inv_arm_eq_loop)
  \\ REPEAT (Q.PAT_X_ASSUM `!xx yy. bb` (K ALL_TAC))
  \\ Q.PAT_X_ASSUM `df = dft` (ASSUME_TAC o GSYM)
  \\ FULL_SIMP_TAC std_ss [GSYM WORD_SUB_PLUS,word_add_n2w]
  \\ REWRITE_TAC [CONJ_ASSOC] \\ STRIP_TAC THEN1
     (`df = ref_set a (limit + limit + 1)` by
        FULL_SIMP_TAC std_ss [lisp_inv_def,LET_DEF]
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
  \\ Q.PAT_X_ASSUM `lisp_inv (x1,x2,x3,x4,x5,x6,limit) (r3,r4,r5,r6,r7,r8,a,df,f,s,rest)` (K ALL_TAC)
  \\ `lisp_inv (LISP_EQUAL x1 x2,x2,x3,x4,x5,x6,limit) (r3u,r4,r5,r6,r7,r8,a,df,f5,s,rest)` by
      (Cases_on `x1 = x2`
       \\ FULL_SIMP_TAC std_ss [LISP_EQUAL_def,LISP_TEST_def,arm_eq_assign_def,LET_DEF]
       \\ METIS_TAC [lisp_inv_t,lisp_inv_nil])
  \\ Q.PAT_X_ASSUM `lisp_inv (x1,x2,x3,x4,x5,x6,limit) (r3,r4,r5,r6,r7,r8,a,df,f5,s,rest)` (K ALL_TAC)
  \\ `w2n a + 16 * limit + 20 < 4294967296` by
      FULL_SIMP_TAC std_ss [lisp_inv_def,LET_DEF]
  \\ `32 <= w2n a` by
      FULL_SIMP_TAC std_ss [lisp_inv_def,LET_DEF]
  \\ `~(a - 20w IN heap_half (a, ~(f5 (a - 28w) = 0w),limit))` by tac2
  \\ `~(a - 16w IN heap_half (a, ~(f5 (a - 28w) = 0w),limit))` by tac2
  \\ `~(a - 12w IN heap_half (a, ~(f5 (a - 28w) = 0w),limit))` by tac2
  \\ `~(a - 8w IN heap_half (a, ~(f5 (a - 28w) = 0w),limit))` by tac2
  \\ `~(a - 4w IN heap_half (a, ~(f5 (a - 28w) = 0w),limit))` by tac2
  \\ `(ft (a - 20w) = r4) /\ (ft (a - 16w) = r5) /\ (ft (a - 12w) = r6) /\
        (ft (a - 8w) = r7) /\ (ft (a - 4w) = r8)` by
     (RES_TAC \\ REPEAT (Q.PAT_X_ASSUM `f5 xx = yy` (fn th => REWRITE_TAC [GSYM th]))
      \\ Q.UNABBREV_TAC `f1` \\ Q.UNABBREV_TAC `f2` \\ Q.UNABBREV_TAC `f3`
      \\ Q.UNABBREV_TAC `f4` \\ Q.UNABBREV_TAC `f5`
      \\ REPEAT (POP_ASSUM (K ALL_TAC))
      \\ SIMP_TAC (std_ss++SIZES_ss) [APPLY_UPDATE_THM,word_sub_def,
           WORD_EQ_ADD_LCANCEL,n2w_11,word_2comp_n2w])
  \\ ASM_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC std_ss [lisp_inv_def,LET_DEF]
  \\ Q.EXISTS_TAC `i` \\ Q.EXISTS_TAC `u`
  \\ FULL_SIMP_TAC std_ss [lisp_inv_def,LET_DEF]
  \\ `~(a - 28w IN heap_half (a, ~(f5 (a - 28w) = 0w),limit))` by tac2
  \\ `~(a - 32w IN heap_half (a, ~(f5 (a - 28w) = 0w),limit))` by tac2
  \\ `~(a + 4w IN heap_half (a, ~(f5 (a - 28w) = 0w),limit))` by tac2
  \\ `~(a IN heap_half (a, ~(f5 (a - 28w) = 0w),limit))` by tac2
  \\ Q.PAT_X_ASSUM `f5 (a - 28w) = (if u then 0w else 1w)` ASSUME_TAC
  \\ FULL_SIMP_TAC std_ss []
  \\ NTAC 4 (STRIP_TAC THEN1 METIS_TAC [])
  \\ Q.ABBREV_TAC `bb = ch_active_set (a,if u then 1 + limit else 1,i)`
  \\ `((if u then 0x0w else 0x1w) <> 0x0w:word32) = ~u` by (Cases_on `u` \\ EVAL_TAC)
  \\ FULL_SIMP_TAC std_ss []
  \\ `bb SUBSET heap_half (a,u,limit)` by
   (Q.UNABBREV_TAC `bb`
    \\ SIMP_TAC std_ss [SUBSET_DEF,ch_active_set_def,heap_half_def,GSPECIFICATION]
    \\ REPEAT STRIP_TAC \\ ASM_SIMP_TAC std_ss [word_mul_n2w]
    \\ Cases_on `u` \\ FULL_SIMP_TAC std_ss [] THENL [
      Q.EXISTS_TAC `2 * (j - 1 - limit)`
      \\ MATCH_MP_TAC (METIS_PROVE []
           ``(m = n) /\ b ==> (a + n2w m = (a:word32) + n2w n) /\ b``)
      \\ FULL_SIMP_TAC std_ss [LEFT_SUB_DISTRIB,LEFT_ADD_DISTRIB,MULT_ASSOC]
      \\ DECIDE_TAC,
      Q.EXISTS_TAC `2 * (j - 1)`
      \\ MATCH_MP_TAC (METIS_PROVE []
           ``(m = n) /\ b ==> (a + n2w m = (a:word32) + n2w n) /\ b``)
      \\ FULL_SIMP_TAC std_ss [LEFT_SUB_DISTRIB,LEFT_ADD_DISTRIB,MULT_ASSOC]
      \\ DECIDE_TAC])
  \\ `{ b + 4w | b IN bb} SUBSET heap_half (a,u,limit)` by
   (Q.UNABBREV_TAC `bb`
    \\ SIMP_TAC std_ss [SUBSET_DEF,ch_active_set_def,heap_half_def,GSPECIFICATION]
    \\ REPEAT STRIP_TAC \\ ASM_SIMP_TAC std_ss [word_mul_n2w]
    \\ Cases_on `u` \\ FULL_SIMP_TAC std_ss [GSYM WORD_ADD_ASSOC,word_add_n2w] THENL [
      Q.EXISTS_TAC `2 * (j - 1 - limit) + 1`
      \\ MATCH_MP_TAC (METIS_PROVE []
           ``(m = n) /\ b ==> (a + n2w m = (a:word32) + n2w n) /\ b``)
      \\ FULL_SIMP_TAC std_ss [LEFT_SUB_DISTRIB,LEFT_ADD_DISTRIB,MULT_ASSOC]
      \\ DECIDE_TAC,
      Q.EXISTS_TAC `2 * (j - 1) + 1`
      \\ MATCH_MP_TAC (METIS_PROVE []
           ``(m = n) /\ b ==> (a + n2w m = (a:word32) + n2w n) /\ b``)
      \\ FULL_SIMP_TAC std_ss [LEFT_SUB_DISTRIB,LEFT_ADD_DISTRIB,MULT_ASSOC]
      \\ DECIDE_TAC])
  \\ `(!x. x IN bb \/ x - 4w IN bb ==> (f5 x = ft x))` by
   (REPEAT STRIP_TAC
    THEN1 (Q.PAT_X_ASSUM `!x. bbb ==> (f5 x = ft x)` MATCH_MP_TAC
    \\ `16 * limit < 2 ** 32` by (SIMP_TAC std_ss [] \\ DECIDE_TAC)
    \\ IMP_RES_TAC (RW [EXTENSION,NOT_IN_EMPTY,IN_INTER] heap_half_DISJOINT)
    \\ Cases_on `u` \\ REWRITE_TAC [] \\ METIS_TAC [SUBSET_DEF])
    \\ REPEAT STRIP_TAC
    \\ Q.PAT_X_ASSUM `!x. bbb ==> (f5 x = ft x)` MATCH_MP_TAC
    \\ `16 * limit < 2 ** 32` by (SIMP_TAC std_ss [] \\ DECIDE_TAC)
    \\ IMP_RES_TAC (RW [EXTENSION,NOT_IN_EMPTY,IN_INTER] heap_half_DISJOINT)
    \\ `x IN {b + 0x4w | b IN bb}` suffices_by
    (STRIP_TAC THEN Cases_on `u` \\ REWRITE_TAC [] \\ METIS_TAC [SUBSET_DEF])
    \\ ASM_SIMP_TAC std_ss [GSPECIFICATION,GSYM WORD_EQ_SUB_RADD])
  \\ IMP_RES_TAC lisp_x_or \\ ASM_SIMP_TAC std_ss []
  \\ REPEAT STRIP_TAC \\ METIS_TAC [WORD_ADD_SUB]);


val _ = export_theory();
