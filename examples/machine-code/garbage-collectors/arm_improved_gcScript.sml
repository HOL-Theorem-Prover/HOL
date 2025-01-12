
open HolKernel boolLib bossLib Parse; val _ = new_theory "arm_improved_gc";
val _ = ParseExtras.temp_loose_equality()

open wordsTheory arithmeticTheory wordsLib listTheory pred_setTheory pairTheory;
open combinTheory finite_mapTheory addressTheory helperLib;
open set_sepTheory bitTheory;

open improved_gcTheory;
open compilerLib;

val RW = REWRITE_RULE;
val RW1 = ONCE_REWRITE_RULE;
fun SUBGOAL q = REVERSE (sg q)


val _ = codegen_x86Lib.set_x86_regs
  [(1,"eax"),(2,"ecx"),(3,"edx"),(4,"ebx"),(5,"edi"),(6,"esi"),(7,"ebp")]

val (th,arm_move_loop_def,arm_move_loop_pre_def) = compile "arm" ``
  arm_move_loop (r2:word32,r3:word32,r4:word32,df:word32 set,f:word32->word32) =
    if r4 = 0w then (r2,r3,r4,df,f) else
      let r5 = f r2 in
      let r4 = r4 - 1w in
      let r2 = r2 + 4w in
      let f = (r3 =+ r5) f in
      let r3 = r3 + 4w in
        arm_move_loop (r2,r3,r4,df,f)``;

val (th,arm_move_def,arm_move_pre_def) = compile "arm" ``
  arm_move (r1:word32,r2:word32,r3:word32,df:word32 set,f:word32->word32) =
    if ~(r2 && 3w = 0w) then (r1,r3,df,f) else
      let r4 = f r2 in
        if r4 && 3w = 0w then
          let f = (r1 =+ r4) f in
            (r1,r3,df,f)
        else
          let f = (r1 =+ r3) f in
          let f = (r3 =+ r4) f in
          let f = (r2 =+ r3) f in
          let r4 = r4 >>> 10 in
          let r3 = r3 + 4w in
          let r2 = r2 + 4w in
          let (r2,r3,r4,df,f) = arm_move_loop (r2,r3,r4,df,f) in
            (r1,r3,df,f)``

val (th,arm_move_list_def,arm_move_list_pre_def) = compile "arm" ``
  arm_move_list (r1:word32,r3:word32,r6:word32,df:word32 set,f:word32->word32) =
    if r6 = 0w then (r1,r3,df,f) else
      let r2 = f r1 in
      let r6 = r6 - 1w in
      let (r1,r3,df,f) = arm_move (r1,r2,r3,df,f) in
      let r1 = r1 + 4w in
        arm_move_list (r1,r3,r6,df,f)``

val (th,arm_loop_def,arm_loop_pre_def) = compile "arm" ``
  arm_loop (r1:word32,r3:word32,df:word32 set,f:word32->word32) =
    if r1 = r3 then (r1,df,f) else
      let r2 = f r1 in
      let r6 = r2 >>> 10 in
      let r1 = r1 + 4w in
        if r2 && 1w = 0w then
          let r6 = r6 << 2 in
          let r1 = r1 + r6 in
            arm_loop (r1,r3,df,f)
        else
          let (r1,r3,df,f) = arm_move_list (r1,r3,r6,df,f) in
            arm_loop (r1,r3,df,f)``

val (th,arm_move_roots_def,arm_move_roots_pre_def) = compile "arm" ``
  arm_move_roots (r1:word32,r3:word32,df:word32 set,f:word32->word32) =
    let r2 = f r1 in
      if r2 = 2w then (r3,df,f) else
        let (r1,r3,df,f) = arm_move (r1,r2,r3,df,f) in
        let r1 = r1 - 4w in
          arm_move_roots (r1,r3,df,f)``

val (th,arm_gc_def,arm_gc_pre_def) = compile "arm" ``
  arm_gc (r1:word32,r7:word32,df:word32 set,f:word32->word32) =
    let r3 = f (r7 + 48w) in
    let r5 = f (r7 + 52w) in
    let r2 = f (r7 + 44w) in
    let r4 = f (r7 + 40w) in
    let f = (r7 + 40w =+ r3) f in
    let f = (r7 + 44w =+ r5) f in
    let f = (r7 + 48w =+ r4) f in
    let f = (r7 + 52w =+ r2) f in
    let (r3,df,f) = arm_move_roots (r1,r3,df,f) in
    let r1 = f (r7 + 40w) in
    let (r1,df,f) = arm_loop (r1,r3,df,f) in
      (r1,r7,df,f)``


val SET_TAC =
  FULL_SIMP_TAC std_ss [EXTENSION,IN_INSERT,IN_UNION,IN_DELETE,SUBSET_DEF,
    DISJOINT_DEF,NOT_IN_EMPTY,EXTENSION,IN_INSERT,IN_INTER,IN_DIFF,IN_UNIV]
  \\ METIS_TAC [PAIR_EQ];

val RANGE_TAC = FULL_SIMP_TAC std_ss [RANGE_def,IN_DEF,gc_inv_def] \\ DECIDE_TAC

val ref_addr_def = Define `ref_addr n = n2w (4 * n):word32`;

val ref_heap_addr_def = Define `
  (ref_heap_addr (H_DATA w) = n2w (w2n (w:31 word) * 2 + 1)) /\
  (ref_heap_addr (H_ADDR a) = ref_addr a)`;

val one_list_def = Define `
  (one_list a [] = emp) /\
  (one_list a (x::xs) = one (a,x) * one_list (a + 4w) xs)`;

val one_list_roots_def = Define `
  (one_list_roots a [] = one (a,2w)) /\
  (one_list_roots a (x::xs) = one_list_roots (a - 4w) xs * one (a,ref_heap_addr x))`;

val ref_tag_def = Define `
  ref_tag (n,b,t:word8) = n2w (n * 1024 + w2n t * 4 + 2 + (if b then 1 else 0)) :word32`;

val ref_aux_def = Define `
  (ref_aux a H_EMP = SEP_EXISTS x. one (a:word32,x)) /\
  (ref_aux a (H_REF n) = one (a,ref_addr n)) /\
  (ref_aux a (H_BLOCK (xs,l,(b,d,ys))) =
     let zs = (if d then MAP ref_heap_addr xs else ys) in
       one (a,ref_tag (LENGTH zs,d,b)) * one_list (a+4w) zs)`;

val ref_mem_def = tDefine "ref_mem" `
  (ref_mem m a e =
     if e <= a then cond (a = e) else
       ref_aux (ref_addr a) (m a) * ref_mem m (a + MAX 1 (getLENGTH (m a))) e)`
  (WF_REL_TAC `measure (\(m,a,e). e - a)`
   \\ SIMP_TAC std_ss [MAX_DEF] \\ DECIDE_TAC)

val ALIGNED_ref_addr = prove(
  ``!n. ALIGNED (ref_addr n)``,
  SIMP_TAC std_ss [ALIGNED_n2w,ref_addr_def,RW1[MULT_COMM]MOD_EQ_0]);

val ref_addr_and_3 = prove(
  ``!n m. ref_addr m + n2w n && 3w = n2w (n MOD 4)``,
  SIMP_TAC std_ss [ref_addr_def,word_add_n2w,n2w_and_3,
    MATCH_MP (RW1[MULT_COMM]MOD_TIMES) (DECIDE``0<4:num``)]);

val ref_addr_NEQ = prove(
  ``!i j. ~(ref_addr i = ref_addr j + 1w) /\
          ~(ref_addr i = ref_addr j + 2w) /\
          ~(ref_addr i = ref_addr j + 3w)``,
  REPEAT STRIP_TAC \\ POP_ASSUM MP_TAC \\ SIMP_TAC std_ss []
  \\ MATCH_MP_TAC (METIS_PROVE [] ``~(x && 3w = y && 3w) ==> ~(x = y)``)
  \\ SIMP_TAC (std_ss++SIZES_ss) [ref_addr_and_3,n2w_11,
       SIMP_RULE std_ss [WORD_ADD_0] (Q.SPEC `0` ref_addr_and_3)]);

val ref_tag_lsr = prove(
  ``n < 2 ** 22 ==> (ref_tag (n,b,t) >>> 10 = n2w n)``,
  SIMP_TAC (std_ss++SIZES_ss) [ref_tag_def,LEFT_ADD_DISTRIB,
    GSYM ADD_ASSOC,word_add_n2w,DECIDE ``8 * (n * 2) = 16 * n:num``,
    SIMP_CONV std_ss [word_lsr_n2w,word_bits_n2w,BITS_THM] ``n2w n >>> k``]
  \\ ASSUME_TAC (Q.ISPEC `t:word8` w2n_lt) \\ FULL_SIMP_TAC (std_ss++SIZES_ss) []
  \\ `w2n t * 4 + (2 + if b then 1 else 0) < 1024` by (Cases_on `b` \\ DECIDE_TAC)
  \\ IMP_RES_TAC DIV_MULT \\ ASM_SIMP_TAC std_ss []);

val MAX_LEMMA = prove(
  ``MAX 1 (n + 1) = n + 1``,
  FULL_SIMP_TAC std_ss [MAX_DEF] \\ DECIDE_TAC);

val ref_heap_addr_NEQ_2 = prove(
  ``!x. ~(ref_heap_addr x = 2w)``,
  Cases \\ MATCH_MP_TAC (METIS_PROVE [] ``~(v && 3w = w && 3w) ==> ~(v = w:word32)``)
  \\ SIMP_TAC (std_ss++SIZES_ss) [ref_heap_addr_def,n2w_11,ref_addr_def]
  \\ SIMP_TAC std_ss [n2w_and_3,DECIDE ``4*n = n*4``,MOD_EQ_0] THEN1 EVAL_TAC
  \\ MATCH_MP_TAC (METIS_PROVE [] ``~(w && 1w = v && 1w) ==> ~(w = v)``)
  \\ SIMP_TAC std_ss [n2w_and_1] \\ SIMP_TAC bool_ss [DECIDE ``4=2*2``]
  \\ SIMP_TAC bool_ss [MATCH_MP MOD_MULT_MOD (DECIDE ``0<2 /\ 0<2``)]
  \\ SIMP_TAC std_ss [MATCH_MP MOD_MULT (DECIDE ``1 < 2``)] \\ EVAL_TAC);

val ok_memory_def = Define `
  ok_memory m =
    !(a:num) l (xs:(31 word) heap_address list) b:word8 t:bool ys:word32 list.
      (m a = H_BLOCK (xs,l,(b,t,ys))) ==>
        LENGTH xs < 2 ** 22 /\ LENGTH ys < 2 ** 22 /\
        if t then l = LENGTH xs else (l = LENGTH ys) /\ (xs = [])`;

val ref_addr_ADD1 = prove(
  ``!i j. (ref_addr (i + 1) = ref_addr i + 4w) /\
          (ref_addr (i + j) = ref_addr i + ref_addr j)``,
  SIMP_TAC std_ss [ref_addr_def,LEFT_ADD_DISTRIB,word_add_n2w]);

val ref_mem_IGNORE = prove(
  ``~(RANGE (b2,e2) j) ==>
    (ref_mem ((j =+ x) m) b2 e2 = ref_mem m b2 e2)``,
  completeInduct_on `e2-b2` \\ REPEAT STRIP_TAC
  \\ ONCE_REWRITE_TAC [ref_mem_def]
  \\ Cases_on `e2<=b2` \\ ASM_SIMP_TAC std_ss []
  \\ `~(b2 = j)` by (FULL_SIMP_TAC std_ss [RANGE_def] \\ DECIDE_TAC)
  \\ FULL_SIMP_TAC std_ss [APPLY_UPDATE_THM]
  \\ Q.ABBREV_TAC `y = MAX 1 (getLENGTH (m b2))`
  \\ `0 < y` by (Q.UNABBREV_TAC `y` \\ SIMP_TAC std_ss [MAX_DEF])
  \\ `e2 - (b2 + y) < e2 - b2` by DECIDE_TAC
  \\ `~RANGE (b2+y,e2) j` by (FULL_SIMP_TAC std_ss [RANGE_def] \\ DECIDE_TAC)
  \\ RES_TAC \\ METIS_TAC []);

val ref_mem_LESS = prove(
  ``!j e. j < e ==> !m. ref_mem m j e =
                        ref_aux (ref_addr j) (m j) *
                        ref_mem m (j + MAX 1 (getLENGTH (m j))) e``,
  METIS_TAC [DECIDE ``j<e = ~(e<=j:num)``,ref_mem_def]);

val arm_move_loop_thm = store_thm("arm_move_loop_thm",
  ``!xs ys r2 r3 r5:word32 f p.
      (one_list r2 xs * one_list r3 ys * p) (fun2set (f,df)) /\
      (LENGTH ys = LENGTH xs) /\ LENGTH xs < 2 ** 23 /\ ALIGNED r2 /\ ALIGNED r3 ==>
      ?r2i r3i fi.
        arm_move_loop_pre (r2,r3,n2w (LENGTH xs),df,f) /\
        (arm_move_loop (r2,r3,n2w (LENGTH xs),df,f) =
                              (r2i,r3 + n2w (4 * LENGTH xs),0w,df,fi)) /\
        (one_list r2 xs * one_list r3 xs * p) (fun2set (fi,df))``,
  Induct \\ REPEAT STRIP_TAC
  \\ PURE_ONCE_REWRITE_TAC [arm_move_loop_def,arm_move_loop_pre_def]
  \\ SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC
  THEN1 (Cases_on `ys` \\ FULL_SIMP_TAC std_ss [LENGTH,WORD_ADD_0] \\ `F` by DECIDE_TAC)
  \\ `?z zs. ys = z::zs` by
   (Cases_on `ys` \\ FULL_SIMP_TAC std_ss [LENGTH,ADD1,CONS_11])
  \\ FULL_SIMP_TAC std_ss [] \\ `LENGTH (h::xs) < 4294967296` by DECIDE_TAC
  \\ FULL_SIMP_TAC (std_ss++SIZES_ss) [n2w_11,LENGTH,DECIDE ``~(SUC n = 0)``,MULT_CLAUSES]
  \\ ASM_SIMP_TAC std_ss [LET_DEF,GSYM word_add_n2w,WORD_ADD_SUB,ADD1]
  \\ FULL_SIMP_TAC std_ss [one_list_def,LET_DEF,ALIGNED_INTRO]
  \\ `(f r2 = h) /\ r2 IN df /\ r3 IN df` by SEP_READ_TAC
  \\ FULL_SIMP_TAC std_ss [WORD_ADD_ASSOC]
  \\ SIMP_TAC std_ss [prove(``one(r2,h)*y*(x2*y2)*p = y*y2*(p*x2*one(r2,h))``,
      SIMP_TAC (std_ss++star_ss) [])]
  \\ Q.PAT_X_ASSUM `!ys.bbb` MATCH_MP_TAC \\ Q.EXISTS_TAC `zs`
  \\ FULL_SIMP_TAC std_ss [ALIGNED] \\ REPEAT STRIP_TAC
  THEN1 SEP_WRITE_TAC \\ DECIDE_TAC);

val ref_mem_one_list = prove(
  ``!k a. k <= e - a /\ (!i. i < k ==> (m (a + i) = H_EMP)) ==>
          (ref_mem m a e = SEP_EXISTS ts. cond (LENGTH ts = k) *
                  one_list (ref_addr a) ts * ref_mem m (a + k) e)``,
  Induct \\ REPEAT STRIP_TAC THEN1
    SIMP_TAC std_ss [FUN_EQ_THM,SEP_CLAUSES,SEP_EXISTS_THM,
       cond_STAR,GSYM STAR_ASSOC,LENGTH_NIL,one_list_def]
  \\ CONV_TAC (RATOR_CONV (ONCE_REWRITE_CONV [ref_mem_def]))
  \\ `~(e <= a)` by DECIDE_TAC \\ ASM_SIMP_TAC std_ss []
  \\ `0 < SUC k` by (FULL_SIMP_TAC std_ss [RANGE_def] \\ DECIDE_TAC)
  \\ RES_TAC \\ FULL_SIMP_TAC std_ss [getLENGTH_def,ref_aux_def,SEP_CLAUSES]
  \\ POP_ASSUM (K ALL_TAC)
  \\ Q.PAT_X_ASSUM `!a.bb /\ bbbb ==> bbb` (ASSUME_TAC o Q.SPEC `a+1`)
  \\ `k <= e - (a + 1)` by DECIDE_TAC
  \\ `(!i. i < k ==> (m ((a + 1) + i) = H_EMP))` by
   (REPEAT STRIP_TAC \\ `1 + i < SUC k` by DECIDE_TAC \\ METIS_TAC [ADD_ASSOC])
  \\ Q.PAT_X_ASSUM `bb ==> bbb` MP_TAC \\ ASM_SIMP_TAC std_ss [SEP_CLAUSES]
  \\ REPEAT STRIP_TAC
  \\ SIMP_TAC (std_ss++sep_cond_ss) [FUN_EQ_THM,SEP_CLAUSES,SEP_EXISTS_THM,cond_STAR]
  \\ REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC THEN1
   (Q.EXISTS_TAC `x'::ts`
    \\ ASM_SIMP_TAC std_ss [LENGTH,one_list_def,ADD1,LEFT_ADD_DISTRIB]
    \\ FULL_SIMP_TAC (std_ss++star_ss) [AC ADD_ASSOC ADD_COMM,
         word_arith_lemma1,ref_addr_ADD1] \\ DECIDE_TAC)
  \\ Cases_on `ts` \\ FULL_SIMP_TAC bool_ss [LENGTH] THEN1 `F` by DECIDE_TAC
  \\ Q.LIST_EXISTS_TAC [`h`,`t`]
  \\ FULL_SIMP_TAC (std_ss++star_ss) [AC ADD_ASSOC ADD_COMM,
         word_arith_lemma1,ref_addr_ADD1,one_list_def,ADD1] \\ DECIDE_TAC);

val part_heap_ref_mem_SPLIT = prove(
  ``!b j m k. part_heap b j m k ==> j <= e ==> (ref_mem m b j * ref_mem m j e = ref_mem m b e)``,
  HO_MATCH_MP_TAC part_heap_ind \\ REPEAT STRIP_TAC
  THEN1 (ONCE_REWRITE_TAC [ref_mem_def] \\ SIMP_TAC std_ss [SEP_CLAUSES]) THEN1
   (REPEAT STRIP_TAC \\ CONV_TAC (RATOR_CONV (ONCE_REWRITE_CONV [ref_mem_def]))
    \\ CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [ref_mem_def]))
    \\ IMP_RES_TAC part_heap_LESS_EQ
    \\ `~(j <= b) /\ ~(e <= b)` by DECIDE_TAC \\ ASM_SIMP_TAC std_ss []
    \\ FULL_SIMP_TAC std_ss [GSYM ref_mem_def]
    \\ `getLENGTH (m b) = 0` by  (Cases_on `m b` \\ FULL_SIMP_TAC std_ss [getLENGTH_def,
         heap_element_distinct,isBLOCK_def,heap_element_11])
    \\ ASM_SIMP_TAC std_ss [GSYM STAR_ASSOC])
  \\ `!i. b < i ==> (ref_mem m b i = ref_aux (ref_addr b) (m b) * ref_mem m (b + n + 1) i)` by
   (REPEAT STRIP_TAC \\ CONV_TAC (RATOR_CONV (ONCE_REWRITE_CONV [ref_mem_def]))
    \\ `MAX 1 (n + 1) = n + 1` by (SIMP_TAC std_ss [MAX_DEF] \\ DECIDE_TAC)
    \\ ASM_SIMP_TAC std_ss [getLENGTH_def,DECIDE ``i<=b=~(b<i:num)``,ADD_ASSOC])
  \\ IMP_RES_TAC part_heap_LESS_EQ \\ `b < j /\ b < e` by DECIDE_TAC
  \\ METIS_TAC [STAR_ASSOC]);

val part_heap_ref_mem_SPLIT_LESS = prove(
  ``!b j m k. part_heap b j m k /\ j < e ==>
              (ref_mem m b e = ref_mem m b j * ref_aux (ref_addr j) (m j) *
                               ref_mem m (j + MAX 1 (getLENGTH (m j))) e)``,
  REPEAT STRIP_TAC \\ `j <= e /\ ~(e <= j)` by DECIDE_TAC
  \\ IMP_RES_TAC (GSYM part_heap_ref_mem_SPLIT)
  \\ ASM_SIMP_TAC std_ss [GSYM STAR_ASSOC] \\ METIS_TAC [ref_mem_def]);

val full_heap_ref_mem_SPLIT = prove(
  ``!b j m. full_heap b j m ==> j <= e ==> (ref_mem m b j * ref_mem m j e = ref_mem m b e)``,
  METIS_TAC [full_heap_IMP_part_heap,part_heap_ref_mem_SPLIT]);

val part_heap_SPLIT = prove(
  ``!b e m k. part_heap b e m k /\ RANGE(b,e)i /\ ~(m i = H_EMP) ==>
              ?k1 k2. part_heap b i m k1 /\ part_heap i e m k2``,
  SIMP_TAC std_ss [GSYM AND_IMP_INTRO]
  \\ HO_MATCH_MP_TAC part_heap_ind \\ REPEAT STRIP_TAC THEN1 `F` by RANGE_TAC THEN1
   (Cases_on `i = b` \\ FULL_SIMP_TAC std_ss [] THEN1 METIS_TAC [part_heap_cases]
    \\ `RANGE (b + 1,e) i` by RANGE_TAC \\ RES_TAC
    \\ Q.LIST_EXISTS_TAC [`k1`,`k2`] \\ ASM_SIMP_TAC std_ss []
    \\ METIS_TAC [part_heap_cases])
  \\ Cases_on `i = b` \\ FULL_SIMP_TAC std_ss [] THEN1 METIS_TAC [part_heap_cases]
  \\ Cases_on `RANGE (b + n + 1,e) i` THEN1
   (RES_TAC \\ Q.LIST_EXISTS_TAC [`k1 + (n + 1)`,`k2`] \\ ASM_SIMP_TAC std_ss []
    \\ ONCE_REWRITE_TAC [part_heap_cases] \\ DISJ2_TAC \\ DISJ2_TAC
    \\ Q.LIST_EXISTS_TAC [`n`,`xs`,`d`,`k1`] \\ ASM_SIMP_TAC std_ss [ADD_ASSOC])
  \\ `RANGE (b + 1,b + n + 1) i` by RANGE_TAC
  \\ FULL_SIMP_TAC std_ss [EMP_RANGE_def,IN_DEF] \\ RES_TAC);

val part_heap_ref_mem_SPLIT3 = prove(
  ``!b e m k a.
      part_heap b e m k /\ RANGE(b,e)a /\ ~(m a = H_EMP) ==>
      (ref_mem m b e = ref_mem m b a * ref_aux (ref_addr a) (m a) *
                       ref_mem m (a + MAX 1 (getLENGTH (m a))) e)``,
  REPEAT STRIP_TAC
  \\ `?k1 k2. part_heap b a m k1 /\ part_heap a e m k2` by METIS_TAC [part_heap_SPLIT]
  \\ `a <= e` by IMP_RES_TAC part_heap_LESS_EQ
  \\ `ref_mem m b e = ref_mem m b a * ref_mem m a e` by METIS_TAC [part_heap_ref_mem_SPLIT]
  \\ ASM_SIMP_TAC std_ss [] \\ `~(e <= a)` by RANGE_TAC
  \\ ONCE_REWRITE_TAC [ref_mem_def] \\ ASM_SIMP_TAC std_ss []
  \\ ASM_SIMP_TAC std_ss [GSYM ref_mem_def] \\ ASM_SIMP_TAC std_ss [STAR_ASSOC]);

val ALIGNED_ref_tag = prove(
  ``~ALIGNED (ref_tag (n,d,t))``,
  SIMP_TAC std_ss [ref_tag_def,ALIGNED_n2w]
  \\ `(n * 1024 + w2n t * 4 + 2 + (if d then 1 else 0) =
       (n * 256 + w2n t) * 4 + (2 + if d then 1 else 0)) /\
      2 + (if d then 1 else 0) < 4`
            by (Cases_on `d` \\ DECIDE_TAC)
  \\ ASM_SIMP_TAC std_ss [MOD_MULT]);

val part_heap_IMP_EMP_RANGE = prove(
  ``!b e m k.
      part_heap b e m k /\ RANGE(b,e)i /\ (m i = H_BLOCK (xs,n,d)) ==>
      EMP_RANGE (i + 1,i + n + 1) m /\ n <= e - (i + 1)``,
  NTAC 5 STRIP_TAC \\ `~(m i = H_EMP)` by FULL_SIMP_TAC std_ss [heap_element_distinct]
  \\ `?k2. part_heap i e m k2` by METIS_TAC [part_heap_SPLIT]
  \\ IMP_RES_TAC part_heap_LENGTH_LESS_EQ
  \\ `RANGE (i,e) i` by RANGE_TAC
  \\ `n + 1 <= k2` by METIS_TAC [part_heap_REF]
  \\ Q.PAT_X_ASSUM `part_heap i e m k2` (MP_TAC o RW1[part_heap_cases])
  \\ `~(e = i)` by RANGE_TAC \\ ASM_SIMP_TAC std_ss [isBLOCK_def,heap_element_11]
  \\ REPEAT STRIP_TAC \\ IMP_RES_TAC part_heap_LENGTH_LESS_EQ \\ ASM_SIMP_TAC std_ss []
  \\ RANGE_TAC);

val arm_move_thm = prove(
  ``gc_inv (h1,roots1,h,ff) (b,i,j,e,b2,e2,m,z UNION ADDR_SET [x]) /\ j2 <= je /\ je <= e /\
    (ADDR_SET [x]) SUBSET (DR0(CUT(b2,e2)m)) /\ ALIGNED r1 /\ b <= ij /\ ij <= j /\
    (one (r1,ref_heap_addr x) * ref_mem m ij je * ref_mem m b2 e2 * p) (fun2set (f,df)) /\
    ok_memory m /\ full_heap ij j m /\ (move(x,j,m) = (x2,j2,m2)) ==>
    ?f2. arm_move_pre (r1,ref_heap_addr x,ref_addr j,df,f) /\
         (arm_move (r1,ref_heap_addr x,ref_addr j,df,f) = (r1,ref_addr j2,df,f2)) /\
         (one (r1,ref_heap_addr x2) * ref_mem m2 ij je * ref_mem m2 b2 e2 * p) (fun2set (f2,df)) /\
         ok_memory m2``,
  REVERSE (Cases_on `x`) THEN1
   (SIMP_TAC std_ss [ref_heap_addr_def]
    \\ ONCE_REWRITE_TAC [arm_move_def,arm_move_pre_def,move_def]
    \\ `(n2w (w2n a * 2 + 1) && 0x3w) <> 0x0w:word32` suffices_by
    (STRIP_TAC THEN ASM_SIMP_TAC std_ss [] \\ METIS_TAC [ref_heap_addr_def])
    \\ MATCH_MP_TAC (METIS_PROVE [] ``~(w && 1w = v && 1w) ==> ~(w = v)``)
    \\ SIMP_TAC std_ss [n2w_and_1,n2w_and_3] \\ SIMP_TAC bool_ss [DECIDE ``4=2*2``]
    \\ SIMP_TAC bool_ss [MATCH_MP MOD_MULT_MOD (DECIDE ``0<2 /\ 0<2``)]
    \\ SIMP_TAC std_ss [MATCH_MP MOD_MULT (DECIDE ``1 < 2``)] \\ EVAL_TAC)
  \\ SIMP_TAC std_ss [ADDR_SET_THM,INSERT_SUBSET,EMPTY_SUBSET]
  \\ STRIP_TAC \\ IMP_RES_TAC move_lemma
  \\ ONCE_REWRITE_TAC [arm_move_def,arm_move_pre_def,move_def]
  \\ SIMP_TAC std_ss [ref_heap_addr_def,ALIGNED_INTRO,LET_DEF,ALIGNED_ref_addr]
  \\ `~(m n = H_EMP)` by ASM_SIMP_TAC std_ss [heap_element_distinct]
  \\ FULL_SIMP_TAC (srw_ss()) [move_def] THEN1
   (SUBGOAL `(f (ref_addr n) = ref_addr (ff n)) /\ (ref_addr n) IN df` THEN1
     (ASM_SIMP_TAC std_ss [ALIGNED_and_1,NOT_ALIGNED,ALIGNED_ref_addr]
      \\ EXPAND_TAC \\ FULL_SIMP_TAC std_ss [ref_heap_addr_def] \\ SEP_R_TAC
      \\ SIMP_TAC std_ss [] \\ SEP_WRITE_TAC)
    \\ FULL_SIMP_TAC std_ss [gc_inv_def] \\ EXPAND_TAC
    \\ `RANGE (b2,e2) n` by FULL_SIMP_TAC std_ss [IN_DEF,R0_def,D0_def,DR0_def,CUT_EQ]
    \\ IMP_RES_TAC part_heap_ref_mem_SPLIT3 \\ FULL_SIMP_TAC std_ss []
    \\ FULL_SIMP_TAC std_ss [ref_aux_def] \\ SEP_R_TAC \\ ASM_SIMP_TAC std_ss [])
  \\ `?xs y d. h ' n = (xs,y,d)` by METIS_TAC [PAIR]
  \\ FULL_SIMP_TAC (srw_ss()) [LET_DEF,getLENGTH_def,ADD_ASSOC] \\ EXPAND_TAC
  \\ `~RANGE (b2,e2) j /\ ~RANGE (ij,je) n /\ n < e2` by RANGE_TAC
  \\ ASM_SIMP_TAC std_ss [ref_mem_IGNORE]
  \\ Q.PAT_X_ASSUM `~(n = j)` (fn th => REWRITE_TAC [MATCH_MP UPDATE_COMMUTES (GSYM th)]
                                      \\ ASSUME_TAC th)
  \\ ASM_SIMP_TAC std_ss [ref_mem_IGNORE]
  \\ `j < e` by RANGE_TAC
  \\ `m j = H_EMP` by
   (FULL_SIMP_TAC std_ss [gc_inv_def]
    \\ Q.PAT_X_ASSUM `!k. bb ==> (m k = H_EMP)` MATCH_MP_TAC \\ RANGE_TAC)
  \\ `((n =+ H_REF j) m) n <> H_EMP` by
         FULL_SIMP_TAC std_ss [APPLY_UPDATE_THM,heap_element_distinct]
  \\ `?len. part_heap b2 e2 m len` by METIS_TAC [gc_inv_def]
  \\ `?len2. part_heap b2 e2 ((n =+ H_REF j) m) len2` by
       (FULL_SIMP_TAC std_ss [IN_DEF,gc_inv_def] \\ METIS_TAC [part_heap_REF])
  \\ `RANGE (b2,e2) n` by FULL_SIMP_TAC std_ss [IN_DEF,R0_def,D0_def,DR0_def,CUT_EQ]
  \\ IMP_RES_TAC part_heap_ref_mem_SPLIT3
  \\ ASM_SIMP_TAC std_ss [APPLY_UPDATE_THM,getLENGTH_def,ref_heap_addr_def]
  \\ `~(RANGE(b2,n)n) /\ ~(RANGE(n+1,e2)n) /\ ~(RANGE(j+MAX 1 (x + 1),je)j) /\
      ~(RANGE(ij,j)j) /\ ~(RANGE(ij,je)n) /\ j < je` by
         (FULL_SIMP_TAC std_ss [RANGE_def,MAX_DEF] \\ DECIDE_TAC)
  \\ FULL_SIMP_TAC std_ss [ref_mem_IGNORE,STAR_ASSOC,getLENGTH_def]
  \\ `j <= je` by DECIDE_TAC
  \\ `full_heap ij j ((j =+ H_BLOCK (xs,y,d)) m)` by
       (MATCH_MP_TAC full_heap_RANGE \\ ASM_SIMP_TAC std_ss [RANGE_def])
  \\ IMP_RES_TAC (GSYM full_heap_ref_mem_SPLIT)
  \\ ASSUME_TAC (UNDISCH (Q.SPECL [`j`,`je`] ref_mem_LESS))
  \\ FULL_SIMP_TAC std_ss [APPLY_UPDATE_THM,getLENGTH_def,ref_mem_IGNORE]
  \\ FULL_SIMP_TAC std_ss [STAR_ASSOC]
  \\ Cases_on `d`
  \\ `ok_memory ((n =+ H_REF j) ((j =+ H_BLOCK (xs,y,q,r)) m))` by
      (FULL_SIMP_TAC std_ss [ok_memory_def,APPLY_UPDATE_THM]
       \\ METIS_TAC [heap_element_distinct,heap_element_11])
  \\ `?z1 z2. r = (z1,z2)` by METIS_TAC [PAIR]
  \\ FULL_SIMP_TAC std_ss [MAX_LEMMA] \\ POP_ASSUM (K ALL_TAC)
  \\ FULL_SIMP_TAC std_ss [ref_aux_def,SEP_CLAUSES,SEP_EXISTS_THM,LET_DEF]
  \\ Q.ABBREV_TAC `qs = if z1 then MAP ref_heap_addr xs else z2`
  \\ `ref_addr n IN df /\ r1 IN df /\ ref_addr j IN df`  by SEP_READ_TAC
  \\ `f (ref_addr n) = ref_tag (LENGTH qs,z1,q)` by SEP_READ_TAC
  \\ ASM_SIMP_TAC std_ss [ALIGNED_ref_tag]
  \\ `LENGTH qs < 2 ** 22` by
   (Q.UNABBREV_TAC `qs` \\ Cases_on `z1` \\ FULL_SIMP_TAC std_ss [ok_memory_def]
    \\ RES_TAC \\ FULL_SIMP_TAC std_ss [LENGTH_MAP])
  \\ ASM_SIMP_TAC std_ss [ref_tag_lsr]
  \\ Q.PAT_ABBREV_TAC `fff = (ref_addr n =+ ref_addr j) ffff`
  \\ `(one (r1,ref_addr j) * ref_mem m ij j *
       one (ref_addr j,ref_tag (LENGTH qs,z1,q)) *
       ref_mem m (j + 1) je * ref_mem m b2 n *
       (one (ref_addr n,ref_addr j) *
        one_list (ref_addr n + 0x4w) qs) * ref_mem m (n + (y + 1)) e2 *
       p) (fun2set (fff,df))` by (Q.UNABBREV_TAC `fff` \\ SEP_WRITE_TAC)
  \\ `y <= je - (j + 1)` by RANGE_TAC
  \\ `!i. i < y ==> (m ((j + 1) + i) = H_EMP)` by
      (FULL_SIMP_TAC std_ss [gc_inv_def] \\ REPEAT STRIP_TAC
       \\ REPEAT (Q.PAT_X_ASSUM `~RANGE(bb,ee)ii` (K ALL_TAC))
       \\ Q.PAT_X_ASSUM `!k. bbb ==> (m k = H_EMP)` MATCH_MP_TAC
       \\ FULL_SIMP_TAC std_ss [RANGE_def] \\ DECIDE_TAC)
  \\ IMP_RES_TAC ref_mem_one_list
  \\ FULL_SIMP_TAC std_ss [] \\ POP_ASSUM (K ALL_TAC)
  \\ FULL_SIMP_TAC (std_ss++sep_cond_ss) [SEP_CLAUSES,cond_STAR]
  \\ Q.PAT_X_ASSUM `bbbb (fun2set (f,df))` (K ALL_TAC)
  \\ FULL_SIMP_TAC std_ss [SEP_EXISTS_THM,ref_addr_ADD1,word_arith_lemma1]
  \\ FULL_SIMP_TAC std_ss [cond_STAR]
  \\ `(one_list (ref_addr n + 0x4w) qs * one_list (ref_addr j + 0x4w) ts *
       (one (r1,ref_addr j) * ref_mem m ij j *
        one (ref_addr j,ref_tag (LENGTH qs,z1,q)) *
        ref_mem m (j + 1 + y) je *
        ref_mem m b2 n * one (ref_addr n,ref_addr j) *
        ref_mem m (n + (y + 1)) e2 * p)) (fun2set (fff,df))` by
          FULL_SIMP_TAC (std_ss++star_ss) []
  \\ `ALIGNED (ref_addr n + 0x4w) /\ ALIGNED (ref_addr j + 0x4w)`
       by ASM_SIMP_TAC std_ss [ALIGNED,ALIGNED_ref_addr]
  \\ `LENGTH ts < 2 ** 23 /\ (LENGTH qs = LENGTH ts) /\ y < 8388608` by
      (FULL_SIMP_TAC std_ss [ok_memory_def] \\ RES_TAC
       \\ Cases_on `z1` \\ Q.UNABBREV_TAC `qs`
       \\ FULL_SIMP_TAC std_ss [LENGTH_MAP] \\ DECIDE_TAC)
  \\ IMP_RES_TAC arm_move_loop_thm
  \\ REPEAT (Q.PAT_X_ASSUM `!xx yy zz. bb` (K ALL_TAC))
  \\ FULL_SIMP_TAC std_ss []
  \\ POP_ASSUM MP_TAC \\ ASM_SIMP_TAC bool_ss [] \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC (std_ss++star_ss) [GSYM ref_addr_ADD1, GSYM ref_addr_def]
  \\ FULL_SIMP_TAC std_ss [AC ADD_ASSOC ADD_COMM]
  \\ `y <= e2 - (n + 1) /\ (!i. i < y ==> (m ((n + 1) + i) = H_EMP))` by
   (IMP_RES_TAC part_heap_IMP_EMP_RANGE \\ ASM_SIMP_TAC std_ss []
    \\ FULL_SIMP_TAC std_ss [EMP_RANGE_def] \\ REPEAT STRIP_TAC
    \\ Q.PAT_X_ASSUM `!k. k IN RANGE (n + 1,n + y + 1) ==> (m k = H_EMP)` MATCH_MP_TAC
    \\ RANGE_TAC)
  \\ IMP_RES_TAC ref_mem_one_list
  \\ `~RANGE(j + (y + 1),je)j` by RANGE_TAC \\ FULL_SIMP_TAC std_ss [ref_mem_IGNORE]
  \\ FULL_SIMP_TAC std_ss [SEP_CLAUSES,SEP_EXISTS_THM] \\ Q.EXISTS_TAC `qs`
  \\ FULL_SIMP_TAC (std_ss++star_ss) [SEP_CLAUSES, AC ADD_ASSOC ADD_COMM]);

val EQ_RANGE_ref_mem = prove(
  ``!i j m m2. EQ_RANGE (i,j) m m2 ==> (ref_mem m i j = ref_mem m2 i j)``,
  NTAC 2 STRIP_TAC \\ completeInduct_on `j-i` \\ ONCE_REWRITE_TAC [ref_mem_def]
  \\ REPEAT STRIP_TAC \\ Cases_on `j<=i` \\ ASM_SIMP_TAC std_ss []
  \\ `m i = m2 i` by
     (FULL_SIMP_TAC std_ss [EQ_RANGE_def,RANGE_def,IN_DEF]
      \\ `i <= i /\ i < j` by DECIDE_TAC \\ METIS_TAC [])
  \\ ASM_SIMP_TAC std_ss []
  \\ Q.ABBREV_TAC `y = MAX 1 (getLENGTH (m2 i))`
  \\ `0 < y` by (Q.UNABBREV_TAC `y` \\ SIMP_TAC std_ss [MAX_DEF] \\ DECIDE_TAC)
  \\ `j - (i + y) < j - i` by DECIDE_TAC
  \\ `EQ_RANGE (i+y,j) m m2` suffices_by METIS_TAC []
  \\ MATCH_MP_TAC EQ_RANGE_IMP_EQ_RANGE \\ Q.LIST_EXISTS_TAC [`i`,`j`]
  \\ ASM_SIMP_TAC std_ss [] \\ DECIDE_TAC);

val EQ_RANGE_TRANS = prove(
  ``!m1 m2 m3. EQ_RANGE (b,e) m1 m2 /\ EQ_RANGE (b,e) m2 m3 ==> EQ_RANGE (b,e) m1 m3``,
  METIS_TAC [EQ_RANGE_def]);

val full_heap_NEXT = prove(
  ``(m i = H_BLOCK (x,n,y)) /\ ~(i = j) /\ full_heap i j m ==>
    full_heap (i + n + 1) j m``,
  CONV_TAC (RATOR_CONV (ONCE_REWRITE_CONV [full_heap_cases]))
  \\ SIMP_TAC std_ss [GSYM AND_IMP_INTRO,heap_element_11]);

val arm_move_list_thm = prove(
  ``!f m j ys p r1 z h f8.
      ADDR_SET xs SUBSET DR0 (CUT (b2,e2) m) /\ ALIGNED r1 /\
      full_heap ij j m /\ b <= ij /\ ij <= j /\ j2 <= je /\ je <= e /\
      gc_inv (h1,roots1,h,f8) (b,i,j,e,b2,e2,m,z UNION ADDR_SET xs) /\ e < 2**30 /\ LENGTH xs < 2**32 /\
      (ref_mem m ij je * ref_mem m b2 e2 * one_list r1 (MAP ref_heap_addr xs) * p) (fun2set (f,df)) /\
      ok_memory m ==> (move_list(xs,j,m) = (ys,j2,m2)) ==>
      ?f2 h3 f3.
        arm_move_list_pre (r1,ref_addr j,n2w (LENGTH xs),df,f)/\
        (arm_move_list (r1,ref_addr j,n2w (LENGTH xs),df,f) = (r1 + n2w (4 * LENGTH xs),ref_addr j2,df,f2)) /\
        (ref_mem m2 ij je * ref_mem m2 b2 e2 * one_list r1 (MAP ref_heap_addr ys) * p) (fun2set (f2,df)) /\
        ok_memory m2 /\ gc_inv (h1,roots1,h3,f3)
                           (b,i,j2,e,b2,e2,m2,z UNION D1 (CUT (j,j2) m2)) /\
        (LENGTH ys = LENGTH xs)``,
  Induct_on `xs` THEN1
   (ONCE_REWRITE_TAC [EQ_SYM_EQ] \\ SIMP_TAC std_ss [move_list_def,one_list_def]
    \\ ONCE_REWRITE_TAC [arm_move_list_def,arm_move_list_pre_def]
    \\ SIMP_TAC std_ss [LENGTH,WORD_ADD_0,CUT_EMPTY,ADDR_SET_THM] \\ METIS_TAC [])
  \\ ONCE_REWRITE_TAC [ADDR_SET_CONS] \\ SIMP_TAC std_ss [UNION_SUBSET]
  \\ NTAC 6 STRIP_TAC \\ `?y j3 m3. move(h,j,m) = (y,j3,m3)` by METIS_TAC [PAIR]
  \\ `?zs j4 m4. move_list (xs,j3,m3) = (zs,j4,m4)` by METIS_TAC [PAIR]
  \\ ASM_SIMP_TAC std_ss [move_list_def,one_list_def,MAP,LET_DEF,STAR_ASSOC]
  \\ REPEAT STRIP_TAC \\ NTAC 2 (POP_ASSUM (fn th => FULL_SIMP_TAC std_ss [GSYM th]))
  \\ FULL_SIMP_TAC std_ss [UNION_ASSOC] \\ IMP_RES_TAC move_thm
  \\ `ADDR_SET xs SUBSET DR0 (CUT (b2,e2) m3)` by METIS_TAC [SUBSET_TRANS]
  \\ `z UNION ADDR_SET xs UNION D1 (CUT (j,j3) m3) =
      (z UNION D1 (CUT (j,j3) m3)) UNION ADDR_SET xs` by SET_TAC
  \\ `j3 <= j4` by METIS_TAC [move_list_thm]
  \\ ONCE_REWRITE_TAC [arm_move_list_def,arm_move_list_pre_def] \\ SEP_R_TAC
  \\ FULL_SIMP_TAC (std_ss++SIZES_ss) [LET_DEF,LENGTH,n2w_11,DECIDE ``~(SUC n = 0)``]
  \\ SIMP_TAC std_ss [MULT_CLAUSES,GSYM word_add_n2w,WORD_ADD_ASSOC]
  \\ ASM_SIMP_TAC std_ss [ADD1,GSYM word_add_n2w,WORD_ADD_SUB,ALIGNED_INTRO]
  \\ `j3 <= je` by DECIDE_TAC
  \\ SEP_S_TAC ["arm_move","move","gc_inv"] (GEN_ALL arm_move_thm)
  \\ ASM_SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC \\ ASM_SIMP_TAC std_ss []
  \\ Q.PAT_X_ASSUM `!xx yy. bbb` (SEP_S_TAC ["arm_move_list","move_list","gc_inv"])
  \\ IMP_RES_TAC full_heap_LESS_EQ
  \\ `ij <= j3 /\ LENGTH xs < 4294967296` by DECIDE_TAC
  \\ ASM_SIMP_TAC std_ss [ALIGNED]
  \\ `EQ_RANGE (ij,j) m m3` by
    (MATCH_MP_TAC EQ_RANGE_IMP_EQ_RANGE \\ METIS_TAC [EQ_RANGE_THM,LESS_EQ_REFL])
  \\ IMP_RES_TAC EQ_RANGE_full_heap
  \\ IMP_RES_TAC full_heap_TRANS \\ ASM_SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC
  \\ ASM_SIMP_TAC std_ss [] \\ EXPAND_TAC
  \\ FULL_SIMP_TAC (std_ss++star_ss) [LENGTH,one_list_def,MAP,ADD1]
  \\ `D1 (CUT (j,j4) m4) = D1 (CUT (j,j3) m4) UNION D1 (CUT (j3,j4) m4)` by
       METIS_TAC [D1_UNION]
  \\ SUBGOAL `CUT (j,j3) m3 = CUT (j,j3) m4` THEN1 METIS_TAC [UNION_ASSOC]
  \\ `(CUT(b,j3)m3 = CUT(b,j3)m4)` by METIS_TAC [move_list_thm]
  \\ FULL_SIMP_TAC std_ss [CUT_def,FUN_EQ_THM,IN_DEF] \\ REPEAT STRIP_TAC
  \\ Cases_on `RANGE (j,j3) x` \\ ASM_SIMP_TAC std_ss []
  \\ `RANGE (b,j3) x` by RANGE_TAC \\ SET_TAC);

val arm_move_roots_thm = prove(
  ``!f m j ys p r1 z h f8.
      ADDR_SET xs SUBSET DR0 (CUT (b2,e2) m) /\ ALIGNED r1 /\
      full_heap ij j m /\ b <= ij /\ ij <= j /\ j2 <= je /\ je <= e /\
      gc_inv (h1,roots1,h,f8) (b,i,j,e,b2,e2,m,z UNION ADDR_SET xs) /\ e < 2**30 /\
      (ref_mem m ij je * ref_mem m b2 e2 * one_list_roots r1 xs * p) (fun2set (f,df)) /\
      ok_memory m ==> (move_list(xs,j,m) = (ys,j2,m2)) ==>
      ?f2 h3 f3.
           arm_move_roots_pre (r1,ref_addr j,df,f)/\
           (arm_move_roots (r1,ref_addr j,df,f) = (ref_addr j2,df,f2)) /\
           (ref_mem m2 ij je * ref_mem m2 b2 e2 * one_list_roots r1 ys * p) (fun2set (f2,df)) /\
           ok_memory m2 /\ gc_inv (h1,roots1,h3,f3)
                           (b,i,j2,e,b2,e2,m2,z UNION D1 (CUT (j,j2) m2))``,
  Induct_on `xs` THEN1
   (ONCE_REWRITE_TAC [EQ_SYM_EQ] \\ SIMP_TAC std_ss [move_list_def,one_list_roots_def]
    \\ ONCE_REWRITE_TAC [arm_move_roots_def,arm_move_roots_pre_def]
    \\ REPEAT STRIP_TAC \\ `(f r1 = 2w) /\ r1 IN df` by SEP_READ_TAC
    \\ FULL_SIMP_TAC std_ss [LET_DEF,ALIGNED_INTRO,ADDR_SET_THM,CUT_EMPTY] \\ SET_TAC)
  \\ ONCE_REWRITE_TAC [ADDR_SET_CONS] \\ SIMP_TAC std_ss [UNION_SUBSET]
  \\ NTAC 6 STRIP_TAC \\ `?y j3 m3. move(h,j,m) = (y,j3,m3)` by METIS_TAC [PAIR]
  \\ `?zs j4 m4. move_list (xs,j3,m3) = (zs,j4,m4)` by METIS_TAC [PAIR]
  \\ ASM_SIMP_TAC std_ss [move_list_def,one_list_roots_def,MAP,LET_DEF,STAR_ASSOC]
  \\ REPEAT STRIP_TAC \\ NTAC 2 (POP_ASSUM (fn th => FULL_SIMP_TAC std_ss [GSYM th]))
  \\ FULL_SIMP_TAC std_ss [UNION_ASSOC] \\ IMP_RES_TAC move_thm
  \\ `ADDR_SET xs SUBSET DR0 (CUT (b2,e2) m3)` by METIS_TAC [SUBSET_TRANS]
  \\ `z UNION ADDR_SET xs UNION D1 (CUT (j,j3) m3) =
      (z UNION D1 (CUT (j,j3) m3)) UNION ADDR_SET xs` by SET_TAC
  \\ `j3 <= j4` by METIS_TAC [move_list_thm]
  \\ ONCE_REWRITE_TAC [arm_move_roots_def,arm_move_roots_pre_def] \\ SEP_R_TAC
  \\ FULL_SIMP_TAC (std_ss++SIZES_ss) [LET_DEF,LENGTH,ref_heap_addr_NEQ_2]
  \\ SIMP_TAC std_ss [MULT_CLAUSES,GSYM word_add_n2w,WORD_ADD_ASSOC]
  \\ ASM_SIMP_TAC std_ss [ADD1,GSYM word_add_n2w,WORD_ADD_SUB,ALIGNED_INTRO]
  \\ `j3 <= je` by DECIDE_TAC
  \\ SEP_S_TAC ["arm_move","move","gc_inv"] (GEN_ALL arm_move_thm)
  \\ ASM_SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC \\ ASM_SIMP_TAC std_ss []
  \\ Q.PAT_X_ASSUM `!xx yy. bbb` (SEP_S_TAC ["arm_move_roots","move_list","gc_inv"])
  \\ IMP_RES_TAC full_heap_LESS_EQ
  \\ `ij <= j3` by DECIDE_TAC
  \\ ASM_SIMP_TAC std_ss [ALIGNED]
  \\ `EQ_RANGE (ij,j) m m3` by
    (MATCH_MP_TAC EQ_RANGE_IMP_EQ_RANGE \\ METIS_TAC [EQ_RANGE_THM,LESS_EQ_REFL])
  \\ IMP_RES_TAC EQ_RANGE_full_heap
  \\ IMP_RES_TAC full_heap_TRANS \\ ASM_SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC
  \\ ASM_SIMP_TAC std_ss [] \\ EXPAND_TAC
  \\ FULL_SIMP_TAC (std_ss++star_ss) [LENGTH,one_list_roots_def,MAP,ADD1]
  \\ `D1 (CUT (j,j4) m4) = D1 (CUT (j,j3) m4) UNION D1 (CUT (j3,j4) m4)` by
       METIS_TAC [D1_UNION]
  \\ SUBGOAL `CUT (j,j3) m3 = CUT (j,j3) m4` THEN1 METIS_TAC [UNION_ASSOC]
  \\ `(CUT(b,j3)m3 = CUT(b,j3)m4)` by METIS_TAC [move_list_thm]
  \\ FULL_SIMP_TAC std_ss [CUT_def,FUN_EQ_THM,IN_DEF] \\ REPEAT STRIP_TAC
  \\ Cases_on `RANGE (j,j3) x` \\ ASM_SIMP_TAC std_ss []
  \\ `RANGE (b,j3) x` by RANGE_TAC \\ SET_TAC);

val ref_tag_and_1 = prove(
  ``(ref_tag (n,x,y) && 1w = 0w) = ~x``,
  SIMP_TAC std_ss [ref_tag_def,n2w_and_1]
  \\ `n * 1024 + w2n y * 4 + 2 = (n * 512 + w2n y * 2 + 1) * 2` by DECIDE_TAC
  \\ `(if x then 1 else 0) < 2` by (Cases_on `x` \\ DECIDE_TAC)
  \\ ASM_SIMP_TAC std_ss [MOD_MULT] \\ Cases_on `x`
  \\ ASM_SIMP_TAC std_ss [] \\ EVAL_TAC);

val arm_loop_thm = prove(
  ``!f m j h8 f8. gc_inv (h1,roots1,h8,f8) (b,i,j,e,b2,e2,m,D1 (CUT (i,j) m)) /\
    e < 2 ** 30 /\
    (ref_mem m b i2 * ref_mem m b2 e2 * p) (fun2set (f,df)) /\
    ok_memory m ==> (gc_loop(i,j,m) = (i2,m2)) ==>
    ?f2. arm_loop_pre (ref_addr i,ref_addr j,df,f) /\
         (arm_loop (ref_addr i,ref_addr j,df,f) = (ref_addr i2,df,f2)) /\
         (ref_mem m2 b i2 * ref_mem m2 b2 e2 * p) (fun2set (f2,df)) /\ ok_memory m2``,
  completeInduct_on `e-i` \\ NTAC 9 STRIP_TAC \\ Cases_on `j <= i` THEN1
   (`i = j` by (FULL_SIMP_TAC std_ss [gc_inv_def] \\ DECIDE_TAC)
    \\ PURE_ONCE_REWRITE_TAC [gc_loop_def,arm_loop_def,arm_loop_pre_def]
    \\ ASM_SIMP_TAC std_ss [] \\ ONCE_REWRITE_TAC [EQ_SYM_EQ]
    \\ FULL_SIMP_TAC std_ss [CUT_EMPTY] \\ METIS_TAC [])
  \\ `~(i = j)` by (FULL_SIMP_TAC std_ss [gc_inv_def] \\ DECIDE_TAC)
  \\ IMP_RES_TAC gc_step_lemma
  \\ PURE_ONCE_REWRITE_TAC [gc_loop_def,arm_loop_def,arm_loop_pre_def]
  \\ ASM_SIMP_TAC std_ss []
  \\ `~(ref_addr i = ref_addr j)` by
   (FULL_SIMP_TAC (std_ss++SIZES_ss) [ref_addr_def,n2w_11]
    \\ `i <= e /\ j <= e` by (FULL_SIMP_TAC std_ss [gc_inv_def] \\ DECIDE_TAC)
    \\ `4 * i < 4 * 1073741824 /\ 4 * j < 4 * 1073741824` by DECIDE_TAC
    \\ FULL_SIMP_TAC bool_ss [EVAL ``4 * 1073741824``,LESS_MOD] \\ DECIDE_TAC)
  \\ `?i8 j8 m8. gc_step (i,j,m) = (i8,j8,m8)` by METIS_TAC [PAIR]
  \\ ASM_SIMP_TAC std_ss [LET_DEF]
  \\ `i < j` by DECIDE_TAC \\ IMP_RES_TAC gc_step_thm
  \\ REPEAT (Q.PAT_X_ASSUM `!xx yy zz dd. bb` (K ALL_TAC))
  \\ Q.PAT_X_ASSUM `m i = H_BLOCK (xs,n,d)` ASSUME_TAC
  \\ FULL_SIMP_TAC std_ss [getBLOCK_def,gc_step_def,LET_DEF]
  \\ STRIP_TAC \\ `i8 <= i2 /\ j8 <= i2 /\ i2 <= e` by
    (IMP_RES_TAC gc_loop_thm \\ ASM_SIMP_TAC std_ss []
     \\ FULL_SIMP_TAC std_ss [gc_inv_def] \\ DECIDE_TAC)
  \\ Q.PAT_X_ASSUM `xx = (i2,m2)` MP_TAC
  \\ `?z1 z2 z3. d = (z1,z2,z3)` by METIS_TAC [PAIR]
  \\ FULL_SIMP_TAC std_ss []
  \\ Q.ABBREV_TAC `qs = if z2 then MAP ref_heap_addr xs else z3`
  \\ `(f (ref_addr i) = ref_tag (LENGTH qs,z2,z1)) /\
      (ref_addr i) IN df` by
     (FULL_SIMP_TAC std_ss [gc_inv_def]
      \\ `i < i2` by (FULL_SIMP_TAC std_ss [gc_inv_def,RANGE_def] \\ DECIDE_TAC)
      \\ IMP_RES_TAC full_heap_IMP_part_heap
      \\ IMP_RES_TAC part_heap_ref_mem_SPLIT_LESS
      \\ FULL_SIMP_TAC std_ss [ref_aux_def,LET_DEF] \\ SEP_READ_TAC)
  \\ ASM_SIMP_TAC std_ss [ref_tag_and_1]
  \\ REVERSE (Cases_on `z2`) THEN1
   (FULL_SIMP_TAC std_ss [] \\ Q.UNABBREV_TAC `qs`
    \\ `(xs = []) /\ LENGTH z3 < 2 ** 22 /\ (LENGTH z3 = n)`
          by METIS_TAC [heap_element_11,ok_memory_def]
    \\ ASM_SIMP_TAC bool_ss [ref_tag_lsr]
    \\ FULL_SIMP_TAC std_ss [move_list_def,UPDATE_APPLY_IMP_ID,GSYM ref_addr_ADD1]
    \\ ASM_SIMP_TAC std_ss [ALIGNED_INTRO,ALIGNED_ref_addr,WORD_MUL_LSL,
          word_mul_n2w,GSYM ref_addr_def,GSYM ref_addr_ADD1]
    \\ `e - (i + n + 1) < e - i` by (FULL_SIMP_TAC std_ss [gc_inv_def] \\ DECIDE_TAC)
    \\ Q.PAT_X_ASSUM `!m. m < e - i ==> bbb` ASSUME_TAC
    \\ POP_ASSUM (ASSUME_TAC o UNDISCH o Q.SPEC `e - (i + n + 1)`)
    \\ POP_ASSUM (MP_TAC o RW[] o Q.SPECL [`e`,`i + n + 1`])
    \\ `i + 1 + n = i + n + 1` by DECIDE_TAC \\ FULL_SIMP_TAC std_ss []
    \\ STRIP_TAC \\ POP_ASSUM MATCH_MP_TAC \\ ASM_SIMP_TAC std_ss [] \\ SET_TAC)
  \\ `i < i2` by RANGE_TAC
  \\ `?k. part_heap b i m k` by (FULL_SIMP_TAC std_ss [gc_inv_def]
       \\ IMP_RES_TAC full_heap_IMP_part_heap \\ SET_TAC)
  \\ `ref_mem m b i2 =
      ref_mem m b i * ref_aux (ref_addr i) (m i) *
      ref_mem m (i + MAX 1 (getLENGTH (m i))) i2` by METIS_TAC [part_heap_ref_mem_SPLIT_LESS]
  \\ FULL_SIMP_TAC std_ss [ref_aux_def,STAR_ASSOC,ALIGNED_INTRO,ALIGNED_ref_addr]
  \\ Q.UNABBREV_TAC `qs`
  \\ `LENGTH xs < 2 ** 22 /\ (LENGTH xs = n)` by METIS_TAC [heap_element_11,ok_memory_def]
  \\ FULL_SIMP_TAC bool_ss [LENGTH_MAP,ref_tag_lsr,LET_DEF]
  \\ `?xs3 j3 m3. move_list (xs,j,m) = (xs3,j3,m3)` by METIS_TAC [PAIR]
  \\ FULL_SIMP_TAC std_ss [LET_DEF,LENGTH_MAP,STAR_ASSOC,getLENGTH_def,MAX_LEMMA]
  \\ Q.PAT_X_ASSUM `LENGTH xs = n` (fn th => FULL_SIMP_TAC std_ss [GSYM th])
  \\ `?f2 h3 f3.
       arm_move_list_pre (ref_addr i + 0x4w,ref_addr j,n2w (LENGTH xs),df,f) /\
       (arm_move_list (ref_addr i + 0x4w,ref_addr j,n2w (LENGTH xs),df,f) =
        (ref_addr i + 0x4w + n2w (4 * LENGTH xs),ref_addr j8,df,f2)) /\
       (ref_mem m3 (i + LENGTH xs + 1) i2 * ref_mem m3 b2 e2 *
        one_list (ref_addr i + 0x4w) (MAP ref_heap_addr xs3) *
        (ref_mem m b i * one (ref_addr i,ref_tag (LENGTH xs,T,z1)) * p))
         (fun2set (f2,df)) /\ ok_memory m3 /\
       gc_inv (h1,roots1,h3,f3)
         (b,i,j8,e,b2,e2,m3,D1 (CUT (i+LENGTH xs+1,j) m) UNION D1 (CUT (j,j8) m3)) /\
       (LENGTH xs3 = LENGTH xs)` by
    (MATCH_MP_TAC (RW [AND_IMP_INTRO] (GEN_ALL arm_move_list_thm))
     \\ Q.LIST_EXISTS_TAC [`m`,`h8`,`f8`]
     \\ `LENGTH xs < 4294967296` by DECIDE_TAC
     \\ ASM_SIMP_TAC std_ss [ALIGNED,ALIGNED_ref_addr]
     \\ `full_heap i8 j m` by METIS_TAC [full_heap_NEXT,gc_inv_def]
     \\ EXPAND_TAC \\ FULL_SIMP_TAC (std_ss++star_ss) [AC ADD_ASSOC ADD_COMM]
     \\ IMP_RES_TAC full_heap_LESS_EQ \\ FULL_SIMP_TAC std_ss [gc_inv_def])
  \\ FULL_SIMP_TAC std_ss [move_list_def,UPDATE_APPLY_IMP_ID,GSYM ref_addr_ADD1]
  \\ ASM_SIMP_TAC std_ss [ALIGNED_INTRO,ALIGNED_ref_addr,WORD_MUL_LSL,
          word_mul_n2w,GSYM ref_addr_def,GSYM ref_addr_ADD1]
  \\ `e - i8 < e - i /\ (i + 1 + LENGTH xs = i8)`  by DECIDE_TAC
  \\ ASM_SIMP_TAC std_ss []
  \\ Q.PAT_X_ASSUM `!m. m < e - i ==> bbb` (ASSUME_TAC o UNDISCH o Q.SPEC `e - i8`)
  \\ POP_ASSUM (MATCH_MP_TAC o RW[] o Q.SPECL [`e`,`i8`])
  \\ Q.PAT_X_ASSUM `(i + LENGTH xs + 1 = i8)` ASSUME_TAC \\ FULL_SIMP_TAC std_ss []
  \\ `i8 <= j` by IMP_RES_TAC full_heap_LESS_EQ
  \\ SUBGOAL `(ref_mem m8 b i2 * ref_mem m8 b2 e2 * p) (fun2set (f2,df)) /\
              ok_memory m8` THEN1 METIS_TAC [D1_UNION]
  \\ Q.PAT_X_ASSUM `mmm = m8` (ASSUME_TAC o GSYM) \\ FULL_SIMP_TAC std_ss []
  \\ REVERSE STRIP_TAC THEN1
   (FULL_SIMP_TAC std_ss [ok_memory_def,APPLY_UPDATE_THM] \\ RES_TAC
    \\ STRIP_TAC \\ Cases_on `i = a` \\ FULL_SIMP_TAC std_ss [heap_element_11]
    \\ METIS_TAC [])
  \\ `full_heap b i ((i =+ H_BLOCK (xs3,LENGTH xs,z1,T,z3)) m3)` by
      (`~(RANGE(b,i)i)` by RANGE_TAC \\ FULL_SIMP_TAC std_ss [gc_inv_def]
       \\ METIS_TAC [full_heap_RANGE])
   \\ `(ref_mem ((i =+ H_BLOCK (xs3,LENGTH xs,z1,T,z3)) m3) b i2 =
       ref_mem ((i =+ H_BLOCK (xs3,LENGTH xs,z1,T,z3)) m3) b i *
       ref_aux (ref_addr i) (((i =+ H_BLOCK (xs3,LENGTH xs,z1,T,z3)) m3) i) *
       ref_mem ((i =+ H_BLOCK (xs3,LENGTH xs,z1,T,z3)) m3)
               (i + MAX 1 (getLENGTH (((i =+ H_BLOCK (xs3,LENGTH xs,z1,T,z3)) m3) i))) i2)` by
        (MATCH_MP_TAC part_heap_ref_mem_SPLIT_LESS
         \\ FULL_SIMP_TAC std_ss [gc_inv_def]
         \\ METIS_TAC [full_heap_IMP_part_heap])
  \\ `~(RANGE (b,i) i) /\ ~(RANGE (i8,i2) i) /\ ~(RANGE (b2,e2) i)`
        by (FULL_SIMP_TAC std_ss [gc_inv_def,RANGE_def] \\ DECIDE_TAC)
  \\ FULL_SIMP_TAC std_ss [APPLY_UPDATE_THM,getLENGTH_def,STAR_ASSOC,
       ref_aux_def,HD,ref_mem_IGNORE,LET_DEF,LENGTH_MAP,MAX_LEMMA,ADD_ASSOC]
  \\ `ref_mem m b i = ref_mem m3 b i`
        suffices_by (STRIP_TAC \\
                     FULL_SIMP_TAC (std_ss++star_ss)
                       [AC ADD_ASSOC ADD_COMM,ref_addr_ADD1])
  \\ MATCH_MP_TAC EQ_RANGE_ref_mem
  \\ MATCH_MP_TAC EQ_RANGE_IMP_EQ_RANGE
  \\ Q.LIST_EXISTS_TAC [`b`,`j`] \\ `i <= j` by RANGE_TAC \\ ASM_SIMP_TAC std_ss []
  \\ MATCH_MP_TAC EQ_RANGE_THM \\ IMP_RES_TAC move_list_thm);

val one_scratch_def = Define `
  one_scratch a (b,e,b2,e2) =
    one (a + 40w,ref_addr b) * one (a + 44w,ref_addr e) *
    one (a + 48w,ref_addr b2) * one (a + 52w,ref_addr e2)`;

val ref_mem_LESS_EQ = prove(
  ``!p x. (ref_mem m b e * p) x ==> b <= e``,
  completeInduct_on `e - b` \\ NTAC 3 STRIP_TAC \\ Cases_on `e <= b`
  \\ ONCE_REWRITE_TAC [ref_mem_def] \\ ASM_SIMP_TAC std_ss [cond_STAR]
  \\ SIMP_TAC std_ss [GSYM STAR_ASSOC]
  \\ ONCE_REWRITE_TAC [STAR_COMM] \\ SIMP_TAC std_ss [GSYM STAR_ASSOC]
  \\ Q.ABBREV_TAC `y = MAX 1 (getLENGTH (m b))`
  \\ `0 < y` by (Q.UNABBREV_TAC `y` \\ FULL_SIMP_TAC std_ss [MAX_DEF] \\ DECIDE_TAC)
  \\ `e - (b+y)<v /\ (e - (b+y) = e - (b+y))` by DECIDE_TAC
  \\ REPEAT STRIP_TAC \\ `b+y <= e` by METIS_TAC [] \\ DECIDE_TAC);

val ref_mem_H_EMP = store_thm("ref_mem_H_EMP",
  ``ref_mem (\a.H_EMP) b e =
    SEP_EXISTS xs. one_list (ref_addr b) xs * cond (LENGTH xs = (e-b)) * cond (b <= e)``,
  Induct_on `e-b` THEN1
   (ONCE_REWRITE_TAC [ref_mem_def] \\ ASM_SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC
    \\ REVERSE (Cases_on `b <= e`)
    THEN1 (`~(b = e)` by DECIDE_TAC \\ ASM_SIMP_TAC std_ss [SEP_CLAUSES])
    \\ `(b = e)` by DECIDE_TAC
    \\ ASM_SIMP_TAC std_ss [FUN_EQ_THM,cond_STAR,SEP_EXISTS_THM,LENGTH_NIL,one_list_def,SEP_CLAUSES])
  \\ REPEAT STRIP_TAC
  \\ ONCE_REWRITE_TAC [ref_mem_def] \\ `~(e <= b)` by DECIDE_TAC
  \\ ASM_SIMP_TAC std_ss [getLENGTH_def,ref_aux_def,STAR_ASSOC,SEP_CLAUSES]
  \\ `v = e - (b + 1)` by DECIDE_TAC
  \\ RES_TAC \\ ASM_SIMP_TAC std_ss [SEP_CLAUSES,STAR_ASSOC]
  \\ SIMP_TAC std_ss [FUN_EQ_THM,SEP_EXISTS_THM]
  \\ REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC THEN1
   (Q.EXISTS_TAC `x'::xs` \\ FULL_SIMP_TAC std_ss [one_list_def,STAR_ASSOC,
       LENGTH,cond_STAR,word_arith_lemma1,GSYM ref_addr_ADD1] \\ DECIDE_TAC)
  \\ FULL_SIMP_TAC std_ss [cond_STAR]
  \\ Cases_on `xs` THEN1 (FULL_SIMP_TAC std_ss [LENGTH] \\ `F` by DECIDE_TAC)
  \\ FULL_SIMP_TAC std_ss [one_list_def,word_arith_lemma1,GSYM ref_addr_ADD1,LENGTH]
  \\ Q.LIST_EXISTS_TAC [`h`,`t`] \\ FULL_SIMP_TAC std_ss [STAR_ASSOC] \\ DECIDE_TAC);

val ref_aux_IMP = prove(
  ``!p x. (ref_aux (ref_addr b) (m b) * p) x /\ ok_memory m ==>
          (ref_mem (\a.H_EMP) b (b + MAX 1 (getLENGTH (m b))) * p) x``,
  REVERSE (Cases_on `m b`) THEN1
   (`?x1 x2 x3 x4 x5. p = (x1,x2,x3,x4,x5)` by METIS_TAC [PAIR]
    \\ FULL_SIMP_TAC std_ss [ref_aux_def,LET_DEF,LENGTH_MAP,getLENGTH_def,MAX_LEMMA]
    \\ REPEAT STRIP_TAC \\ SIMP_TAC std_ss [ref_mem_H_EMP,SEP_CLAUSES]
    \\ SIMP_TAC (std_ss++sep_cond_ss) [SEP_EXISTS_THM,cond_STAR]
    \\ Q.ABBREV_TAC `y = if x4 then MAP ref_heap_addr x1 else x5`
    \\ Q.EXISTS_TAC `ref_tag (LENGTH y,x4,x3) :: y`
    \\ FULL_SIMP_TAC std_ss [LENGTH,ADD1,one_list_def,STAR_ASSOC]
    \\ FULL_SIMP_TAC std_ss [ok_memory_def] \\ RES_TAC
    \\ Q.UNABBREV_TAC `y` \\ METIS_TAC [LENGTH_MAP])
  \\ NTAC 2 (ONCE_REWRITE_TAC [ref_mem_def])
  \\ SIMP_TAC std_ss [getLENGTH_def,ref_aux_def,DECIDE ``~(b+1<=b)``,
       SEP_CLAUSES,SEP_EXISTS_THM] \\ METIS_TAC []);

val ref_mem_H_EMP_SPLIT = prove(
  ``b <= i /\ i <= e ==>
    (ref_mem (\a. H_EMP) b e = ref_mem (\a. H_EMP) b i * ref_mem (\a. H_EMP) i e)``,
  Induct_on `i-b` \\ REPEAT STRIP_TAC \\ ONCE_REWRITE_TAC [ref_mem_def]
  THEN1 (`i = b` by DECIDE_TAC \\ ASM_SIMP_TAC std_ss [SEP_CLAUSES])
  \\ `~(e <= b) /\ ~(i <= b)` by DECIDE_TAC \\ ASM_SIMP_TAC std_ss []
  \\ SIMP_TAC std_ss [GSYM ref_mem_def,getLENGTH_def]
  \\ `b + 1 <= i /\ (v = i - (b + 1))` by DECIDE_TAC
  \\ RES_TAC \\ ASM_SIMP_TAC (std_ss++star_ss) []);

val ref_mem_IMP_H_EMP = prove(
  ``!m p x. (ref_mem m b e * p) x /\ ok_memory m ==> (ref_mem (\a.H_EMP) b e * p) x``,
  STRIP_TAC \\ completeInduct_on `e - b` \\ REPEAT STRIP_TAC \\ Cases_on `e <= b`
  THEN1 (METIS_TAC [ref_mem_def])
  \\ Q.PAT_X_ASSUM `(ref_mem m b e * p) x` MP_TAC
  \\ CONV_TAC (RATOR_CONV (ONCE_REWRITE_CONV [ref_mem_def]))
  \\ FULL_SIMP_TAC std_ss [GSYM STAR_ASSOC] \\ REPEAT STRIP_TAC
  \\ IMP_RES_TAC ref_aux_IMP \\ POP_ASSUM MP_TAC \\ POP_ASSUM (K ALL_TAC)
  \\ ONCE_REWRITE_TAC [STAR_COMM] \\ SIMP_TAC std_ss [GSYM STAR_ASSOC]
  \\ Q.ABBREV_TAC `y = MAX 1 (getLENGTH (m b))`
  \\ `0 < y` by (Q.UNABBREV_TAC `y` \\ FULL_SIMP_TAC std_ss [MAX_DEF] \\ DECIDE_TAC)
  \\ REPEAT STRIP_TAC \\ IMP_RES_TAC ref_mem_LESS_EQ
  \\ `e - (b + y) < e - b /\ (e - (b + y) = e - (b + y))` by DECIDE_TAC
  \\ RES_TAC \\ POP_ASSUM MP_TAC \\ `b <= b + y` by DECIDE_TAC
  \\ IMP_RES_TAC ref_mem_H_EMP_SPLIT \\ ONCE_ASM_REWRITE_TAC []
  \\ SIMP_TAC (std_ss++star_ss) []);

val arm_heap_ok_def = Define `
  arm_heap_ok (h,xs) (b,i,j,e,b2,e2,m) (r1,r6,df,f,p,l) =
    ok_full_heap (h,xs) (b,i,e,b2,e2,m) /\
    ALIGNED r1 /\ ALIGNED r6 /\ e2 < 2 ** 30 /\ e < 2 ** 30 /\ ok_memory m /\
    (ref_mem m b e * ref_mem m b2 l * one_list_roots r1 xs *
     one_scratch r6 (b,e,b2,e2) * p) (fun2set (f,df))`;

val arm_gc_lemma = store_thm("arm_gc_lemma",
  ``arm_heap_ok (h,xs) (b,i,j11,e,b2,e2,m) (r1,r6,df,f,p,i2) ==>
    (gc(b,e,b2,e2,xs,m) = (b2,i2,e2,b,e,xs2,m2)) ==>
    ?f2. arm_gc_pre (r1,r6,df,f) /\
         (arm_gc (r1,r6,df,f) = (ref_addr i2,r6,df,f2)) /\
         (ref_mem m2 b e * ref_mem m2 b2 i2 * one_list_roots r1 xs2 *
          one_scratch r6 (b2,e2,b,e) * p) (fun2set (f2,df)) /\ ok_memory m2``,
  STRIP_TAC \\ SIMP_TAC std_ss [LET_DEF,gc_def,arm_gc_def,arm_gc_pre_def]
  \\ FULL_SIMP_TAC std_ss [arm_heap_ok_def]
  \\ IMP_RES_TAC ok_full_heap_IMP
  \\ ASM_SIMP_TAC std_ss [ALIGNED_INTRO,ALIGNED]
  \\ Q.PAT_ABBREV_TAC `f5 = (r6 + 0x34w =+ f (r6 + 0x2Cw)) xxx`
  \\ `(ref_mem m b2 i2 * ref_mem m b e * one_list_roots r1 xs *
         (one_scratch r6 (b2,e2,b,e) * p)) (fun2set (f5,df)) /\
      (f (r6 + 0x30w) = ref_addr b2) /\
      (f (r6 + 0x28w) = ref_addr b)` by
   (Q.UNABBREV_TAC `f5` \\ FULL_SIMP_TAC std_ss [one_scratch_def]
    \\ SEP_R_TAC \\ ASM_SIMP_TAC std_ss [] \\ SEP_WRITE_TAC)
  \\ Q.PAT_X_ASSUM `Abbrev (f5 = fghfgh)` (K ALL_TAC)
  \\ `?j m3 xs3. move_list (xs,b2,m) = (xs3,j,m3)` by METIS_TAC [PAIR]
  \\ `?i4 m4. gc_loop (b2,j,m3) = (i4,m4)` by METIS_TAC [PAIR]
  \\ ASM_SIMP_TAC std_ss [] \\ ONCE_REWRITE_TAC [EQ_SYM_EQ] \\ SIMP_TAC std_ss []
  \\ STRIP_TAC \\ EXPAND_TAC
  \\ SEP_S_TAC ["gc_inv"] (RW [UNION_EMPTY]
       (SUBST_INST [``z:num set``|->``{}:num set``] (GEN_ALL arm_move_roots_thm)))
  \\ ASM_SIMP_TAC std_ss [full_heap_REFL]
  \\ FULL_SIMP_TAC std_ss []
  \\ REPEAT STRIP_TAC
  \\ IMP_RES_TAC (RW [UNION_EMPTY] (helperLib.SUBST_INST [``z:num set``|->``{}:num set``] move_list_thm))
  \\ Q.PAT_X_ASSUM `gc_inv (h,roots,h3,f3) ttt` MP_TAC
  \\ REPEAT (Q.PAT_X_ASSUM `gc_inv xxx yyy` (K ALL_TAC)) \\ STRIP_TAC
  \\ IMP_RES_TAC gc_loop_thm
  \\ Q.PAT_X_ASSUM `r3 = ADDR_MAP f3 roots` MP_TAC
  \\ REPEAT (Q.PAT_X_ASSUM `r3 = ADDR_MAP xx roots` (K ALL_TAC)) \\ STRIP_TAC
  \\ `i2 <= e2` by RANGE_TAC \\ FULL_SIMP_TAC std_ss [] \\ CLEAN_TAC
  \\ `f2 (r6 + 0x28w) = ref_addr b2` by (FULL_SIMP_TAC std_ss [one_scratch_def] \\ SEP_READ_TAC)
  \\ FULL_SIMP_TAC std_ss []
  \\ SEP_S_TAC ["arm_loop","gc_inv"] (GEN_ALL arm_loop_thm)
  \\ ASM_SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC \\ ASM_SIMP_TAC std_ss []
  \\ SIMP_TAC std_ss [CONJ_ASSOC] \\ REVERSE STRIP_TAC
  THEN1 (FULL_SIMP_TAC std_ss [ok_memory_def,CUT_EQ] \\ METIS_TAC [])
  \\ STRIP_TAC THEN1 (FULL_SIMP_TAC std_ss [one_scratch_def] \\ SEP_READ_TAC)
  \\ `EQ_RANGE (b2,i2) m4 (CUT (b2,i2) m4)` by METIS_TAC [EQ_RANGE_CUT]
  \\ IMP_RES_TAC (GSYM EQ_RANGE_ref_mem) \\ ASM_SIMP_TAC std_ss []
  \\ NTAC 2 (POP_ASSUM (K ALL_TAC))
  \\ `EQ_RANGE (b,e) (CUT (b2,i2) m4) (\a.H_EMP)` by
    (Q.PAT_X_ASSUM `gc_inv xxx (b2,i2,i2,e2,b,e,m4,{})` MP_TAC
     \\ SIMP_TAC std_ss [gc_inv_def]
     \\ SIMP_TAC std_ss [EQ_RANGE_def,IN_DEF] \\ REPEAT STRIP_TAC
     \\ Cases_on `RANGE (b2,i2) a` \\ ASM_SIMP_TAC std_ss [CUT_def]
     \\ Q.PAT_X_ASSUM `!k. bbb ==> (m4 k = H_EMP)` MATCH_MP_TAC
     \\ IMP_RES_TAC full_heap_LESS_EQ \\ RANGE_TAC)
  \\ IMP_RES_TAC EQ_RANGE_ref_mem \\ ASM_SIMP_TAC std_ss []
  \\ SIMP_TAC std_ss [GSYM STAR_ASSOC] \\ MATCH_MP_TAC ref_mem_IMP_H_EMP
  \\ Q.EXISTS_TAC `m4` \\ FULL_SIMP_TAC (std_ss++star_ss) []);

val _ = export_theory();
