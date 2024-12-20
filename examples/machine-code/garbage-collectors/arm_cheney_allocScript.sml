
open HolKernel boolLib bossLib Parse; val _ = new_theory "arm_cheney_alloc";
val _ = ParseExtras.temp_loose_equality()

open wordsTheory arithmeticTheory wordsLib listTheory pred_setTheory pairTheory;
open combinTheory finite_mapTheory;

open addressTheory mc_tailrecLib tailrecTheory;
open cheney_gcTheory cheney_allocTheory arm_cheney_gcTheory;


val _ = map Parse.hide ["r0","r1","r2","r3","r4","r5","r6","r7","r8","r9","r10","r11","r12","r13"];
val RW = REWRITE_RULE;
val RW1 = ONCE_REWRITE_RULE;

val arm_alloc_gc_lemma = prove(
  ``ok_state (i,e,rs,l,u,m) ==>
    arm_coll_inv (a,x,xs) (i,e,rs,l,u,m) ==>
    (cheney_alloc_gc (i,e,rs,l,u,m) = (i',e',rs',l',u',m')) ==>
    (arm_alloc_gc (ref_addr a i,ref_addr a e,r5,r6,r7,r8,a,x,xs) =
                   (r3',r4',r5',r6',r7',r8',a',x',xs')) ==>
    arm_coll_inv (a,x,xs') (i,e',rs',l',u',m') /\ (a = a') /\ (l = l') /\
    (r3' = ref_addr a i') /\ (r4' = ref_addr a e') /\ (x = x') /\
    arm_alloc_gc_pre (ref_addr a i,ref_addr a e,r5,r6,r7,r8,a,x,xs)``,
  REWRITE_TAC [arm_alloc_gc_def,arm_alloc_gc_pre_def,cheney_alloc_gc_def]
  \\ STRIP_TAC \\ STRIP_TAC
  \\ `valid_address a i /\ valid_address a e /\ i <= e` by (Cases_on `u` \\
    FULL_SIMP_TAC bool_ss [ok_state_def,LET_DEF,arm_coll_inv_def,valid_address_def] \\ DECIDE_TAC)
  \\ `(ref_addr a i = ref_addr a e) = (i = e)` by METIS_TAC [ref_addr_NEQ]
  \\ `(i = e) = ~(i < e)` by DECIDE_TAC
  \\ Cases_on `i < e` \\ ASM_SIMP_TAC bool_ss []
  THEN1 (ONCE_REWRITE_TAC [EQ_SYM_EQ] \\ ASM_SIMP_TAC bool_ss [PAIR_EQ] \\ METIS_TAC [])
  \\ `?r3i r4i r5i r6i r7i r8i r10i xi xsi. arm_collect (r7,r8,a,x,xs) =
                         (r3i,r4i,r5i,r6i,r7i,r8i,r10i,xi,xsi)` by METIS_TAC [PAIR]
  \\ ASM_SIMP_TAC std_ss [LET_DEF] \\ STRIP_TAC
  \\ ONCE_REWRITE_TAC [EQ_SYM_EQ] \\ SIMP_TAC bool_ss [GSYM AND_IMP_INTRO]
  \\ REPEAT (MATCH_MP_TAC (METIS_PROVE [] ``P ==> (Q ==> P)``))
  \\ IMP_RES_TAC arm_collect_lemma
  \\ FULL_SIMP_TAC bool_ss []
  \\ METIS_TAC []);

val LO_IMP_ref_addr = prove(
  ``!b a. b <+ ref_addr a 1 /\ valid_address a i /\ ~(i = 0) ==>
          ~(ref_addr a i = b) /\ ~(ref_addr a i + 4w = b) /\ ~(ref_addr a i + 8w = b)``,
  Cases_word \\ Cases_word
  \\ ASM_SIMP_TAC (std_ss++SIZES_ss) [ref_addr_def,WORD_LO,w2n_n2w,valid_address_def,word_add_n2w,n2w_11]
  \\ REPEAT STRIP_TAC
  \\ `n' + 12 * i + 4 < 4294967296 /\ n' + 12 * i < 4294967296` by DECIDE_TAC
  \\ `n' + 12 < 4294967296` by DECIDE_TAC
  \\ FULL_SIMP_TAC std_ss [LESS_MOD] \\ DECIDE_TAC);

val roots_in_mem_UPDATE = prove(
  ``!p b. valid_address a i /\ ~(i = 0) /\ roots_in_mem p (a,b,xs) ==>
          roots_in_mem p (a,b,(ref_addr a i =+ y) xs)``,
  Induct \\ ASM_SIMP_TAC std_ss [roots_in_mem_def,APPLY_UPDATE_THM]
  \\ REPEAT STRIP_TAC \\ IMP_RES_TAC WORD_LOWER_NOT_EQ \\ IMP_RES_TAC LO_IMP_ref_addr
  \\ ASM_SIMP_TAC bool_ss []);

val roots_in_mem_UPDATE4 = prove(
  ``!p b. valid_address a i /\ ~(i = 0) /\ roots_in_mem p (a,b,xs) ==>
          roots_in_mem p (a,b,(ref_addr a i + 4w  =+ y) xs) /\
          roots_in_mem p (a,b,(ref_addr a i + 8w  =+ y) xs)``,
  Induct \\ ASM_SIMP_TAC std_ss [roots_in_mem_def,APPLY_UPDATE_THM]
  \\ REPEAT STRIP_TAC \\ IMP_RES_TAC WORD_LOWER_NOT_EQ \\ IMP_RES_TAC LO_IMP_ref_addr
  \\ ASM_SIMP_TAC bool_ss []);

val arm_alloc_aux_lemma = prove(
  ``ok_state (i,e,rs,l,u,m) ==>
    arm_coll_inv (a,x,xs) (q,e,rs,l,u,m) ==>
    (cheney_alloc_aux (i,e,rs,l,u,m) 0w = (i',e',rs',l',u',m')) ==>
    (arm_alloc_aux (ref_addr a i,ref_addr a e,a,x,xs) = (r3',r4',r6',r8',r9',r10',x',xs')) ==>
    arm_coll_inv (a,x,xs') (i',e',rs',l',u',m') /\ (l = l') /\ (x = x') /\ (a = r10') /\
    arm_alloc_aux_pre (ref_addr a i,ref_addr a e,a,x,xs)``,
  STRIP_TAC \\ REWRITE_TAC [arm_alloc_aux_def,arm_alloc_aux_pre_def,cheney_alloc_aux_def]
  \\ STRIP_TAC \\ Cases_on `i = e` \\ ASM_SIMP_TAC std_ss [] THEN1
   (SIMP_TAC std_ss [LET_DEF]
    \\ ONCE_REWRITE_TAC [EQ_SYM_EQ]
    \\ SIMP_TAC std_ss [LET_DEF]
    \\ NTAC 2 STRIP_TAC
    \\ IMP_RES_TAC arm_coll_inv_pre_lemma
    \\ FULL_SIMP_TAC std_ss [arm_coll_inv_def,TL,CONS_11,APPEND]
    \\ FULL_SIMP_TAC std_ss [APPEND,GSYM CONJ_ASSOC]
    \\ STRIP_TAC THEN1
     (FULL_SIMP_TAC std_ss [roots_in_mem_def,APPLY_UPDATE_THM,word_arith_lemma1]
      \\ FULL_SIMP_TAC std_ss [word_arith_lemma3,WORD_EQ_SUB_RADD]
      \\ FULL_SIMP_TAC std_ss [roots_in_mem_def,APPLY_UPDATE_THM,word_arith_lemma1]
      \\ FULL_SIMP_TAC (std_ss++SIZES_ss) [WORD_EQ_ADD_CANCEL,n2w_11]
      \\ FULL_SIMP_TAC std_ss [word_arith_lemma3,WORD_EQ_SUB_LADD]
      \\ FULL_SIMP_TAC (std_ss++SIZES_ss) [WORD_EQ_ADD_CANCEL,n2w_11,ref_addr_def])
    \\ `a <+ ref_addr a 1 /\ a - 24w <+ ref_addr a 1` by (FULL_SIMP_TAC std_ss [roots_in_mem_def,APPEND,word_arith_lemma1,word_arith_lemma2,ZIP]
      \\ FULL_SIMP_TAC std_ss [word_arith_lemma3,word_arith_lemma4,WORD_ADD_0])
    \\ STRIP_TAC THEN1 METIS_TAC [lemma]
    \\ FULL_SIMP_TAC std_ss [roots_in_mem_def,APPLY_UPDATE_THM,word_arith_lemma1]
    \\ FULL_SIMP_TAC std_ss [word_arith_lemma3,WORD_EQ_SUB_RADD]
    \\ FULL_SIMP_TAC std_ss [roots_in_mem_def,APPLY_UPDATE_THM,word_arith_lemma1]
    \\ FULL_SIMP_TAC (std_ss++SIZES_ss) [WORD_EQ_ADD_CANCEL,n2w_11]
    \\ FULL_SIMP_TAC std_ss [word_arith_lemma3,WORD_EQ_SUB_LADD]
    \\ FULL_SIMP_TAC (std_ss++SIZES_ss) [WORD_EQ_ADD_CANCEL,n2w_11,ref_addr_def]
    \\ FULL_SIMP_TAC std_ss [ALIGNED_INTRO]
    \\ ONCE_REWRITE_TAC [ALIGNED_MOD_4]
    \\ SIMP_TAC std_ss [WORD_ADD_0,WORD_SUB_RZERO]
    \\ FULL_SIMP_TAC std_ss [INSERT_SUBSET,IN_INSERT] \\ METIS_TAC [])
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
  \\ Q.ABBREV_TAC `xs1 = ((ref_addr a i + 4w + 4w =+ 0w)
                         ((ref_addr a i + 4w =+ xs (a - 20w))
                         ((ref_addr a i =+ xs (a - 24w)) xs2)))`
  \\ `ref_addr a i + 12w = ref_addr a (i+1)` by
      FULL_SIMP_TAC std_ss [ref_addr_def,MULT_CLAUSES,GSYM ADD1,
        GSYM WORD_ADD_ASSOC,word_add_n2w,AC ADD_ASSOC ADD_COMM]
  \\ ASM_SIMP_TAC std_ss []
  \\ `a <+ ref_addr a 1 /\ a - 24w <+ ref_addr a 1` by (FULL_SIMP_TAC std_ss [roots_in_mem_def,APPEND,word_arith_lemma1,word_arith_lemma2,ZIP]
    \\ FULL_SIMP_TAC std_ss [word_arith_lemma3,word_arith_lemma4,WORD_ADD_0])
  \\ `ref_cheney (m,l+l+1) (a,x,xs2,xs2)` by METIS_TAC [lemma]
  \\ `ref_cheney ((i =+ DATA (x1,x2,0w)) m,l+l+1) (a,x,xs1,xs1)` by
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
          \\ SIMP_TAC std_ss [word_arith_lemma1]
          \\ ASM_SIMP_TAC bool_ss [ref_addr_ADD_NEQ,ref_addr_NEQ,UPDATE_def,ref_mem_def,WORD_EQ_ADD_RCANCEL]
          \\ METIS_TAC [ref_mem_def]])
  \\ `ref_cheney ((i =+ DATA (x1,x2,0w)) m,l+l+1)
      (a,x,(a =+ ref_addr a (i + 1)) xs1,(a =+ ref_addr a (i + 1)) xs1)` by METIS_TAC [lemma]
  \\ ASM_SIMP_TAC std_ss []
  \\ Q.ABBREV_TAC `xxx = [i; x2; x3; x4; x5; x6; q; e]`
  \\ `roots_in_mem xxx (a,a - 24w,xs2)` by
     (Q.UNABBREV_TAC `xxx` \\ Q.UNABBREV_TAC `xs2`
      \\ FULL_SIMP_TAC std_ss [roots_in_mem_def,APPLY_UPDATE_THM,word_arith_lemma1,word_arith_lemma2,APPEND,ZIP]
      \\ FULL_SIMP_TAC std_ss [word_arith_lemma3,word_arith_lemma4,WORD_ADD_0]
      \\ SIMP_TAC (std_ss++WORD_ss) [RW [WORD_ADD_0] (Q.SPECL [`v`,`0w`] WORD_EQ_ADD_LCANCEL),n2w_11]
      \\ SIMP_TAC (std_ss++WORD_ss) [RW [WORD_ADD_0] (Q.SPECL [`v`,`x`,`0w`] WORD_EQ_ADD_LCANCEL),
           RW [WORD_ADD_0] (Q.SPECL [`v`,`0w`] WORD_EQ_ADD_LCANCEL),n2w_11,WORD_EQ_ADD_LCANCEL])
  \\ ONCE_REWRITE_TAC [EQ_SYM_EQ]
  \\ REWRITE_TAC [GSYM ALIGNED_def,ALIGNED_CLAUSES]
  \\ FULL_SIMP_TAC std_ss [word_arith_lemma1]
  \\ `roots_in_mem xxx (a,a - 24w,xs1)` by METIS_TAC [roots_in_mem_UPDATE,roots_in_mem_UPDATE4]
  \\ REVERSE STRIP_TAC THEN1
   (`i <= l+l+1` by (Cases_on `u` \\ FULL_SIMP_TAC bool_ss [ok_state_def,LET_DEF] \\ DECIDE_TAC)
    \\ IMP_RES_TAC ref_cheney_d
    \\ ONCE_REWRITE_TAC [EQ_SYM_EQ]
    \\ FULL_SIMP_TAC std_ss [ref_cheney_def,GSYM ALIGNED_def,INSERT_SUBSET,LENGTH,ALIGNED_ref_addr]
    \\ REPEAT STRIP_TAC \\ REWRITE_TAC [word_sub_def]
    \\ REPEAT (MATCH_MP_TAC ALIGNED_ADD) \\ ASM_SIMP_TAC bool_ss [] \\ EVAL_TAC)
  \\ STRIP_TAC THEN1
     (Q.UNABBREV_TAC `xxx`
      \\ FULL_SIMP_TAC std_ss [roots_in_mem_def,APPLY_UPDATE_THM,word_arith_lemma1,word_arith_lemma2,APPEND,ZIP]
      \\ FULL_SIMP_TAC std_ss [word_arith_lemma3,word_arith_lemma4,WORD_ADD_0]
      \\ SIMP_TAC (std_ss++WORD_ss) [RW [WORD_ADD_0] (Q.SPECL [`v`,`0w`] WORD_EQ_ADD_LCANCEL),n2w_11]
      \\ SIMP_TAC (std_ss++WORD_ss) [RW [WORD_ADD_0] (Q.SPECL [`v`,`x`,`0w`] WORD_EQ_ADD_LCANCEL),
           RW [WORD_ADD_0] (Q.SPECL [`v`,`0w`] WORD_EQ_ADD_LCANCEL),n2w_11,WORD_EQ_ADD_LCANCEL])
  \\ ASM_SIMP_TAC std_ss [word_arith_lemma1]
  \\ Q.UNABBREV_TAC `xs1` \\ Q.UNABBREV_TAC `xs2`
  \\ IMP_RES_TAC LO_IMP_ref_addr
  \\ SIMP_TAC bool_ss [UPDATE_def]
  \\ ASM_SIMP_TAC std_ss [word_arith_lemma1]
  \\ SIMP_TAC (std_ss++WORD_ss) [RW [WORD_ADD_0] (Q.SPECL [`v`,`0w`] WORD_EQ_ADD_LCANCEL),n2w_11]
  \\ SIMP_TAC (std_ss++WORD_ss) [RW [WORD_ADD_0] (Q.SPECL [`v`,`x`,`0w`] WORD_EQ_ADD_LCANCEL),
         RW [WORD_ADD_0] (Q.SPECL [`v`,`0w`] WORD_EQ_ADD_LCANCEL),n2w_11,WORD_EQ_ADD_LCANCEL]);

val arm_alloc_lemma = prove(
  ``ok_state (i,e,rs,l,u,m) ==>
    arm_coll_inv (a,x,xs) (i,e,rs,l,u,m) ==>
    (cheney_alloc (i,e,rs,l,u,m) 0w = (i',e',rs',l',u',m')) ==>
    (arm_alloc_mem (r5,r6,r7,r8,a,x,xs) = (r3',r4',r5',r6',r7',r8',a',x',xs')) ==>
    arm_coll_inv (a',x,xs') (i',e',rs',l',u',m') /\ (a' = a) /\ (l' = l) /\ (x = x') /\
    arm_alloc_mem_pre (r5,r6,r7,r8,a,x,xs)``,
  REWRITE_TAC [cheney_alloc_def,arm_alloc_mem_def,arm_alloc_mem_pre_def] \\ STRIP_TAC \\ STRIP_TAC
  \\ `~(i = 0) /\ ~(e = 0)` by
         (Cases_on `u` \\ FULL_SIMP_TAC bool_ss [ok_state_def,LET_DEF] \\ DECIDE_TAC)
  \\ `(xs a = ref_addr a i) /\ (xs (a+4w) = ref_addr a e)` by
   (FULL_SIMP_TAC std_ss [arm_coll_inv_def,APPEND,roots_in_mem_def,ZIP]
    \\ FULL_SIMP_TAC std_ss [arm_coll_inv_def,APPEND,roots_in_mem_def,ZIP]
    \\ FULL_SIMP_TAC std_ss [roots_in_mem_def,APPLY_UPDATE_THM,word_arith_lemma1,word_arith_lemma2,APPEND]
    \\ FULL_SIMP_TAC std_ss [word_arith_lemma3,word_arith_lemma4,WORD_ADD_0]
    \\ SIMP_TAC (std_ss++WORD_ss) [RW [WORD_ADD_0] (Q.SPECL [`v`,`0w`] WORD_EQ_ADD_LCANCEL),n2w_11])
  \\ `?r3i r4i r5i r6i r7i r8i r10i xi xsi.
        arm_alloc_gc (ref_addr a i,ref_addr a e,r5,r6,r7,r8,a,x,xs) =
                      (r3i,r4i,r5i,r6i,r7i,r8i,r10i,xi,xsi)` by METIS_TAC [PAIR]
  \\ `?r3j r4j r6j r7j r8j r10j xj xsj.
        arm_alloc_aux (r3i,r4i,r10i,xi,xsi) = (r3j,r4j,r6j,r7j,r8j,r10j,xj,xsj)` by METIS_TAC [PAIR]
  \\ `?i2 e2 rs2 l2 u2 m2. cheney_alloc_gc (i,e,rs,l,u,m) = (i2,e2,rs2,l2,u2,m2)` by METIS_TAC [PAIR]
  \\ ASM_SIMP_TAC std_ss [LET_DEF] \\ STRIP_TAC
  \\ ONCE_REWRITE_TAC [EQ_SYM_EQ] \\ ASM_SIMP_TAC std_ss [GSYM CONJ_ASSOC]
  \\ ONCE_REWRITE_TAC [EQ_SYM_EQ] \\ ASM_SIMP_TAC std_ss [GSYM ALIGNED_def]
  \\ IMP_RES_TAC arm_alloc_gc_lemma
  \\ `ok_state (i2,e2,rs2,l2,u2,m2)` by METIS_TAC [cheney_collector_spec,cheney_alloc_gc_def]
  \\ IMP_RES_TAC arm_coll_inv_pre_lemma
  \\ ONCE_REWRITE_TAC [EQ_SYM_EQ] \\ ASM_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC std_ss [INSERT_SUBSET,NOT_IN_EMPTY,IN_INSERT,EMPTY_SUBSET]
  \\ ONCE_REWRITE_TAC [EQ_SYM_EQ] \\ STRIP_TAC \\ FULL_SIMP_TAC bool_ss []
  \\ REPEAT (Q.PAT_X_ASSUM `~(i = 0)` ((K ALL_TAC)))
  \\ IMP_RES_TAC arm_alloc_aux_lemma \\ ASM_SIMP_TAC std_ss []
  \\ REVERSE (REPEAT STRIP_TAC) \\ METIS_TAC []);

val field_list_def = Define `
  (field_list [] (a,r12,m) = T) /\
  (field_list (x::xs) (a,r12,m) = (m r12 = ref_addr a x) /\ field_list xs (a,r12 + 4w,m))`;

val roots_in_mem_IMP_addr_list = prove(
  ``!p a b xs. roots_in_mem p (a,b,xs) ==> field_list p (a,b,xs)``,
  Induct \\ ASM_SIMP_TAC std_ss [field_list_def,roots_in_mem_def]);

val ch_mem_def = Define `
  ch_mem (i,e,rs,l,u,m) (a,x,xs) =
    ?x1 x2 x3 x4 x5 x6:num.
      32 <= w2n a /\ w2n a + 2 * 12 * l + 20 < 2**32 /\
      ok_state(i,e,rs,l,u,m) /\
      field_list (rs ++ [i;e]) (a,a-24w,xs) /\
      (rs = [x1;x2;x3;x4;x5;x6]) /\
      ref_cheney (m,l+l+1) (a,x,xs,xs) /\
      (xs (a-28w) = if u then 0w else 1w) /\
      (xs (a-32w) = n2w (12 * l))`;

val ch_word_def = Define `
  ch_word (i,e,rs,l,u,m) (v1,v2,v3,v4,v5,v6,a,x,xs) =
    ?x1 x2 x3 x4 x5 x6:num.
      (rs = [x1;x2;x3;x4;x5;x6]) /\
      ok_state(i,e,rs,l,u,m) /\ ref_cheney (m,l+l+1) (a,x,xs,xs) /\
      32 <= w2n a /\ w2n a + 2 * 12 * l + 20 < 2**32 /\
      (v1 = ref_addr a x1) /\ (v2 = ref_addr a x2) /\ (v3 = ref_addr a x3) /\
      (v4 = ref_addr a x4) /\ (v5 = ref_addr a x5) /\ (v6 = ref_addr a x6) /\
      (xs a = ref_addr a i) /\ (xs (a+4w) = ref_addr a e) /\
      (xs (a-28w) = if u then 0w else 1w) /\ (xs (a-32w) = n2w (12 * l))`;

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
  ``ch_mem (i,e,rs,l,u,m) (a,x,xs) ==>
    (cheney_alloc (i,e,rs,l,u,m) 0w = (i',e',rs',l',u',m')) ==>
    (arm_alloc_mem (r5,r6,r7,r8,a,x,xs) = (r3',r4',r5',r6',r7',r8',a',x',xs')) ==>
    ch_mem (i',e',rs',l',u',m') (a',x,xs') /\ (a = a') /\ (l = l') /\ (x = x') /\
    arm_alloc_mem_pre (r5,r6,r7,r8,a,x,xs) /\ arm_coll_inv (a,x,xs) (i,e,rs,l,u,m)``,
  NTAC 4 STRIP_TAC \\ IMP_RES_TAC ch_mem_IMP_arm_coll_inv
  \\ IMP_RES_TAC arm_alloc_lemma
  \\ FULL_SIMP_TAC bool_ss [ch_mem_def,APPEND,ZIP]
  \\ `ok_state (i',e',rs',l',u',m')` by METIS_TAC [cheney_alloc_ok]
  \\ FULL_SIMP_TAC std_ss [arm_coll_inv_def,CONS_11,ZIP,APPEND]
  \\ Q.PAT_X_ASSUM `rs' = xxxxx` (fn th => FULL_SIMP_TAC std_ss [th])
  \\ FULL_SIMP_TAC bool_ss [APPEND,roots_in_mem_def,field_list_def,ZIP,CONS_11]
  \\ Q.PAT_X_ASSUM `ok_state (i',e',[x1''; x2''; x3''; x4''; x5''; x6''],l',u',m')` MP_TAC
  \\ ASM_SIMP_TAC std_ss []);

val ch_word_alloc = prove(
  ``ch_word (i,e,rs,l,u,m) (v1,v2,v3,v4,v5,v6,a,x,xs) ==>
    (cheney_alloc (i,e,rs,l,u,m) 0w = (i',e',rs',l',u',m')) ==>
    (arm_alloc (v1,v2,v3,v4,v5,v6,a,x,xs) = (w1,w2,w3,w4,w5,w6,a',x',xs')) ==>
    ch_word (i',e',rs',l',u',m') (w1,w2,w3,w4,w5,w6,a',x',xs') /\ (a = a') /\ (l = l') /\ (x = x') /\
    arm_alloc_pre (v1,v2,v3,v4,v5,v6,a,x,xs)``,
  SIMP_TAC std_ss [arm_alloc_def,arm_alloc_pre_def,LET_DEF]
  \\ Q.ABBREV_TAC `xs1 = (a - 4w =+ v6)
      ((a - 8w =+ v5) ((a - 12w =+ v4) ((a - 16w =+ v3)
      ((a - 20w =+ v2) ((a - 24w =+ v1) (xs))))))`
  \\ `?r3i r4i r5i r6i r7i r8i r10i xi xsi.
        arm_alloc_mem (v3,v4,v5,v6,a,x,xs1) = (r3i,r4i,r5i,r6i,r7i,r8i,r10i,xi,xsi)` by METIS_TAC [PAIR]
  \\ ASM_SIMP_TAC std_ss [LET_DEF] \\ STRIP_TAC \\ STRIP_TAC
  \\ REWRITE_TAC [GSYM ALIGNED_def]
  \\ ONCE_REWRITE_TAC [EQ_SYM_EQ] \\ ASM_SIMP_TAC std_ss []
  \\ MATCH_MP_TAC (METIS_PROVE [] ``Q ==> (P ==> Q)``)
  \\ sg `ch_mem (i,e,rs,l,u,m) (a,x,xs1)` THENL [
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
          (Cases_on `u` \\ FULL_SIMP_TAC bool_ss [ok_state_def,LET_DEF] \\ DECIDE_TAC),
    IMP_RES_TAC ch_mem_cheney_alloc_lemma
    \\ Q.PAT_X_ASSUM `ch_mem (i,e,rs,l,u,m) (a,x,xs1)` (K ALL_TAC)
    \\ FULL_SIMP_TAC bool_ss [APPEND,ZIP,ch_word_def,ch_mem_def,field_list_def,CONS_11]
    \\ FULL_SIMP_TAC bool_ss [APPEND,ZIP,ch_word_def,ch_mem_def,field_list_def,CONS_11]
    \\ FULL_SIMP_TAC std_ss [field_list_def,ZIP,APPEND,word_arith_lemma1,word_arith_lemma2]
    \\ FULL_SIMP_TAC std_ss [field_list_def,ZIP,APPEND,word_arith_lemma3,word_arith_lemma4]
    \\ IMP_RES_TAC arm_coll_inv_pre_lemma
    \\ FULL_SIMP_TAC std_ss [WORD_ADD_0,LENGTH,IN_INSERT,NOT_IN_EMPTY,INSERT_SUBSET,ALIGNED_def]
    \\ `~(i' = 0) /\ ~(e' = 0)` by
          (Cases_on `u'` \\ FULL_SIMP_TAC bool_ss [ok_state_def,LET_DEF] \\ DECIDE_TAC)
    \\ METIS_TAC []]);

val ch_word_cheney_alloc = store_thm("ch_word_cheney_alloc",
  ``!s t. ch_word s t ==> ch_word (cheney_alloc s 0w) (arm_alloc t) /\ arm_alloc_pre t``,
  Cases \\ REPEAT (Cases_on `r` \\ REPEAT (Cases_on `r'`))
  \\ Cases \\ REPEAT (Cases_on `r'` \\ REPEAT (Cases_on `r''`))
  \\ `?a1 a2 a3 a4 a5 a6. cheney_alloc (q,q',q'',q''',q'''',r) 0w = (a1,a2,a3,a4,a5,a6)` by METIS_TAC [PAIR]
  \\ `?r3 r4 r5 r6 r7 r8 r9 df f. arm_alloc (q''''',q'''''',q''''''',q'''''''',q''''''''',q'''''''''',
          q''''''''''',q'''''''''''',r'') =
          (r3,r4,r5,r6,r7,r8,r9,df,f)` by METIS_TAC [PAIR]
  \\ ASM_REWRITE_TAC [] \\ METIS_TAC [ch_word_alloc]);

val ch_rel_def = Define `
  ch_rel s t = ?u. ch_inv s u /\ ch_word u t`;

val ch_arm_alloc = store_thm("ch_arm_alloc",
  ``(arm_alloc (v1,v2,v3,v4,v5,v6,a,x,xs) = (w1,w2,w3,w4,w5,w6,a',x',xs')) ==>
    CARD (reachables (t1::t2::ts) (ch_set h)) < l ==>
    ch_rel (t1::t2::ts,h,l) (v1,v2,v3,v4,v5,v6,a,x,xs) ==>
    ch_rel (fresh h::t2::ts,h |+ (fresh h,t1,t2,0w),l) (w1,w2,w3,w4,w5,w6,a',x,xs') /\
    (a' = a) /\ (x' = x) /\ arm_alloc_pre (v1,v2,v3,v4,v5,v6,a,x,xs)``,
  REWRITE_TAC [ch_rel_def] \\ STRIP_TAC \\ STRIP_TAC \\ STRIP_TAC
  \\ `?i e rs l u' m. u = (i,e,rs,l,u',m)` by METIS_TAC [PAIR]
  \\ `?i' e' rs' l'' u'' m'. cheney_alloc (i,e,rs,l,u',m) 0w = (i',e',rs',l'',u'',m')` by METIS_TAC [PAIR]
  \\ `l' = l` by METIS_TAC [ch_inv_def] \\ FULL_SIMP_TAC bool_ss []
  \\ FULL_SIMP_TAC bool_ss []
  \\ IMP_RES_TAC ch_word_alloc
  \\ RES_TAC \\ ASM_SIMP_TAC bool_ss []
  \\ Q.EXISTS_TAC `(i',e',rs',l'',u'',m')`
  \\ ASM_SIMP_TAC bool_ss [cheney_alloc_spec,FST]
  \\ MATCH_MP_TAC (GEN_ALL (RW [AND_IMP_INTRO] cheney_alloc_spec))
  \\ FULL_SIMP_TAC bool_ss [] \\ METIS_TAC []);

val aHEAP_def = Define `
  aHEAP (a,l) (v1,v2,v3,v4,v5,v6,h) =
    SEP_EXISTS r3 r4 r5 r6 r7 r8 x xs.
      aR 3w r3 * aR 4w r4 * aR 5w r5 * aR 6w r6 * aR 7w r7 * aR 8w r8 * aR 9w a * aMEMORY x xs *
      cond (ch_rel ([v1;v2;v3;v4;v5;v6],h,l) (r3,r4,r5,r6,r7,r8,a,x,xs))`;

open progTheory set_sepTheory helperLib;

val SPEC_ARM_ALLOC = save_thm("SPEC_ARM_ALLOC",let
  val th = arm_alloc_thm
  val th = SIMP_RULE std_ss [LET_DEF] th
  val th = MATCH_MP SPEC_FRAME th
  val th = Q.SPEC `cond (ch_rel ([v1;v2;v3;v4;v5;v6],h,l) (r3,r4,r5,r6,r7,r8,r9,df,f) /\
                           CARD (reachables [v1;v2;v3;v4;v5;v6] (ch_set h)) < l)` th
  val th = MATCH_MP SPEC_WEAKEN th
  val th = Q.SPEC `aHEAP (r9,l) (fresh h,v2,v3,v4,v5,v6,h |+ (fresh h,v1,v2,0w)) * ~aS * aPC (p + 356w)` th
  val goal = (fst o dest_imp o concl) th
  val lemma = prove(goal,
    REWRITE_TAC [SEP_IMP_MOVE_COND] \\ REPEAT STRIP_TAC
    \\ `?w1 w2 w3 w4 w5 w6 a' x' xs'.
          arm_alloc (r3,r4,r5,r6,r7,r8,r9,df,f) =
          (w1,w2,w3,w4,w5,w6,a',x',xs')` by METIS_TAC [PAIR]
    \\ ASM_SIMP_TAC std_ss [aHEAP_def,SEP_CLAUSES]
    \\ IMP_RES_TAC ch_arm_alloc
    \\ SIMP_TAC (std_ss++sep_cond_ss) [SEP_IMP_def,SEP_EXISTS,cond_STAR]
    \\ REPEAT STRIP_TAC  \\ Q.EXISTS_TAC `w1`
    \\ Q.EXISTS_TAC `w2` \\ Q.EXISTS_TAC `w3`
    \\ Q.EXISTS_TAC `w4` \\ Q.EXISTS_TAC `w5`
    \\ Q.EXISTS_TAC `w6` \\ Q.EXISTS_TAC `x'`  \\ Q.EXISTS_TAC `xs'`
    \\ FULL_SIMP_TAC (bool_ss++star_ss) [] \\ REPEAT (POP_ASSUM MP_TAC)
    \\ ONCE_REWRITE_TAC [EQ_SYM_EQ] \\ SIMP_TAC (bool_ss++star_ss) [] \\ METIS_TAC [])
  val th = MP th lemma
  val th = EXISTS_PRE `f` th
  val th = EXISTS_PRE `df` th
  val th = EXISTS_PRE `r8` th
  val th = EXISTS_PRE `r7` th
  val th = EXISTS_PRE `r6` th
  val th = EXISTS_PRE `r5` th
  val th = EXISTS_PRE `r4` th
  val th = EXISTS_PRE `r3` th
  val th = MATCH_MP SPEC_STRENGTHEN th
  val th = Q.SPEC `aHEAP (r9,l) (v1,v2,v3,v4,v5,v6,h) * ~aS * aPC p *
      cond (CARD (reachables [v1;v2;v3;v4;v5;v6] (ch_set h)) < l)` th
  val goal = (fst o dest_imp o concl) th
  val lemma = prove(goal,
    REWRITE_TAC [SEP_IMP_MOVE_COND] \\ REPEAT STRIP_TAC
    \\ ASM_SIMP_TAC (bool_ss++sep_cond_ss) [FST,SND,aHEAP_def,SEP_CLAUSES]
    \\ SIMP_TAC std_ss [SEP_IMP_def,SEP_EXISTS,cond_STAR] \\ REPEAT STRIP_TAC
    \\ `?w1 w2 w3 w4 w5 w6 a' x' xs'.
          arm_alloc (y,y',y'',y''',y'''',y''''',r9,y'''''',y''''''') =
          (w1,w2,w3,w4,w5,w6,a',x',xs')` by METIS_TAC [PAIR]
    \\ IMP_RES_TAC ch_arm_alloc
    \\ FULL_SIMP_TAC (bool_ss++star_ss) [] \\ METIS_TAC [])
  val th = MP th lemma
  in th end);


val _ = export_theory();
