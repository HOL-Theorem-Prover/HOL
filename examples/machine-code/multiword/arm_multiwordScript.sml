
open HolKernel Parse boolLib bossLib; val _ = new_theory "arm_multiword";

infix \\ val op \\ = op THEN;
open multiwordTheory;

open decompilerLib codegenLib prog_armLib compilerLib;
open wordsTheory wordsLib addressTheory arithmeticTheory listTheory pairSyntax;
open addressTheory pairTheory set_sepTheory rich_listTheory integerTheory;

val REV = Tactical.REVERSE;


(* general setup *)

val small_int_def = Define `small_int i = 0 <= i /\ (i:int) < 2**30`;

val int_op_def = Define `
  int_op p i j = if p = 0w then (if i = j then 0 else if i < j then 2 else 1) else
                 if p = 1w then i + j else
                 if p = 2w then i - j else
                 if p = 3w then i * j else
                 if p = 4w then i quot j else i rem j`;

val mwi_header_def = Define `
  mwi_header (neg,xs:word32 list) =
    n2w ((LENGTH xs) * 1024 + (if neg then 4 else 0) + 2) :word32`;

val mwi_size_def = Define `
  mwi_size i = LENGTH (SND (i2mw i) :word32 list)`;

val mwi_real_size_def = Define `
  mwi_real_size i = if small_int i then 0 else SUC (mwi_size i)`;

val one_rev_list_def = Define `
  (one_rev_list a [] = emp) /\
  (one_rev_list a (x::xs) = one_rev_list (a-4w) xs * one (a,x))`;

val one_list_rev_def = Define `
  one_list_rev a xs = one_rev_list (a + n2w (4 * LENGTH xs) - 4w) xs`;

val one_list_rev_old_def = Define `
  one_list_rev_old a xs = one_rev_list (a + n2w (4 * LENGTH xs)) xs`;

val one_list_rev_old_EQ = prove(
  ``!a xs. one_list_rev_old a xs = one_list_rev (a + 4w) xs``,
  SIMP_TAC (std_ss++WORD_ARITH_ss) [one_list_rev_old_def,one_list_rev_def]);

val one_list_def = Define `
  (one_list a [] = emp) /\
  (one_list a (x::xs) = one (a,x) * one_list (a+4w) xs)`;

val one_list_ex_def = Define `
  (one_list_ex a 0 = emp) /\
  (one_list_ex a (SUC n) = SEP_EXISTS x. one (a,x) * one_list_ex (a+4w) n)`;

val mwi_header_lsl = prove(
  ``!x xs. mwi_header (x,xs) = n2w (LENGTH xs) << 10 !! if x then 6w else 2w``,
  SIMP_TAC std_ss [mwi_header_def,GSYM ADD_ASSOC] \\ ONCE_REWRITE_TAC [GSYM word_add_n2w]
  \\ REPEAT STRIP_TAC
  \\ `n2w (LENGTH xs * 1024) = (n2w (LENGTH xs) << 10):word32` by
        SIMP_TAC (std_ss++SIZES_ss) [word_lsl_n2w]
  \\ Cases_on `x` \\ ASM_SIMP_TAC std_ss []
  \\ MATCH_MP_TAC WORD_ADD_OR \\ WORD_DECIDE_TAC);

val mwi_header_XOR_4 = prove(
  ``!x xs. mwi_header (x,xs) ?? 4w = mwi_header (~x,xs)``,
  Cases \\ SIMP_TAC std_ss [mwi_header_lsl] \\ WORD_DECIDE_TAC);

val one_list_ex_thm = prove(
  ``one_list_ex a n = if n = 0 then emp else
                        SEP_EXISTS x. one (a,x) * one_list_ex (a+4w) (n-1)``,
  Cases_on `n` \\ SIMP_TAC std_ss [one_list_ex_def,DECIDE ``~(SUC n = 0)``]);

val one_list_ex_ADD = prove(
  ``!m n a. one_list_ex a (m + n) =
            one_list_ex a m * one_list_ex (a + n2w (4 * m)) n``,
  Induct \\ ASM_SIMP_TAC std_ss [one_list_ex_def,SEP_CLAUSES,WORD_ADD_0,ADD,
      MULT_CLAUSES,word_arith_lemma1,STAR_ASSOC]);

val one_mwi_basic_def = Define `
  one_mwi_basic a i =
    let (x,xs) = i2mw i in
      one_list a (mwi_header(x,xs) :: REVERSE xs) * cond (ALIGNED a /\ LENGTH xs < 2**22)`;

val one_mwi_def = Define `
  one_mwi a i = if small_int i then cond (a = n2w ((Num i) * 4 + 1)) else one_mwi_basic a i`;

val one_rev_list_APPEND = prove(
  ``!xs ys a. one_rev_list a (xs++ys) =
              one_rev_list a xs * one_rev_list (a - 4w * n2w (LENGTH xs)) ys``,
  Induct THEN1 SRW_TAC [] [APPEND,one_rev_list_def,SEP_CLAUSES,LENGTH]
  \\ FULL_SIMP_TAC (std_ss++star_ss) [LENGTH,word_mul_n2w,one_rev_list_def,APPEND,
       GSYM WORD_SUB_PLUS,word_add_n2w,MULT_CLAUSES]);

val one_list_rev_SNOC = prove(
  ``!a x xs. one_list_rev a (SNOC x xs) = one (a,x) * one_list_rev (a + 4w) xs``,
  SIMP_TAC std_ss [SNOC_APPEND,one_list_rev_def,one_rev_list_APPEND]
  \\ SIMP_TAC std_ss [GSYM SNOC_APPEND,LENGTH_SNOC,word_add_n2w,GSYM WORD_ADD_ASSOC]
  \\ SIMP_TAC std_ss [MULT_CLAUSES,one_rev_list_def,SEP_CLAUSES]
  \\ SIMP_TAC std_ss [GSYM word_add_n2w,word_mul_n2w,WORD_ADD_SUB,
        GSYM WORD_SUB_PLUS,GSYM WORD_ADD_ASSOC] \\ SIMP_TAC (std_ss++star_ss) []);

val one_list_rev_EQ = prove(
  ``!xs a. one_list a xs = one_list_rev a (REVERSE xs)``,
  Induct THEN1 SIMP_TAC std_ss [one_list_def,REVERSE,one_list_rev_def,one_rev_list_def]
  \\ ASM_SIMP_TAC std_ss [one_list_def,REVERSE,one_list_rev_SNOC]);

val WORD_EQ_SUB_CANCEL = prove(
  ``(w - v = w) = (v = 0w)``,
  SIMP_TAC std_ss [word_sub_def,WORD_EQ_ADD_CANCEL,WORD_NEG_EQ_0]);

val WORD_4_MULT_EQ_0 = prove(
  ``!n. n < 1073741824 ==> ((n2w (4 * n) = 0w:word32) = (n = 0))``,
  SIMP_TAC (std_ss++SIZES_ss) [n2w_11] \\ SIMP_TAC bool_ss [GSYM (EVAL ``4 * 1073741824``)]
  \\ SIMP_TAC std_ss [MATCH_MP (GSYM MOD_COMMON_FACTOR) (DECIDE ``0 < 4 /\ 0 < 1073741824``)]);

val ALIGNED_ADD_MULT4 = prove(
  ``!a. ALIGNED (a + n2w (4 * n)) = ALIGNED a``,
  Cases \\ SIMP_TAC std_ss [ALIGNED_n2w,word_add_n2w]
  \\ METIS_TAC [MATCH_MP MOD_TIMES (DECIDE ``0<4``),ADD_COMM,MULT_COMM]);

val ALIGNED_SUB_MULT4 = prove(
  ``!a. (ALIGNED (a - n2w (4 * n)) = ALIGNED a) /\
        (ALIGNED (n2w (4 * n) - a) = ALIGNED a)``,
  ONCE_REWRITE_TAC [ALIGNED_MOD_4]
  \\ SIMP_TAC std_ss [RW1[MULT_COMM]MOD_EQ_0,WORD_SUB_RZERO]
  \\ SIMP_TAC std_ss [word_sub_def]
  \\ ONCE_REWRITE_TAC [WORD_ADD_COMM] \\ ONCE_REWRITE_TAC [ALIGNED_MOD_4]
  \\ SIMP_TAC std_ss [RW1[MULT_COMM]MOD_EQ_0,WORD_ADD_0,ALIGNED_NEG]);

val ALIGNED_MULT4 = prove(
  ``!a. (ALIGNED (a + n2w (4 * n)) = ALIGNED a) /\
        (ALIGNED (a + n2w (n * 4)) = ALIGNED a) /\
        (ALIGNED (a - n2w (4 * n)) = ALIGNED a) /\
        (ALIGNED (a - n2w (n * 4)) = ALIGNED a) /\
        (ALIGNED (n2w (4 * n) + a) = ALIGNED a) /\
        (ALIGNED (n2w (n * 4) + a) = ALIGNED a) /\
        (ALIGNED (n2w (4 * n) - a) = ALIGNED a) /\
        (ALIGNED (n2w (n * 4) - a) = ALIGNED a)``,
  METIS_TAC [ALIGNED_SUB_MULT4,ALIGNED_ADD_MULT4,MULT_COMM,WORD_ADD_COMM]);

fun SEP_TAC rw =
  SEP_R_TAC \\ FULL_SIMP_TAC (std_ss++star_ss) []
  \\ FULL_SIMP_TAC (std_ss++sep_cond_ss) (rw @
       [STAR_ASSOC,ALIGNED_INTRO,ALIGNED,SEP_CLAUSES,cond_STAR,ALIGNED_MULT4])
  \\ FULL_SIMP_TAC (std_ss++star_ss) [] \\ FULL_SIMP_TAC std_ss [STAR_ASSOC]


(* mw_cmp *)

val (th1,arm_cmp_def,arm_cmp_pre) = compile "arm" ``
  arm_cmp (r1:word32,r2:word32,r3:word32,df:word32 set,f:word32->word32) =
    let r4 = f r1 in
    let r5 = f r2 in
    let r1 = r1 + 4w in
    let r2 = r2 + 4w in
    let r3 = r3 - 1w in
      if r3 = 0w then (r4,r5,df,f) else
      if ~(r4 = r5) then (r4,r5,df,f) else
        arm_cmp (r1,r2,r3,df,f)``

val arm_cmp_thm = prove(
  ``!xs ys r1 r2 df f p.
      (LENGTH ys = LENGTH xs) /\ ~(xs = []) /\ (LENGTH xs < 2**32) /\
      ALIGNED r1 /\ ALIGNED r2 /\
      (one_list_rev r1 xs * one_list_rev r2 ys * p) (fun2set (f,df)) ==>
      ?r4 r5. arm_cmp_pre (r1,r2,n2w (LENGTH xs),df,f) /\
              (arm_cmp (r1,r2,n2w (LENGTH xs),df,f) = (r4,r5,df,f)) /\
              (mw_cmp xs ys = if r4 = r5 then NONE else SOME (r4 <+ r5))``,
  HO_MATCH_MP_TAC SNOC_INDUCT \\ SIMP_TAC std_ss [NOT_SNOC_NIL,ALIGNED_INTRO]
  \\ REPEAT STRIP_TAC
  \\ `(ys = []) \/ ?z zs. ys = SNOC z zs` by METIS_TAC [SNOC_CASES]
  \\ FULL_SIMP_TAC std_ss [LENGTH_SNOC,DECIDE ``~(SUC n = 0)``,LENGTH]
  \\ ONCE_REWRITE_TAC [arm_cmp_pre,arm_cmp_def,mw_cmp_def]
  \\ FULL_SIMP_TAC std_ss [ADD1,GSYM word_add_n2w,LET_DEF,WORD_ADD_SUB,
       one_list_rev_SNOC,ALIGNED_INTRO,NOT_SNOC_NIL,LAST_SNOC,FRONT_SNOC]
  \\ SEP_R_TAC \\ `LENGTH xs < 4294967296` by DECIDE_TAC
  \\ FULL_SIMP_TAC (std_ss++SIZES_ss) [n2w_11,LENGTH_NIL]
  \\ Cases_on `xs = []` \\ ASM_SIMP_TAC std_ss [] THEN1 METIS_TAC [mw_cmp_def]
  \\ REV (Cases_on `x = z`) THEN1 ASM_SIMP_TAC std_ss []
  \\ ASM_SIMP_TAC std_ss [] \\ Q.PAT_ASSUM `!z.bb` MATCH_MP_TAC
  \\ Q.EXISTS_TAC `one (r1,x) * one (r2,z) * p`
  \\ FULL_SIMP_TAC (std_ss++star_ss) [ALIGNED]);

val arm_cmp_alias_thm = prove(
  ``!xs r1 df f p.
      ~(xs = []) /\ (LENGTH xs < 2**32) /\ ALIGNED r1 /\
      (one_list_rev r1 xs * p) (fun2set (f,df)) ==>
      ?r4 r5. arm_cmp_pre (r1,r1,n2w (LENGTH xs),df,f) /\
              (arm_cmp (r1,r1,n2w (LENGTH xs),df,f) = (r4,r4,df,f))``,
  HO_MATCH_MP_TAC SNOC_INDUCT \\ SIMP_TAC std_ss [NOT_SNOC_NIL,ALIGNED_INTRO]
  \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [LENGTH_SNOC,DECIDE ``~(SUC n = 0)``,LENGTH]
  \\ ONCE_REWRITE_TAC [arm_cmp_pre,arm_cmp_def,mw_cmp_def]
  \\ FULL_SIMP_TAC std_ss [ADD1,GSYM word_add_n2w,LET_DEF,WORD_ADD_SUB,
       one_list_rev_SNOC,ALIGNED_INTRO,NOT_SNOC_NIL,LAST_SNOC,FRONT_SNOC]
  \\ SEP_R_TAC \\ `LENGTH xs < 4294967296` by DECIDE_TAC
  \\ FULL_SIMP_TAC (std_ss++SIZES_ss) [n2w_11,LENGTH_NIL]
  \\ Cases_on `xs = []` \\ ASM_SIMP_TAC std_ss []
  \\ SEP_F_TAC \\ SEP_TAC []);


(* mw_compare *)

val (th1,arm_compare_def,arm_compare_pre) = compile "arm" ``
  arm_compare (r1:word32,r2:word32,r4:word32,r5:word32,df:word32 set,f:word32->word32) =
    if ~(r4 = r5) then (r4,r5,df,f) else
    if r4 = 0w then (r4,r5,df,f) else
      let r3 = r4 in
      let (r4,r5,df,f) = arm_cmp (r1,r2,r3,df,f) in
        (r4,r5,df,f)``

val arm_compare_thm = prove(
  ``!xs ys r1 r2 df f p.
      (LENGTH xs < 2**32) /\ (LENGTH ys < 2**32) /\ ALIGNED r1 /\ ALIGNED r2 /\
      (one_list_rev r1 xs * one_list_rev r2 ys * p) (fun2set (f,df)) ==>
      ?r4 r5. arm_compare_pre (r1,r2,n2w (LENGTH xs),n2w (LENGTH ys),df,f) /\
              (arm_compare (r1,r2,n2w (LENGTH xs),n2w (LENGTH ys),df,f) = (r4,r5,df,f)) /\
              (mw_compare xs ys = if r4 = r5 then NONE else SOME (r4 <+ r5))``,
  SIMP_TAC std_ss [arm_compare_def,arm_compare_pre,mw_compare_def]
  \\ ASM_SIMP_TAC (std_ss++SIZES_ss) [n2w_11,LET_DEF] \\ REPEAT STRIP_TAC
  \\ REV (Cases_on `LENGTH xs = LENGTH ys`) THEN1
   (ASM_SIMP_TAC (std_ss++SIZES_ss) [n2w_11,WORD_LO,w2n_n2w]
    \\ Cases_on `LENGTH xs < LENGTH ys` \\ ASM_SIMP_TAC std_ss []
    \\ `LENGTH ys < LENGTH xs` by DECIDE_TAC \\ ASM_SIMP_TAC std_ss [])
  \\ Cases_on `xs = []` THEN1 (FULL_SIMP_TAC std_ss [LENGTH] \\ METIS_TAC [mw_cmp_def])
  \\ MP_TAC ((SPEC_ALL o SIMP_RULE std_ss [GSYM AND_IMP_INTRO]) arm_cmp_thm)
  \\ ASM_SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC \\ ASM_SIMP_TAC std_ss [LENGTH_NIL]
  \\ Cases_on `ys = []` \\ ASM_SIMP_TAC std_ss [] \\ Cases_on `xs`
  \\ FULL_SIMP_TAC std_ss [LENGTH] \\ `F` by DECIDE_TAC);

val arm_compare_alias_thm = prove(
  ``!xs ys r1 r2 df f p.
      (LENGTH xs < 2**32) /\ ALIGNED r1 /\
      (one_list_rev r1 xs * p) (fun2set (f,df)) ==>
      ?r4 r5. arm_compare_pre (r1,r1,n2w (LENGTH xs),n2w (LENGTH xs),df,f) /\
              (arm_compare (r1,r1,n2w (LENGTH xs),n2w (LENGTH xs),df,f) = (r4,r4,df,f))``,
  SIMP_TAC std_ss [arm_compare_def,arm_compare_pre,mw_compare_def]
  \\ ASM_SIMP_TAC (std_ss++SIZES_ss) [n2w_11,LET_DEF,LENGTH_NIL] \\ REPEAT STRIP_TAC
  \\ Cases_on `xs = []` \\ ASM_SIMP_TAC std_ss []
  \\ ASSUME_TAC (GEN_ALL arm_cmp_alias_thm)
  \\ SEP_I_TAC "arm_cmp" \\ SEP_F_TAC
  \\ FULL_SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss []);


(* mwi_compare *)

val (th1,arm_icompare_aux_def,arm_icompare_aux_pre) = compile "arm" ``
  arm_icompare_aux (r0:word32,r4:word32,r5:word32) =
    if r4 <+ r5 then let r0 = ~r0 in (r0,r4,r5) else (r0,r4,r5)``;

val (th1,arm_icompare_def,arm_icompare_pre) = compile "arm" ``
  arm_icompare (r1:word32,r2:word32,r4:word32,r5:word32,df:word32 set,f:word32->word32) =
    let r3 = r4 ?? r5 in
      if ~(r3 && 7w = 0w) then
        if r4 && 4w = 0w then let r3 = 1w in (r3,df,f)
                         else let r3 = 2w in (r3,df,f)
      else
        let r0 = r4 in
        let r4 = r4 >>> 10 in
        let r5 = r5 >>> 10 in
        let (r4,r5,df,f) = arm_compare (r1,r2,r4,r5,df,f) in
          if r4 = r5 then let r3 = 0w in (r3,df,f) else
            let (r0,r4,r5) = arm_icompare_aux(r0,r4,r5) in
            let r3 = (1w:word32) in
              if r0 && 4w = 0w then (r3,df,f) else
                let r3 = r3 + 1w in (r3,df,f)``

val mwi_cmp_res_def = Define `
  (mwi_cmp_res NONE = 0w) /\
  (mwi_cmp_res (SOME F) = 1w) /\
  (mwi_cmp_res (SOME T) = 2w)`;

val mwi_header_7 = prove(
  ``!x xs. mwi_header (x,xs) && 0x7w = if x then 6w else 2w``,
  SIMP_TAC bool_ss [mwi_header_def,n2w_and_7,GSYM (EVAL ``128 * 8``)]
  \\ Cases \\ SIMP_TAC std_ss [MULT_ASSOC,GSYM ADD_ASSOC,MOD_MULT]);

val mwi_header_EQ = prove(
  ``!x xs y ys. (mwi_header (x,xs) && 0x7w = mwi_header (y,ys) && 0x7w) = (x = y)``,
  SIMP_TAC std_ss [mwi_header_7] \\ REPEAT Cases \\ EVAL_TAC);

val mwi_header_EQ_const = prove(
  ``!zs z. LENGTH zs < 4194304 ==>
           ((mwi_header (z,zs) = 2w) = ~z /\ (zs = [])) /\
           ?w. ((mwi_header (z,zs) = 1026w) = ~z /\ (zs = [w]))``,
  SIMP_TAC (std_ss++SIZES_ss) [mwi_header_def,n2w_11] \\ REPEAT STRIP_TAC
  \\ `LENGTH zs * 1024 + (if z then 4 else 0) + 2 < 4294967296` by
      (Cases_on `z` \\ DECIDE_TAC) \\ ASM_SIMP_TAC std_ss []
  \\ Cases_on `z` \\ ASM_SIMP_TAC std_ss [LENGTH_NIL]
  \\ Cases_on `zs` \\ ASM_SIMP_TAC std_ss [LENGTH,NOT_NIL_CONS]
  \\ Cases_on `t` \\ ASM_SIMP_TAC std_ss [NOT_NIL_CONS,CONS_11,LENGTH]
  \\ DECIDE_TAC);

val WORD_AND_TWOEXP = prove(
  ``!i w. ((w && n2w (2**i)) = if i < dimindex (:'a) /\ (w:'a word) ' i then n2w (2**i) else 0w)``,
  CONV_TAC (RAND_CONV (ALPHA_CONV ``j:num``))
  \\ SIMP_TAC std_ss [fcpTheory.CART_EQ,word_and_def,word_0,DECIDE ``SUC n - n = 1``,
      fcpTheory.FCP_BETA,word_index,bitTheory.BIT_def,bitTheory.BITS_THM]
  \\ REPEAT STRIP_TAC
  \\ REV (Cases_on `j < dimindex (:'a)`) \\ ASM_SIMP_TAC std_ss [] THEN1
   (`i < j /\ i <= j` by DECIDE_TAC
    \\ FULL_SIMP_TAC std_ss [GSYM EXP_SUB,word_0]
    \\ FULL_SIMP_TAC std_ss [LESS_EQ]
    \\ `?p. j = SUC i + p` by METIS_TAC [LESS_EQ_EXISTS]
    \\ `SUC i + p - i = SUC p` by DECIDE_TAC
    \\ ASM_SIMP_TAC std_ss [EXP,RW1[MULT_COMM]MOD_EQ_0])
  \\ REV (`!n. ((2 ** j DIV 2 ** n) MOD 2 = 1) = (n = j)` by ALL_TAC)
  \\ ASM_SIMP_TAC std_ss [] THEN1
   (Cases_on `i = j` \\ ASM_SIMP_TAC std_ss []
    \\ Cases_on `w ' j` \\ ASM_SIMP_TAC std_ss [word_index,word_0,
         bitTheory.BIT_def,bitTheory.BITS_THM,DECIDE ``SUC j - j = 1``])
  \\ REPEAT STRIP_TAC \\ Cases_on `j = n` \\ ASM_SIMP_TAC std_ss []
  \\ `j < n \/ n < j` by DECIDE_TAC \\ IMP_RES_TAC bitTheory.TWOEXP_MONO
  \\ ASM_SIMP_TAC std_ss [LESS_DIV_EQ_ZERO]
  \\ FULL_SIMP_TAC std_ss [LESS_EQ] \\ POP_ASSUM (K ALL_TAC)
  \\ IMP_RES_TAC LESS_EQ_EXISTS
  \\ ASM_SIMP_TAC std_ss [(DECIDE ``SUC n + p = p + 1 + n``)]
  \\ SIMP_TAC std_ss [EXP_ADD,MULT_DIV,bitTheory.ZERO_LT_TWOEXP,MOD_EQ_0]);

val WORD_AND_TWOEXP_EQ_ZERO = prove(
  ``!i w. (w && n2w (2**i) = 0w) = ~(w:'a word) ' i \/ ~(i < dimindex (:'a))``,
  SIMP_TAC std_ss [WORD_AND_TWOEXP] \\ REPEAT STRIP_TAC
  \\ Cases_on `i < dimindex (:'a)` \\ ASM_SIMP_TAC std_ss []
  \\ Cases_on `w ' i` \\ ASM_SIMP_TAC std_ss [n2w_11,ZERO_LT_dimword]
  \\ `2 ** i < dimword (:'a)` by ASM_SIMP_TAC std_ss [dimword_def]
  \\ ASM_SIMP_TAC std_ss []);

val mwi_header_sign_index = prove(
  ``!x xs. mwi_header (x,xs) ' 2 = x``,
  REPEAT STRIP_TAC \\ SIMP_TAC (std_ss++SIZES_ss)
    [mwi_header_def,word_index,bitTheory.BIT_def,bitTheory.BITS_THM2,GSYM ADD_ASSOC]
  \\ SIMP_TAC bool_ss [GSYM (EVAL ``128*8``),MULT_ASSOC]
  \\ `(if x then 4 else 0) + 2 < 8` by (Cases_on `x` \\ DECIDE_TAC)
  \\ ASM_SIMP_TAC std_ss [MOD_MULT]
  \\ `(if x then 4 else 0) + 2 = (if x then 1 else 0) * 4 + 2` by (Cases_on `x` \\ DECIDE_TAC)
  \\ FULL_SIMP_TAC std_ss [DIV_MULT] \\ Cases_on `x` \\ ASM_SIMP_TAC std_ss []);

val mwi_header_sign = prove(
  ``!x xs. ((mwi_header (x,xs) && 4w = 0w) = ~x) /\
           ((~mwi_header (x,xs) && 4w = 0w) = x)``,
  REPEAT STRIP_TAC
  \\ ASSUME_TAC (GEN_ALL (Q.ISPECL [`2`,`w:word32`] WORD_AND_TWOEXP_EQ_ZERO))
  \\ FULL_SIMP_TAC (std_ss++SIZES_ss) [mwi_header_sign_index,
       word_1comp_def,fcpTheory.FCP_BETA]);

val WORD_LSR = prove(
  ``!n p i.
      n < 2 ** (dimindex(:'a) - i) /\ p < 2 ** i ==>
      (n2w (n * 2 ** i + p) >>> i = n2w n:'a word)``,
  SIMP_TAC std_ss [word_lsr_n2w,word_bits_n2w,bitTheory.BITS_THM]
  \\ ASM_SIMP_TAC std_ss [ADD1,DIV_MULT,
        DECIDE ``0<n ==> (n-1+1 = n)``,DIMINDEX_GT_0]);

val mwi_header_length = prove(
  ``!xs x. LENGTH xs < 4194304 ==> (mwi_header (x,xs) >>> 10 = n2w (LENGTH xs))``,
  SIMP_TAC std_ss [mwi_header_def,GSYM ADD_ASSOC] \\ REPEAT STRIP_TAC
  \\ SIMP_TAC bool_ss [GSYM (EVAL ``(2:num)**10``)]
  \\ MATCH_MP_TAC WORD_LSR \\ Cases_on `x` \\ ASM_SIMP_TAC (std_ss++SIZES_ss) []);

val mwi_header_length_8 = prove(
  ``!xs x. LENGTH xs < 4194304 ==> (mwi_header (x,xs) >>> 8 = n2w (4 * LENGTH xs))``,
  ONCE_REWRITE_TAC [MULT_COMM]
  \\ SIMP_TAC std_ss [mwi_header_def,GSYM ADD_ASSOC] \\ REPEAT STRIP_TAC
  \\ SIMP_TAC bool_ss [GSYM (EVAL ``4 * (2:num)**8``),MULT_ASSOC]
  \\ MATCH_MP_TAC WORD_LSR \\ Cases_on `x`
  \\ ASM_SIMP_TAC (std_ss++SIZES_ss) [] \\ DECIDE_TAC);

val arm_icompare_thm = (RW [markerTheory.Abbrev_def] o prove)(
  ``!x xs y ys r1 r2 df f p.
      (LENGTH xs < 2**22) /\ (LENGTH ys < 2**22) /\ ALIGNED r1 /\ ALIGNED r2 /\
      (one_list_rev r1 xs * one_list_rev r2 ys * p) (fun2set (f,df)) ==>
      Abbrev (arm_icompare_pre (r1,r2,mwi_header (x,xs),mwi_header (y,ys),df,f) /\
              (arm_icompare (r1,r2,mwi_header (x,xs),mwi_header (y,ys),df,f) =
                (mwi_cmp_res (mwi_compare (x,xs) (y,ys)),df,f)))``,
  SIMP_TAC std_ss [arm_icompare_pre,arm_icompare_def,LET_DEF,WORD_RIGHT_AND_OVER_XOR,
    WORD_EQ_XOR_ZERO,mwi_header_EQ,mwi_compare_def] \\ REPEAT STRIP_TAC
  \\ REV (Cases_on `x = y`)
  \\ ASM_SIMP_TAC std_ss [mwi_header_sign,markerTheory.Abbrev_def]
  THEN1 (Cases_on `x` \\ ASM_SIMP_TAC std_ss [mwi_cmp_res_def])
  \\ ASM_SIMP_TAC std_ss [mwi_header_length]
  \\ (MP_TAC o SIMP_RULE std_ss [GSYM AND_IMP_INTRO] o SPEC_ALL) arm_compare_thm
  \\ ASM_SIMP_TAC std_ss [DECIDE ``n < 4194304 ==> n < 4294967296``] \\ STRIP_TAC
  \\ ASM_SIMP_TAC std_ss [arm_icompare_aux_def]
  \\ Cases_on `r4 = r5` \\ ASM_SIMP_TAC std_ss [option_eq_def,mwi_cmp_res_def,LET_DEF]
  \\ Cases_on `r4 <+ r5` \\ Cases_on `y`
  \\ ASM_SIMP_TAC std_ss [mwi_cmp_res_def,mwi_header_sign,word_add_n2w]);

val arm_icompare_alias_thm = (RW [markerTheory.Abbrev_def] o prove)(
  ``!x xs r1 r2 df f p.
      (LENGTH xs < 2**22) /\ ALIGNED r1 /\ mw_ok xs /\
      (one_list_rev r1 xs * p) (fun2set (f,df)) ==>
      Abbrev (arm_icompare_pre (r1,r1,mwi_header (x,xs),mwi_header (x,xs),df,f) /\
              (arm_icompare (r1,r1,mwi_header (x,xs),mwi_header (x,xs),df,f) =
                (mwi_cmp_res (mwi_compare (x,xs) (x,xs)),df,f)))``,
  SIMP_TAC std_ss [arm_icompare_pre,arm_icompare_def,LET_DEF,WORD_RIGHT_AND_OVER_XOR,
    WORD_EQ_XOR_ZERO,mwi_header_EQ,mwi_compare_def] \\ REPEAT STRIP_TAC
  \\ ASM_SIMP_TAC std_ss [arm_icompare_aux_def,mwi_header_length]
  \\ ASSUME_TAC (GEN_ALL arm_compare_alias_thm) \\ SEP_I_TAC "arm_compare"
  \\ SEP_F_TAC
  \\ `LENGTH xs < 4294967296` by DECIDE_TAC
  \\ ASM_SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC \\ ASM_SIMP_TAC std_ss []
  \\ ASM_SIMP_TAC std_ss [mw_compare_def,mw_cmp_thm,option_eq_def,
       mwi_cmp_res_def,markerTheory.Abbrev_def]);


(* mw_addv *)

(* r1 - length of number r3, in number of words
   r2 - length of number r4, in number of words, r4 <= r3 *)

val (arm_add_th,arm_add_def) = decompile_io_strings arm_tools_no_status "arm_add"
  (SOME (``(r1:word32,r2:word32,r3:word32,r4:word32,r5:word32,df:word32 set,f:word32->word32)``,
         ``(r5:word32,df:word32 set,f:word32->word32)``)) (assemble "arm" `

    mov r7,r3
    adds r6,r4,#0
    add r3,r3,r1,lsl #2
    add r4,r4,r2,lsl #2
    b L0

L1: ldr r1,[r3],#-4
    ldr r2,[r4],#-4
    adcs r1,r1,r2
    str r1,[r5],#-4
L0: teq r6,r4
    bne L1

L2: teq r7,r3
    beq L3
    ldr r1,[r3],#-4
    adcs r1,r1,#0
    str r1,[r5],#-4
    b L2

L3: mov r1,#0
    adc r1,r1,#0
    strcs r1,[r5],#-4

  `)

val arm_add1_thm = prove(
  ``!r1 r2 r3 r4 r5 f sc sv xs ys zs qs p.
      (mw_add xs ys sc = (zs,d)) /\ (LENGTH qs = LENGTH xs) /\ (LENGTH ys = LENGTH xs) /\
      (4 * LENGTH xs < 4294967296) /\ ALIGNED r3 /\ ALIGNED r4 /\ ALIGNED r5 /\
      (one_rev_list r3 xs * one_rev_list r4 ys * one_rev_list r5 qs * p) (fun2set (f,df)) ==>
      ?r1i r2i r4i sni svi szi fi.
        arm_add1_pre (r1,r2,r3,r4,r5,r4 - n2w (4 * LENGTH xs),df,f,sc,sv) /\
        (arm_add1 (r1,r2,r3,r4,r5,r4 - n2w (4 * LENGTH xs),df,f,sc,sv) =
          (r1i,r2i,r3 - n2w (4 * LENGTH xs),r4 - n2w (4 * LENGTH xs),r5 - n2w (4 * LENGTH xs),r4i,df,fi,d,sni,svi,szi)) /\
        (one_rev_list r3 xs * one_rev_list r4 ys * one_rev_list r5 zs * p) (fun2set (fi,df))``,
  Induct_on `xs` \\ Cases_on `ys` \\ Cases_on `qs`
  \\ SIMP_TAC std_ss [LENGTH,DECIDE ``~(SUC n = 0)``,NOT_CONS_NIL,mw_add_def,HD,TL]
  \\ TRY (BasicProvers.LET_ELIM_TAC) \\ ONCE_REWRITE_TAC [EQ_SYM_EQ]
  \\ FULL_SIMP_TAC std_ss [one_rev_list_def,STAR_ASSOC] \\ ONCE_REWRITE_TAC [EQ_SYM_EQ]
  \\ ONCE_REWRITE_TAC [arm_add_def] \\ SIMP_TAC std_ss [LET_DEF,MULT_CLAUSES,WORD_SUB_RZERO]
  \\ FULL_SIMP_TAC (std_ss++SIZES_ss) [WORD_EQ_SUB_CANCEL,MULT_CLAUSES,n2w_11]
  \\ FULL_SIMP_TAC std_ss [WORD_SUB_PLUS,GSYM word_add_n2w,single_add_eq] \\ SEP_R_TAC
  \\ `SND (add_with_carry (h'',h,sc)) = (c1,SND (SND (add_with_carry (h'',h,sc))))` by
        (EXPAND_TAC \\ ASM_SIMP_TAC std_ss [])
  \\ PURE_ONCE_ASM_REWRITE_TAC [] \\ SEP_I_TAC "arm_add1" \\ SEP_TAC []
  \\ POP_ASSUM MP_TAC \\ ASM_SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC \\ SEP_W_TAC \\ SEP_F_TAC
  \\ `4 * LENGTH xs < 4294967296` by DECIDE_TAC \\ ASM_SIMP_TAC std_ss []
  \\ REPEAT STRIP_TAC \\ ASM_SIMP_TAC std_ss [] \\ EXPAND_TAC \\ SEP_TAC [one_rev_list_def]);

val arm_add1_alias_thm = prove(
  ``!r1 r2 r3 r5 f sc sv xs ys zs qs p.
      (mw_add xs xs sc = (zs,d)) /\ (LENGTH qs = LENGTH xs) /\
      (4 * LENGTH xs < 4294967296) /\ ALIGNED r3 /\ ALIGNED r5 /\
      (one_rev_list r3 xs * one_rev_list r5 qs * p) (fun2set (f,df)) ==>
      ?r1i r2i r4i sni svi szi fi.
        arm_add1_pre (r1,r2,r3,r3,r5,r3 - n2w (4 * LENGTH xs),df,f,sc,sv) /\
        (arm_add1 (r1,r2,r3,r3,r5,r3 - n2w (4 * LENGTH xs),df,f,sc,sv) =
          (r1i,r2i,r3 - n2w (4 * LENGTH xs),r3 - n2w (4 * LENGTH xs),r5 - n2w (4 * LENGTH xs),r4i,df,fi,d,sni,svi,szi)) /\
        (one_rev_list r3 xs * one_rev_list r5 zs * p) (fun2set (fi,df))``,
  Induct_on `xs` \\ Cases_on `qs`
  \\ SIMP_TAC std_ss [LENGTH,DECIDE ``~(SUC n = 0)``,NOT_CONS_NIL,mw_add_def,HD,TL]
  \\ TRY (BasicProvers.LET_ELIM_TAC) \\ ONCE_REWRITE_TAC [EQ_SYM_EQ]
  \\ FULL_SIMP_TAC std_ss [one_rev_list_def,STAR_ASSOC] \\ ONCE_REWRITE_TAC [EQ_SYM_EQ]
  \\ ONCE_REWRITE_TAC [arm_add_def] \\ SIMP_TAC std_ss [LET_DEF,MULT_CLAUSES,WORD_SUB_RZERO]
  \\ FULL_SIMP_TAC (std_ss++SIZES_ss) [WORD_EQ_SUB_CANCEL,MULT_CLAUSES,n2w_11]
  \\ FULL_SIMP_TAC std_ss [WORD_SUB_PLUS,GSYM word_add_n2w,single_add_eq] \\ SEP_R_TAC
  \\ `SND (add_with_carry (h',h',sc)) = (c1,SND (SND (add_with_carry (h',h',sc))))` by
        (EXPAND_TAC \\ ASM_SIMP_TAC std_ss [])
  \\ PURE_ONCE_ASM_REWRITE_TAC [] \\ SEP_I_TAC "arm_add1" \\ SEP_TAC []
  \\ POP_ASSUM MP_TAC \\ ASM_SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC \\ SEP_W_TAC \\ SEP_F_TAC
  \\ `4 * LENGTH xs < 4294967296` by DECIDE_TAC \\ ASM_SIMP_TAC std_ss []
  \\ REPEAT STRIP_TAC \\ ASM_SIMP_TAC std_ss [] \\ EXPAND_TAC \\ SEP_TAC [one_rev_list_def]);

val arm_add2_thm = prove(
  ``!r1 r3 r5 f sc sv xs zs qs p.
      (mw_add xs (MAP (\x.0w) xs) sc = (zs,d)) /\ (LENGTH qs = LENGTH xs) /\
      (LENGTH xs < 1073741824) /\ ALIGNED r3 /\ ALIGNED r5 /\
      (one_rev_list r3 xs * one_rev_list r5 qs * p) (fun2set (f,df)) ==>
      ?r1i r2i r4i sni svi szi fi.
        arm_add2_pre (r1,r3,r5,r3 - n2w (4 * LENGTH xs),df,f,sc,sv) /\
        (arm_add2 (r1,r3,r5,r3 - n2w (4 * LENGTH xs),df,f,sc,sv) =
          (r1i,r3 - n2w (4 * LENGTH xs),r5 - n2w (4 * LENGTH xs),r4i,df,fi,d,sni,svi,szi)) /\
        (one_rev_list r3 xs * one_rev_list r5 zs * p) (fun2set (fi,df))``,
  Induct_on `xs` THEN1
   (SIMP_TAC std_ss [mw_add_def,MAP,LENGTH_NIL,LENGTH,WORD_SUB_RZERO]
    \\ ONCE_REWRITE_TAC [arm_add_def] \\ SIMP_TAC std_ss [LET_DEF])
  \\ Cases_on `qs`
  \\ SIMP_TAC std_ss [LENGTH,DECIDE ``~(SUC n = 0)``,NOT_CONS_NIL,mw_add_def,MAP,HD,TL]
  \\ BasicProvers.LET_ELIM_TAC
  \\ ONCE_REWRITE_TAC [arm_add_def]
  \\ ASM_SIMP_TAC std_ss [LET_DEF,WORD_EQ_SUB_CANCEL,WORD_4_MULT_EQ_0,DECIDE ``~(SUC n = 0)``]
  \\ FULL_SIMP_TAC std_ss [one_rev_list_def,STAR_ASSOC,MULT_CLAUSES,GSYM word_add_n2w]
  \\ FULL_SIMP_TAC std_ss [WORD_SUB_PLUS,single_add_eq]
  \\ SEP_TAC [] \\ IMP_RES_TAC (DECIDE ``SUC n < k ==> n < k``)
  \\ ONCE_REWRITE_TAC [Q.ISPEC `x:bool#bool` (GSYM pairTheory.PAIR)]
  \\ SEP_I_TAC "arm_add2" \\ SEP_W_TAC \\ SEP_F_TAC
  \\ SEP_TAC [] \\ REPEAT STRIP_TAC \\ EXPAND_TAC \\ ASM_SIMP_TAC std_ss []
  \\ SEP_TAC [one_rev_list_def]);

val APPEND_EXISTS = prove(
  ``!xs ys. LENGTH ys <= LENGTH xs ==> ?xs1 xs2. (xs = xs1 ++ xs2) /\ (LENGTH ys = LENGTH xs1)``,
  HO_MATCH_MP_TAC SNOC_INDUCT \\ SIMP_TAC std_ss [LENGTH,LENGTH_NIL,APPEND_eq_NIL,LENGTH_SNOC]
  \\ REPEAT STRIP_TAC \\ Cases_on `LENGTH ys = LENGTH (SNOC x xs)`
  THEN1 (Q.EXISTS_TAC `SNOC x xs` \\ Q.EXISTS_TAC `[]` \\ ASM_SIMP_TAC std_ss [LENGTH_SNOC,APPEND_NIL])
  \\ FULL_SIMP_TAC std_ss [LENGTH_SNOC]
  \\ `LENGTH ys <= LENGTH xs` by DECIDE_TAC \\ RES_TAC
  \\ FULL_SIMP_TAC std_ss [SNOC_APPEND]
  \\ Q.EXISTS_TAC `xs1` \\ Q.EXISTS_TAC `xs2 ++ [x]` \\ ASM_SIMP_TAC std_ss [APPEND_ASSOC]);

val LESS_EQ_EXISTS_APPEND = prove(
  ``!xs n. n <= LENGTH xs ==> ?xs1 xs2. (xs = xs1 ++ xs2) /\ (LENGTH xs1 = n)``,
  HO_MATCH_MP_TAC SNOC_INDUCT \\ SIMP_TAC std_ss [LENGTH,LENGTH_NIL,APPEND_eq_NIL,LENGTH_SNOC]
  \\ REPEAT STRIP_TAC \\ Cases_on `n = LENGTH (SNOC x xs)`
  THEN1 (Q.EXISTS_TAC `SNOC x xs` \\ Q.EXISTS_TAC `[]` \\ ASM_SIMP_TAC std_ss [LENGTH_SNOC,APPEND_NIL])
  \\ FULL_SIMP_TAC std_ss [LENGTH_SNOC] \\ `n <= LENGTH xs` by DECIDE_TAC \\ RES_TAC
  \\ FULL_SIMP_TAC std_ss [SNOC_APPEND]
  \\ Q.EXISTS_TAC `xs1` \\ Q.EXISTS_TAC `xs2 ++ [x]` \\ ASM_SIMP_TAC std_ss [APPEND_ASSOC]);

val LENGTH_EQ_ADD = prove(
  ``!m n xs. (LENGTH xs = m + n) ==>
             ?ys1 ys2. (xs = ys1 ++ ys2) /\ (LENGTH ys1 = m) /\ (LENGTH ys2 = n)``,
  Induct \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [LENGTH_NIL,APPEND]
  \\ Cases_on `xs` \\ FULL_SIMP_TAC std_ss [LENGTH,ADD] \\ FULL_SIMP_TAC std_ss [ADD1]
  \\ RES_TAC \\ Q.EXISTS_TAC `h::ys1` \\ Q.EXISTS_TAC `ys2`
  \\ ASM_SIMP_TAC std_ss [APPEND,LENGTH,ADD1]);

val ADD_LESS_EQ_EXISTS_APPEND = prove(
  ``!xs n m. n + m <= LENGTH xs ==>
      ?xs1 xs2 xs3. (xs = xs1 ++ xs2 ++ xs3) /\ (LENGTH xs1 = n) /\ (LENGTH xs2 = m)``,
  REPEAT STRIP_TAC \\ IMP_RES_TAC LESS_EQ_EXISTS_APPEND
  \\ IMP_RES_TAC LENGTH_EQ_ADD \\ ASM_SIMP_TAC std_ss [] \\ METIS_TAC []);

val CARRY_OUT_F = prove(
  ``!w. (FST (SND (add_with_carry (w,0w,F))) = F) /\ (FST (SND (add_with_carry (0w,w,F))) = F)``,
  Cases \\ ASM_SIMP_TAC std_ss [add_with_carry_def,LET_DEF,w2n_n2w,WORD_ADD_0,ZERO_LT_dimword]);

val LENGTH_mw_add = prove(
  ``!xs ys c zs d. (mw_add xs ys c = (zs,d)) ==> (LENGTH zs = LENGTH xs)``,
  Induct \\ SIMP_TAC std_ss [mw_add_def,LENGTH] \\ REPEAT STRIP_TAC
  \\ Cases_on `single_add h (HD ys) c` \\ FULL_SIMP_TAC std_ss [LET_DEF]
  \\ Cases_on `mw_add xs (TL ys) r` \\ FULL_SIMP_TAC std_ss [] \\ RES_TAC
  \\ EXPAND_TAC \\ FULL_SIMP_TAC std_ss [LENGTH]);

val arm_add_thm = prove(
  ``(mw_addv xs ys F = zs) /\ LENGTH ys <= LENGTH xs /\ LENGTH xs < 1073741824 /\
    (LENGTH res = LENGTH zs) /\ ALIGNED r3 /\ ALIGNED r4 /\ ALIGNED r5 /\
    (one_list_rev_old r3 xs * one_list_rev_old r4 ys * one_rev_list r5 res * p) (fun2set (f,df)) ==>
    ?fi. arm_add_pre (n2w (LENGTH xs),n2w (LENGTH ys),r3,r4,r5,df,f) /\
         (arm_add (n2w (LENGTH xs),n2w (LENGTH ys),r3,r4,r5,df,f) = (r5 - n2w (4 * LENGTH zs),df,fi)) /\
         (one_list_rev_old r3 xs * one_list_rev_old r4 ys * one_rev_list r5 zs * p) (fun2set (fi,df))``,
  REPEAT STRIP_TAC \\ IMP_RES_TAC APPEND_EXISTS
  \\ FULL_SIMP_TAC std_ss [mw_addv_EQ_mw_add]
  \\ `?zs1 c2. mw_add xs1 ys F = (zs1,c2)` by METIS_TAC [PAIR]
  \\ `?zs2 c3. mw_add xs2 (MAP (\x.0w) xs2) c2 = (zs2,c3)` by METIS_TAC [PAIR]
  \\ FULL_SIMP_TAC std_ss [LET_DEF] \\ EXPAND_TAC
  \\ PURE_ONCE_REWRITE_TAC [arm_add_def] \\ SIMP_TAC std_ss [LET_DEF,WORD_MUL_LSL,word_mul_n2w]
  \\ ASSUME_TAC (GEN_ALL arm_add1_thm)
  \\ Q.ABBREV_TAC `r4i = r4 + n2w (4 * LENGTH xs1)`
  \\ `SND (add_with_carry (r4,0w,F)) = (F,SND (SND (add_with_carry (r4,0w,F))))` by
        (CONV_TAC ((RATOR_CONV o RAND_CONV) (PURE_ONCE_REWRITE_CONV [GSYM PAIR]))
         \\ PURE_ONCE_REWRITE_TAC [CARRY_OUT_F] \\ ASM_SIMP_TAC std_ss []) \\ ASM_SIMP_TAC std_ss []
  \\ `r4 = (r4 + n2w (4 * LENGTH xs1)) - n2w (4 * LENGTH xs1)` by METIS_TAC [WORD_ADD_SUB]
  \\ ONCE_ASM_REWRITE_TAC [] \\ Q.UNABBREV_TAC `r4i`
  \\ SEP_I_TAC "arm_add1" \\ FULL_SIMP_TAC std_ss [WORD_ADD_SUB]
  \\ `?res1 res2 res3. (res = res1 ++ res2 ++ res3) /\
                    (LENGTH res1 = LENGTH xs1)  /\
                    (LENGTH res2 = LENGTH xs2)  /\
                    (LENGTH res3 = if c3 then 1 else 0)` by ALL_TAC THEN1
     (FULL_SIMP_TAC std_ss [LENGTH_APPEND]
      \\ `LENGTH zs1 <= LENGTH res` by DECIDE_TAC \\ IMP_RES_TAC APPEND_EXISTS
      \\ FULL_SIMP_TAC std_ss [LENGTH_APPEND]
      \\ `LENGTH zs2 <= LENGTH xs2'` by DECIDE_TAC \\ IMP_RES_TAC APPEND_EXISTS
      \\ FULL_SIMP_TAC std_ss [LENGTH_APPEND,GSYM ADD_ASSOC]
      \\ Q.EXISTS_TAC `xs1'` \\ Q.EXISTS_TAC `xs1''` \\ Q.EXISTS_TAC `xs2''`
      \\ FULL_SIMP_TAC std_ss [APPEND_ASSOC] \\ IMP_RES_TAC LENGTH_mw_add
      \\ FULL_SIMP_TAC std_ss [] \\ Cases_on `c3` \\ FULL_SIMP_TAC std_ss [LENGTH])
  \\ FULL_SIMP_TAC std_ss [one_rev_list_APPEND,one_list_rev_old_def]
  \\ SEP_F_TAC \\ SEP_TAC []
  \\ SIMP_TAC bool_ss [GSYM (EVAL ``4 * 1073741824``),LT_MULT_LCANCEL]
  \\ `LENGTH xs1 < 1073741824 /\ LENGTH xs2 < 1073741824` by
        (FULL_SIMP_TAC std_ss [LENGTH_APPEND] \\ DECIDE_TAC) \\ FULL_SIMP_TAC std_ss []
  \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss []
  \\ (ASSUME_TAC o GEN_ALL o RW[WORD_ADD_SUB] o SUBST_INST
        [``r3:word32``|->``r3 + n2w (4 * LENGTH (xs:word32 list)):word32``,
         ``xs:word32 list``|->``xs:word32 list``]) arm_add2_thm
  \\ `!r w v. r + w + v - w = r + v:word32` by METIS_TAC [WORD_ADD_SUB,WORD_ADD_COMM,WORD_ADD_ASSOC]
  \\ FULL_SIMP_TAC std_ss [LENGTH_APPEND,LEFT_ADD_DISTRIB,GSYM word_add_n2w,WORD_ADD_ASSOC]
  \\ SEP_I_TAC "arm_add2"
  \\ POP_ASSUM MP_TAC \\ ASM_SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [word_mul_n2w]
  \\ SEP_F_TAC \\ SEP_TAC [] \\ REPEAT STRIP_TAC \\ ASM_SIMP_TAC std_ss []
  \\ IMP_RES_TAC LENGTH_mw_add \\ REV (Cases_on `c3`) THEN1
   (Cases_on `res3` \\ FULL_SIMP_TAC std_ss [LENGTH,DECIDE ``~(SUC n = 0)``]
    \\ SEP_TAC [LENGTH,one_rev_list_def,WORD_ADD_0,word_add_n2w,word_mul_n2w,
         LEFT_ADD_DISTRIB,GSYM WORD_SUB_PLUS,word_arith_lemma1])
  \\ SEP_TAC [LENGTH,one_rev_list_def,WORD_ADD_0,word_add_n2w,word_mul_n2w,
         LEFT_ADD_DISTRIB,GSYM WORD_SUB_PLUS,word_arith_lemma1]
  \\ Cases_on `res3` \\ FULL_SIMP_TAC std_ss [LENGTH,DECIDE ``~(SUC n = 0)``]
  \\ Cases_on `t` \\ FULL_SIMP_TAC std_ss [LENGTH,DECIDE ``~(SUC n = 0)``]
  \\ FULL_SIMP_TAC std_ss [one_rev_list_def,SEP_CLAUSES] \\ SEP_R_TAC
  \\ SIMP_TAC std_ss [add_with_carry_def,LET_DEF,w2n_n2w,ZERO_LT_dimword]
  \\ SEP_WRITE_TAC);

val arm_add_alias_thm = prove(
  ``(mw_addv xs xs F = zs) /\ LENGTH xs < 1073741824 /\
    (LENGTH res = LENGTH zs) /\ ALIGNED r3 /\ ALIGNED r5 /\
    (one_list_rev_old r3 xs * one_rev_list r5 res * p) (fun2set (f,df)) ==>
    ?fi. arm_add_pre (n2w (LENGTH xs),n2w (LENGTH xs),r3,r3,r5,df,f) /\
         (arm_add (n2w (LENGTH xs),n2w (LENGTH xs),r3,r3,r5,df,f) = (r5 - n2w (4 * LENGTH zs),df,fi)) /\
         (one_list_rev_old r3 xs * one_rev_list r5 zs * p) (fun2set (fi,df))``,
  REPEAT STRIP_TAC
  \\ `mw_addv (xs ++ []) xs F = zs` by FULL_SIMP_TAC std_ss [APPEND_NIL]
  \\ FULL_SIMP_TAC std_ss [mw_addv_EQ_mw_add,mw_add_def]
  \\ `?zs1 c2. mw_add xs xs F = (zs1,c2)` by METIS_TAC [PAIR]
  \\ Q.PAT_ASSUM `mw_addv xs xs F = zs` (K ALL_TAC)
  \\ FULL_SIMP_TAC std_ss [LET_DEF,APPEND_NIL] \\ EXPAND_TAC
  \\ PURE_ONCE_REWRITE_TAC [arm_add_def] \\ SIMP_TAC std_ss [LET_DEF,WORD_MUL_LSL,word_mul_n2w]
  \\ ASSUME_TAC (GEN_ALL arm_add1_alias_thm)
  \\ `SND (add_with_carry (r3,0w,F)) = (F,SND (SND (add_with_carry (r3,0w,F))))` by
        (CONV_TAC ((RATOR_CONV o RAND_CONV) (PURE_ONCE_REWRITE_CONV [GSYM PAIR]))
         \\ PURE_ONCE_REWRITE_TAC [CARRY_OUT_F] \\ ASM_SIMP_TAC std_ss []) \\ ASM_SIMP_TAC std_ss []
  \\ Q.ABBREV_TAC `r3i = r3 + n2w (4 * LENGTH xs)`
  \\ `r3 = (r3 + n2w (4 * LENGTH xs)) - n2w (4 * LENGTH xs)` by METIS_TAC [WORD_ADD_SUB]
  \\ ONCE_ASM_REWRITE_TAC [] \\ Q.UNABBREV_TAC `r3i`
  \\ SEP_I_TAC "arm_add1" \\ FULL_SIMP_TAC std_ss [WORD_ADD_SUB]
  \\ `?res1 res3. (res = res1 ++ res3) /\
                  (LENGTH res1 = LENGTH xs)  /\
                  (LENGTH res3 = if c2 then 1 else 0)` by ALL_TAC THEN1
     (FULL_SIMP_TAC std_ss [LENGTH_APPEND]
      \\ `LENGTH zs1 <= LENGTH res` by DECIDE_TAC \\ IMP_RES_TAC APPEND_EXISTS
      \\ FULL_SIMP_TAC std_ss [LENGTH_APPEND]
      \\ Q.EXISTS_TAC `xs1` \\ Q.EXISTS_TAC `xs2` \\ FULL_SIMP_TAC std_ss []
      \\ IMP_RES_TAC LENGTH_mw_add
      \\ FULL_SIMP_TAC std_ss [] \\ Cases_on `c2` \\ FULL_SIMP_TAC std_ss [LENGTH])
  \\ FULL_SIMP_TAC std_ss [one_rev_list_APPEND,one_list_rev_old_def]
  \\ SEP_F_TAC \\ SEP_TAC []
  \\ SIMP_TAC bool_ss [GSYM (EVAL ``4 * 1073741824``),LT_MULT_LCANCEL]
  \\ `LENGTH xs < 1073741824` by
        (FULL_SIMP_TAC std_ss [LENGTH_APPEND] \\ DECIDE_TAC) \\ FULL_SIMP_TAC std_ss []
  \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss []
  \\ ONCE_REWRITE_TAC [arm_add_def] \\ FULL_SIMP_TAC std_ss [LET_DEF]
  \\ IMP_RES_TAC LENGTH_mw_add \\ REV (Cases_on `c2`) THEN1
   (Cases_on `res3` \\ FULL_SIMP_TAC std_ss [LENGTH,DECIDE ``~(SUC n = 0)``]
    \\ SEP_TAC [LENGTH,one_rev_list_def,WORD_ADD_0,word_add_n2w,word_mul_n2w,
         LEFT_ADD_DISTRIB,GSYM WORD_SUB_PLUS,word_arith_lemma1,APPEND_NIL])
  \\ SEP_TAC [LENGTH,one_rev_list_def,WORD_ADD_0,word_add_n2w,word_mul_n2w,
         LEFT_ADD_DISTRIB,GSYM WORD_SUB_PLUS,word_arith_lemma1,LENGTH_APPEND,RIGHT_ADD_DISTRIB]
  \\ Cases_on `res3` \\ FULL_SIMP_TAC std_ss [LENGTH,DECIDE ``~(SUC n = 0)``]
  \\ Cases_on `t` \\ FULL_SIMP_TAC std_ss [LENGTH,DECIDE ``~(SUC n = 0)``]
  \\ FULL_SIMP_TAC std_ss [one_rev_list_def,SEP_CLAUSES] \\ SEP_R_TAC
  \\ SIMP_TAC std_ss [add_with_carry_def,LET_DEF,w2n_n2w,ZERO_LT_dimword]
  \\ SEP_WRITE_TAC);


(* mw_sub -- store result into the first operand *)

val (arm_sub_id_th,arm_sub_id_def) = decompile_io_strings arm_tools_no_status "arm_sub_id"
  (SOME (``(r1:word32,r2:word32,r3:word32,r4:word32,df:word32 set,f:word32->word32)``,
         ``(df:word32 set,f:word32->word32)``)) (assemble "arm" `

    sub r1,r4,r1,lsl #2
    subs r6,r1,#0
    b L0

L1: ldr r1,[r3]
    ldr r2,[r4],#-4
    sbcs r1,r1,r2
    str r1,[r3],#-4
L0: teq r6,r4
    bne L1

  `)

val arm_sub_id1_thm = prove(
  ``!r1 r2 r3 r4 r5 f sc sv xs ys zs qs p.
      (mw_sub xs ys sc = (zs,d)) /\ (LENGTH ys = LENGTH xs) /\
      (4 * LENGTH xs < 4294967296) /\ ALIGNED r3 /\ ALIGNED r4 /\
      (one_rev_list r3 xs * one_rev_list r4 ys * p) (fun2set (f,df)) ==>
      ?r1i r2i r4i sni svi szi fi.
        arm_sub_id1_pre (r1,r2,r3,r4,r4 - n2w (4 * LENGTH xs),df,f,sc,sv) /\
        (arm_sub_id1 (r1,r2,r3,r4,r4 - n2w (4 * LENGTH xs),df,f,sc,sv) =
          (r1i,r2i,r3 - n2w (4 * LENGTH xs),r4 - n2w (4 * LENGTH xs),r4i,df,fi,d,sni,svi,szi)) /\
        (one_rev_list r3 zs * one_rev_list r4 ys * p) (fun2set (fi,df))``,
  Induct_on `xs` \\ Cases_on `ys`
  \\ SIMP_TAC std_ss [LENGTH,DECIDE ``~(SUC n = 0)``,NOT_CONS_NIL,mw_sub_def,HD,TL]
  \\ TRY (BasicProvers.LET_ELIM_TAC) \\ ONCE_REWRITE_TAC [EQ_SYM_EQ]
  \\ FULL_SIMP_TAC std_ss [one_rev_list_def,STAR_ASSOC] \\ ONCE_REWRITE_TAC [EQ_SYM_EQ]
  \\ ONCE_REWRITE_TAC [arm_sub_id_def] \\ SIMP_TAC std_ss [LET_DEF,MULT_CLAUSES,WORD_SUB_RZERO]
  \\ FULL_SIMP_TAC (std_ss++SIZES_ss) [WORD_EQ_SUB_CANCEL,MULT_CLAUSES,n2w_11]
  \\ FULL_SIMP_TAC std_ss [WORD_SUB_PLUS,GSYM word_add_n2w,single_add_eq,single_sub_def] \\ SEP_R_TAC
  \\ `SND (add_with_carry (h',~h,sc)) = (c1,SND (SND (add_with_carry (h',~h,sc))))` by
        (EXPAND_TAC \\ ASM_SIMP_TAC std_ss [])
  \\ PURE_ONCE_ASM_REWRITE_TAC [] \\ SEP_I_TAC "arm_sub_id1" \\ SEP_TAC []
  \\ POP_ASSUM MP_TAC \\ ASM_SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC \\ SEP_W_TAC \\ SEP_F_TAC
  \\ `4 * LENGTH xs < 4294967296` by DECIDE_TAC \\ ASM_SIMP_TAC std_ss []
  \\ REPEAT STRIP_TAC \\ ASM_SIMP_TAC std_ss [] \\ EXPAND_TAC \\ SEP_TAC [one_rev_list_def]);

val arm_sub_id_thm = prove(
  ``!r1 r2 r3 r4 r5 f sc sv xs ys zs qs p.
      (LENGTH ys = LENGTH xs) /\
      (4 * LENGTH xs < 4294967296) /\ ALIGNED r3 /\ ALIGNED r4 /\
      (one_rev_list r3 xs * one_rev_list r4 ys * p) (fun2set (f,df)) ==>
      ?r1i r2i r4i sni svi szi fi.
        arm_sub_id_pre (n2w (LENGTH xs),r2,r3,r4,df,f) /\
        (arm_sub_id (n2w (LENGTH xs),r2,r3,r4,df,f) = (df,fi)) /\
        (one_rev_list r3 (FST (mw_sub xs ys T)) * one_rev_list r4 ys * p) (fun2set (fi,df))``,
  REPEAT STRIP_TAC \\ SIMP_TAC std_ss [] \\ ONCE_REWRITE_TAC [arm_sub_id_def]
  \\ SIMP_TAC std_ss [LET_DEF,WORD_0_LS,WORD_MUL_LSL,word_mul_n2w]
  \\ ASSUME_TAC (GEN_ALL arm_sub_id1_thm)
  \\ SEP_I_TAC "arm_sub_id1" \\ SEP_F_TAC \\ ASM_SIMP_TAC std_ss []
  \\ `?zs d. mw_sub xs ys T = (zs,d)` by METIS_TAC [PAIR]
  \\ ASM_SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC \\ ASM_SIMP_TAC std_ss []);


(* mwi_sub *)

val (arm_sub_th,arm_sub_def) = decompile_io_strings arm_tools_no_status "arm_sub"
  (SOME (``(r1:word32,r2:word32,r3:word32,r4:word32,r5:word32,df:word32 set,f:word32->word32)``,
         ``(r5:word32,df:word32 set,f:word32->word32)``)) (assemble "arm" `

    mov r7,r3
    subs r6,r4,#0
    add r3,r3,r1,lsl #2
    add r4,r4,r2,lsl #2
    b L0

L1: ldr r1,[r3],#-4
    ldr r2,[r4],#-4
    sbcs r1,r1,r2
    str r1,[r5],#-4
L0: teq r6,r4
    bne L1

L2: teq r7,r3
    beq L3
    ldr r1,[r3],#-4
    sbcs r1,r1,#0
    str r1,[r5],#-4
    b L2

L3: ldr r3, [r5, #4]!
    cmp r3, #0
    beq L3
    sub r5, r5, #4

  `)


val arm_sub1_thm = prove(
  ``!r1 r2 r3 r4 r5 f sc sv xs ys zs qs p.
      (mw_sub xs ys sc = (zs,d)) /\ (LENGTH qs = LENGTH xs) /\ (LENGTH ys = LENGTH xs) /\
      (4 * LENGTH xs < 4294967296) /\ ALIGNED r3 /\ ALIGNED r4 /\ ALIGNED r5 /\
      (one_rev_list r3 xs * one_rev_list r4 ys * one_rev_list r5 qs * p) (fun2set (f,df)) ==>
      ?r1i r2i r4i sni svi szi fi.
        arm_sub1_pre (r1,r2,r3,r4,r5,r4 - n2w (4 * LENGTH xs),df,f,sc,sv) /\
        (arm_sub1 (r1,r2,r3,r4,r5,r4 - n2w (4 * LENGTH xs),df,f,sc,sv) =
          (r1i,r2i,r3 - n2w (4 * LENGTH xs),r4 - n2w (4 * LENGTH xs),r5 - n2w (4 * LENGTH xs),r4i,df,fi,d,sni,svi,szi)) /\
        (one_rev_list r3 xs * one_rev_list r4 ys * one_rev_list r5 zs * p) (fun2set (fi,df))``,
  Induct_on `xs` \\ Cases_on `ys` \\ Cases_on `qs`
  \\ SIMP_TAC std_ss [LENGTH,DECIDE ``~(SUC n = 0)``,NOT_CONS_NIL,mw_sub_def,HD,TL]
  \\ TRY (BasicProvers.LET_ELIM_TAC) \\ ONCE_REWRITE_TAC [EQ_SYM_EQ]
  \\ FULL_SIMP_TAC std_ss [one_rev_list_def,STAR_ASSOC] \\ ONCE_REWRITE_TAC [EQ_SYM_EQ]
  \\ ONCE_REWRITE_TAC [arm_sub_def] \\ SIMP_TAC std_ss [LET_DEF,MULT_CLAUSES,WORD_SUB_RZERO]
  \\ FULL_SIMP_TAC (std_ss++SIZES_ss) [WORD_EQ_SUB_CANCEL,MULT_CLAUSES,n2w_11]
  \\ FULL_SIMP_TAC std_ss [WORD_SUB_PLUS,GSYM word_add_n2w,single_add_eq,single_sub_def] \\ SEP_R_TAC
  \\ `SND (add_with_carry (h'',~h,sc)) = (c1,SND (SND (add_with_carry (h'',~h,sc))))` by
        (EXPAND_TAC \\ ASM_SIMP_TAC std_ss [])
  \\ PURE_ONCE_ASM_REWRITE_TAC [] \\ SEP_I_TAC "arm_sub1" \\ SEP_TAC []
  \\ POP_ASSUM MP_TAC \\ ASM_SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC \\ SEP_W_TAC \\ SEP_F_TAC
  \\ `4 * LENGTH xs < 4294967296` by DECIDE_TAC \\ ASM_SIMP_TAC std_ss []
  \\ REPEAT STRIP_TAC \\ ASM_SIMP_TAC std_ss [] \\ EXPAND_TAC \\ SEP_TAC [one_rev_list_def]);

val arm_sub2_thm = prove(
  ``!r1 r3 r5 f sc sv xs zs qs p.
      (mw_sub xs (MAP (\x.0w) xs) sc = (zs,d)) /\ (LENGTH qs = LENGTH xs) /\
      (LENGTH xs < 1073741824) /\ ALIGNED r3 /\ ALIGNED r5 /\
      (one_rev_list r3 xs * one_rev_list r5 qs * p) (fun2set (f,df)) ==>
      ?r1i r2i r4i sni svi szi fi.
        arm_sub2_pre (r1,r3,r5,r3 - n2w (4 * LENGTH xs),df,f,sc,sv) /\
        (arm_sub2 (r1,r3,r5,r3 - n2w (4 * LENGTH xs),df,f,sc,sv) =
          (r1i,r3 - n2w (4 * LENGTH xs),r5 - n2w (4 * LENGTH xs),r4i,df,fi,d,sni,svi,szi)) /\
        (one_rev_list r3 xs * one_rev_list r5 zs * p) (fun2set (fi,df))``,
  Induct_on `xs` THEN1
   (SIMP_TAC std_ss [mw_sub_def,MAP,LENGTH_NIL,LENGTH,WORD_SUB_RZERO]
    \\ ONCE_REWRITE_TAC [arm_sub_def] \\ SIMP_TAC std_ss [LET_DEF])
  \\ Cases_on `qs`
  \\ SIMP_TAC std_ss [LENGTH,DECIDE ``~(SUC n = 0)``,NOT_CONS_NIL,mw_sub_def,MAP,HD,TL]
  \\ BasicProvers.LET_ELIM_TAC
  \\ ONCE_REWRITE_TAC [arm_sub_def]
  \\ ASM_SIMP_TAC std_ss [LET_DEF,WORD_EQ_SUB_CANCEL,WORD_4_MULT_EQ_0,DECIDE ``~(SUC n = 0)``]
  \\ FULL_SIMP_TAC std_ss [one_rev_list_def,STAR_ASSOC,MULT_CLAUSES,GSYM word_add_n2w]
  \\ FULL_SIMP_TAC std_ss [WORD_SUB_PLUS,single_add_eq,single_sub_def,EVAL ``~0w:word32``]
  \\ SEP_TAC [] \\ IMP_RES_TAC (DECIDE ``SUC n < k ==> n < k``)
  \\ ONCE_REWRITE_TAC [Q.ISPEC `x:bool#bool` (GSYM pairTheory.PAIR)]
  \\ SEP_I_TAC "arm_sub2" \\ SEP_W_TAC \\ SEP_F_TAC
  \\ SEP_TAC [] \\ REPEAT STRIP_TAC \\ EXPAND_TAC \\ ASM_SIMP_TAC std_ss []
  \\ SEP_TAC [one_rev_list_def]);

val LENGTH_mw_trailing = prove(
  ``!xs. LENGTH (mw_trailing xs) <= LENGTH xs``,
  HO_MATCH_MP_TAC SNOC_INDUCT \\ REPEAT STRIP_TAC \\ ONCE_REWRITE_TAC [mw_trailing_def]
  \\ SRW_TAC [] [NOT_NIL_SNOC,LAST_SNOC,FRONT_SNOC] \\ DECIDE_TAC);

val arm_sub3_thm = prove(
  ``!xs r5 p df f.
      ALIGNED r5 /\ ~(EVERY (\x. x = 0w) xs) /\
      (one_rev_list (r5 + n2w (4 * LENGTH xs)) xs * p) (fun2set (f,df)) ==>
      ?ts r3i s1 s2 s3 s4.
           arm_sub3_pre (r5,df,f) /\
           (arm_sub3 (r5,df,f) = (r3i,r5 + n2w (4 * LENGTH ts) + 4w,df,f,s1,s2,s3,s4)) /\
           (LENGTH ts = LENGTH xs - LENGTH (mw_trailing xs)) /\
           (one_rev_list (r5 + n2w (4 * LENGTH ts)) ts *
            one_rev_list (r5 + n2w (4 * LENGTH xs)) (mw_trailing xs) * p) (fun2set (f,df))``,
  HO_MATCH_MP_TAC SNOC_INDUCT \\ FULL_SIMP_TAC std_ss [EVERY_DEF] \\ REPEAT STRIP_TAC
  \\ Cases_on `~(x = 0w)` THEN1
   (ONCE_REWRITE_TAC [arm_sub_def,mw_trailing_def]
    \\ FULL_SIMP_TAC std_ss [LAST_SNOC,FRONT_SNOC,NOT_NIL_SNOC] \\ Q.EXISTS_TAC `[]`
    \\ FULL_SIMP_TAC std_ss [LENGTH_SNOC,MULT_CLAUSES,GSYM word_add_n2w,WORD_ADD_ASSOC]
    \\ FULL_SIMP_TAC std_ss [one_rev_list_APPEND,SNOC_APPEND,LET_DEF,ALIGNED_INTRO,
         ALIGNED,WORD_ADD_SUB,one_rev_list_def,word_mul_n2w] \\ SEP_TAC [LENGTH,WORD_ADD_0])
  \\ ONCE_REWRITE_TAC [arm_sub_def,mw_trailing_def]
  \\ FULL_SIMP_TAC std_ss [LAST_SNOC,FRONT_SNOC,NOT_NIL_SNOC,LET_DEF,ALL_EL_SNOC]
  \\ FULL_SIMP_TAC std_ss [LENGTH_SNOC,MULT_CLAUSES,GSYM word_add_n2w,WORD_ADD_ASSOC]
  \\ FULL_SIMP_TAC std_ss [one_rev_list_APPEND,SNOC_APPEND,LET_DEF,ALIGNED_INTRO,
         ALIGNED,WORD_ADD_SUB,one_rev_list_def,word_mul_n2w] \\ SEP_TAC []
  \\ SEP_I_TAC "arm_sub3" \\ SEP_F_TAC \\ SEP_TAC [] \\ REPEAT STRIP_TAC \\ ASM_SIMP_TAC std_ss []
  \\ Q.EXISTS_TAC `SNOC 0w ts`
  \\ ASM_SIMP_TAC std_ss [LENGTH_SNOC,MULT_CLAUSES,WORD_ADD_ASSOC,GSYM word_add_n2w]
  \\ FULL_SIMP_TAC std_ss [one_rev_list_APPEND,SNOC_APPEND,LET_DEF,ALIGNED_INTRO,
         ALIGNED,WORD_ADD_SUB,one_rev_list_def] \\ SEP_TAC []
  \\ STRIP_TAC THEN1 (`LENGTH (mw_trailing xs) <= LENGTH xs` by METIS_TAC [LENGTH_mw_trailing] \\ DECIDE_TAC)
  \\ POP_ASSUM MP_TAC \\ ASM_SIMP_TAC (std_ss++star_ss) [word_mul_n2w,WORD_ADD_SUB]);

val LENGTH_mw_sub = prove(
  ``!xs ys c zs d. (mw_sub xs ys c = (zs,d)) ==> (LENGTH xs = LENGTH zs)``,
  Induct \\ SIMP_TAC std_ss [mw_sub_def,LENGTH] \\ REPEAT STRIP_TAC
  \\ Cases_on `single_sub h (HD ys) c` \\ FULL_SIMP_TAC std_ss [LET_DEF]
  \\ Cases_on `mw_sub xs (TL ys) r` \\ FULL_SIMP_TAC std_ss [] \\ RES_TAC
  \\ EXPAND_TAC \\ FULL_SIMP_TAC std_ss [LENGTH]);

val mw_trailing_NIL = store_thm("mw_trailing_NIL",
  ``!xs. (mw_trailing xs = []) = EVERY (\x. x = 0w) xs``,
  HO_MATCH_MP_TAC SNOC_INDUCT \\ REPEAT STRIP_TAC
  \\ ONCE_REWRITE_TAC [mw_trailing_def] \\ SIMP_TAC std_ss [ALL_EL_SNOC,EVERY_DEF]
  \\ Cases_on `x = 0w` \\ ASM_SIMP_TAC std_ss [NOT_SNOC_NIL,LAST_SNOC,FRONT_SNOC]);

val arm_sub_thm = prove(
  ``(mw_subv xs ys = zs) /\ LENGTH ys <= LENGTH xs /\ LENGTH xs < 1073741824 /\ ~(zs = []) /\
    (LENGTH res = LENGTH xs) /\ ALIGNED r3 /\ ALIGNED r4 /\ ALIGNED r5 /\
    (one_list_rev_old r3 xs * one_list_rev_old r4 ys * one_rev_list r5 res * p) (fun2set (f,df)) ==>
    ?fi ts.
       arm_sub_pre (n2w (LENGTH xs),n2w (LENGTH ys),r3,r4,r5,df,f) /\
       (arm_sub (n2w (LENGTH xs),n2w (LENGTH ys),r3,r4,r5,df,f) = (r5 - n2w (4 * LENGTH zs),df,fi)) /\
       (LENGTH ts = LENGTH xs - LENGTH zs) /\
       (one_list_rev_old r3 xs * one_list_rev_old r4 ys *
        one_rev_list r5 zs * one_rev_list (r5 - n2w (4 * LENGTH zs)) ts * p) (fun2set (fi,df))``,
  REPEAT STRIP_TAC \\ IMP_RES_TAC APPEND_EXISTS
  \\ FULL_SIMP_TAC std_ss [mw_subv_def,mw_sub2_def,FIRSTN_LENGTH_APPEND,BUTFIRSTN_LENGTH_APPEND]
  \\ `?zs1 c2. mw_sub xs1 ys T = (zs1,c2)` by METIS_TAC [PAIR]
  \\ `?zs2 c3. mw_sub xs2 (MAP (\x.0w) xs2) c2 = (zs2,c3)` by METIS_TAC [PAIR]
  \\ FULL_SIMP_TAC std_ss [LET_DEF]
  \\ PURE_ONCE_REWRITE_TAC [arm_sub_def] \\ SIMP_TAC std_ss [LET_DEF,WORD_MUL_LSL,word_mul_n2w]
  \\ ASSUME_TAC (GEN_ALL arm_sub1_thm)
  \\ Q.ABBREV_TAC `r4i = r4 + n2w (4 * LENGTH xs1)` \\ FULL_SIMP_TAC std_ss [WORD_0_LS]
  \\ `r4 = (r4 + n2w (4 * LENGTH xs1)) - n2w (4 * LENGTH xs1)` by METIS_TAC [WORD_ADD_SUB]
  \\ ONCE_ASM_REWRITE_TAC [] \\ Q.UNABBREV_TAC `r4i`
  \\ SEP_I_TAC "arm_sub1" \\ FULL_SIMP_TAC std_ss [WORD_ADD_SUB]
  \\ `?res1 res2. (res = res1 ++ res2) /\ (LENGTH res1 = LENGTH xs1) /\ (LENGTH res2 = LENGTH xs2)` by ALL_TAC THEN1
     (FULL_SIMP_TAC std_ss [LENGTH_APPEND]
      \\ `LENGTH xs1 <= LENGTH res` by DECIDE_TAC \\ IMP_RES_TAC APPEND_EXISTS
      \\ Q.EXISTS_TAC `xs1'` \\ Q.EXISTS_TAC `xs2'` \\ FULL_SIMP_TAC std_ss [LENGTH_APPEND])
  \\ FULL_SIMP_TAC std_ss [one_rev_list_APPEND,one_list_rev_old_def]
  \\ SEP_F_TAC \\ SEP_TAC []
  \\ SIMP_TAC bool_ss [GSYM (EVAL ``4 * 1073741824``),LT_MULT_LCANCEL]
  \\ `LENGTH xs1 < 1073741824 /\ LENGTH xs2 < 1073741824` by
        (FULL_SIMP_TAC std_ss [LENGTH_APPEND] \\ DECIDE_TAC) \\ FULL_SIMP_TAC std_ss []
  \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss []
  \\ (ASSUME_TAC o GEN_ALL o RW[WORD_ADD_SUB] o SUBST_INST
        [``r3:word32``|->``r3 + n2w (4 * LENGTH (xs:word32 list)):word32``,
         ``xs:word32 list``|->``xs:word32 list``]) arm_sub2_thm
  \\ `!r w v. r + w + v - w = r + v:word32` by METIS_TAC [WORD_ADD_SUB,WORD_ADD_COMM,WORD_ADD_ASSOC]
  \\ FULL_SIMP_TAC std_ss [LENGTH_APPEND,LEFT_ADD_DISTRIB,GSYM word_add_n2w,WORD_ADD_ASSOC]
  \\ SEP_I_TAC "arm_sub2"
  \\ POP_ASSUM MP_TAC \\ ASM_SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [word_mul_n2w]
  \\ SEP_F_TAC \\ SEP_TAC [] \\ REPEAT STRIP_TAC \\ ASM_SIMP_TAC std_ss []
  \\ IMP_RES_TAC LENGTH_mw_sub \\ FULL_SIMP_TAC std_ss []
  \\ ASSUME_TAC ((RW [one_rev_list_APPEND] o Q.SPEC `zs1 ++ zs2`) arm_sub3_thm)
  \\ SEP_I_TAC "arm_sub3"
  \\ FULL_SIMP_TAC std_ss [GSYM WORD_SUB_PLUS,word_add_n2w,LENGTH_APPEND,
        GSYM LEFT_ADD_DISTRIB,WORD_SUB_ADD,word_mul_n2w]
  \\ SEP_F_TAC \\ SEP_TAC [GSYM mw_trailing_NIL] \\ REPEAT STRIP_TAC
  \\ ASM_SIMP_TAC std_ss [WORD_ADD_SUB] \\ Q.EXISTS_TAC `ts`
  \\ ASM_SIMP_TAC std_ss []
  \\ REV (`r5 - n2w (4 * (LENGTH zs1 + LENGTH zs2)) + n2w (4 * LENGTH ts) =
           r5 - n2w (4 * LENGTH zs)` by ALL_TAC)
  THEN1 (FULL_SIMP_TAC std_ss [] \\ SEP_TAC [] \\ METIS_TAC [])
  \\ ASM_SIMP_TAC std_ss [] \\ ASM_SIMP_TAC std_ss [word_arith_lemma3,GSYM LEFT_SUB_DISTRIB]
  \\ `LENGTH zs <= LENGTH (zs1 ++ zs2)` by METIS_TAC [LENGTH_mw_trailing]
  \\ FULL_SIMP_TAC std_ss [LENGTH_APPEND,DECIDE ``0<n = ~(n = 0:num)``,LENGTH_NIL]
  \\ `LENGTH zs1 + LENGTH zs2 - (LENGTH zs1 + LENGTH zs2 - LENGTH zs) = LENGTH zs` by DECIDE_TAC
  \\ ASM_SIMP_TAC std_ss [] \\ Cases_on `zs1 = []` \\ Cases_on `zs2 = []`
  \\ FULL_SIMP_TAC std_ss [GSYM LENGTH_NIL,LENGTH]);


(* mwi_add *)

val _ = codegenLib.add_compiled [arm_add_th,arm_sub_th];

val mk_header_def = Define `
  mk_header (c,c2,ah:word32) = ((c - c2) << 8) !! (ah && 7w)`;

val (* ( *)arm_iadd_def(*,arm_iadd_pre_def)*) = Define `
  arm_iadd (ah,bh,a,b,c,df,f) =
    if (ah ?? bh) && 7w = 0w then
      let (c,df,f) = arm_add (ah >>> 10,bh >>> 10,a,b,c,df,f) in
        (ah,c,df,f)
    else
      let (x,y,df,f) = arm_compare (a+4w,b+4w,ah >>> 10,bh >>> 10,df,f) in
        if x = y then (2w,c,df,f) else
          let (ah,bh,a,b) = (if x <+ y then (bh,ah,b,a) else (ah,bh,a,b)) in
          let (c,df,f) = arm_sub (ah >>> 10,bh >>> 10,a,b,c,df,f) in
            (ah,c,df,f)`;

val mwi_header_LO = prove(
  ``LENGTH xs < 4194304 /\ LENGTH ys < 4194304 ==>
    (mwi_header (y,xs) <+ mwi_header (y,ys) = ~(LENGTH ys <= LENGTH xs))``,
  SIMP_TAC (std_ss++SIZES_ss) [mwi_header_def,WORD_LO,w2n_n2w,GSYM NOT_LESS] \\ REPEAT STRIP_TAC
  \\ `LENGTH xs * 1024 + (if y then 4 else 0) + 2 < 4294967296 /\
      LENGTH ys * 1024 + (if y then 4 else 0) + 2 < 4294967296` by
        (Cases_on `y` \\ FULL_SIMP_TAC std_ss [] \\ DECIDE_TAC)
  \\ ASM_SIMP_TAC std_ss []);

val LENGTH_mw_addv = prove(
  ``!xs ys c zs.
      (mw_addv xs ys c = zs) ==>
      (LENGTH xs = LENGTH zs) \/ (SUC (LENGTH xs) = LENGTH zs)``,
  SIMP_TAC std_ss [] \\ Induct
  THEN1 (SIMP_TAC std_ss [mw_addv_def] \\ Cases \\ SIMP_TAC std_ss [LENGTH])
  \\ SRW_TAC [] [mw_addv_def,LENGTH]
  \\ FULL_SIMP_TAC std_ss [LENGTH,METIS_PROVE [] ``b \/ c = (~b ==> c)``]);

val SUC_LENGTH_LESS_EQ_IMP = prove(
  ``SUC (LENGTH zs) <= LENGTH res ==>
    ?r res1 res2. (LENGTH res1 = LENGTH zs) /\ (res = res1 ++ [r] ++ res2)``,
  Cases_on `res = []` \\ ASM_SIMP_TAC std_ss [LENGTH,DECIDE ``~(SUC n = 0)``]
  \\ REPEAT STRIP_TAC \\ IMP_RES_TAC LESS_EQ_EXISTS_APPEND
  \\ Cases_on `xs1 = []` \\ FULL_SIMP_TAC std_ss [LENGTH,DECIDE ``~(SUC n = 0)``]
  \\ `?r res2. xs1 = SNOC r res2` by METIS_TAC [SNOC_CASES]
  \\ FULL_SIMP_TAC std_ss [LENGTH_SNOC] \\ METIS_TAC [SNOC_APPEND]);

val LENGTH_LESS_EQ_IMP = prove(
  ``LENGTH (zs:word32 list) <= LENGTH (res:word32 list) ==>
    ?res1 res2. (LENGTH res1 = LENGTH zs) /\ (res = res1 ++ res2)``,
  REPEAT STRIP_TAC \\ IMP_RES_TAC LESS_EQ_EXISTS_APPEND \\ METIS_TAC []);

val LESS_EQ_IMP_MAX = prove(
  ``!m n. m <= n ==> (MAX m n = n) /\ (MAX n m = n)``,
  SIMP_TAC std_ss [MAX_DEF] \\ DECIDE_TAC);

val LESS_IMP_MAX = prove(
  ``!m n. m < n ==> (MAX m n = n) /\ (MAX n m = n)``,
  SIMP_TAC std_ss [MAX_DEF] \\ DECIDE_TAC);

val LENGTH_TAKE_LESS_EQ = prove(
  ``!xs k. LENGTH (TAKE k xs) <= k /\ LENGTH (TAKE k xs) <= LENGTH xs``,
  Induct \\ SIMP_TAC std_ss [TAKE_def,LENGTH] \\ REPEAT STRIP_TAC
  \\ Cases_on `k` \\ ASM_SIMP_TAC std_ss [TAKE_def,LENGTH,ADD1]);

val LENGTH_mw_subv = prove(
  ``!xs ys. LENGTH (mw_subv xs ys) <= LENGTH (xs:'a word list)``,
  SIMP_TAC std_ss [mw_subv_def] \\ REPEAT STRIP_TAC
  \\ MATCH_MP_TAC (MATCH_MP (DECIDE ``m <= n ==> n <= p ==> m <= p:num``)
       (SPEC_ALL LENGTH_mw_trailing))
  \\ SIMP_TAC std_ss [mw_sub2_def]
  \\ `?ts d. mw_sub (TAKE (LENGTH ys) xs) ys T = (ts,d)` by METIS_TAC [PAIR]
  \\ `?ts2 d2. mw_sub (DROP (LENGTH ys) xs)
           (MAP (\x. 0x0w) (DROP (LENGTH ys) xs)) d = (ts2,d2)` by METIS_TAC [PAIR]
  \\ ASM_SIMP_TAC std_ss [LET_DEF,LENGTH_APPEND]
  \\ IMP_RES_TAC LENGTH_mw_sub \\ FULL_SIMP_TAC std_ss [LENGTH_DROP]
  \\ `LENGTH (TAKE (LENGTH (ys:'a word list)) xs) <= LENGTH ys /\
      LENGTH (TAKE (LENGTH (ys:'a word list)) xs) <= LENGTH xs` by METIS_TAC [LENGTH_TAKE_LESS_EQ]
  \\ DECIDE_TAC);

fun COND_TAC p (t1:tactic) (t2:tactic) g = if p g then t1 g else t2 g;
fun HAS_ASSUM x (hs,g) = mem x hs

val arm_iadd_thm = prove(
  ``(mwi_add (x,xs) (y,ys) = (z,zs)) /\ LENGTH xs < 4194304 /\ LENGTH ys < 4194304 /\
    (SUC (MAX (LENGTH xs) (LENGTH ys)) <= LENGTH res) /\ LENGTH ys <= LENGTH xs /\
    ALIGNED xp /\ ALIGNED yp /\ ALIGNED zp /\ mw_ok xs /\ mw_ok ys /\
    (one_list_rev_old xp xs * one_list_rev_old yp ys * one_rev_list zp res * p) (fun2set (f,df)) ==>
    ?fi ts q.
      (arm_iadd (mwi_header(x,xs),mwi_header(y,ys),xp,yp,zp,df,f) =
        (q,zp - n2w (4 * LENGTH zs),df,fi)) /\ (q ' 2 = z) /\
      (LENGTH ts = LENGTH res - LENGTH zs) /\
      (one_list_rev_old xp xs * one_list_rev_old yp ys *
       one_rev_list zp zs * one_rev_list (zp - n2w (4 * LENGTH zs)) ts * p) (fun2set (fi,df))``,
  SIMP_TAC std_ss [mwi_add_def,arm_iadd_def,WORD_RIGHT_AND_OVER_XOR,WORD_EQ_XOR_ZERO,
    mwi_header_EQ] \\ Cases_on `x = y` \\ ASM_SIMP_TAC std_ss [mwi_header_LO] THEN1
   (Cases_on `LENGTH ys <= LENGTH xs` \\ ASM_SIMP_TAC std_ss [LET_DEF,mwi_header_length]
    \\ FULL_SIMP_TAC std_ss [DECIDE ``~(m <= n) = n < m:num``]
    \\ ASM_SIMP_TAC std_ss [MAX_DEF,DECIDE ``m<=n ==> ~(n < m:num)``] \\ REPEAT STRIP_TAC
    \\ IMP_RES_TAC (DECIDE ``n < 4194304 ==> n < 1073741824``)
    \\ ASSUME_TAC (GEN_ALL arm_add_thm) \\ SEP_I_TAC "arm_add"
    \\ POP_ASSUM MP_TAC \\ ASM_SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC
    \\ IMP_RES_TAC LENGTH_mw_addv \\ FULL_SIMP_TAC std_ss []
    \\ COND_TAC (HAS_ASSUM ``SUC (LENGTH (zs:word32 list)) <= LENGTH (res:word32 list)``)
         (IMP_RES_TAC SUC_LENGTH_LESS_EQ_IMP)
         (STRIP_ASSUME_TAC (UNDISCH LENGTH_LESS_EQ_IMP))
    \\ FULL_SIMP_TAC std_ss [one_rev_list_APPEND,word_mul_n2w]
    \\ SEP_F_TAC \\ FULL_SIMP_TAC std_ss [GSYM SNOC_APPEND,LENGTH_SNOC,LENGTH_APPEND]
    \\ FULL_SIMP_TAC std_ss [GSYM NOT_LESS,DECIDE ``m < n ==> ~(n < m:num)``,LENGTH]
    \\ REPEAT STRIP_TAC
    \\ ASM_SIMP_TAC std_ss [LENGTH_NIL,DECIDE ``SUC n - n = 1``,mwi_header_sign_index]
    \\ SEP_TAC [hd (CONJUNCTS one_rev_list_def)]
    \\ COND_TAC (HAS_ASSUM ``res = res1 ++ res2:word32 list``)
         (Q.EXISTS_TAC `res2`)
         (Q.EXISTS_TAC `[r]++res2`)
    \\ FULL_SIMP_TAC std_ss [LENGTH,one_rev_list_APPEND,word_mul_n2w,
         GSYM WORD_SUB_PLUS,word_add_n2w,LEFT_ADD_DISTRIB,LENGTH,LENGTH_APPEND]
    \\ SEP_TAC [] \\ DECIDE_TAC)
  \\ SIMP_TAC std_ss [mwi_header_length] \\ REPEAT STRIP_TAC
  \\ IMP_RES_TAC (DECIDE ``n < 4194304 ==> n < 1073741824 /\ n < 4294967296``)
  \\ ASSUME_TAC (GEN_ALL (arm_compare_thm)) \\ FULL_SIMP_TAC std_ss [one_list_rev_old_EQ]
  \\ SEP_I_TAC "arm_compare" \\ SEP_F_TAC
  \\ ASM_SIMP_TAC std_ss [ALIGNED] \\ REPEAT STRIP_TAC \\ ASM_SIMP_TAC std_ss [LET_DEF]
  \\ Cases_on `mw2n ys = mw2n xs` THEN1
   (`r4 = r5` by METIS_TAC [mw_compare_thm,optionTheory.NOT_NONE_SOME]
    \\ FULL_SIMP_TAC std_ss [] \\ EXPAND_TAC \\ Q.EXISTS_TAC `res`
    \\ FULL_SIMP_TAC std_ss [LENGTH,hd (CONJUNCTS one_rev_list_def),WORD_SUB_RZERO]
    \\ STRIP_TAC THEN1 EVAL_TAC \\ SEP_TAC [])
  \\ `(r4 <+ r5 = mw2n xs < mw2n ys) /\ ~(r4 = r5)` by
      METIS_TAC [mw_compare_thm,optionTheory.NOT_NONE_SOME,optionTheory.SOME_11]
  \\ ASM_SIMP_TAC std_ss []
  \\ `mw2n xs < mw2n ys \/ mw2n ys < mw2n xs` by DECIDE_TAC
  \\ FULL_SIMP_TAC std_ss [mwi_header_length,GSYM one_list_rev_old_EQ,
       DECIDE ``m < n ==> ~(n < m:num)``]
  \\ ASSUME_TAC (GEN_ALL arm_sub_thm) \\ SEP_I_TAC "arm_sub"
  \\ POP_ASSUM MP_TAC \\ IMP_RES_TAC mw2n_LESS_IMP_LENGTH_LESS_EQ
  \\ FULL_SIMP_TAC std_ss [LESS_EQ_IMP_MAX]
  \\ IMP_RES_TAC SUC_LENGTH_LESS_EQ_IMP
  \\ FULL_SIMP_TAC std_ss [LENGTH_APPEND,LENGTH,ADD_CLAUSES,ADD1,mw_subv_NOT_NIL,LENGTH]
  \\ FULL_SIMP_TAC std_ss [one_rev_list_APPEND] \\ REPEAT STRIP_TAC \\ SEP_F_TAC
  \\ `LENGTH (mw_subv ys xs) <= LENGTH ys` by ASM_SIMP_TAC std_ss [LENGTH_mw_subv]
  \\ `LENGTH (mw_subv xs ys) <= LENGTH xs` by ASM_SIMP_TAC std_ss [LENGTH_mw_subv]
  \\ IMP_RES_TAC LENGTH_mw_subv
  \\ ASM_SIMP_TAC std_ss [LENGTH,LENGTH_APPEND,word_mul_n2w]
  \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [GSYM NOT_LESS]
  \\ FULL_SIMP_TAC std_ss [DECIDE ``m < n ==> ~(n < m:num)``]
  \\ EXPAND_TAC \\ FULL_SIMP_TAC std_ss []
  \\ Q.EXISTS_TAC `ts ++ [r] ++ res2`  \\ ASM_SIMP_TAC std_ss [LENGTH_APPEND,LENGTH]
  \\ FULL_SIMP_TAC std_ss [word_mul_n2w,mwi_header_sign_index,
         METIS_PROVE [] ``(x = ~y) = ~(x = y)``]
  \\ FULL_SIMP_TAC std_ss [SNOC_APPEND,one_rev_list_APPEND,word_mul_n2w,LENGTH,
         GSYM WORD_SUB_PLUS,word_add_n2w,GSYM LEFT_ADD_DISTRIB,LENGTH_APPEND]
  \\ (STRIP_TAC THEN1 DECIDE_TAC
      \\ IMP_RES_TAC (DECIDE ``~(n < m) ==> (m + (n - m) = n:num) /\ (m + (n - m + 1) = n + 1:num)``)
      \\ ASM_SIMP_TAC std_ss []
      \\ SEP_TAC []));

val arm_iadd_alias_thm = prove(
  ``(mwi_add (x,xs) (y,xs) = (z,zs)) /\ LENGTH xs < 4194304 /\
    (SUC (LENGTH xs) <= LENGTH res) /\
    ALIGNED xp /\ ALIGNED zp /\ mw_ok xs /\
    (one_list_rev_old xp xs * one_rev_list zp res * p) (fun2set (f,df)) ==>
    ?fi ts q.
      (arm_iadd (mwi_header(x,xs),mwi_header(y,xs),xp,xp,zp,df,f) =
        (q,zp - n2w (4 * LENGTH zs),df,fi)) /\ (q ' 2 = z) /\
      (LENGTH ts = LENGTH res - LENGTH zs) /\
      (one_list_rev_old xp xs *
       one_rev_list zp zs * one_rev_list (zp - n2w (4 * LENGTH zs)) ts * p) (fun2set (fi,df))``,
  SIMP_TAC std_ss [mwi_add_def,arm_iadd_def,WORD_RIGHT_AND_OVER_XOR,WORD_EQ_XOR_ZERO,
    mwi_header_EQ] \\ Cases_on `x = y` \\ ASM_SIMP_TAC std_ss [mwi_header_LO] THEN1
   (ASM_SIMP_TAC std_ss [LET_DEF,mwi_header_length]
    \\ FULL_SIMP_TAC std_ss [DECIDE ``~(m <= n) = n < m:num``]
    \\ ASM_SIMP_TAC std_ss [MAX_DEF,DECIDE ``m<=n ==> ~(n < m:num)``] \\ REPEAT STRIP_TAC
    \\ IMP_RES_TAC (DECIDE ``n < 4194304 ==> n < 1073741824``)
    \\ ASSUME_TAC (GEN_ALL arm_add_alias_thm) \\ SEP_I_TAC "arm_add"
    \\ POP_ASSUM MP_TAC \\ ASM_SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC
    \\ IMP_RES_TAC LENGTH_mw_addv \\ FULL_SIMP_TAC std_ss []
    \\ COND_TAC (HAS_ASSUM ``SUC (LENGTH (zs:word32 list)) <= LENGTH (res:word32 list)``)
         (IMP_RES_TAC SUC_LENGTH_LESS_EQ_IMP)
         (STRIP_ASSUME_TAC (UNDISCH LENGTH_LESS_EQ_IMP))
    \\ FULL_SIMP_TAC std_ss [one_rev_list_APPEND,word_mul_n2w]
    \\ SEP_F_TAC \\ FULL_SIMP_TAC std_ss [GSYM SNOC_APPEND,LENGTH_SNOC,LENGTH_APPEND]
    \\ FULL_SIMP_TAC std_ss [GSYM NOT_LESS,DECIDE ``m < n ==> ~(n < m:num)``,LENGTH]
    \\ REPEAT STRIP_TAC
    \\ ASM_SIMP_TAC std_ss [LENGTH_NIL,DECIDE ``SUC n - n = 1``,mwi_header_sign_index]
    \\ SEP_TAC [hd (CONJUNCTS one_rev_list_def)]
    \\ COND_TAC (HAS_ASSUM ``res = res1 ++ res2:word32 list``)
         (Q.EXISTS_TAC `res2`)
         (Q.EXISTS_TAC `[r]++res2`)
    \\ FULL_SIMP_TAC std_ss [LENGTH,one_rev_list_APPEND,word_mul_n2w,
         GSYM WORD_SUB_PLUS,word_add_n2w,LEFT_ADD_DISTRIB,LENGTH,LENGTH_APPEND]
    \\ SEP_TAC [] \\ DECIDE_TAC)
  \\ SIMP_TAC std_ss [mwi_header_length] \\ REPEAT STRIP_TAC
  \\ IMP_RES_TAC (DECIDE ``n < 4194304 ==> n < 1073741824 /\ n < 4294967296``)
  \\ ASSUME_TAC (GEN_ALL (arm_compare_alias_thm))
  \\ FULL_SIMP_TAC std_ss [one_list_rev_old_EQ]
  \\ SEP_I_TAC "arm_compare" \\ SEP_F_TAC
  \\ ASM_SIMP_TAC std_ss [ALIGNED] \\ REPEAT STRIP_TAC \\ ASM_SIMP_TAC std_ss [LET_DEF]
  \\ FULL_SIMP_TAC std_ss [] \\ EXPAND_TAC \\ Q.EXISTS_TAC `res`
  \\ FULL_SIMP_TAC std_ss [LENGTH,hd (CONJUNCTS one_rev_list_def),WORD_SUB_RZERO]
  \\ STRIP_TAC THEN1 EVAL_TAC \\ SEP_TAC []);



(* single_mul_add *)

val (arm_sa_mul_th,arm_sa_mul_def) = decompile_io_strings arm_tools "arm_sa_mul"
  (SOME (``(r0:word32,r2:word32,r3:word32,r4:word32)``,
         ``(r2:word32,r3:word32,r4:word32)``)) (assemble "arm" `

    mov r1,#0
    umlal r0,r1,r2,r3
    adds r3,r0,r4
    adc r4,r1,#0

  `)

val word_contcat_0 = prove(
  ``!w. (0w:word32) @@ (w:word32) = (w2w w):word64``,
  WORD_DECIDE_TAC);

val arm_sa_mul_thm = prove(
  ``!p q k s. arm_sa_mul(k,p,q,s) = (p,single_mul_add p q k s)``,
  REPEAT Cases \\ ASM_SIMP_TAC (std_ss++SIZES_ss) [single_mul_add_def,arm_sa_mul_def,
    LET_DEF,w2w_def,w2n_n2w,single_mul_def,mw_add_def,HD,TL,single_add_eq,
    word_contcat_0,word_add_n2w,word_mul_n2w,word_extract_n2w,bitTheory.BITS_THM,
    SIMP_RULE (std_ss++SIZES_ss) [] (INST_TYPE [``:'a``|->``:32``] n2w_mod),
    AC ADD_ASSOC ADD_COMM, AC MULT_ASSOC MULT_COMM]
  \\ SIMP_TAC std_ss [add_with_carry_def,LET_DEF,w2n_n2w]
  \\ ONCE_REWRITE_TAC [GSYM n2w_mod] \\ SIMP_TAC std_ss [MOD_PLUS,ZERO_LT_dimword]
  \\ SIMP_TAC std_ss [AC ADD_ASSOC ADD_COMM, AC MULT_ASSOC MULT_COMM]);


(* mw_mul_pass *)

val arm_mul_pass_def = tailrecLib.tailrec_define ``
  arm_mul_pass (x,yp,zp,k,yl,df:word32 set,f:word32->word32) =
    if yl = 0w:word32 then
      let f = (zp =+ k) f in
        (f,df)
    else
      let (x,y,k) = arm_sa_mul (k,x,f yp,f zp) in
      let f = (zp =+ y) f in
      let yp = yp-4w in
      let zp = zp-4w in
      let yl = yl-4w in
        arm_mul_pass (x,yp,zp,k,yl,df,f)``

val arm_mul_pass_thm = prove(
  ``!ys zs ts x k yp zp res df f p.
      (mw_mul_pass x ys zs k = ts) /\ 4 * LENGTH ys < 4294967296 /\ ~(res = []) /\
      (LENGTH zs = LENGTH ys) /\ ALIGNED yp /\ ALIGNED zp /\
      (one_rev_list yp ys * one_rev_list zp (zs++res) * p) (fun2set (f,df)) ==>
      ?fi. (arm_mul_pass (x,yp,zp,k,n2w (4 * LENGTH ys),df,f) = (fi,df)) /\
           (one_rev_list yp ys * one_rev_list zp (ts++TL res) * p) (fun2set (fi,df))``,
  Induct THEN1
   (SIMP_TAC std_ss [LENGTH,LENGTH_NIL] \\ SIMP_TAC std_ss [mw_mul_pass_def]
    \\ ONCE_REWRITE_TAC [arm_mul_pass_def] \\ SIMP_TAC std_ss [LET_DEF]
    \\ Cases_on `res` \\ ASM_SIMP_TAC std_ss [TL,WORD_SUB_RZERO]
    \\ REPEAT STRIP_TAC \\ EXPAND_TAC
    \\ FULL_SIMP_TAC std_ss [APPEND,one_rev_list_def,SEP_CLAUSES] \\ SEP_WRITE_TAC)
  \\ Cases_on `zs` \\ SIMP_TAC std_ss [DECIDE ``~(SUC n = 0)``,LENGTH]
  \\ ONCE_REWRITE_TAC [RW[arm_sa_mul_thm]arm_mul_pass_def]
  \\ ONCE_REWRITE_TAC [mw_mul_pass_def,HD,TL]
  \\ SIMP_TAC (std_ss++SIZES_ss) [n2w_11,ADD1] \\ REPEAT STRIP_TAC
  \\ `?y1 k1. single_mul_add x h' k h = (y1,k1)` by METIS_TAC [PAIR]
  \\ FULL_SIMP_TAC std_ss [APPEND,one_rev_list_def,HD] \\ SEP_R_TAC
  \\ FULL_SIMP_TAC std_ss [LET_DEF,LEFT_ADD_DISTRIB,GSYM word_add_n2w,WORD_ADD_SUB,TL]
  \\ ONCE_REWRITE_TAC [WORD_ADD_COMM] \\ SIMP_TAC std_ss [WORD_SUB_PLUS]
  \\ `4 * LENGTH ys < 4294967296` by DECIDE_TAC
  \\ SEP_I_TAC "arm_mul_pass" \\ SEP_W_TAC \\ SEP_F_TAC \\ SEP_TAC []
  \\ REPEAT STRIP_TAC \\ ASM_SIMP_TAC std_ss [APPEND,one_rev_list_def] \\ SEP_TAC []);


(* mw_mul_pass with zero input *)

val arm_mul_pass_zero_def = tailrecLib.tailrec_define ``
  arm_mul_pass_zero (x,yp,zp,k,yl,df:word32 set,f:word32->word32) =
    if yl = 0w:word32 then
      let f = (zp =+ k) f in
        (f,df)
    else
      let (x,y,k) = arm_sa_mul (k,x,f yp,0w) in
      let f = (zp =+ y) f in
      let yp = yp-4w in
      let zp = zp-4w in
      let yl = yl-4w in
        arm_mul_pass_zero (x,yp,zp,k,yl,df,f)``

val arm_mul_pass_zero_thm = prove(
  ``!ys zs ts x k yp zp res df f p.
      (mw_mul_pass x ys (MAP (\x.0w) ys) k = ts) /\ 4 * LENGTH ys < 4294967296 /\ ~(res = []) /\
      (LENGTH zs = LENGTH ys) /\ ALIGNED yp /\ ALIGNED zp /\
      (one_rev_list yp ys * one_rev_list zp (zs++res) * p) (fun2set (f,df)) ==>
      ?fi. (arm_mul_pass_zero (x,yp,zp,k,n2w (4 * LENGTH ys),df,f) = (fi,df)) /\
           (one_rev_list yp ys * one_rev_list zp (ts++TL res) * p) (fun2set (fi,df))``,
  Induct THEN1
   (SIMP_TAC std_ss [LENGTH,LENGTH_NIL] \\ SIMP_TAC std_ss [mw_mul_pass_def]
    \\ ONCE_REWRITE_TAC [arm_mul_pass_zero_def] \\ SIMP_TAC std_ss [LET_DEF]
    \\ Cases_on `res` \\ ASM_SIMP_TAC std_ss [TL,WORD_SUB_RZERO]
    \\ REPEAT STRIP_TAC \\ EXPAND_TAC
    \\ FULL_SIMP_TAC std_ss [APPEND,one_rev_list_def,SEP_CLAUSES] \\ SEP_WRITE_TAC)
  \\ Cases_on `zs` \\ SIMP_TAC std_ss [DECIDE ``~(SUC n = 0)``,LENGTH,MAP]
  \\ ONCE_REWRITE_TAC [RW[arm_sa_mul_thm]arm_mul_pass_zero_def]
  \\ ONCE_REWRITE_TAC [mw_mul_pass_def,HD,TL]
  \\ SIMP_TAC (std_ss++SIZES_ss) [n2w_11,ADD1] \\ REPEAT STRIP_TAC
  \\ `?y1 k1. single_mul_add x h' k 0w = (y1,k1)` by METIS_TAC [PAIR]
  \\ FULL_SIMP_TAC std_ss [APPEND,one_rev_list_def,HD] \\ SEP_R_TAC
  \\ FULL_SIMP_TAC std_ss [LET_DEF,LEFT_ADD_DISTRIB,GSYM word_add_n2w,WORD_ADD_SUB,TL]
  \\ ONCE_REWRITE_TAC [WORD_ADD_COMM] \\ SIMP_TAC std_ss [WORD_SUB_PLUS]
  \\ `4 * LENGTH ys < 4294967296` by DECIDE_TAC
  \\ SEP_I_TAC "arm_mul_pass_zero" \\ SEP_W_TAC \\ SEP_F_TAC \\ SEP_TAC []
  \\ REPEAT STRIP_TAC \\ ASM_SIMP_TAC std_ss [APPEND,one_rev_list_def] \\ SEP_TAC []);


(* mw_mul *)

val arm_mul_def = tailrecLib.tailrec_define ``
  arm_mul (xp,yp,zp,xl,yl,df:word32 set,f:word32->word32) =
    if xl = 0w:word32 then (f,df) else
      let (f,df) = arm_mul_pass (f xp,yp,zp,0w,yl,df,f) in
      let zp = zp - 4w in
      let xp = xp - 4w in
      let xl = xl - 4w in
        arm_mul (xp,yp,zp,xl,yl,df,f)``

val LENGTH_mw_mul_pass = prove(
  ``!ys x zs k. LENGTH (mw_mul_pass x ys zs k) = SUC (LENGTH ys)``,
  Induct \\ SIMP_TAC std_ss [mw_mul_pass_def,LENGTH]
  \\ Cases_on `single_mul_add x h k (HD zs)`
  \\ ASM_SIMP_TAC std_ss [LET_DEF,LENGTH])

val arm_mul_thm = prove(
  ``!xs ys zs xp yp zp res df f p.
      4 * LENGTH xs < 4294967296 /\ 4 * LENGTH ys < 4294967296 /\
      (LENGTH res = LENGTH xs) /\ (LENGTH zs = LENGTH ys) /\
      ALIGNED yp /\ ALIGNED zp /\ ALIGNED xp /\
      (one_rev_list xp xs * one_rev_list yp ys * one_rev_list zp (zs++res) * p) (fun2set (f,df)) ==>
      ?fi. (arm_mul (xp,yp,zp,n2w (4 * LENGTH xs),n2w (4 * LENGTH ys),df,f) = (fi,df)) /\
           (one_rev_list xp xs * one_rev_list yp ys * one_rev_list zp (mw_mul xs ys zs) * p) (fun2set (fi,df))``,
  Induct \\ ONCE_REWRITE_TAC [arm_mul_def]
  THEN1 SIMP_TAC std_ss [LENGTH,mw_mul_def,LENGTH_NIL,APPEND_NIL]
  \\ ASM_SIMP_TAC (std_ss++SIZES_ss) [LENGTH,n2w_11,ADD1,one_rev_list_def]
  \\ REPEAT STRIP_TAC \\ SEP_TAC []
  \\ ASSUME_TAC (GEN_ALL arm_mul_pass_thm) \\ SEP_I_TAC "arm_mul_pass"
  \\ `?ts. mw_mul_pass h ys zs 0x0w = ts` by METIS_TAC []
  \\ `~(res = [])` by (Cases_on `res` \\ FULL_SIMP_TAC std_ss [LENGTH,ADD1,NOT_NIL_CONS])
  \\ SEP_F_TAC \\ ASM_SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC
  \\ ASM_SIMP_TAC std_ss [LET_DEF,mw_mul_def,one_rev_list_def,LEFT_ADD_DISTRIB,
       GSYM word_add_n2w,WORD_ADD_SUB] \\ SEP_I_TAC "arm_mul"
  \\ `4 * LENGTH xs < 4294967296` by DECIDE_TAC
  \\ `LENGTH ts = SUC (LENGTH ys)` by METIS_TAC [LENGTH_mw_mul_pass]
  \\ `?t ts2. ts = t::ts2` by (Cases_on `ts` \\ FULL_SIMP_TAC std_ss [LENGTH,ADD1,CONS_11])
  \\ `?r rs2. res = r::rs2` by (Cases_on `res` \\ FULL_SIMP_TAC std_ss [LENGTH,ADD1,CONS_11])
  \\ FULL_SIMP_TAC std_ss [APPEND,one_rev_list_def,TL,HD] \\ SEP_F_TAC
  \\ SEP_TAC [] \\ FULL_SIMP_TAC std_ss [ADD1,LENGTH]);

val arm_mul_alias_thm = prove(
  ``!xs xs2 ys zs xp yp zp res df f p.
      4 * LENGTH xs < 4294967296 /\ 4 * LENGTH ys < 4294967296 /\
      (LENGTH res = LENGTH xs) /\ (LENGTH zs = LENGTH ys) /\ (xp = yp - n2w (4 * LENGTH xs2)) /\
      ALIGNED yp /\ ALIGNED zp /\ ALIGNED xp /\ (ys = xs2 ++ xs) /\
      (one_rev_list yp ys * one_rev_list zp (zs++res) * p) (fun2set (f,df)) ==>
      ?fi. (arm_mul (xp,yp,zp,n2w (4 * LENGTH xs),n2w (4 * LENGTH ys),df,f) = (fi,df)) /\
           (one_rev_list yp ys * one_rev_list zp (mw_mul xs ys zs) * p) (fun2set (fi,df))``,
  Induct \\ ONCE_REWRITE_TAC [arm_mul_def]
  THEN1 SIMP_TAC std_ss [LENGTH,mw_mul_def,LENGTH_NIL,APPEND_NIL]
  \\ ASM_SIMP_TAC (std_ss++SIZES_ss) [LENGTH,n2w_11,ADD1,one_rev_list_def]
  \\ REPEAT STRIP_TAC \\ SEP_TAC []
  \\ ASSUME_TAC (GEN_ALL arm_mul_pass_thm) \\ SEP_I_TAC "arm_mul_pass"
  \\ `(f (yp - n2w (4 * LENGTH xs2)) = h) /\
      (yp - n2w (4 * LENGTH xs2)) IN df` by ALL_TAC THEN1
   (FULL_SIMP_TAC std_ss [one_rev_list_APPEND,word_mul_n2w,one_rev_list_def]
    \\ SEP_R_TAC \\ ASM_SIMP_TAC std_ss [])
  \\ FULL_SIMP_TAC std_ss []
  \\ `?ts. mw_mul_pass h (xs2 ++ h::xs) zs 0x0w = ts` by METIS_TAC []
  \\ `~(res = [])` by (Cases_on `res` \\ FULL_SIMP_TAC std_ss [LENGTH,ADD1,NOT_NIL_CONS])
  \\ ASM_SIMP_TAC std_ss [] \\ SEP_F_TAC \\ ASM_SIMP_TAC std_ss [] \\ STRIP_TAC
  \\ ASM_SIMP_TAC std_ss [LET_DEF,mw_mul_def,one_rev_list_def,LEFT_ADD_DISTRIB,
       GSYM word_add_n2w,WORD_ADD_SUB]
  \\ `xs2 ++ h::xs = SNOC h xs2 ++ xs` by
    SIMP_TAC std_ss [SNOC_APPEND,GSYM APPEND_ASSOC,APPEND]
  \\ FULL_SIMP_TAC std_ss [GSYM WORD_SUB_PLUS,word_add_n2w]
  \\ `4 * LENGTH xs2 + 4 = 4 * LENGTH (SNOC h xs2)` by ALL_TAC THEN1
        FULL_SIMP_TAC std_ss [LENGTH_SNOC,ADD1,LEFT_ADD_DISTRIB]
  \\ FULL_SIMP_TAC std_ss [] \\ SEP_I_TAC "arm_mul"
  \\ `4 * LENGTH xs < 4294967296` by DECIDE_TAC
  \\ `LENGTH ts = SUC (LENGTH ((SNOC h xs2 ++ xs)))` by METIS_TAC [LENGTH_mw_mul_pass]
  \\ `?t ts2. ts = t::ts2` by (Cases_on `ts` \\ FULL_SIMP_TAC std_ss [LENGTH,ADD1,CONS_11])
  \\ `?r rs2. res = r::rs2` by (Cases_on `res` \\ FULL_SIMP_TAC std_ss [LENGTH,ADD1,CONS_11])
  \\ FULL_SIMP_TAC std_ss [APPEND,one_rev_list_def,TL,HD] \\ SEP_F_TAC
  \\ SEP_TAC [] \\ FULL_SIMP_TAC std_ss [ADD1,LENGTH]);


(* mw_mul with zero accumulator *)

val arm_mul_zero_def = tailrecLib.tailrec_define ``
  arm_mul_zero (xp,yp,zp,xl,yl,df:word32 set,f:word32->word32) =
    let (f,df) = arm_mul_pass_zero (f xp,yp,zp,0w,yl,df,f) in
    let zp = zp - 4w in
    let xp = xp - 4w in
    let xl = xl - 4w in
    let (f,df) = arm_mul (xp,yp,zp,xl,yl,df,f) in
      (f,df)``

val arm_mul_zero_thm = prove(
  ``!xs ys zs xp yp zp res df f p.
      4 * LENGTH xs < 4294967296 /\ 4 * LENGTH ys < 4294967296 /\
      (LENGTH res = LENGTH xs) /\ (LENGTH zs = LENGTH ys) /\
      ALIGNED yp /\ ALIGNED zp /\ ALIGNED xp /\ ~(xs = []) /\
      (one_rev_list xp xs * one_rev_list yp ys * one_rev_list zp (zs++res) * p) (fun2set (f,df)) ==>
      ?fi. (arm_mul_zero (xp,yp,zp,n2w (4 * LENGTH xs),n2w (4 * LENGTH ys),df,f) = (fi,df)) /\
           (one_rev_list xp xs * one_rev_list yp ys * one_rev_list zp (mw_mul xs ys (MAP (\x.0w) ys)) * p) (fun2set (fi,df))``,
  Cases \\ ASM_SIMP_TAC std_ss [mw_mul_def,one_rev_list_def,NOT_CONS_NIL,
             arm_mul_zero_def] \\ REPEAT STRIP_TAC \\ SEP_R_TAC
  \\ ASSUME_TAC (GEN_ALL arm_mul_pass_zero_thm) \\ SEP_I_TAC "arm_mul_pass_zero"
  \\ `~(res = [])` by (Cases_on `res` \\ FULL_SIMP_TAC std_ss [LENGTH,ADD1,NOT_NIL_CONS])
  \\ FULL_SIMP_TAC std_ss [] \\ SEP_F_TAC \\ ASM_SIMP_TAC std_ss []
  \\ REPEAT STRIP_TAC \\ ASM_SIMP_TAC std_ss [LET_DEF]
  \\ `?ts. mw_mul_pass h ys (MAP (\x.0w) ys) 0x0w = ts` by METIS_TAC []
  \\ `LENGTH ts = SUC (LENGTH ys)` by METIS_TAC [LENGTH_mw_mul_pass]
  \\ `?t ts2. ts = t::ts2` by (Cases_on `ts` \\ FULL_SIMP_TAC std_ss [LENGTH,ADD1,CONS_11])
  \\ `?r rs2. res = r::rs2` by (Cases_on `res` \\ FULL_SIMP_TAC std_ss [LENGTH,ADD1,CONS_11])
  \\ FULL_SIMP_TAC std_ss [LENGTH,ADD1,LEFT_ADD_DISTRIB,APPEND,
       GSYM word_add_n2w,WORD_ADD_SUB,HD,TL,one_rev_list_def]
  \\ `4 * LENGTH t < 4294967296` by DECIDE_TAC
  \\ ASSUME_TAC (GEN_ALL arm_mul_thm) \\ SEP_I_TAC "arm_mul"
  \\ SEP_F_TAC \\ SEP_TAC [] \\ REPEAT STRIP_TAC \\ ASM_SIMP_TAC std_ss []);

val arm_mul_zero_alias_thm = prove(
  ``!xs zs xp zp res df f p.
      4 * LENGTH xs < 4294967296 /\
      (LENGTH res = LENGTH xs) /\ (LENGTH zs = LENGTH xs) /\
      ALIGNED zp /\ ALIGNED xp /\ ~(xs = []) /\
      (one_rev_list xp xs * one_rev_list zp (zs++res) * p) (fun2set (f,df)) ==>
      ?fi. (arm_mul_zero (xp,xp,zp,n2w (4 * LENGTH xs),n2w (4 * LENGTH xs),df,f) = (fi,df)) /\
           (one_rev_list xp xs * one_rev_list zp (mw_mul xs xs (MAP (\x.0w) xs)) * p) (fun2set (fi,df))``,
  Cases \\ ASM_SIMP_TAC std_ss [mw_mul_def,one_rev_list_def,NOT_CONS_NIL,
             arm_mul_zero_def] \\ REPEAT STRIP_TAC \\ SEP_R_TAC
  \\ ASSUME_TAC (GEN_ALL arm_mul_pass_zero_thm) \\ SEP_I_TAC "arm_mul_pass_zero"
  \\ `~(res = [])` by (Cases_on `res` \\ FULL_SIMP_TAC std_ss [LENGTH,ADD1,NOT_NIL_CONS])
  \\ FULL_SIMP_TAC std_ss [one_rev_list_def]
  \\ SEP_F_TAC \\ ASM_SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC
  \\ `n2w (4 * LENGTH (h::t)) - 0x4w = n2w (4 * LENGTH (t:word32 list)):word32` by
     ASM_SIMP_TAC std_ss [LENGTH,ADD1,LEFT_ADD_DISTRIB,GSYM word_add_n2w,WORD_ADD_SUB]
  \\ ASM_SIMP_TAC std_ss [LET_DEF]
  \\ `?ts. mw_mul_pass h (h::t) (MAP (\x.0w) (h::t)) 0x0w = ts` by METIS_TAC []
  \\ `LENGTH ts = SUC (LENGTH (h::t))` by METIS_TAC [LENGTH_mw_mul_pass]
  \\ `?t ts2. ts = t::ts2` by (Cases_on `ts` \\ FULL_SIMP_TAC std_ss [LENGTH,ADD1,CONS_11])
  \\ `?r rs2. res = r::rs2` by (Cases_on `res` \\ FULL_SIMP_TAC std_ss [LENGTH,ADD1,CONS_11])
  \\ FULL_SIMP_TAC std_ss []
  \\ ASSUME_TAC (GEN_ALL arm_mul_alias_thm) \\ SEP_I_TAC "arm_mul"
  \\ POP_ASSUM (ASSUME_TAC o Q.SPEC `[h]`)
  \\ FULL_SIMP_TAC std_ss [HD,TL,APPEND,one_rev_list_def,LENGTH] \\ SEP_F_TAC
  \\ `4 * LENGTH t < 4294967296` by DECIDE_TAC
  \\ ASM_SIMP_TAC std_ss [] \\ SEP_TAC []
  \\ REPEAT STRIP_TAC \\ ASM_SIMP_TAC std_ss []);


(* mwi_mul *)

val arm_imul_def = Define `
  arm_imul (xh,yh,xp,yp,zp,df,f) =
    if yh = 2w then (2w,zp,df,f) else
      let sign = xh ?? yh in
      let xl = xh >>> 8 in
      let yl = yh >>> 8 in
      let (f,df) = arm_mul_zero (yp+yl,xp+xl,zp,yl,xl,df,f) in
      let zp = zp - (xl + yl) in
      let (y,zp,df,f,x) = arm_sub3 (zp,df,f) in
        (sign,zp-4w,df,f)`

val i2mw_NEQ_IMP = prove(
  ``!i x xs. (i2mw i = (x,xs)) /\ ~(i = 0) ==> ~(xs = []) /\ ~(mw2n xs = 0)``,
  REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [i2mw_def,mw_NIL]
  \\ Cases_on `x` \\ FULL_SIMP_TAC std_ss [] \\ EXPAND_TAC
  \\ FULL_SIMP_TAC std_ss [mw2n_mw] \\ intLib.COOPER_TAC);

val LENGTH_mw_mul = prove(
  ``!xs ys zs. (LENGTH zs = LENGTH ys) ==>
               (LENGTH (mw_mul xs ys zs) = LENGTH xs + LENGTH ys)``,
  Induct \\ ASM_SIMP_TAC std_ss [LENGTH,mw_mul_def,LET_DEF] \\ REPEAT STRIP_TAC
  \\ `LENGTH (mw_mul_pass h ys zs 0x0w) = SUC (LENGTH ys)` by METIS_TAC [LENGTH_mw_mul_pass]
  \\ Cases_on `mw_mul_pass h ys zs 0x0w` \\ FULL_SIMP_TAC std_ss [LENGTH,ADD1]
  \\ ASM_SIMP_TAC std_ss [TL] \\ DECIDE_TAC);

val EVERY_ZERO = prove(
  ``!xs. EVERY (\x. x = 0w) xs = (mw2n xs = 0)``,
  Induct \\ REPEAT Cases \\ ASM_SIMP_TAC std_ss [mw2n_def,EVERY_DEF,n2w_11,
    w2n_n2w,MATCH_MP (DECIDE ``0<n ==> ~(n = 0:num)``) ZERO_LT_dimword,
    ZERO_LT_dimword]);

val mw_0_LEMMA = prove(
  ``(mw (Num (ABS 0)) = xs) = (xs = [])``,
  SIMP_TAC std_ss [EVAL ``(Num (ABS 0))``] \\ METIS_TAC [mw_def]);

val Num_ABS_EQ_0 = prove(
  ``!i. (Num (ABS i) = 0) = (i = 0)``,
  intLib.COOPER_TAC);

val arm_imul_thm = prove(
  ``(LENGTH ys + LENGTH xs <= LENGTH res) /\ (i2mw i = (x,xs)) /\ (i2mw j = (y,ys)) /\
    (mwi_mul (x,xs) (y,ys) = (z,zs)) /\ LENGTH xs < 4194304 /\ LENGTH ys < 4194304 /\
    ALIGNED xp /\ ALIGNED yp /\ ALIGNED zp /\ (LENGTH ys <= LENGTH xs) /\
    (one_list_rev_old xp xs * one_list_rev_old yp ys * one_rev_list zp res * p) (fun2set (f,df)) ==>
    ?(fi:word32->word32) ts q.
      (arm_imul (mwi_header(x,xs),mwi_header(y,ys),xp,yp,zp,df,f) =
        (q,zp - n2w (4 * LENGTH zs),df,fi)) /\ (q ' 2 = z) /\
      (LENGTH ts = LENGTH res - LENGTH zs) /\
      (one_list_rev_old xp xs * one_list_rev_old yp ys *
       one_rev_list zp zs * one_rev_list (zp - n2w (4 * LENGTH zs)) ts * p) (fun2set (fi,df))``,
  Cases_on `i = 0` THEN1
   (ASM_SIMP_TAC std_ss [i2mw_def,EVAL ``0<0:int``,mw_0_LEMMA,GSYM AND_IMP_INTRO]
    \\ SIMP_TAC std_ss [LENGTH,DECIDE ``n <= 0 = (n = 0)``,LENGTH_NIL]
    \\ SIMP_TAC std_ss [mwi_mul_def] \\ REPEAT STRIP_TAC \\ EXPAND_TAC
    \\ FULL_SIMP_TAC std_ss [EVAL ``mwi_header (0<0:int,[])``,arm_imul_def,LENGTH,Num_ABS_EQ_0,
         WORD_SUB_RZERO,one_rev_list_def,SEP_CLAUSES,EVAL ``(2w:word32) ' 2``,mw_NIL]
    \\ Q.EXISTS_TAC `res` \\ SEP_TAC [])
  \\ Cases_on `j = 0` THEN1
   (ASM_SIMP_TAC std_ss [i2mw_def,EVAL ``0<0:int``,mw_0_LEMMA,GSYM AND_IMP_INTRO]
    \\ SIMP_TAC std_ss [mwi_mul_def] \\ REPEAT STRIP_TAC \\ EXPAND_TAC
    \\ FULL_SIMP_TAC std_ss [EVAL ``mwi_header (F,[])``,arm_imul_def,LENGTH,
         WORD_SUB_RZERO,one_rev_list_def,SEP_CLAUSES,EVAL ``(2w:word32) ' 2``]
    \\ Q.EXISTS_TAC `res` \\ SEP_TAC [])
  \\ SIMP_TAC std_ss [arm_imul_def,mwi_header_length_8] \\ REPEAT STRIP_TAC
  \\ ASM_SIMP_TAC std_ss [mwi_header_EQ_const]
  \\ `4 * LENGTH xs < 4294967296 /\ 4 * LENGTH ys < 4294967296` by DECIDE_TAC
  \\ ASM_SIMP_TAC (std_ss++SIZES_ss) [LET_DEF,WORD_LS,w2n_n2w]
  \\ IMP_RES_TAC i2mw_NEQ_IMP
  \\ ASM_SIMP_TAC std_ss [] \\ FULL_SIMP_TAC std_ss [one_list_rev_old_def]
  \\ IMP_RES_TAC (RW1[ADD_COMM]ADD_LESS_EQ_EXISTS_APPEND)
  \\ ASM_SIMP_TAC std_ss []
  \\ ASSUME_TAC (GEN_ALL arm_mul_zero_thm) \\ SEP_I_TAC "arm_mul_zero"
  \\ FULL_SIMP_TAC std_ss [one_rev_list_APPEND,LENGTH_APPEND,GSYM AND_IMP_INTRO]
  \\ FULL_SIMP_TAC std_ss [AND_IMP_INTRO,GSYM CONJ_ASSOC,word_mul_n2w]
  \\ SEP_F_TAC \\ ASM_SIMP_TAC std_ss [] \\ SEP_TAC [] \\ REPEAT STRIP_TAC
  \\ SEP_TAC [] \\ FULL_SIMP_TAC std_ss [GSYM LEFT_ADD_DISTRIB,word_add_n2w]
  \\ `LENGTH xs + LENGTH ys = LENGTH ys + LENGTH xs` by DECIDE_TAC
  \\ FULL_SIMP_TAC std_ss [word_mul_n2w,LENGTH_APPEND]
  \\ FULL_SIMP_TAC std_ss [mwi_mul_def,LET_DEF,DECIDE ``m <= n ==> ~(n < m:num)``]
  \\ EXPAND_TAC
  \\ `?res2. mw_mul ys xs (MAP (\x. 0x0w) xs) = res2` by METIS_TAC []
  \\ `LENGTH xs + LENGTH ys = LENGTH res2` by METIS_TAC [LENGTH_mw_mul,LENGTH_MAP,ADD_COMM]
  \\ `LENGTH ys + LENGTH xs = LENGTH res2` by METIS_TAC [LENGTH_mw_mul,LENGTH_MAP,ADD_COMM]
  \\ FULL_SIMP_TAC std_ss []
  \\ ASSUME_TAC (GEN_ALL arm_sub3_thm) \\ SEP_I_TAC "arm_sub3"
  \\ POP_ASSUM (ASSUME_TAC o Q.SPEC `res2`) \\ FULL_SIMP_TAC std_ss [WORD_SUB_ADD]
  \\ SEP_F_TAC
  \\ `~EVERY (\x. x = 0w) res2 /\ ~(mw_trailing res2 = [])` by
   (FULL_SIMP_TAC std_ss [EVERY_ZERO,mw_trailing_NIL]
    \\ EXPAND_TAC \\ REPEAT STRIP_TAC
    \\ FULL_SIMP_TAC std_ss [mw_mul_thm,LENGTH_MAP] \\ METIS_TAC [])
  \\ `~(res2 = [])` by METIS_TAC [mw_trailing_def]
  \\ FULL_SIMP_TAC std_ss [] \\ SEP_TAC [] \\ REPEAT STRIP_TAC
    \\ ASM_SIMP_TAC std_ss [] \\ Q.EXISTS_TAC `ts ++ xs3`
  \\ FULL_SIMP_TAC (std_ss++SIZES_ss) [word_xor_def,fcpTheory.FCP_BETA,
      mwi_header_sign_index] \\ POP_ASSUM MP_TAC
  \\ `LENGTH (mw_trailing res2) <= LENGTH res2` by METIS_TAC [LENGTH_mw_trailing]
  \\ ASM_SIMP_TAC std_ss [LENGTH_APPEND,word_add_n2w,WORD_ADD_SUB,
       one_rev_list_APPEND,word_mul_n2w,GSYM WORD_SUB_PLUS,GSYM LEFT_ADD_DISTRIB]
  \\ ASM_SIMP_TAC std_ss [word_arith_lemma3,DECIDE ``0 < n = ~(n = 0:num)``,
       LENGTH_NIL,GSYM LEFT_SUB_DISTRIB]
  \\ ASM_SIMP_TAC std_ss [DECIDE ``n <= m ==> (n + (m - n) = m:num)``,
       DECIDE ``n <= m ==> (m - (m - n) = n:num)``] \\ SEP_TAC []
  \\ REPEAT STRIP_TAC \\ DECIDE_TAC);

val arm_imul_alias_thm = prove(
  ``(LENGTH xs + LENGTH xs <= LENGTH res) /\ (i2mw i = (x,xs)) /\
    (mwi_mul (x,xs) (x,xs) = (z,zs)) /\ LENGTH xs < 4194304 /\
    ALIGNED xp /\ ALIGNED zp /\
    (one_list_rev_old xp xs * one_rev_list zp res * p) (fun2set (f,df)) ==>
    ?(fi:word32->word32) ts q.
      (arm_imul (mwi_header(x,xs),mwi_header(x,xs),xp,xp,zp,df,f) =
        (q,zp - n2w (4 * LENGTH zs),df,fi)) /\ (q ' 2 = z) /\
      (LENGTH ts = LENGTH res - LENGTH zs) /\
      (one_list_rev_old xp xs * one_rev_list zp zs *
       one_rev_list (zp - n2w (4 * LENGTH zs)) ts * p) (fun2set (fi,df))``,
  Cases_on `i = 0` THEN1
   (ASM_SIMP_TAC std_ss [i2mw_def,EVAL ``0<0:int``,mw_0_LEMMA,GSYM AND_IMP_INTRO]
    \\ SIMP_TAC std_ss [mwi_mul_def] \\ REPEAT STRIP_TAC \\ EXPAND_TAC
    \\ FULL_SIMP_TAC std_ss [EVAL ``mwi_header (F,[])``,arm_imul_def,LENGTH,
         WORD_SUB_RZERO,one_rev_list_def,SEP_CLAUSES,EVAL ``(2w:word32) ' 2``]
    \\ Q.EXISTS_TAC `res` \\ SEP_TAC [])
  \\ SIMP_TAC std_ss [arm_imul_def,mwi_header_length_8] \\ REPEAT STRIP_TAC
  \\ ASM_SIMP_TAC std_ss [mwi_header_EQ_const]
  \\ `4 * LENGTH xs < 4294967296` by DECIDE_TAC
  \\ ASM_SIMP_TAC (std_ss++SIZES_ss) [LET_DEF,WORD_LS,w2n_n2w]
  \\ IMP_RES_TAC i2mw_NEQ_IMP
  \\ ASM_SIMP_TAC std_ss [] \\ FULL_SIMP_TAC std_ss [one_list_rev_old_def]
  \\ IMP_RES_TAC ADD_LESS_EQ_EXISTS_APPEND \\ ASM_SIMP_TAC std_ss []
  \\ ASSUME_TAC (GEN_ALL arm_mul_zero_alias_thm) \\ SEP_I_TAC "arm_mul_zero"
  \\ FULL_SIMP_TAC std_ss [one_rev_list_APPEND,LENGTH_APPEND,GSYM AND_IMP_INTRO]
  \\ FULL_SIMP_TAC std_ss [AND_IMP_INTRO,GSYM CONJ_ASSOC]
  \\ SEP_F_TAC \\ ASM_SIMP_TAC std_ss [] \\ SEP_TAC [] \\ REPEAT STRIP_TAC
  \\ SEP_TAC [] \\ FULL_SIMP_TAC std_ss [GSYM LEFT_ADD_DISTRIB,word_add_n2w]
  \\ FULL_SIMP_TAC std_ss [word_mul_n2w,LENGTH_APPEND]
  \\ FULL_SIMP_TAC std_ss [mwi_mul_def,LET_DEF] \\ EXPAND_TAC
  \\ `?res2. mw_mul xs xs (MAP (\x. 0x0w) xs) = res2` by METIS_TAC []
  \\ `LENGTH xs + LENGTH xs = LENGTH res2` by METIS_TAC [LENGTH_mw_mul,LENGTH_MAP,ADD_COMM]
  \\ FULL_SIMP_TAC std_ss []
  \\ ASSUME_TAC (GEN_ALL arm_sub3_thm) \\ SEP_I_TAC "arm_sub3"
  \\ POP_ASSUM (ASSUME_TAC o Q.SPEC `res2`) \\ FULL_SIMP_TAC std_ss [WORD_SUB_ADD]
  \\ SEP_F_TAC
  \\ `~EVERY (\x. x = 0w) res2 /\ ~(mw_trailing res2 = [])` by
   (FULL_SIMP_TAC std_ss [EVERY_ZERO,mw_trailing_NIL]
    \\ EXPAND_TAC \\ REPEAT STRIP_TAC
    \\ FULL_SIMP_TAC std_ss [mw_mul_thm,LENGTH_MAP] \\ METIS_TAC [])
  \\ `~(res2 = [])` by METIS_TAC [mw_trailing_def]
  \\ FULL_SIMP_TAC std_ss [] \\ SEP_TAC [] \\ REPEAT STRIP_TAC
  \\ ASM_SIMP_TAC std_ss [] \\ Q.EXISTS_TAC `ts ++ xs3`
  \\ FULL_SIMP_TAC (std_ss++SIZES_ss) [word_xor_def,fcpTheory.FCP_BETA,
      mwi_header_sign_index] \\ POP_ASSUM MP_TAC
  \\ `LENGTH (mw_trailing res2) <= LENGTH res2` by METIS_TAC [LENGTH_mw_trailing]
  \\ ASM_SIMP_TAC std_ss [LENGTH_APPEND,word_add_n2w,WORD_ADD_SUB,
       one_rev_list_APPEND,word_mul_n2w,GSYM WORD_SUB_PLUS,GSYM LEFT_ADD_DISTRIB]
  \\ ASM_SIMP_TAC std_ss [word_arith_lemma3,DECIDE ``0 < n = ~(n = 0:num)``,
       LENGTH_NIL,GSYM LEFT_SUB_DISTRIB]
  \\ ASM_SIMP_TAC std_ss [DECIDE ``n <= m ==> (n + (m - n) = m:num)``,
       DECIDE ``n <= m ==> (m - (m - n) = n:num)``] \\ SEP_TAC []
  \\ REPEAT STRIP_TAC \\ DECIDE_TAC);


(* mw_shift *)

val (arm_shift_def,arm_shift_pre_def) = mc_define `
  arm_shift (xp:word32,xl:word32,df:word32 set,f:word32->word32) =
    if xl = 1w then
      let f = (xp =+ f xp >>> 1) f in (df,f)
    else
      let y = f (xp-4w) in
      let f = (xp =+ ((f xp >>> 1) !! (y << 31))) f in
        arm_shift (xp-4w,xl-1w,df,f)`

val arm_shift_thm = prove(
  ``!xs xp f df p.
      LENGTH xs < 2**32 /\
      (one_rev_list xp xs * p) (fun2set (f,df)) /\ ~(xs = []) /\ ALIGNED xp ==>
      ?fi.
        arm_shift_pre (xp,n2w (LENGTH xs),df,f) /\
        (arm_shift (xp,n2w (LENGTH xs),df,f) = (df,fi)) /\
        (one_rev_list xp (mw_shift xs) * p) (fun2set (fi,df))``,
  Induct \\ SIMP_TAC std_ss [NOT_CONS_NIL] \\ Cases_on `xs`
  \\ SIMP_TAC std_ss [LENGTH,mw_shift_def,one_rev_list_def]
  \\ ONCE_REWRITE_TAC [arm_shift_def,arm_shift_pre_def]
  THEN1 (SIMP_TAC std_ss [LET_DEF] \\ REPEAT STRIP_TAC \\ SEP_TAC [] \\ SEP_WRITE_TAC)
  \\ FULL_SIMP_TAC (std_ss++SIZES_ss) [n2w_11,ADD1,LET_DEF,LENGTH,NOT_CONS_NIL]
  \\ SIMP_TAC std_ss [GSYM word_add_n2w,WORD_ADD_SUB]
  \\ SIMP_TAC std_ss [word_add_n2w] \\ REPEAT STRIP_TAC \\ SEP_I_TAC "arm_shift"
  \\ `LENGTH t + 1 < 4294967296` by DECIDE_TAC
  \\ FULL_SIMP_TAC std_ss [one_rev_list_def]
  \\ SEP_W_TAC \\ SEP_F_TAC \\ SEP_TAC [] \\ REPEAT STRIP_TAC
  \\ ASM_SIMP_TAC std_ss [] \\ SEP_TAC []);



(* copy over and append 0 *)

val (arm_copy_over_def,arm_copy_over_pre_def) = mc_define `
  arm_copy_over (i:word32,sp,dp,df:word32 set,f:word32->word32) =
    let f = (dp =+ f sp) f in
    let dp = dp - 4w in
    let i = i - 1w in
      if i = 0w then
        let f = (dp =+ 0w) f in (dp,df,f)
      else
        arm_copy_over (i,sp-4w,dp,df,f)`;

val arm_copy_over_thm = prove(
  ``!xs ys y sp dp df f p.
      (one_rev_list sp xs * one_rev_list dp (ys ++ [y]) * p) (fun2set (f,df)) /\
      ~(xs = []) /\ ALIGNED sp /\ ALIGNED dp /\ LENGTH xs < 2**32 /\ (LENGTH xs = LENGTH ys) ==>
      ?fi. arm_copy_over_pre (n2w (LENGTH xs),sp,dp,df,f) /\
           (arm_copy_over (n2w (LENGTH xs),sp,dp,df,f) = (dp - n2w (4 * LENGTH xs),df,fi)) /\
           (one_rev_list sp xs * one_rev_list dp (xs ++ [0w]) * p) (fun2set (fi,df))``,
  Induct \\ SIMP_TAC std_ss [NOT_CONS_NIL] \\ STRIP_TAC
  \\ Cases_on `ys` \\ SIMP_TAC std_ss [LENGTH,ADD1,APPEND,one_rev_list_def]
  \\ ONCE_REWRITE_TAC [arm_copy_over_def,arm_copy_over_pre_def]
  \\ SIMP_TAC (std_ss++SIZES_ss) [LET_DEF,GSYM word_add_n2w,WORD_ADD_SUB,n2w_11]
  \\ REPEAT STRIP_TAC \\ `LENGTH t < 4294967296` by DECIDE_TAC
  \\ ASM_SIMP_TAC std_ss [LENGTH_NIL] \\ SEP_TAC []
  \\ Cases_on `t = []` \\ FULL_SIMP_TAC std_ss [LENGTH,one_rev_list_def,APPEND,LENGTH_NIL]
  THEN1 (SEP_TAC [] \\ SEP_WRITE_TAC)
  \\ SEP_W_TAC \\ SEP_I_TAC "arm_copy_over" \\ SEP_F_TAC
  \\ FULL_SIMP_TAC std_ss [GSYM LENGTH_NIL] \\ SEP_TAC [] \\ REPEAT STRIP_TAC
  \\ ASM_SIMP_TAC std_ss [LEFT_ADD_DISTRIB,GSYM WORD_SUB_PLUS,word_add_n2w,AC ADD_COMM ADD_ASSOC]);



(* copy over, second version *)

val (arm_copy_over2_def,arm_copy_over2_pre_def) = mc_define `
  arm_copy_over2 (i:word32,sp,dp,df:word32 set,f:word32->word32) =
    let f = (dp =+ f sp) f in
    let dp = dp - 4w in
    let i = i - 1w in
      if i = 0w then (dp,df,f)
      else
        arm_copy_over2 (i,sp-4w,dp,df,f)`;

val arm_copy_over2_thm = prove(
  ``!xs ys y sp dp df f p.
      (one_rev_list sp xs * one_rev_list dp ys * p) (fun2set (f,df)) /\
      ~(xs = []) /\ ALIGNED sp /\ ALIGNED dp /\ LENGTH xs < 2**32 /\ (LENGTH xs = LENGTH ys) ==>
      ?fi. arm_copy_over2_pre (n2w (LENGTH xs),sp,dp,df,f) /\
           (arm_copy_over2 (n2w (LENGTH xs),sp,dp,df,f) = (dp - n2w (4 * LENGTH xs),df,fi)) /\
           (one_rev_list sp xs * one_rev_list dp xs * p) (fun2set (fi,df))``,
  Induct \\ SIMP_TAC std_ss [NOT_CONS_NIL] \\ STRIP_TAC
  \\ Cases_on `ys` \\ SIMP_TAC std_ss [LENGTH,ADD1,APPEND,one_rev_list_def]
  \\ ONCE_REWRITE_TAC [arm_copy_over2_def,arm_copy_over2_pre_def]
  \\ SIMP_TAC (std_ss++SIZES_ss) [LET_DEF,GSYM word_add_n2w,WORD_ADD_SUB,n2w_11]
  \\ REPEAT STRIP_TAC \\ `LENGTH t < 4294967296` by DECIDE_TAC
  \\ ASM_SIMP_TAC std_ss [LENGTH_NIL] \\ SEP_TAC []
  \\ Cases_on `t = []` \\ FULL_SIMP_TAC std_ss [LENGTH,one_rev_list_def,APPEND,LENGTH_NIL]
  THEN1 (SEP_TAC [] \\ SEP_WRITE_TAC)
  \\ SEP_W_TAC \\ SEP_I_TAC "arm_copy_over2" \\ SEP_F_TAC
  \\ FULL_SIMP_TAC std_ss [GSYM LENGTH_NIL] \\ SEP_TAC [] \\ REPEAT STRIP_TAC
  \\ ASM_SIMP_TAC std_ss [LEFT_ADD_DISTRIB,GSYM WORD_SUB_PLUS,word_add_n2w,AC ADD_COMM ADD_ASSOC]);


(* copy down *)

val (arm_copy_down_def,arm_copy_down_pre_def) = mc_define `
  arm_copy_down (i:word32,sp,dp,df:word32 set,f:word32->word32) =
    let f = (dp =+ f sp) f in
    let dp = dp - 4w in
    let i = i - 1w in
      if i = 0w then (dp,df,f)
      else
        arm_copy_down (i,sp-4w,dp,df,f)`;

val (arm_copy_down_pred_def,arm_copy_down_pred_pre_def) = mc_define `
  arm_copy_down_pred (opp:word32,zp_div,zp_mod,i,sp,dp,df,f) =
    if opp = 4w then
      let (dp,df,f) = arm_copy_down (i,sp,dp,df,f) in
        (opp,zp_div:word32,dp,df,f)
    else (opp,zp_mod:word32,dp,df,f)`;

val WORD_SUB_COMM = prove(
  ``!w x y. w - x - y = w - y - x: 'a word``,
  SIMP_TAC (std_ss++WORD_ARITH_EQ_ss++WORD_ARITH_ss) []);

val arm_copy_down_thm = prove(
  ``!ys xs sp dp df f p.
      (one_rev_list dp (xs ++ ys) * p) (fun2set (f,df)) /\
      ~(xs = []) /\ ~(ys = []) /\ ALIGNED dp /\ LENGTH ys < 2**32 ==>
      ?fi zs. arm_copy_down_pre (n2w (LENGTH ys),dp - n2w (4 * LENGTH xs),dp,df,f) /\
              (arm_copy_down (n2w (LENGTH ys),dp - n2w (4 * LENGTH xs),dp,df,f) = (dp - n2w (4 * LENGTH ys),df,fi)) /\
              (one_rev_list dp (ys ++ zs) * p) (fun2set (fi,df)) /\ (LENGTH zs = LENGTH xs)``,
  Induct \\ REPEAT STRIP_TAC
  \\ Cases_on `xs` \\ FULL_SIMP_TAC std_ss [NOT_CONS_NIL,LENGTH,ADD1]
  \\ ONCE_REWRITE_TAC [arm_copy_down_def,arm_copy_down_pre_def]
  \\ SIMP_TAC (std_ss++SIZES_ss) [LET_DEF,GSYM word_add_n2w,WORD_ADD_SUB,n2w_11,
       LENGTH,ADD1] \\ SIMP_TAC std_ss [one_rev_list_APPEND,word_mul_n2w,LENGTH,ADD1]
  \\ SIMP_TAC std_ss [one_rev_list_def] \\ REPEAT STRIP_TAC \\ SEP_TAC []
  \\ `LENGTH ys < 4294967296` by DECIDE_TAC \\ ASM_SIMP_TAC std_ss []
  \\ Cases_on `LENGTH ys = 0` \\ ASM_SIMP_TAC std_ss [] THEN1
   (FULL_SIMP_TAC std_ss [LENGTH_NIL,one_rev_list_def,SEP_CLAUSES]
    \\ Q.EXISTS_TAC `t ++ [h]`
    \\ FULL_SIMP_TAC std_ss [one_rev_list_APPEND,word_mul_n2w,GSYM WORD_SUB_PLUS]
    \\ FULL_SIMP_TAC std_ss [word_add_n2w,LENGTH,LENGTH_APPEND,LEFT_ADD_DISTRIB,
         AC ADD_COMM ADD_ASSOC, one_rev_list_def,SEP_CLAUSES,ADD1] \\ SEP_TAC []
    \\ SEP_WRITE_TAC)
  \\ ONCE_REWRITE_TAC [WORD_SUB_COMM]
  \\ Q.PAT_ASSUM `!xs. bbb` (ASSUME_TAC o Q.SPECL [`t ++ [h]`,`dp-4w`])
  \\ FULL_SIMP_TAC std_ss [one_rev_list_APPEND,word_mul_n2w,GSYM WORD_SUB_PLUS,
       one_rev_list_def,SEP_CLAUSES,STAR_ASSOC,word_add_n2w,LENGTH,ADD1,
       LENGTH_APPEND,LEFT_ADD_DISTRIB,AC ADD_COMM ADD_ASSOC,LENGTH_NIL]
  \\ SEP_W_TAC \\ SEP_F_TAC \\ SEP_TAC [APPEND_eq_NIL,NOT_CONS_NIL]
  \\ REPEAT STRIP_TAC \\ ASM_SIMP_TAC std_ss []);


(* arm_trailing *)

val (arm_trailing_def,arm_trailing_pre_def) = mc_define `
  arm_trailing (xp,yp,df:word32 set,f:word32->word32) =
    if ~(f (xp+4w) = 0w) then (xp,df,f) else
      let xp = xp + 4w in
        if yp = xp then (xp,df,f) else arm_trailing (xp,yp,df,f)`

val WORD_EQ_SUB_CANCEL2 = prove(
  ``!x y. (x = x - y) = (y = 0w)``,
  SIMP_TAC (std_ss++WORD_ARITH_EQ_ss++WORD_ARITH_ss) []);

val arm_trailing_thm = prove(
  ``!xs xp df f p.
      (one_rev_list xp xs * p) (fun2set (f,df)) /\
      ~(xs = []) /\ ALIGNED xp /\ LENGTH xs < 2**30 ==>
      ?fi zs. arm_trailing_pre (xp - n2w (4 * LENGTH xs),xp,df,f) /\
              (arm_trailing (xp - n2w (4 * LENGTH xs),xp,df,f) =
                  (xp - n2w (4 * LENGTH (mw_trailing xs)),df,f)) /\
              (one_rev_list xp (mw_trailing xs ++ zs) * p) (fun2set (f,df)) /\
              (mw_trailing xs ++ zs = xs)``,
  HO_MATCH_MP_TAC SNOC_INDUCT \\ SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC
  \\ ONCE_REWRITE_TAC [mw_trailing_def]
  \\ FULL_SIMP_TAC std_ss [NOT_SNOC_NIL,LAST_SNOC,FRONT_SNOC]
  \\ ONCE_REWRITE_TAC [arm_trailing_def,arm_trailing_pre_def]
  \\ FULL_SIMP_TAC std_ss [LET_DEF,SNOC_APPEND,LENGTH_APPEND,LENGTH,
       one_rev_list_APPEND,word_mul_n2w,one_rev_list_def,SEP_CLAUSES,
       LEFT_ADD_DISTRIB,GSYM word_add_n2w,WORD_SUB_ADD,WORD_SUB_PLUS]
  \\ SEP_TAC [] \\ REV (Cases_on `x = 0w`) \\ ASM_SIMP_TAC std_ss [] THEN1
   (Q.EXISTS_TAC `[]` \\ FULL_SIMP_TAC std_ss [one_rev_list_def,APPEND_NIL,
       one_rev_list_APPEND,SEP_CLAUSES,word_mul_n2w] \\ SEP_TAC []
    \\ SIMP_TAC std_ss [LENGTH_APPEND,LENGTH,LEFT_ADD_DISTRIB,WORD_SUB_PLUS,
         GSYM word_add_n2w])
  \\ ASM_SIMP_TAC (std_ss++SIZES_ss) [LET_DEF,WORD_EQ_SUB_CANCEL2,n2w_11]
  \\ `4 * LENGTH xs < 4294967296` by DECIDE_TAC
  \\ ASM_SIMP_TAC std_ss [LENGTH_NIL,WORD_SUB_RZERO]
  \\ Cases_on `xs = []` \\ ASM_SIMP_TAC std_ss [] THEN1
   (ONCE_REWRITE_TAC [mw_trailing_def]
    \\ FULL_SIMP_TAC std_ss [LENGTH,APPEND,WORD_SUB_RZERO,one_rev_list_def]
    \\ SEP_TAC []) \\ `LENGTH xs < 1073741824` by DECIDE_TAC
  \\ SEP_I_TAC "arm_trailing" \\ SEP_F_TAC \\ ASM_SIMP_TAC std_ss []
  \\ REPEAT STRIP_TAC \\ ASM_SIMP_TAC std_ss []
  \\ Q.EXISTS_TAC `zs ++ [0w]`
  \\ ASM_SIMP_TAC std_ss [APPEND_ASSOC,one_rev_list_APPEND,one_rev_list_def]
  \\ ASM_SIMP_TAC std_ss [SEP_CLAUSES,word_mul_n2w,GSYM WORD_SUB_PLUS,word_add_n2w,
       GSYM LEFT_ADD_DISTRIB,GSYM LENGTH_APPEND]
  \\ FULL_SIMP_TAC (std_ss++star_ss) []);


(* arm_read_mwi -- decompress small integers *)

val arm_read_mwi_def = Define `
  arm_read_mwi (r1,r3,df,f) =
    if r1 && 3w = 0w then (r1, df, f) else
    if r1 = 1w then (r3, df, (r3 =+ 2w) f) else
      let f = (r3 =+ 1026w) f in
      let f = (r3 + 4w =+ r1 >>> 2) f in
        (r3, df, f)`;

val one_mwi_compl_def = Define `
  one_mwi_compl i x =
    if i = 0 then one_list_ex (x+4w) 1 else
    if ~small_int i then one_list_ex x 2 else emp`;

val arm_read_mwi_thm = prove(
  ``!a x i t1 t2 p df f.
      (one_mwi a i * one_list_ex x 2 * p) (fun2set (f,df)) /\ ALIGNED x ==>
      ?f2 a2.
        (arm_read_mwi (a,x,df,f) = (a2,df,f2)) /\
        (one_mwi_compl i x * one_mwi_basic a2 i * p) (fun2set (f2,df)) /\
        SEP_IMP (one_mwi_compl i x * one_mwi_basic a2 i) (one_mwi a i * one_list_ex x 2)``,
  NTAC 8 STRIP_TAC
  \\ SIMP_TAC std_ss [arm_read_mwi_def,one_mwi_def,one_mwi_basic_def,one_mwi_compl_def]
  \\ Cases_on `i = 0` \\ ASM_SIMP_TAC intLib.int_ss [cond_STAR,EVAL ``small_int 0``] THEN1
   (NTAC 3 (ONCE_REWRITE_TAC [one_list_ex_thm]) \\ SIMP_TAC std_ss [SEP_CLAUSES]
    \\ ASM_SIMP_TAC (intLib.int_ss++sep_cond_ss++WORD_ss) [cond_STAR,EVAL ``i2mw 0``,small_int_def,
      mwi_header_def,LENGTH,SEP_CLAUSES,SEP_EXISTS_THM,one_rev_list_def,one_list_rev_def,
      LET_DEF,REVERSE,one_list_def,ALIGNED_INTRO]
    \\ REPEAT STRIP_TAC \\ ASM_SIMP_TAC std_ss [ALIGNED_INTRO,ALIGNED_n2w] \\ REPEAT STRIP_TAC
    THEN1 (Q.EXISTS_TAC `x''` \\ SEP_TAC [] \\ SEP_WRITE_TAC)
    \\ SIMP_TAC std_ss [SEP_IMP_def,SEP_EXISTS] \\ REPEAT STRIP_TAC
    \\ Q.EXISTS_TAC `2w` \\ Q.EXISTS_TAC `y` \\ SEP_TAC [])
  \\ REV (Cases_on `small_int i`) THEN1
    (ASM_SIMP_TAC (std_ss++sep_cond_ss) [ALIGNED_INTRO,i2mw_def,LET_DEF,cond_STAR]
     \\ REPEAT STRIP_TAC \\ SEP_TAC [SEP_EXISTS_THM,SEP_IMP_REFL])
  \\ NTAC 3 (ONCE_REWRITE_TAC [one_list_ex_thm]) \\ SIMP_TAC std_ss [SEP_CLAUSES]
  \\ FULL_SIMP_TAC (std_ss++sep_cond_ss++WORD_ss) [cond_STAR,ALIGNED_INTRO,
      ALIGNED_n2w,RW1[MULT_COMM]MOD_TIMES,small_int_def,LET_DEF,n2w_11,
      EVAL ``(2:int)**30``,SEP_EXISTS_THM] \\ REPEAT STRIP_TAC
  \\ `4 * Num i + 1 < 4294967296 /\ ~(Num i = 0) /\ ~(i < 0)` by intLib.COOPER_TAC
  \\ ASM_SIMP_TAC intLib.int_ss [i2mw_def,INT_ABS]
  \\ FULL_SIMP_TAC (std_ss++WORD_ss) [ALIGNED_n2w,RW1[MULT_COMM]MOD_TIMES,n2w_11]
  \\ ONCE_REWRITE_TAC [mw_def] \\ ONCE_REWRITE_TAC [mw_def]
  \\ `~(Num i = 0) /\ (Num i < 4294967296)` by intLib.COOPER_TAC
  \\ ASM_SIMP_TAC (std_ss++SIZES_ss) [LESS_DIV_EQ_ZERO,one_list_rev_def,
         one_rev_list_def,SEP_CLAUSES,LENGTH,WORD_ADD_SUB,mwi_header_def]
  \\ REV (`n2w (4 * Num i + 1) >>> 2 = n2w (Num i):word32` by ALL_TAC)
  THEN1 (ASM_SIMP_TAC std_ss [REVERSE,one_list_def,SNOC_APPEND,APPEND]
         \\ SEP_TAC [] \\ REPEAT STRIP_TAC THEN1 SEP_WRITE_TAC
         \\ SIMP_TAC std_ss [SEP_IMP_def,SEP_EXISTS] \\ REPEAT STRIP_TAC
         \\ Q.EXISTS_TAC `1026w` \\ Q.EXISTS_TAC `n2w (Num i)` \\ SEP_TAC [])
  \\ ONCE_REWRITE_TAC [GSYM n2w_w2n] \\ SIMP_TAC std_ss [w2n_lsr]
  \\ SIMP_TAC std_ss [w2n_n2w,n2w_mod]
  \\ ASM_SIMP_TAC (std_ss++SIZES_ss) [RW1[MULT_COMM]DIV_MULT]);


(* make header *)

val arm_mwi_header_def = Define `
  arm_mwi_header (zp_new,zp_old,sign) =
    let zp = zp_old - zp_new in
    let zh = zp << 8 in
    let sign = sign && 4w in
    let zh = zh + sign + 2w in
      zh`;

val arm_mwi_header_thm = prove(
  ``arm_mwi_header (zp - n2w (4 * LENGTH xs),zp,sign) = mwi_header (sign ' 2,xs)``,
  SIMP_TAC std_ss [arm_mwi_header_def,LET_DEF,RW1[WORD_ADD_COMM]WORD_SUB_SUB]
  \\ SIMP_TAC (std_ss++SIZES_ss) [WORD_ADD_SUB,word_lsl_n2w,mwi_header_def,
       SIMP_RULE std_ss [] (Q.SPEC `2` WORD_AND_TWOEXP)]
  \\ ONCE_REWRITE_TAC [MULT_COMM] \\ ASM_SIMP_TAC std_ss [MULT_ASSOC]
  \\ REPEAT STRIP_TAC THEN1 (Cases_on `sign ' 2`
    \\ ASM_SIMP_TAC std_ss [word_add_n2w,AC ADD_ASSOC ADD_COMM]));

val DIV_EQ_X = prove(
  ``!x y z. 0 < z ==> ((y DIV z = x) = x * z <= y /\ y < SUC x * z)``,
  SIMP_TAC bool_ss [EQ_LESS_EQ,DIV_LE_X,X_LE_DIV,GSYM ADD1,AC CONJ_COMM CONJ_ASSOC]);

(* construct one_mwi *)

val arm_make_mwi_def = Define `
  arm_make_mwi (zp,zh,df,f) =
    if zh = 2w then (zp+4w,1w,df,f) else
      let x = f (zp + 8w) in
        if ~(zh = 1026w) \/ ~(x <+ n2w (2**30)) then
          let f = (zp + 4w =+ zh) f in (zp,zp+4w,df,f)
        else
          (zp+8w,x << 2 + 1w,df,f)`;

val small_int_IMP = prove(
  ``!i z zs. small_int i /\ (i2mw i = (z,zs:word32 list)) ==> ~z /\ LENGTH zs < 2``,
  SIMP_TAC std_ss [i2mw_def,small_int_def] \\ NTAC 2 (ONCE_REWRITE_TAC [mw_def])
  \\ REPEAT STRIP_TAC THEN1 intLib.COOPER_TAC
  \\ Cases_on `Num (ABS i) = 0` \\ ASM_SIMP_TAC (std_ss++SIZES_ss) [LENGTH]
  \\ FULL_SIMP_TAC std_ss [EVAL ``(2:int)**30``]
  \\ `Num (ABS i) < 4294967296` by intLib.COOPER_TAC
  \\ ASM_SIMP_TAC std_ss [DIV_EQ_X,LENGTH]);

val LESS_TEST = prove(
  ``!w i. (i2mw i = (F,[w:word32])) ==> (w <+ 0x40000000w = small_int i /\ ~(i = 0))``,
  Cases \\ SIMP_TAC std_ss [i2mw_def] \\ ONCE_REWRITE_TAC [mw_def]
  \\ ONCE_REWRITE_TAC [mw_def] \\ REPEAT STRIP_TAC
  \\ Cases_on `i = 0` \\ FULL_SIMP_TAC intLib.int_ss [NOT_NIL_CONS]
  \\ `~(Num (ABS i) = 0)` by intLib.COOPER_TAC \\ FULL_SIMP_TAC std_ss []
  \\ Cases_on `Num (ABS i) < dimword (:32)`
  \\ FULL_SIMP_TAC std_ss [CONS_11,DIV_EQ_X,ZERO_LT_dimword,NOT_NIL_CONS]
  \\ FULL_SIMP_TAC (std_ss++SIZES_ss) [n2w_11,WORD_LO,w2n_n2w,small_int_def]
  \\ FULL_SIMP_TAC std_ss [EVAL ``(2:int)**30``,INT_NOT_LT]
  \\ Q.PAT_ASSUM `n < 4294967296` ASSUME_TAC \\ FULL_SIMP_TAC std_ss []
  \\ intLib.COOPER_TAC);

val small_int_lemma = prove(
  ``small_int i ==> Num (ABS i) < 4294967296``,
  SIMP_TAC std_ss [small_int_def,EVAL ``(2:int)**30``] \\ intLib.COOPER_TAC);

val arm_make_mwi_thm = prove(
  ``(i2mw i = (z,zs)) /\ LENGTH zs < 4194304 /\ ALIGNED zp /\ ~(ts = []) /\
    (one_rev_list (zp - n2w (4 * LENGTH zs)) ts *
     one_rev_list zp zs * p) (fun2set (f,df)) ==>
    ?r2 zp2 f3 ts2.
      (arm_make_mwi
        (zp - n2w (4 * LENGTH zs) - 0x4w,mwi_header (z,zs),df,f) =
        (r2,zp2,df,f3)) /\
      (one_rev_list r2 ts2 * one_mwi zp2 i * p) (fun2set (f3,df)) /\
      (LENGTH ts2 = LENGTH ts + LENGTH zs - mwi_real_size i)``,
  SIMP_TAC std_ss [arm_make_mwi_def] \\ Cases_on `i = 0` THEN1
   (ASM_SIMP_TAC std_ss [EVAL ``i2mw 0``] \\ REPEAT STRIP_TAC
    \\ EXPAND_TAC \\ FULL_SIMP_TAC intLib.int_ss [mwi_header_def,LENGTH,
         one_mwi_def,EVAL ``small_int 0``,SEP_CLAUSES,one_rev_list_def,
         mwi_real_size_def] \\ Q.EXISTS_TAC `ts` \\ SEP_TAC [WORD_SUB_ADD])
  \\ ASM_SIMP_TAC std_ss [mwi_header_EQ_const]
  \\ Cases_on `zs = []` THEN1
   (ASM_SIMP_TAC std_ss [i2mw_def,mw_NIL,
      prove(``(Num (ABS i) = 0) = (i = 0)``,intLib.COOPER_TAC)])
  \\ ASM_SIMP_TAC std_ss [LET_DEF,WORD_SUB_ADD] \\ REPEAT STRIP_TAC
  \\ `?w. (mwi_header (z,zs) = 0x402w) <=> ~z /\ (zs = [w])` by METIS_TAC [mwi_header_EQ_const]
  \\ Cases_on `(mwi_header (z,zs) = 0x402w)` THEN1
   (FULL_SIMP_TAC std_ss [LENGTH,GSYM WORD_SUB_PLUS,word_add_n2w]
    \\ FULL_SIMP_TAC std_ss [one_rev_list_def,SEP_CLAUSES,WORD_SUB_ADD]
    \\ SEP_R_TAC \\ ASSUME_TAC (UNDISCH (SPEC_ALL LESS_TEST))
    \\ ASM_SIMP_TAC std_ss [] \\ Cases_on `small_int i` \\ ASM_SIMP_TAC std_ss []
    \\ ASM_SIMP_TAC std_ss [one_mwi_def] THEN1
     (Q.EXISTS_TAC `w::ts` \\ ASM_SIMP_TAC (std_ss++sep_cond_ss) [cond_STAR]
      \\ FULL_SIMP_TAC std_ss [one_rev_list_def]
      \\ REV (`w = n2w (Num (ABS i))` by ALL_TAC) THEN1
       (FULL_SIMP_TAC (std_ss++SIZES_ss) [word_lsl_n2w,word_add_n2w,
          small_int_def,INT_ABS,GSYM INT_NOT_LT,mwi_real_size_def,LENGTH,ADD1])
      \\ Q.PAT_ASSUM `i2mw i = (F,[w])` MP_TAC
      \\ SIMP_TAC std_ss [i2mw_def] \\ NTAC 2 (ONCE_REWRITE_TAC [mw_def])
      \\ ASM_SIMP_TAC std_ss [prove(``(Num (ABS i) = 0) = (i = 0)``,intLib.COOPER_TAC)]
      \\ IMP_RES_TAC small_int_lemma
      \\ ASM_SIMP_TAC (std_ss++SIZES_ss) [CONS_11])
    \\ ASM_SIMP_TAC std_ss [one_mwi_basic_def,LET_DEF,one_list_def,word_arith_lemma3,
      REVERSE,SNOC_APPEND,APPEND,SEP_CLAUSES,mwi_header_def,LENGTH,ALIGNED]
    \\ Cases_on `ts` \\ FULL_SIMP_TAC std_ss [one_rev_list_def,
        GSYM WORD_SUB_PLUS,WORD_ADD_0,word_add_n2w] \\ Q.EXISTS_TAC `t`
    \\ STRIP_TAC THEN1 SEP_WRITE_TAC
    \\ ASM_SIMP_TAC std_ss [mwi_real_size_def,i2mw_def,mwi_size_def,LENGTH,ADD1]
    \\ DECIDE_TAC)
  \\ ASM_SIMP_TAC std_ss []
  \\ Cases_on `small_int i` THEN1
     (IMP_RES_TAC small_int_IMP
      \\ Cases_on `zs` \\ FULL_SIMP_TAC std_ss [CONS_11]
      \\ Cases_on `t` \\ FULL_SIMP_TAC std_ss [CONS_11,mwi_header_def,LENGTH]
      \\ `F` by DECIDE_TAC)
  \\ Q.PAT_ASSUM `bbb = ~z /\ (zs = [w])` (K ALL_TAC)
  \\ Cases_on `ts` \\ FULL_SIMP_TAC std_ss [one_rev_list_def,
        GSYM WORD_SUB_PLUS,WORD_ADD_0,word_add_n2w] \\ Q.EXISTS_TAC `t`
  \\ ASM_SIMP_TAC std_ss [one_mwi_def,one_mwi_basic_def,LET_DEF,one_list_def]
  \\ SIMP_TAC std_ss [one_list_rev_EQ,one_list_rev_def,REVERSE_REVERSE]
  \\ ONCE_REWRITE_TAC [WORD_ADD_SUB_SYM]
  \\ SIMP_TAC std_ss [WORD_ADD_SUB,WORD_SUB_ADD]
  \\ SEP_TAC [] \\ STRIP_TAC THEN1 SEP_WRITE_TAC
  \\ ASM_SIMP_TAC std_ss [mwi_real_size_def,i2mw_def,mwi_size_def,LENGTH,ADD1]
  \\ DECIDE_TAC);


val _ = export_theory();

