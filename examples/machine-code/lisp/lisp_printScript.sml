open HolKernel boolLib bossLib Parse; val _ = new_theory "lisp_print";
val _ = ParseExtras.temp_loose_equality()

open wordsTheory arithmeticTheory wordsLib listTheory pred_setTheory pairTheory;
open compilerLib;

open combinTheory finite_mapTheory addressTheory stringTheory helperLib;;
open lisp_gcTheory;
open lisp_typeTheory lisp_invTheory;
open set_sepTheory;
open divideTheory;
open lisp_parseTheory;

open decompilerLib prog_armLib prog_ppcLib prog_x86Lib;

val decompile_arm = decompile prog_armLib.arm_tools;
val decompile_ppc = decompile prog_ppcLib.ppc_tools;
val decompile_x86 = decompile prog_x86Lib.x86_tools;


val RW = REWRITE_RULE;
val RW1 = ONCE_REWRITE_RULE;
val bool_ss = bool_ss -* ["lift_disj_eq", "lift_imp_disj"]
val std_ss = std_ss -* ["lift_disj_eq", "lift_imp_disj"]


(* setting up the compiler *)
val _ = codegen_x86Lib.set_x86_regs
  [(3,"eax"),(4,"ecx"),(5,"edx"),(6,"ebx"),(7,"edi"),(8,"esi"),(9,"ebp")]


(* teach the compiler to compile ``let r4 = r4 * 10w in`` *)

val (x86_10_th,x86_10_def) = decompile_x86 "x86_10" `
  01C9
  8D0C89`;

val x86_10_lemma = prove(
  ``!w. x86_10 w = w * 10w``,
  SIMP_TAC (std_ss++SIZES_ss) [x86_10_def,LET_DEF,w2n_n2w]
  THEN SIMP_TAC (std_ss++wordsLib.WORD_ss) []);

val (arm_10_th,arm_10_def,_) = compile "arm" ``
  arm_10 r4 = let r2 = 10w in
              let r4 = r4 * r2 in r4:word32``

val (ppc_10_th,ppc_10_def,_) = compile "ppc" ``
  ppc_10 r4 = let r4 = r4 * 10w in r4:word32``

val x86_10_thm = SIMP_RULE std_ss [LET_DEF,x86_10_lemma] x86_10_th
val ppc_10_thm = SIMP_RULE std_ss [LET_DEF,ppc_10_def] ppc_10_th
val arm_10_thm = SIMP_RULE std_ss [LET_DEF,arm_10_def] arm_10_th

val _ = codegenLib.add_compiled [x86_10_thm,ppc_10_thm,arm_10_thm]


(* reverse a string *)

val (thms,arm_str_rev_def,arm_str_rev_pre_def) = compile_all ``
  arm_string_rev(r3:word32,r6,r7,df:word32 set,f:word32->word8) =
    if r3 = 0w then (r7,df,f) else
      let r4 = (w2w (f r6)):word32 in
      let r5 = (w2w (f r7)):word32 in
      let f = (r6 =+ w2w r5) f in
      let f = (r7 =+ w2w r4) f in
      let r6 = r6 - 1w in
      let r7 = r7 + 1w in
      let r3 = r3 - 1w in
        arm_string_rev(r3,r6,r7,df,f)``

val (thms,arm_str_reverse_def,arm_str_reverse_pre_def) = compile_all ``
  arm_string_reverse1(r6,r7,df:word32 set,f:word32->word8) =
    let r3 = r7 - r6 in
    let r3 = r3 >>> 1 in
    let r6 = r6 + r3 in
    let r6 = r6 - 1w in
    let r7 = r7 - r3 in
    let (r7,df,f) = arm_string_rev(r3,r6,r7,df,f) in
      (r7,df,f)``

val one_list_def = Define `
  (one_list a [] b = cond (b = a)) /\
  (one_list a (x::xs) b = one (a,x) * one_list (a + 1w) xs b)`;

val one_space_def = Define `
  (one_space a 0 b = cond (b = a)) /\
  (one_space a (SUC n) b = SEP_EXISTS y. one (a,y) * one_space (a + 1w) n b)`;

val one_string_def = Define `
  one_string a (s:string) b = one_list a (MAP (n2w o ORD) s) b`;

val one_list_SNOC = prove(
  ``!a xs x b. one_list a (xs ++ [x]) b =
               one_list a xs (b - 1w) * one (b - 1w, x)``,
  Induct_on `xs`
  \\ ASM_REWRITE_TAC [one_list_def,APPEND,cond_STAR,FUN_EQ_THM,STAR_ASSOC]
  \\ REWRITE_TAC [WORD_EQ_SUB_RADD] \\ METIS_TAC [WORD_ADD_SUB]);

val w2w_w2w_lemma = prove(
  ``!x. w2w ((w2w x):word32) = x:word8``,
  Cases_word
  \\ FULL_SIMP_TAC (std_ss++SIZES_ss) [w2w_def,w2n_n2w]
  \\ `n < 4294967296` by DECIDE_TAC
  \\ FULL_SIMP_TAC (std_ss++SIZES_ss) [w2w_def,w2n_n2w]);

val arm_string_rev_lemma = prove(
  ``!ys xs r6 r7 r6i r7i f p.
      (p * one_list r6i xs (r6 + 1w) * one_list r7 ys r7i) (fun2set (f,df)) /\
      (LENGTH xs = LENGTH ys) /\ LENGTH ys < 2 ** 32 ==>
      ?fi. arm_string_rev_pre (n2w (LENGTH ys),r6,r7,df,f) /\
           (arm_string_rev (n2w (LENGTH ys),r6,r7,df,f) = (r7i,df,fi)) /\
           (p * one_list r6i (REVERSE ys) (r6 + 1w) *
                one_list r7 (REVERSE xs) r7i) (fun2set (fi,df))``,
  Induct THEN1
   (Cases \\ SIMP_TAC std_ss [LENGTH, DECIDE ``~(SUC n = 0:num)``]
    \\ SIMP_TAC std_ss [REVERSE_DEF,one_list_def,cond_STAR,LENGTH]
    \\ ONCE_REWRITE_TAC [arm_str_rev_def,arm_str_rev_pre_def]
    \\ SIMP_TAC std_ss [])
  \\ NTAC 8 STRIP_TAC
  \\ STRIP_ASSUME_TAC (Q.ISPEC `xs:word8 list` rich_listTheory.SNOC_CASES)
  \\ FULL_SIMP_TAC std_ss [LENGTH, DECIDE ``~(SUC n = 0:num)``]
  \\ REWRITE_TAC [rich_listTheory.SNOC_APPEND,REVERSE_APPEND,REVERSE_DEF]
  \\ REWRITE_TAC [APPEND,one_list_def,STAR_ASSOC,LENGTH_APPEND,LENGTH]
  \\ REWRITE_TAC [DECIDE ``(m + SUC 0 = SUC n) = (m = n:num)``]
  \\ SIMP_TAC std_ss [one_list_SNOC,WORD_ADD_SUB,STAR_ASSOC]
  \\ POP_ASSUM (K ALL_TAC) \\ POP_ASSUM (ASSUME_TAC o Q.SPEC `l`)
  \\ REPEAT STRIP_TAC \\ `LENGTH ys < 4294967296` by DECIDE_TAC
  \\ FULL_SIMP_TAC std_ss []
  \\ ONCE_REWRITE_TAC [arm_str_rev_def,arm_str_rev_pre_def]
  \\ ASM_SIMP_TAC (std_ss++SIZES_ss) [LET_DEF,n2w_11,DECIDE ``~(SUC n = 0:num)``]
  \\ REWRITE_TAC [w2w_w2w_lemma,ADD1,GSYM word_add_n2w,WORD_ADD_SUB]
  \\ `(f r6 = x) /\ r6 IN df` by SEP_READ_TAC
  \\ `(f r7 = h) /\ r7 IN df` by SEP_READ_TAC
  \\ ASM_SIMP_TAC std_ss []
  \\ Q.ABBREV_TAC `f2 = (r7 =+ x) ((r6 =+ h) f)`
  \\ `(p * one (r6,h) * one (r7,x) * one_list r6i l (r6 - 1w + 1w) *
       one_list (r7 + 0x1w) ys r7i) (fun2set (f2,df))` by
   (REWRITE_TAC [WORD_SUB_ADD] \\ Q.UNABBREV_TAC `f2` \\ SEP_WRITE_TAC)
  \\ RES_TAC \\ ASM_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC (std_ss++star_ss) [WORD_SUB_ADD])

val one_list_LENGTH = prove(
  ``!xs p r6 r7. (p * one_list r6 xs r7) (fun2set (f,df)) ==>
                 (r7 - r6 = n2w (LENGTH xs))``,
  Induct
  \\ SIMP_TAC std_ss [LENGTH,one_list_def,cond_STAR,WORD_SUB_REFL]
  \\ REPEAT STRIP_TAC
  \\ `!n. (r7 - r6 = n2w (SUC n)) = (r7 - (r6 + 1w) = n2w n)` by
   (ONCE_REWRITE_TAC [GSYM WORD_EQ_SUB_ZERO]
    \\ SIMP_TAC std_ss [ADD1,GSYM word_add_n2w,WORD_SUB_PLUS]
    \\ SIMP_TAC std_ss [AC WORD_ADD_COMM WORD_ADD_ASSOC, word_sub_def])
  \\ ASM_SIMP_TAC std_ss []
  \\ POP_ASSUM (K ALL_TAC)
  \\ Q.PAT_X_ASSUM `!p. bbb` MATCH_MP_TAC
  \\ FULL_SIMP_TAC std_ss [STAR_ASSOC] \\ METIS_TAC []);

val SPLIT_LIST_MIDDLE = prove(
  ``!xs:'a list.
      ?ys qs zs. (xs = ys ++ qs ++ zs) /\ ((LENGTH xs) DIV 2 = LENGTH ys) /\
                 (LENGTH zs = LENGTH ys) /\ LENGTH qs < 2``,
  STRIP_TAC
  \\ Q.EXISTS_TAC `TAKE ((LENGTH xs) DIV 2) xs`
  \\ Q.EXISTS_TAC `TAKE ((LENGTH xs) - (LENGTH xs) DIV 2 * 2) (DROP ((LENGTH xs) DIV 2) xs)`
  \\ Q.EXISTS_TAC `DROP ((LENGTH xs) - (LENGTH xs) DIV 2 * 2) (DROP ((LENGTH xs) DIV 2) xs)`
  \\ REWRITE_TAC [TAKE_DROP]
  \\ (ASSUME_TAC o Q.SPEC `LENGTH (xs:'a list)` o MATCH_MP (GSYM DIVISION)) (DECIDE ``0 < 2:num``)
  \\ `LENGTH xs DIV 2 <= LENGTH xs` by DECIDE_TAC
  \\ `LENGTH xs - LENGTH xs DIV 2 * 2 = LENGTH xs MOD 2` by DECIDE_TAC
  \\ ASM_SIMP_TAC std_ss [TAKE_DROP, GSYM APPEND_ASSOC]
  \\ IMP_RES_TAC LENGTH_TAKE \\ ASM_SIMP_TAC std_ss [LENGTH_DROP]
  \\ STRIP_TAC THEN1 DECIDE_TAC
  \\ Cases_on `LENGTH xs MOD 2` THEN1 ASM_SIMP_TAC std_ss [rich_listTheory.FIRSTN,LENGTH]
  \\ Tactical.REVERSE (Cases_on `n`) THEN1 (`F` by DECIDE_TAC)
  \\ Cases_on `DROP (LENGTH xs DIV 2) xs` \\ EVAL_TAC);

val one_list_APPEND = prove(
  ``!xs ys a b. one_list a (xs ++ ys) b =
                one_list a xs (a + n2w (LENGTH xs)) *
                one_list (a + n2w (LENGTH xs)) ys b``,
  Induct
  \\ ASM_REWRITE_TAC [one_list_def,APPEND,LENGTH,WORD_ADD_0,SEP_CLAUSES]
  \\ REWRITE_TAC [GSYM WORD_ADD_ASSOC, word_add_n2w, ADD1]
  \\ SIMP_TAC (std_ss++star_ss) [AC ADD_ASSOC ADD_COMM]);

val arm_string_rev_lemma = prove(
  ``!xs r6 r7 f p.
      (p * one_list r6 xs r7) (fun2set (f,df)) /\ LENGTH xs < 2 ** 32 ==>
      ?fi. arm_string_reverse1_pre (r6,r7,df,f) /\
           (arm_string_reverse1 (r6,r7,df,f) = (r7,df,fi)) /\
           (p * one_list r6 (REVERSE xs) r7) (fun2set (fi,df))``,
  REWRITE_TAC [arm_str_reverse_def,arm_str_reverse_pre_def]
  \\ SIMP_TAC std_ss [LET_DEF,EVAL ``w2n (1w:word32)``]
  \\ REPEAT STRIP_TAC
  \\ IMP_RES_TAC one_list_LENGTH
  \\ `LENGTH xs < dimword (:32)` by (ASM_SIMP_TAC (std_ss++SIZES_ss) [])
  \\ IMP_RES_TAC word_LSR_n2w
  \\ ASM_SIMP_TAC std_ss []
  \\ STRIP_ASSUME_TAC (ISPEC ``xs:word8 list`` SPLIT_LIST_MIDDLE)
  \\ Q.PAT_X_ASSUM `LENGTH xs DIV 2 = LENGTH ys` (fn th => REWRITE_TAC [th])
  \\ FULL_SIMP_TAC std_ss [REVERSE_APPEND]
  \\ `REVERSE qs = qs` by
   (Cases_on `qs` \\ FULL_SIMP_TAC std_ss [LENGTH,REVERSE_DEF]
    \\ Cases_on `t` \\ FULL_SIMP_TAC std_ss [LENGTH,REVERSE_DEF,APPEND]
    \\ `F` by DECIDE_TAC)
  \\ `LENGTH zs < 2**32 /\ (LENGTH ys = LENGTH zs)` by
        (FULL_SIMP_TAC std_ss [LENGTH_APPEND] \\ DECIDE_TAC)
  \\ FULL_SIMP_TAC bool_ss [one_list_APPEND,STAR_ASSOC,LENGTH_APPEND,
        rich_listTheory.LENGTH_REVERSE,WORD_ADD_ASSOC]
  \\ `r7 - n2w (LENGTH ys) = r6 + n2w (LENGTH ys + LENGTH qs)` by
    FULL_SIMP_TAC bool_ss [WORD_EQ_SUB_RADD,GSYM word_add_n2w,
      AC WORD_ADD_COMM WORD_ADD_ASSOC]
  \\ ASM_SIMP_TAC bool_ss []
  \\ `((p * one_list (r6 + n2w (LENGTH ys)) qs (r6 + n2w (LENGTH ys) + n2w (LENGTH qs))) *
       one_list r6 ys (r6 + n2w (LENGTH ys) - 1w + 1w) *
       one_list (r7 - n2w (LENGTH ys)) zs r7)
        (fun2set (f,df))` by
    FULL_SIMP_TAC (std_ss++star_ss) [WORD_SUB_ADD,GSYM word_add_n2w, WORD_ADD_ASSOC]
  \\ IMP_RES_TAC arm_string_rev_lemma
  \\ Q.PAT_X_ASSUM `r7 - n2w (LENGTH ys) = r6 + n2w (LENGTH ys + LENGTH qs)` ASSUME_TAC
  \\ Q.PAT_X_ASSUM `LENGTH ys = LENGTH zs` (ASSUME_TAC o GSYM)
  \\ FULL_SIMP_TAC std_ss [GSYM word_add_n2w]
  \\ FULL_SIMP_TAC std_ss [WORD_ADD_SUB,WORD_SUB_ADD]
  \\ FULL_SIMP_TAC (std_ss++star_ss) [AC WORD_ADD_COMM WORD_ADD_ASSOC]);


(* print a number reversed *)

val _ = codegenLib.add_compiled [arm_div_mod_thm,x86_div_mod_thm,ppc_div_mod_thm];

val (thms,arm_str2num_def,arm_str2num_pre_def) = compile_all ``
  arm_str2num1(r3:word32,r4,r7,df:word32 set,f:word32->word8) =
    let (r3,r5) = (r3 // r4, word_mod r3 r4) in
    let r5 = r5 + 48w in
    let f = (r7 =+ w2w r5) f in
    let r7 = r7 + 1w in
      if r3 = 0w then (r7,f,df) else
        arm_str2num1(r3,r4,r7,df,f)``

val arm_str2num_lemma = prove(
  ``!n r7 a f p.
      (p * one_space r7 (LENGTH (num2str n)) a) (fun2set (f,df)) /\ n < 2 ** 31 ==>
      ?fi. arm_str2num1_pre (n2w n,10w,r7,df,f) /\
           (arm_str2num1 (n2w n,10w,r7,df,f) = (a,fi,df)) /\
           (p * one_string r7 (REVERSE (num2str n)) a) (fun2set (fi,df))``,
  completeInduct_on `n`
  \\ ONCE_REWRITE_TAC [arm_str2num_def,arm_str2num_pre_def]
  \\ SIMP_TAC (std_ss++SIZES_ss) [LET_DEF,n2w_11,w2n_n2w]
  \\ REPEAT STRIP_TAC
  \\ `n < 4294967296` by DECIDE_TAC
  \\ ASM_SIMP_TAC (std_ss++SIZES_ss) [LET_DEF,n2w_11,w2n_n2w,word_mod_def,word_div_def,word_add_n2w]
  \\ `(n DIV 10) < 4294967296` by (ASM_SIMP_TAC std_ss [DIV_LT_X] \\ DECIDE_TAC)
  \\ ASM_SIMP_TAC std_ss []
  \\ `w2w ((n2w (n MOD 10 + 48)):word32) = n2w (ORD (CHR (n MOD 10 + 48))):word8` by
   (`n MOD 10 < 10` by (MATCH_MP_TAC MOD_LESS THEN SIMP_TAC std_ss [])
    \\ `n MOD 10 + 48 < 256 /\ n MOD 10 + 48 < 4294967296` by DECIDE_TAC
    \\ FULL_SIMP_TAC (std_ss++SIZES_ss) [ORD_CHR,w2w_def,n2w_w2n,w2n_n2w])
  \\ ASM_SIMP_TAC std_ss []
  \\ Cases_on `n < 10` THEN1
   (IMP_RES_TAC LESS_DIV_EQ_ZERO \\ ASM_SIMP_TAC std_ss []
    \\ `num2str n = [CHR (n + 48)]` by
      (ONCE_REWRITE_TAC [num2str_def] \\ ASM_SIMP_TAC std_ss [dec2str_def])
    \\ FULL_SIMP_TAC bool_ss [LENGTH,one_space_def,SEP_CLAUSES,one_string_def]
    \\ FULL_SIMP_TAC bool_ss [SEP_EXISTS,cond_STAR,STAR_ASSOC,MAP,REVERSE_DEF,APPEND]
    \\ FULL_SIMP_TAC std_ss [one_list_def,SEP_CLAUSES]
    \\ `(f r7 = y) /\ r7 IN df` by SEP_READ_TAC
    \\ ASM_SIMP_TAC std_ss [] \\ SEP_WRITE_TAC)
  \\ `~(n DIV 10 < 1)` by ASM_SIMP_TAC std_ss [DIV_LT_X]
  \\ FULL_SIMP_TAC std_ss [DECIDE ``n < 1 = (n = 0:num)``]
  \\ `(n DIV 10 < n)` by (ASM_SIMP_TAC std_ss [DIV_LT_X] THEN DECIDE_TAC)
  \\ Q.PAT_X_ASSUM `!m. bbb` (ASSUME_TAC o UNDISCH o Q.SPEC `n DIV 10`)
  \\ `n DIV 10 < 2147483648` by DECIDE_TAC
  \\ FULL_SIMP_TAC std_ss []
  \\ `num2str n = STRCAT (num2str (n DIV 10)) (dec2str (n MOD 10))` by METIS_TAC [num2str_def]
  \\ FULL_SIMP_TAC std_ss [dec2str_def,REVERSE_APPEND,APPEND,REVERSE_DEF,
       LENGTH_APPEND,LENGTH,GSYM ADD1,one_space_def]
  \\ FULL_SIMP_TAC bool_ss [LENGTH,one_space_def,SEP_CLAUSES,one_string_def]
  \\ FULL_SIMP_TAC bool_ss [SEP_EXISTS,cond_STAR,STAR_ASSOC,MAP,REVERSE_DEF,APPEND]
  \\ FULL_SIMP_TAC std_ss [one_list_def,SEP_CLAUSES]
  \\ ` ((p * one (r7,n2w (ORD (CHR (n MOD 10 + 48))))) *
       one_space (r7 + 0x1w) (STRLEN (num2str (n DIV 10))) a)
        (fun2set ((r7 =+ n2w (ORD (CHR (n MOD 10 + 48)))) f,df))` by SEP_WRITE_TAC
  \\ `(f r7 = y) /\ r7 IN df` by SEP_READ_TAC
  \\ RES_TAC \\ ASM_SIMP_TAC std_ss [STAR_ASSOC]);


(* printing a number properly *)

val (thms,arm_print_num_def,arm_print_num_pre_def) = compile_all ``
  arm_print_num(r3:word32,r7,df:word32 set,f:word32->word8) =
    let r3 = r3 >>> 2 in
    let r4 = 10w:word32 in
    let r6 = r7:word32 in
    let (r7,f,df) = arm_str2num1(r3,r4,r7,df,f) in
    let (r7,df,f) = arm_string_reverse1(r6,r7,df,f) in
      (r7,f,df)``;

val LENGTH_num2str = prove(
  ``!n. 0 < n ==> LENGTH (num2str n) <= n``,
  completeInduct_on `n` \\ Cases_on `n < 10` THEN1
   (ONCE_REWRITE_TAC [num2str_def]
    \\ IMP_RES_TAC LESS_DIV_EQ_ZERO
    \\ ASM_SIMP_TAC std_ss [dec2str_def,LENGTH]
    \\ DECIDE_TAC)
  \\ `~(n DIV 10 < 1)` by ASM_SIMP_TAC std_ss [DIV_LT_X]
  \\ FULL_SIMP_TAC std_ss [DECIDE ``n < 1 = (n = 0:num)``]
  \\ ONCE_REWRITE_TAC [num2str_def]
  \\ ASM_SIMP_TAC std_ss [LENGTH_APPEND,APPEND,dec2str_def,LENGTH]
  \\ FULL_SIMP_TAC std_ss [DECIDE ``(n <> 0) = 0 < n:num``]
  \\ REPEAT STRIP_TAC
  \\ `(n DIV 10 < n)` by (ASM_SIMP_TAC std_ss [DIV_LT_X] THEN DECIDE_TAC)
  \\ `STRLEN (num2str (n DIV 10)) <= n DIV 10` by METIS_TAC []
  \\ ASSUME_TAC (Q.SPEC `n` (MATCH_MP DIVISION (DECIDE ``0 < 10:num``)))
  \\ DECIDE_TAC);

val arm_print_num_lemma = prove(
  ``!n r7 a f p.
      (p * one_space r7 (LENGTH (num2str n)) a) (fun2set (f,df)) /\ n < 2 ** 30 ==>
      ?fi. arm_print_num_pre (n2w (4 * n + 2),r7,df,f) /\
           (arm_print_num (n2w (4 * n + 2),r7,df,f) = (a,fi,df)) /\
           (p * one_string r7 (num2str n) a) (fun2set (fi,df))``,
  REWRITE_TAC [arm_print_num_def,arm_print_num_pre_def]
  \\ SIMP_TAC std_ss [LET_DEF]
  \\ REPEAT STRIP_TAC
  \\ `4 * n + 2 < dimword (:32)` by (SIMP_TAC (std_ss++SIZES_ss) [] \\ DECIDE_TAC)
  \\ IMP_RES_TAC word_LSR_n2w
  \\ ASM_SIMP_TAC std_ss []
  \\ ONCE_REWRITE_TAC [MULT_COMM]
  \\ SIMP_TAC std_ss [DIV_MULT]
  \\ `n < 2**31` by (SIMP_TAC std_ss [] \\ DECIDE_TAC)
  \\ IMP_RES_TAC arm_str2num_lemma
  \\ ASM_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC std_ss [one_string_def]
  \\ `LENGTH (MAP (n2w o ORD) (REVERSE (num2str n))) < 2**32 /\
      LENGTH (MAP ((n2w:num->word8) o ORD) (REVERSE (num2str n))) < 2**32` suffices_by
  (STRIP_TAC THEN IMP_RES_TAC arm_string_rev_lemma
    \\ FULL_SIMP_TAC std_ss [rich_listTheory.MAP_REVERSE,REVERSE_REVERSE])
  \\ REWRITE_TAC [LENGTH_MAP,rich_listTheory.LENGTH_REVERSE]
  \\ Cases_on `n = 0` THEN1 (ASM_SIMP_TAC std_ss [] \\ EVAL_TAC)
  \\ MATCH_MP_TAC LESS_EQ_LESS_TRANS
  \\ Q.EXISTS_TAC `n`
  \\ FULL_SIMP_TAC std_ss [LENGTH_num2str,DECIDE ``n <> 0 = 0 < n:num``]
  \\ DECIDE_TAC)


(* copy a string *)

val (thms,arm_string_copy_def,arm_string_copy_pre_def) = compile_all ``
  arm_string_copy (r5,r6,r7,dg:word32 set,g:word32->word8,df:word32 set,f:word32->word8) =
    if r5 = 0w:word32 then (r7,dg,g,f,df) else
      let r3 = (w2w (g r6)):word32 in
      let r6 = r6 + 1w in
      let f = (r7 =+ w2w r3) f in
      let r7 = r7 + 1w in
      let r5 = r5 - 1w in
        arm_string_copy (r5,r6,r7,dg,g,df,f)``

val arm_string_copy_lemma = prove(
  ``!s r6 r7 f p.
      string_mem s (r6,g,dg) /\
      (p * one_space r7 (LENGTH s) a) (fun2set (f,df)) /\ LENGTH s < 2 ** 32 ==>
      ?fi. arm_string_copy_pre (n2w (LENGTH s),r6,r7,dg,g,df,f) /\
           (arm_string_copy (n2w (LENGTH s),r6,r7,dg,g,df,f) = (a,dg,g,fi,df)) /\
           (p * one_string r7 s a) (fun2set (fi,df))``,
  Induct \\ ONCE_REWRITE_TAC [arm_string_copy_def,arm_string_copy_pre_def]
  \\ SIMP_TAC std_ss [one_string_def,one_list_def,LENGTH,one_space_def,MAP,cond_STAR]
  \\ SIMP_TAC (std_ss++SIZES_ss) [n2w_11,DECIDE ``~(SUC n = 0:num)``,LET_DEF]
  \\ SIMP_TAC std_ss [ADD1,GSYM word_add_n2w,WORD_ADD_SUB,string_mem_def,w2w_w2w_lemma]
  \\ SIMP_TAC std_ss [STAR_ASSOC,SEP_CLAUSES]
  \\ SIMP_TAC std_ss [SEP_EXISTS]
  \\ REPEAT STRIP_TAC
  \\ `STRLEN s < 4294967296` by DECIDE_TAC
  \\ FULL_SIMP_TAC std_ss []
  \\ `(p * one (r7, n2w (ORD h)) * one_space (r7 + 0x1w) (STRLEN s) a)
        (fun2set ((r7 =+ n2w (ORD h)) f,df))` by SEP_WRITE_TAC
  \\ RES_TAC \\ ASM_SIMP_TAC std_ss []
  \\ `(f r7 = y) /\ r7 IN df` by SEP_READ_TAC
  \\ FULL_SIMP_TAC (std_ss++star_ss) [one_string_def]);


(* printing a symbol *)

val (thms,arm_copy_symbol_def,arm_copy_symbol_pre_def) = compile_all ``
  arm_copy_symbol (r3,r7,dm:word32 set,m:word32->word32,dg:word32 set,g:word32->word8,df:word32 set,f:word32->word8) =
    let r5 = m (r3 - 3w) in  (* length *)
    let r6 = r3 + 5w in  (* init pointer *)
    let (r7,dg,g,f,df) = arm_string_copy (r5,r6,r7,dg,g,df,f) in
      (r7,dm,m,dg,g,df,f)``

val symbol_table_IMP = prove(
  ``!xs a w sym.
      (a + w - 0x3w,s) IN sym /\
      symbol_table xs sym (a,dm,m,dg,g) /\ ALL_DISTINCT xs ==>
      (m (a + w - 0x3w) = n2w (STRLEN s)) /\ (a + w - 0x3w) IN dm /\
      string_mem s (a + w + 0x5w,g,dg)``,
  Induct THEN1
   (SIMP_TAC std_ss [symbol_table_def,set_add_def,EXTENSION,FORALL_PROD,
       NOT_IN_EMPTY] \\ SIMP_TAC std_ss [IN_DEF,set_add_def]
    \\ METIS_TAC [])
  \\ NTAC 5 STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [ALL_DISTINCT]
  \\ FULL_SIMP_TAC std_ss [symbol_table_def,LET_DEF]
  \\ REVERSE (Cases_on `h = s`) THENL [
    Q.ABBREV_TAC `a2 = a + n2w (8 + (STRLEN h + 3) DIV 4 * 4)`
    \\ Q.PAT_X_ASSUM `!a. bbb` (MP_TAC o Q.SPECL [`a2`,`(w + a) - a2`,`sym DELETE (a,h)`])
    \\ ASM_SIMP_TAC std_ss [WORD_SUB_ADD2]
    \\ FULL_SIMP_TAC std_ss [IN_DELETE,AC WORD_ADD_COMM WORD_ADD_ASSOC],
    Cases_on `(a + w - 0x3w,s) IN sym DELETE (a,h)`
    THEN1 (IMP_RES_TAC symbol_table_MEM \\ METIS_TAC [])
    \\ POP_ASSUM MP_TAC
    \\ ASM_SIMP_TAC std_ss [IN_DELETE]
    \\ ONCE_REWRITE_TAC [EQ_SYM_EQ]
    \\ SIMP_TAC std_ss [WORD_EQ_ADD_CANCEL,WORD_ADD_SUB_ASSOC]
    \\ FULL_SIMP_TAC std_ss [WORD_EQ_SUB_ZERO,word_arith_lemma1,INSERT_SUBSET]]);

val arm_copy_symbol_lemma = prove(
  ``!r3 r7 r9 f p.
      ALIGNED r9 /\ ALIGNED (r3 - 0x3w) /\ (r3 - 0x3w,s) IN sym /\
      lisp_symbol_table sym (r9,dm,m,dg,g) /\ STRLEN s < 2**32 /\
      (p * one_space r7 (LENGTH s) a) (fun2set (f,df)) ==>
      ?fi. arm_copy_symbol_pre (r3 + r9,r7,dm,m,dg,g,df,f) /\
           (arm_copy_symbol (r3 + r9,r7,dm,m,dg,g,df,f) = (a,dm,m,dg,g,df,fi)) /\
           (p * one_string r7 s a) (fun2set (fi,df))``,
  SIMP_TAC std_ss [lisp_symbol_table_def] \\ REPEAT STRIP_TAC
  \\ REPEAT (POP_ASSUM MP_TAC)
  \\ Q.SPEC_TAC (`builtin_symbols ++ symbols`,`xs`)
  \\ REPEAT STRIP_TAC
  \\ `(r9 + r3 - 0x3w,s) IN (set_add r9 sym)` by
   (SIMP_TAC std_ss [IN_DEF,set_add_def,WORD_ADD_SUB_ASSOC]
    \\ ONCE_REWRITE_TAC [WORD_ADD_COMM]
    \\ FULL_SIMP_TAC std_ss [WORD_SUB_ADD,IN_DEF])
  \\ IMP_RES_TAC symbol_table_IMP
  \\ ASM_SIMP_TAC std_ss [arm_copy_symbol_def,arm_copy_symbol_pre_def,LET_DEF]
  \\ ONCE_REWRITE_TAC [WORD_ADD_COMM]
  \\ ASM_SIMP_TAC std_ss [ALIGNED_INTRO,ALIGNED_ADD_EQ,WORD_ADD_SUB_ASSOC]
  \\ `?fi. arm_string_copy_pre (n2w (STRLEN s),r9 + r3 + 0x5w,r7,dg,g,df,f) /\
        (arm_string_copy (n2w (STRLEN s),r9 + r3 + 0x5w,r7,dg,g,df,f) =
        (a,dg,g,fi,df)) /\ (p * one_string r7 s a) (fun2set (fi,df))`
          by METIS_TAC [SIMP_RULE std_ss [] arm_string_copy_lemma]
  \\ FULL_SIMP_TAC std_ss [AC WORD_ADD_ASSOC WORD_ADD_COMM]);



(* lisp_inv ==> lisp_tree *)

val lisp_tree_def = Define `
  (lisp_tree (Val k) (a,dm,m) sym = (a = n2w (k * 4 + 2)) /\ k < 2 ** 30) /\
  (lisp_tree (Sym s) (a,dm,m) sym = ALIGNED (a - 3w) /\ (a - 3w,s) IN sym) /\
  (lisp_tree (Dot x y) (a,dm,m) sym = a IN dm /\ (a + 4w) IN dm /\ ALIGNED a /\
    lisp_tree x (m a,dm,m) sym /\ lisp_tree y (m (a+4w),dm,m) sym)`;

val lisp_x_IMP_lisp_tree = prove(
  ``!t w a i n sym.
      lisp_x t (w,ch_active_set (a,i,n),m) sym ==>
      lisp_tree t (w,ch_active_set2 (a,i,n),m) sym``,
  Induct \\ SIMP_TAC std_ss [lisp_tree_def,lisp_x_def,ALIGNED_INTRO]
  \\ REVERSE (REPEAT STRIP_TAC)
  THEN1 METIS_TAC [] THEN1 METIS_TAC []
  \\ ASM_SIMP_TAC std_ss [ch_active_set2_def,IN_UNION]
  \\ DISJ2_TAC
  \\ FULL_SIMP_TAC std_ss [ch_active_set_def,GSPECIFICATION]
  \\ SIMP_TAC std_ss [GSYM WORD_ADD_ASSOC,WORD_EQ_ADD_CANCEL]
  \\ SIMP_TAC std_ss [word_mul_n2w,word_add_n2w]
  \\ Q.EXISTS_TAC `j` \\ ASM_SIMP_TAC std_ss []);

val lisp_inv_IMP_lisp_tree = prove(
  ``lisp_inv (t1,t2,t3,t4,t5,t6,l) (w1,w2,w3,w4,w5,w6,a,dm,m,sym,rest) ==>
    ?i n. lisp_tree t1 (w1,ch_active_set2 (a,i,n),m) sym /\
          0 < i /\ i <= n /\ n <= i + l``,
  SIMP_TAC std_ss [lisp_inv_def,LET_DEF] \\ REPEAT STRIP_TAC
  \\ Q.EXISTS_TAC `if u then 1 + l else 1`
  \\ Q.EXISTS_TAC `i` \\ STRIP_TAC
  THEN1 (MATCH_MP_TAC lisp_x_IMP_lisp_tree \\ ASM_SIMP_TAC std_ss [])
  \\ Cases_on `u` \\ FULL_SIMP_TAC std_ss [] \\ DECIDE_TAC);


(* testing isQuote *)

val lisp_symbol_table_consts = prove(
  ``!sym a dm m dg g.
      lisp_symbol_table sym (a,rest) ==>
        ((w - 3w, "nil") IN sym ==> (w = 3w)) /\
        ((w - 3w, "quote") IN sym ==> (w = 27w))``,
  REPEAT STRIP_TAC
  \\ IMP_RES_TAC builti_symbols_thm THENL [
    `w - 3w = ADDR32 0w` by METIS_TAC [lisp_symbol_table_11]
    \\ FULL_SIMP_TAC std_ss [WORD_EQ_SUB_RADD] \\ EVAL_TAC,
    `w - 3w = ADDR32 6w` by METIS_TAC [lisp_symbol_table_11]
    \\ FULL_SIMP_TAC std_ss [WORD_EQ_SUB_RADD] \\ EVAL_TAC]);

val (thms,arm_is_quote_def,arm_is_quote_pre_def) = compile_all ``
  arm_is_quote (r3:word32,r4:word32,dh:word32 set,h:word32->word32) =
    if r4 && 2w = 0w then (let r5 = 0w in (r3,r4,r5,dh,h)) else
      let r5 = h r3 in
      let r6 = h (r3 + 4w) in
        if ~(r5 = 27w) then (let r5 = 0w in (r3,r4,r5,dh,h)) else
        if ~(r6 && 3w = 0w) then (let r5 = 0w in (r3,r4,r5,dh,h)) else
          let r5 = h (r6 + 4w) in
          let r6 = h r6 in
            if ~(r5 = 3w) then (let r5 = 0w in (r3,r4,r5,dh,h)) else
              let r3 = r6 in (r3,r4,r5,dh,h)``;

val arm_is_quote_lemma = prove(
  ``!x w v dh h.
      lisp_symbol_table sym (a,rest) /\
      lisp_tree x (w,dh,h) sym /\ isDot x ==>
      arm_is_quote_pre(w,v,dh,h) /\
      if isQuote x /\ ~(v && 2w = 0w) then
        (arm_is_quote(w,v,dh,h) = (h (h (w + 4w)), v, 3w, dh,h)) /\
        lisp_tree (CAR (CDR x)) (h (h (w + 4w)),dh,h) sym
      else
        (arm_is_quote(w,v,dh,h) = (w, v, 0w, dh,h))``,
  NTAC 6 STRIP_TAC \\ Cases_on `~(v && 2w = 0w) /\ isQuote x` THEN1
   (FULL_SIMP_TAC std_ss [isQuote_thm,SExp_11,CAR_def,CDR_def]
    \\ FULL_SIMP_TAC std_ss [lisp_tree_def]
    \\ ONCE_REWRITE_TAC [arm_is_quote_def,arm_is_quote_pre_def]
    \\ ASM_SIMP_TAC std_ss [LET_DEF,ALIGNED_INTRO]
    \\ ONCE_REWRITE_TAC [ALIGNED_MOD_4]
    \\ ASM_SIMP_TAC std_ss [WORD_ADD_0]
    \\ IMP_RES_TAC lisp_symbol_table_consts
    \\ ASM_SIMP_TAC std_ss [])
  \\ ASM_SIMP_TAC std_ss []
  \\ Cases_on `v && 2w = 0w` THEN1
   (ASM_SIMP_TAC std_ss [arm_is_quote_pre_def,arm_is_quote_def,LET_DEF]
    \\ ONCE_REWRITE_TAC [WORD_AND_COMM] \\ ASM_SIMP_TAC std_ss [])
  \\ Q.PAT_X_ASSUM `~(bbb /\ cc)` MP_TAC
  \\ ASM_SIMP_TAC std_ss []
  \\ STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [isQuote_thm,SExp_11,CAR_def,CDR_def]
  \\ Q.PAT_X_ASSUM `isDot x` ASSUME_TAC
  \\ FULL_SIMP_TAC std_ss [isDot_thm,SExp_11,lisp_tree_def]
  \\ ONCE_REWRITE_TAC [arm_is_quote_def,arm_is_quote_pre_def]
  \\ ASM_SIMP_TAC std_ss [LET_DEF,ALIGNED_INTRO]
  \\ ONCE_REWRITE_TAC [ALIGNED_MOD_4]
  \\ ASM_SIMP_TAC std_ss [WORD_ADD_0]
  \\ REVERSE (Cases_on `h w = 0x1Bw` \\ ASM_SIMP_TAC std_ss [])
  THEN1 FULL_SIMP_TAC std_ss [lisp_tree_def]
  \\ Cases_on `ALIGNED (h (w + 0x4w))` \\ ASM_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC std_ss [SExp_11,lisp_tree_def]
  \\ `isDot b` by
   (Cases_on `b` \\ FULL_SIMP_TAC std_ss [lisp_tree_def,isDot_def]
    \\ IMP_RES_TAC NOT_ALIGNED
    \\ FULL_SIMP_TAC std_ss [WORD_SUB_ADD]
    \\ FULL_SIMP_TAC std_ss [GSYM word_add_n2w,RW1 [MULT_COMM] (GSYM ADDR32_n2w)]
    \\ Q.PAT_X_ASSUM `h (w + 0x4w) = ADDR32 (n2w n) + 0x2w` ASSUME_TAC
    \\ FULL_SIMP_TAC std_ss [word_arith_lemma1]
    \\ Q.PAT_X_ASSUM `~ALIGNED (ADDR32 (n2w n) + 0x4w)` MP_TAC
    \\ ONCE_REWRITE_TAC [ALIGNED_MOD_4]
    \\ ASM_SIMP_TAC std_ss [WORD_ADD_0,ALIGNED_ADDR32]
    \\ ONCE_REWRITE_TAC [ALIGNED_MOD_4]
    \\ ASM_SIMP_TAC std_ss [WORD_ADD_0,ALIGNED_ADDR32])
  \\ FULL_SIMP_TAC std_ss [isDot_thm,lisp_tree_def]
  \\ FULL_SIMP_TAC std_ss [isDot_thm,lisp_tree_def]
  \\ Cases_on `h (h (w + 0x4w) + 0x4w) <> 0x3w`
  \\ FULL_SIMP_TAC std_ss [isDot_thm,lisp_tree_def,SExp_11]
  THEN1
   (REVERSE (Cases_on `a'`)
    \\ FULL_SIMP_TAC std_ss [lisp_tree_def,ALIGNED_n2w]
    \\ IMP_RES_TAC builti_symbols_thm THEN1
     (FULL_SIMP_TAC std_ss [SExp_11]
      \\ `0x1Bw - 0x3w <> ADDR32 0x6w` by METIS_TAC [lisp_symbol_table_11]
      \\ FULL_SIMP_TAC std_ss [WORD_EQ_SUB_RADD,ADDR32_n2w,word_add_n2w])
    \\ FULL_SIMP_TAC std_ss [GSYM ADDR32_n2w,GSYM word_add_n2w,GSYM WORD_EQ_SUB_RADD]
    \\ FULL_SIMP_TAC std_ss [word_arith_lemma2,RW1 [MULT_COMM] (GSYM ADDR32_n2w)]
    \\ `ALIGNED (ADDR32 (n2w n)) /\ ~(ALIGNED (0x19w))` by
      SIMP_TAC std_ss [ALIGNED_ADDR32,ALIGNED_n2w]
    \\ FULL_SIMP_TAC std_ss [] \\ METIS_TAC [])
  \\ REVERSE (Cases_on `b'`)
  \\ FULL_SIMP_TAC std_ss [lisp_tree_def,ALIGNED_n2w]
  \\ IMP_RES_TAC builti_symbols_thm THEN1
    (FULL_SIMP_TAC std_ss [SExp_11]
     \\ `0x3w - 0x3w <> ADDR32 0w` by METIS_TAC [lisp_symbol_table_11]
     \\ FULL_SIMP_TAC std_ss [WORD_EQ_SUB_RADD,ADDR32_n2w,word_add_n2w])
   \\ FULL_SIMP_TAC std_ss [GSYM ADDR32_n2w,GSYM word_add_n2w,GSYM WORD_EQ_SUB_RADD]
   \\ FULL_SIMP_TAC std_ss [word_arith_lemma2,RW1 [MULT_COMM] (GSYM ADDR32_n2w)]
   \\ `ALIGNED (ADDR32 (n2w n)) /\ ~(ALIGNED (0x1w))` by
        SIMP_TAC std_ss [ALIGNED_ADDR32,ALIGNED_n2w]
   \\ FULL_SIMP_TAC std_ss [] \\ METIS_TAC []);


(* main print loop

  r4 = 000 --> stop
  r4 = 001 --> print second part of dot, no parenthesis
  r4 = 010 --> print second part of dot, with parenthesis
  r4 = 101 --> print normal expression, no parenthesis
  r4 = 110 --> print normal expression, with parenthesis
  r4 = 011 --> print parenthesis only

*)

val (thms,arm_print_exit_def,arm_print_exit_pre_def) = compile_all ``
  arm_print_exit(r3:word32,r4:word32) =
    (* return r5: 0w = do nothing; 1w = print ")"; 2w = print " " or " . " *)
    if r4 = 3w then let r5 = 1w in (r3,r4,r5) else
    if r3 = 3w then let r5 = r4 - 1w in (r3,r4,r5) else
      let r5 = 2w in (r3,r4,r5)``;

val (thms,arm_set_return_def,arm_set_return_pre_def) = compile_all ``
  arm_set_return (r4:word32,r5:word32,r8:word32,dh:word32 set,h:word32->word32) =
    if r4 = 2w then
      let r5 = 3w in
      let h = (r8 =+ r5) h in
      let r4 = 5w in
        (r4,r5,r8,dh,h)
    else
      let r8 = r8 - 8w in
      let r4 = 5w:word32 in
        (r4,r5,r8,dh,h)``;

(* val (arm_print_loop_aux_def,arm_print_loop_aux_pre_def) = mc_tailrecLib.tailrec_define *)
val (thms,arm_print_loop_aux_def,arm_print_loop_aux_pre_def) = compile_all ``
  arm_print_loop_aux (r3:word32,r4:word32,r7:word32,r8:word32,dh:word32 set,h:word32->word32,df:word32 set,f:word32->word8) =
    let (r3,r4,r5) = arm_print_exit(r3,r4) in
      if r5 = 2w then (* print second part of dot *)
        let r6 = 32w:word32 in
        let (r4,r5,r8,dh,h) = arm_set_return (r4,r5,r8,dh,h) in
        let f = (r7 =+ w2w r6) f in
          if r3 && 3w = 0w then (* print " " *)
            let r7 = r7 + 1w in
              (r3,r4,r7,r8,dh,h,df,f)
          else (* print " . " *)
            let r5 = 46w:word32 in
            let f = (r7 + 2w =+ w2w r6) f in
            let f = (r7 + 1w =+ w2w r5) f in
            let r7 = r7 + 3w in
              (r3,r4,r7,r8,dh,h,df,f)
      else
        let r8 = r8 - 8w in
        let r4 = h r8 in
        let r3 = h (r8 + 4w) in
          if r5 = 0w then
            (r3,r4,r7,r8,dh,h,df,f)
          else
            let r5 = 41w:word32 in
            let f = (r7 =+ w2w r5) f in
            let r7 = r7 + 1w in
              (r3,r4,r7,r8,dh,h,df,f)``;

val (thms,arm_print_loop_def,arm_print_loop_pre_def) = compile_all ``
  arm_print_loop (r3:word32,r4:word32,r7:word32,r8:word32,r9:word32,dh:word32 set,h:word32->word32,dm:word32 set,m:word32->word32,dg:word32 set,g:word32->word8,df:word32 set,f:word32->word8) =
  if r4 = 0w then
    let r5 = 0w:word32 in
    let f = (r7 =+ w2w r5) f in
    let r7 = r7 + 1w in
      (r3,r4,r7,r8,r9,dh,h,dm,m,dg,g,df,f)
  else
    if r4 && 4w = 0w then (* if true, first part of dot pair evaluated *)
      let (r3,r4,r7,r8,dh,h,df,f) = arm_print_loop_aux (r3,r4,r7,r8,dh,h,df,f) in
        arm_print_loop (r3,r4,r7,r8,r9,dh,h,dm,m,dg,g,df,f)
    else if ~(r3 && 1w = 0w) then (* must be symbol *)
      let r3 = r3 + r9 in
      let (r7,dm,m,dg,g,df,f) = arm_copy_symbol (r3,r7,dm,m,dg,g,df,f) in
      let r4 = h r8 in
      let r3 = h (r8 + 4w) in
        arm_print_loop (r3,r4,r7,r8,r9,dh,h,dm,m,dg,g,df,f)
    else if ~(r3 && 3w = 0w) then (* must be val *)
      let (r7,f,df) = arm_print_num (r3,r7,df,f) in
      let r4 = h r8 in
      let r3 = h (r8 + 4w) in
        arm_print_loop (r3,r4,r7,r8,r9,dh,h,dm,m,dg,g,df,f)
    else (* must be a pair *)
      let (r3,r4,r5,dh,h) = arm_is_quote (r3,r4,dh,h) in
        if ~(r5 = 0w) then (* print quote *)
          let r5 = 39w:word32 in
          let f = (r7 =+ w2w r5) f in
          let r7 = r7 + 1w in
          let r4 = 6w in
            arm_print_loop (r3,r4,r7,r8,r9,dh,h,dm,m,dg,g,df,f)
        else
          let r8 = r8 + 8w in
          let r5 = h (r3 + 4w) in
          let r6 = r4 - 4w in
          let r3 = h r3 in
          let h = (r8 =+ r6) h in
          let r6 = 40w:word32 in
          let h = (r8 + 4w =+ r5) h in
            if r4 && 2w = 0w then (* parenthesis *)
              let r4 = 6w in
                arm_print_loop (r3,r4,r7,r8,r9,dh,h,dm,m,dg,g,df,f)
            else
              let r4 = 6w:word32 in
              let f = (r7 =+ w2w r6) f in
              let r7 = r7 + 1w in
                arm_print_loop (r3,r4,r7,r8,r9,dh,h,dm,m,dg,g,df,f)``



val arm_print_loop1_def = Define `arm_print_loop1 = arm_print_loop`;
val arm_print_loop1_pre_def = Define `arm_print_loop1_pre = arm_print_loop_pre`;

val lisp_tree_SUBSET = prove(
  ``!t w. lisp_tree t (w,d,h) sym /\ d SUBSET dh ==>
          lisp_tree t (w,dh,h) sym``,
  Induct \\ SIMP_TAC std_ss [lisp_tree_def] \\ METIS_TAC [SUBSET_DEF]);

val stack_slots_def = Define `
  (stack_slots (a:word32) 0 = emp) /\
  (stack_slots a (SUC n) = SEP_EXISTS u1 u2. one (a,u1:word32) * one (a+4w,u2) * stack_slots (a+8w) n)`;

val stack_slots_ADD = prove(
  ``!n a m. ?fr. stack_slots a (n + m) = stack_slots a n * fr``,
  Induct \\ SIMP_TAC std_ss [stack_slots_def,SEP_CLAUSES,ADD]
  \\ REPEAT STRIP_TAC
  \\ POP_ASSUM (STRIP_ASSUME_TAC o Q.SPECL[`a+8w`,`m`])
  \\ ASM_SIMP_TAC std_ss [STAR_ASSOC] \\ METIS_TAC []);

val IF_SIMPS = prove(
  ``!b f x g y.
      ((if b then f x else g y) = (if b then f else g) (if b then x else y)) /\
      ((if b then x else x) = x)``,
  Cases \\ SIMP_TAC std_ss []);

val NOT_IN_lisp_tree = prove(
  ``!t w d a h r3.
      ~(a IN d) ==>
      (lisp_tree t (r3,d,(a =+ w) h) sym = lisp_tree t (r3,d,h) sym)``,
  Induct \\ ASM_SIMP_TAC std_ss [lisp_tree_def,APPLY_UPDATE_THM] \\ METIS_TAC [])

val one_space_ADD = prove(
  ``!m n a c.
      one_space a (m + n) c =
      one_space a m (a + n2w m) *
      one_space (a + n2w m) n c``,
  Induct
  \\ ASM_SIMP_TAC std_ss [one_space_def,WORD_ADD_0,SEP_CLAUSES,ADD]
  \\ SIMP_TAC std_ss [ADD1,GSYM word_add_n2w]
  \\ SIMP_TAC std_ss [AC WORD_ADD_ASSOC WORD_ADD_COMM,STAR_ASSOC]);

val one_string_STRCAT = prove(
  ``!s t a c.
      one_string a (s ++ t) c =
      one_string a s (a + n2w (LENGTH s)) *
      one_string (a + n2w (LENGTH s)) t c``,
  Induct
  \\ FULL_SIMP_TAC std_ss [one_string_def,WORD_ADD_0,SEP_CLAUSES,
       ADD,MAP,LENGTH,one_list_def,APPEND]
  \\ SIMP_TAC std_ss [ADD1,GSYM word_add_n2w]
  \\ SIMP_TAC std_ss [AC WORD_ADD_ASSOC WORD_ADD_COMM,STAR_ASSOC]);

val stack_slots_MAX = prove(
  ``!m n a. ?fr. stack_slots a (MAX m n) =
                 stack_slots a m * fr``,
  REPEAT STRIP_TAC
  \\ SIMP_TAC std_ss [MAX_DEF]
  \\ REVERSE (Cases_on `m < n`)
  \\ ASM_SIMP_TAC std_ss []
  THEN1 (Q.EXISTS_TAC `emp` \\ SIMP_TAC std_ss [SEP_CLAUSES])
  \\ `m <= n` by DECIDE_TAC
  \\ FULL_SIMP_TAC std_ss [LESS_EQ_EXISTS]
  \\ SIMP_TAC std_ss [stack_slots_ADD]
  \\ METIS_TAC [stack_slots_ADD]);

val fun_eq_def = Define `fun_eq d h1 h2 = !w. w IN d ==> (h1 w = h2 w)`;

val fun_eq_lisp_tree = prove(
  ``!d h hi.
      fun_eq d h hi ==>
      !t a sym. lisp_tree t (a,d,h) sym = lisp_tree t (a,d,hi) sym``,
  SIMP_TAC std_ss [fun_eq_def] \\ NTAC 4 STRIP_TAC
  \\ Induct \\ SIMP_TAC std_ss [lisp_tree_def]
  \\ REPEAT STRIP_TAC
  \\ Cases_on `a IN d /\ a + 4w IN d` \\ ASM_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC std_ss []);

val arm_print_loop_lemma = prove(
  ``!t b p w1 w2 r3 r7 r8 a h f q c.
      let s = sexp2string_aux (t, b) in
      let r4 = if b then 6w else 5w in
        (p * one_space r7 (STRLEN s) c) (fun2set (f,df)) /\
        lisp_symbol_table sym (r9,dm,m,dg,g) /\
        ALIGNED r8 /\ ALIGNED r9 /\ STRLEN s < 2**32 /\
        lisp_tree t (r3,d,h) sym /\ d SUBSET dh /\
        (q * one (r8,w2) * one (r8 + 4w,w1) * stack_slots (r8 + 8w) (LDEPTH t))
           (fun2set (h,dh DIFF d)) ==>
        ?hi fi.
          (arm_print_loop_pre (r3,r4,r7,r8,r9,dh,h,dm,m,dg,g,df,f) =
           arm_print_loop1_pre (w1,w2,c,r8,r9,dh,hi,dm,m,dg,g,df,fi)) /\
          (arm_print_loop (r3,r4,r7,r8,r9,dh,h,dm,m,dg,g,df,f) =
           arm_print_loop1 (w1,w2,c,r8,r9,dh,hi,dm,m,dg,g,df,fi)) /\
          (p * one_string r7 s c) (fun2set (fi,df)) /\
          (q * one (r8,w2) * one (r8 + 4w,w1) * stack_slots (r8 + 8w) (LDEPTH t))
             (fun2set (hi,dh DIFF d)) /\ fun_eq d h hi``,
  completeInduct_on `LSIZE t`
  \\ POP_ASSUM (ASSUME_TAC o RW1 [GSYM CONTAINER_def])
  \\ SIMP_TAC std_ss [LET_DEF]
  \\ REPEAT STRIP_TAC
  \\ `~((if b then 6w else 5w) = 0w:word32)` by (Cases_on `b` \\ EVAL_TAC)
  \\ `~((if b then 6w else 5w) && 4w = 0w:word32)` by (Cases_on `b` \\ EVAL_TAC)
  \\ `~((if b then 0x6w else 0x5w) = 0x3w:word32)` by (Cases_on `b` \\ EVAL_TAC)
  \\ ONCE_REWRITE_TAC [arm_print_loop_def]
  \\ ASM_SIMP_TAC std_ss [LET_DEF]
  \\ Cases_on `isVal t` THEN1
   (Q.PAT_X_ASSUM `CONTAINER (!m. bbb)` (K ALL_TAC)
    \\ FULL_SIMP_TAC std_ss [isVal_thm]
    \\ FULL_SIMP_TAC std_ss [lisp_tree_def]
    \\ FULL_SIMP_TAC std_ss [STAR_ASSOC,ALIGNED_INTRO]
    \\ `~ALIGNED (n2w (a * 4 + 2))` by
     (ONCE_REWRITE_TAC [MULT_COMM]
      \\ SIMP_TAC std_ss [GSYM word_add_n2w]
      \\ SIMP_TAC std_ss [GSYM ADDR32_n2w]
      \\ SIMP_TAC std_ss [ALIGNED_ADD_EQ,ALIGNED_ADDR32,ALIGNED_n2w])
    \\ ASM_SIMP_TAC std_ss []
    \\ `n2w (a * 4 + 2) && 0x1w = 0w:word32` by
     (SIMP_TAC std_ss [n2w_and_1]
      \\ REWRITE_TAC [DECIDE ``n * 4 + 2 = (n * 2 + 1) * 2:num``]
      \\ REWRITE_TAC [MATCH_MP MOD_EQ_0 (DECIDE ``0<2:num``)])
    \\ ASM_SIMP_TAC std_ss []
    \\ FULL_SIMP_TAC std_ss [sexp2string_aux_def]
    \\ (STRIP_ASSUME_TAC o UNDISCH_ALL o Q.SPECL [`a`,`r7`,`c`,`f`,`p`] o
        RW1 [MULT_COMM] o
        SIMP_RULE std_ss [GSYM AND_IMP_INTRO]) arm_print_num_lemma
    \\ ASM_SIMP_TAC std_ss []
    \\ `(h r8 = w2) /\ r8 IN dh DIFF d` by SEP_READ_TAC
    \\ `(h (r8 + 4w) = w1) /\ (r8 + 4w) IN dh DIFF d` by SEP_READ_TAC
    \\ FULL_SIMP_TAC std_ss [IN_DIFF]
    \\ Q.EXISTS_TAC `h`
    \\ Q.EXISTS_TAC `fi`
    \\ ASM_SIMP_TAC std_ss [arm_print_loop1_def]
    \\ ONCE_REWRITE_TAC [arm_print_loop_pre_def]
    \\ ASM_SIMP_TAC std_ss [arm_print_loop1_pre_def,LET_DEF]
    \\ ASM_SIMP_TAC std_ss [LET_DEF,ALIGNED_INTRO]
    \\ ONCE_REWRITE_TAC [WORD_AND_COMM]
    \\ ASM_SIMP_TAC std_ss [fun_eq_def]
    \\ ALIGNED_TAC)
  \\ Cases_on `isSym t` THEN1
   (Q.PAT_X_ASSUM `CONTAINER (!m. bbb)` (K ALL_TAC)
    \\ FULL_SIMP_TAC std_ss [isSym_thm]
    \\ FULL_SIMP_TAC std_ss [isSym_thm,lisp_tree_def,GSYM STAR_ASSOC]
    \\ FULL_SIMP_TAC std_ss [STAR_ASSOC,ALIGNED_INTRO]
    \\ `~((r3 && 0x1w) = 0x0w)` by
     (`ALIGNED (r3 - 3w + 4w)` by ALIGNED_TAC
      \\ FULL_SIMP_TAC std_ss [word_arith_lemma3]
      \\ POP_ASSUM MP_TAC
      \\ REPEAT (POP_ASSUM (K ALL_TAC))
      \\ Q.SPEC_TAC (`r3`,`w`) \\ Cases_word
      \\ SIMP_TAC std_ss [ALIGNED_n2w,word_add_n2w,n2w_and_1]
      \\ SIMP_TAC std_ss [bitTheory.MOD_PLUS_1]
      \\ STRIP_TAC
      \\ STRIP_ASSUME_TAC (Q.SPEC `n` (MATCH_MP DIVISION (DECIDE ``0<4:num``)))
      \\ `n MOD 4 = 3` by DECIDE_TAC
      \\ ONCE_ASM_REWRITE_TAC []
      \\ Q.PAT_X_ASSUM `n = mmm` (K ALL_TAC)
      \\ ASM_SIMP_TAC std_ss []
      \\ REWRITE_TAC [DECIDE ``m * 4 + 3 = (m * 2 + 1) * 2 + 1:num``]
      \\ REWRITE_TAC [MATCH_MP MOD_MULT (DECIDE ``1 < 2:num``)] \\ EVAL_TAC)
    \\ FULL_SIMP_TAC std_ss [sexp2string_aux_def]
    \\ `(h r8 = w2) /\ r8 IN dh DIFF d` by SEP_READ_TAC
    \\ `(h (r8 + 4w) = w1) /\ (r8 + 4w) IN dh DIFF d` by SEP_READ_TAC
    \\ FULL_SIMP_TAC std_ss [IN_DIFF]
    \\ `?fi. arm_copy_symbol_pre (r3 + r9,r7,dm,m,dg,g,df,f) /\
             (arm_copy_symbol (r3 + r9,r7,dm,m,dg,g,df,f) =
               (c,dm,m,dg,g,df,fi)) /\
             (p * one_string r7 a c) (fun2set (fi,df))` by
              METIS_TAC [EVAL ``(2:num)**32``,arm_copy_symbol_lemma]
    \\ Q.EXISTS_TAC `h`
    \\ Q.EXISTS_TAC `fi`
    \\ ASM_SIMP_TAC std_ss [arm_print_loop1_def]
    \\ ONCE_REWRITE_TAC [arm_print_loop_pre_def]
    \\ ASM_SIMP_TAC std_ss [arm_print_loop1_pre_def,LET_DEF]
    \\ ASM_SIMP_TAC std_ss [LET_DEF,ALIGNED_INTRO]
    \\ ONCE_REWRITE_TAC [WORD_AND_COMM]
    \\ ASM_SIMP_TAC std_ss [fun_eq_def]
    \\ ALIGNED_TAC)
  \\ `isDot t` by (Cases_on `t` \\ FULL_SIMP_TAC std_ss [isVal_def,isSym_def,isDot_def])
  \\ `ALIGNED r3` by
   (FULL_SIMP_TAC std_ss [isDot_thm,lisp_tree_def,GSYM STAR_ASSOC]
    \\ FULL_SIMP_TAC std_ss [isDot_thm,lisp_tree_def,GSYM STAR_ASSOC]
    \\ FULL_SIMP_TAC std_ss [isSym_thm,lisp_tree_def,GSYM STAR_ASSOC])
  \\ `r3 && 0x1w = 0x0w` by
   (POP_ASSUM MP_TAC \\ Q.SPEC_TAC (`r3`,`a`) \\ Cases
    \\ SIMP_TAC std_ss [ALIGNED_n2w,n2w_and_1] \\ STRIP_TAC
    \\ `n = n DIV 4 * 4` by METIS_TAC [DIVISION,ADD_0,DECIDE ``0<4:num``]
    \\ ONCE_ASM_REWRITE_TAC []
    \\ REWRITE_TAC [MATCH_MP MOD_EQ_0 (DECIDE ``0<2:num``),DECIDE ``n * 4:num = (n * 2) * 2``])
  \\ ASM_SIMP_TAC std_ss [ALIGNED_INTRO]
  \\ Q.ABBREV_TAC `r = if b then 0x6w else 0x5w:word32`
  \\ `arm_is_quote_pre (r3,r,dh,h) /\
       (if isQuote t /\ ~((r && 0x2w) = 0x0w) then
         (arm_is_quote (r3,r,dh,h) = (h (h (r3 + 0x4w)),r,0x3w,dh,h)) /\
         lisp_tree (CAR (CDR t)) (h (h (r3 + 0x4w)),dh,h) sym
        else arm_is_quote (r3,r,dh,h) = (r3,r,0x0w,dh,h))` by
      (IMP_RES_TAC lisp_tree_SUBSET
       \\ IMP_RES_TAC arm_is_quote_lemma \\ METIS_TAC [])
  \\ `~((r && 0x2w) = 0x0w) = b` by
       (Q.UNABBREV_TAC `r` \\ Cases_on `b` \\ EVAL_TAC)
  \\ FULL_SIMP_TAC std_ss []
  \\ Cases_on `isQuote t /\ b` THEN1
   (FULL_SIMP_TAC std_ss [CONTAINER_def]
    \\ REWRITE_TAC [EVAL ``3w = 0w:word32``]
    \\ `sexp2string_aux (t,T) = (#"'")::sexp2string_aux (CAR (CDR t),T)` by
     (FULL_SIMP_TAC std_ss [isQuote_thm,CAR_def,CDR_def,LET_DEF]
      \\ ASM_SIMP_TAC std_ss [sexp2string_aux_def,SExp_11,isQuote_thm]
      \\ SIMP_TAC std_ss [LIST_STRCAT_def,CAR_def,CDR_def,APPEND_NIL,APPEND])
    \\ FULL_SIMP_TAC std_ss [LENGTH,one_space_def,SEP_CLAUSES,one_string_def]
    \\ Q.ABBREV_TAC `f2 = (r7 =+ w2w (0x27w:word32)) f`
    \\ SIMP_TAC std_ss [MAP,one_list_def,GSYM one_string_def]
    \\ FULL_SIMP_TAC std_ss [EVAL ``ORD #"'"``,STAR_ASSOC,SEP_EXISTS]
    \\ Q.ABBREV_TAC `r3n = h (h (r3 + 0x4w))`
    \\ `(p * one (r7,0x27w) *
         one_space (r7 + 0x1w) (STRLEN (sexp2string_aux (CAR (CDR t),T)))c)
           (fun2set (f2,df))` by
     (Q.UNABBREV_TAC `f2`
      \\ REWRITE_TAC [EVAL ``(w2w:word32->word8) 0x27w``]
      \\ SEP_WRITE_TAC)
    \\ `LSIZE (CAR (CDR t)) < LSIZE t` by
     (FULL_SIMP_TAC std_ss [isQuote_thm,CAR_def,CDR_def,LSIZE_def] \\ DECIDE_TAC)
    \\ `(STRLEN (sexp2string_aux (CAR (CDR t),T))) < 4294967296` by DECIDE_TAC
    \\ `LDEPTH (CAR (CDR t)) <= LDEPTH t` by
     (FULL_SIMP_TAC std_ss [isQuote_thm,CAR_def,CDR_def,LDEPTH_def] \\ DECIDE_TAC)
    \\ FULL_SIMP_TAC std_ss [LESS_EQ_EXISTS]
    \\ STRIP_ASSUME_TAC (Q.SPECL [`LDEPTH (CAR (CDR t))`,`r8+8w`,`p'`] stack_slots_ADD)
    \\ FULL_SIMP_TAC std_ss []
    \\ `(q * fr * one (r8,w2) * one (r8 + 0x4w,w1) *
         stack_slots (r8 + 0x8w) (LDEPTH (CAR (CDR t))))
          (fun2set (h,dh DIFF d))` by FULL_SIMP_TAC (std_ss++star_ss) []
    \\ `lisp_tree (CAR (CDR t)) (r3n,d,h) sym` by
     (Q.UNABBREV_TAC `r3n`
      \\ FULL_SIMP_TAC std_ss [isQuote_thm,CAR_def,CDR_def]
      \\ FULL_SIMP_TAC std_ss [isQuote_thm,CAR_def,CDR_def,lisp_tree_def])
    \\ Q.PAT_X_ASSUM `!m. bbb` (ASSUME_TAC o UNDISCH o Q.SPEC `LSIZE (CAR (CDR t))`)
    \\ POP_ASSUM (ASSUME_TAC o RW [] o Q.SPEC `(CAR (CDR t))`)
    \\ POP_ASSUM (ASSUME_TAC o
         SIMP_RULE std_ss [LET_DEF,GSYM AND_IMP_INTRO,GSYM one_string_def] o
         Q.SPECL [`T`,`p * one (r7,0x27w)`,`w1`,`w2`,`r3n`,`r7+1w`,`r8`,`h`,`f2`,`q * fr`,`c`])
    \\ REPEAT (POP_ASSUM (STRIP_ASSUME_TAC o UNDISCH))
    \\ Q.EXISTS_TAC `hi`
    \\ Q.EXISTS_TAC `fi`
    \\ ASM_SIMP_TAC std_ss [one_string_def,MAP,one_list_def]
    \\ ASM_SIMP_TAC std_ss [GSYM one_string_def,EVAL ``ORD #"'"``,STAR_ASSOC]
    \\ FULL_SIMP_TAC (std_ss++star_ss) []
    \\ ONCE_REWRITE_TAC [arm_print_loop_pre_def]
    \\ ASM_SIMP_TAC std_ss [LET_DEF,ALIGNED_INTRO]
    \\ ONCE_REWRITE_TAC [WORD_AND_COMM]
    \\ ASM_SIMP_TAC std_ss [LET_DEF,EVAL ``3w = 0w:word32``]
    \\ ASM_SIMP_TAC std_ss [LET_DEF,ALIGNED_INTRO]
    \\ ONCE_REWRITE_TAC [WORD_AND_COMM]
    \\ ASM_SIMP_TAC std_ss [LET_DEF,ALIGNED_INTRO]
    \\ `r7 IN df` by SEP_READ_TAC
    \\ ASM_SIMP_TAC std_ss [arm_print_loop1_pre_def])
  \\ POP_ASSUM MP_TAC
  \\ REWRITE_TAC [METIS_PROVE [] ``~(b /\ c) = b ==> ~c``]
  \\ STRIP_TAC
  \\ ONCE_REWRITE_TAC [arm_print_loop_pre_def]
  \\ ASM_SIMP_TAC std_ss [LET_DEF,ALIGNED_INTRO]
  \\ ONCE_REWRITE_TAC [WORD_AND_COMM]
  \\ ASM_SIMP_TAC std_ss [LET_DEF,ALIGNED_INTRO]
  \\ `arm_is_quote (r3,r,dh,h) = (r3,r,0x0w,dh,h)` by METIS_TAC []
  \\ `((r && 0x2w) = 0x0w) <=> ~b` by METIS_TAC []
  \\ ASM_SIMP_TAC std_ss [NOT_IF,word_arith_lemma1]
  \\ ONCE_REWRITE_TAC [WORD_AND_COMM]
  \\ ASM_SIMP_TAC std_ss [LET_DEF,ALIGNED_INTRO]
  \\ Q.ABBREV_TAC `h2 = (r8 + 0xCw =+ h (r3 + 0x4w)) ((r8 + 0x8w =+ r - 0x4w) h)`
  \\ `?a1 a2. t = Dot a1 a2` by FULL_SIMP_TAC std_ss [isDot_thm,SExp_11]
  \\ `lisp_tree t (r3,d,h2) sym /\ (h2 r3 = h r3) /\ (h2 (r3 + 4w) = h (r3 + 4w))` by
   (FULL_SIMP_TAC std_ss [LDEPTH_def,stack_slots_def,word_arith_lemma1]
    \\ FULL_SIMP_TAC std_ss [SEP_CLAUSES]
    \\ FULL_SIMP_TAC std_ss [SEP_EXISTS,STAR_ASSOC]
    \\ `r8 + 0x8w IN dh DIFF d /\ r8 + 0xCw IN dh DIFF d` by SEP_READ_TAC
    \\ FULL_SIMP_TAC std_ss [IN_DIFF]
    \\ Q.UNABBREV_TAC `h2`
    \\ ASM_SIMP_TAC std_ss [NOT_IN_lisp_tree]
    \\ FULL_SIMP_TAC std_ss [lisp_tree_def,APPLY_UPDATE_THM]
    \\ METIS_TAC [])
  \\ `ALIGNED (r8 + 8w)` by ALIGNED_TAC
  \\ Q.ABBREV_TAC `s1 = sexp2string_aux (a1,T)`
  \\ Q.ABBREV_TAC `s2 = if a2 = Sym "nil" then "" else sexp2string_aux (a2,F)`
  \\ Q.ABBREV_TAC `s3 = if a2 = Sym "nil" then "" else if isDot a2 then " " else " . "`
  \\ Q.ABBREV_TAC `p1 = if b then "(" else ""`
  \\ Q.ABBREV_TAC `p2 = if b then ")" else ""`
  \\ `sexp2string_aux (t,b) = p1 ++ s1 ++ s3 ++ s2 ++ p2` by
      (Q.UNABBREV_TAC `s1` \\ Q.UNABBREV_TAC `s2`
       \\ Q.UNABBREV_TAC `p1` \\ Q.UNABBREV_TAC `p2`
       \\ Q.UNABBREV_TAC `s3` \\ Cases_on `b`
       \\ Cases_on `a2 = Sym "nil"`
       \\ Cases_on `isDot a2`
       \\ FULL_SIMP_TAC std_ss [sexp2string_aux_def,LET_DEF,IF_SIMPS,
            APPEND,APPEND_NIL,LIST_STRCAT_def,APPEND_ASSOC]
       \\ FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC,APPEND])
  \\ ONCE_REWRITE_TAC [WORD_AND_COMM] \\ ASM_SIMP_TAC std_ss []
  \\ `ALIGNED (r3 + 4w) /\ ALIGNED (r8 + 12w)` by ALIGNED_TAC
  \\ `r3 + 0x4w IN dh /\ r3 IN dh /\ r8 + 0x8w IN dh /\ r8 + 0xCw IN dh` by
   (Q.PAT_X_ASSUM `isDot t` (ASSUME_TAC)
    \\ FULL_SIMP_TAC std_ss [isDot_thm,LDEPTH_def]
    \\ FULL_SIMP_TAC std_ss [stack_slots_def,SEP_CLAUSES]
    \\ FULL_SIMP_TAC std_ss [SEP_EXISTS,lisp_tree_def]
    \\ STRIP_TAC THEN1 METIS_TAC [SUBSET_DEF]
    \\ STRIP_TAC THEN1 METIS_TAC [SUBSET_DEF]
    \\ FULL_SIMP_TAC std_ss [word_arith_lemma1]
    \\ `r8 + 0x8w IN dh DIFF d /\ r8 + 0xCw IN dh DIFF d` by SEP_READ_TAC
    \\ FULL_SIMP_TAC std_ss [IN_DIFF])
  \\ `b ==> r7 IN df` by
   (REPEAT STRIP_TAC
    \\ Q.PAT_X_ASSUM `t = Dot a1 a2` (K ALL_TAC)
    \\ Q.UNABBREV_TAC `p1`
    \\ FULL_SIMP_TAC bool_ss [one_space_def,LENGTH_APPEND,one_space_ADD,one_space_def,LENGTH]
    \\ FULL_SIMP_TAC std_ss [stack_slots_def,SEP_CLAUSES]
    \\ FULL_SIMP_TAC std_ss [SEP_EXISTS,lisp_tree_def]
    \\ SEP_READ_TAC)
  \\ ASM_SIMP_TAC std_ss [NOT_IF]
  \\ FULL_SIMP_TAC std_ss [IF_SIMPS,EVAL ``(w2w:word32->word8) 0x29w``]
  \\ Q.ABBREV_TAC `f2 = if b then (r7 =+ 0x28w) f else f`
  \\ Q.ABBREV_TAC `r72 = if b then r7 + 0x1w else r7`
  \\ FULL_SIMP_TAC std_ss [isVal_def,isDot_def,isSym_def]
  \\ REPEAT (Q.PAT_X_ASSUM `T` (K ALL_TAC))
  \\ FULL_SIMP_TAC std_ss [LENGTH_APPEND]
  \\ `STRLEN s1 < 4294967296 /\ STRLEN s2 < 4294967296` by DECIDE_TAC
  \\ `(p * one_string r7 p1 r72 *
       one_space r72 (LENGTH (s1++s3++s2++p2)) c) (fun2set (f2,df))` by
   (Q.UNABBREV_TAC `r72` \\ Q.UNABBREV_TAC `p1`
    \\ Q.UNABBREV_TAC `p2` \\ Q.UNABBREV_TAC `f2`
    \\ REVERSE (Cases_on `b`)
    \\ FULL_SIMP_TAC std_ss [one_string_def,MAP,one_list_def,
         SEP_CLAUSES,LENGTH_APPEND,LENGTH,EVAL ``ORD #"("``,GSYM ADD_ASSOC]
    \\ Q.PAT_X_ASSUM `pp (fun2set (f,df))` (ASSUME_TAC o RW [GSYM (RW1[ADD_COMM]ADD1)])
    \\ FULL_SIMP_TAC std_ss [one_space_def,SEP_CLAUSES]
    \\ FULL_SIMP_TAC std_ss [SEP_EXISTS,STAR_ASSOC]
    \\ SEP_WRITE_TAC)
  \\ Q.PAT_X_ASSUM `bb (fun2set (h,dh DIFF d))` (ASSUME_TAC o RW [LDEPTH_def])
  \\ FULL_SIMP_TAC std_ss [stack_slots_def,SEP_CLAUSES]
  \\ FULL_SIMP_TAC std_ss [SEP_EXISTS,STAR_ASSOC,word_arith_lemma1]
  \\ STRIP_ASSUME_TAC (Q.SPECL [`LDEPTH a1`,`LDEPTH a2`,`r8+16w`] stack_slots_MAX)
  \\ FULL_SIMP_TAC std_ss []
  \\ `(q * fr * one (r8,w2) * one (r8 + 0x4w,w1) * one (r8 + 0x8w,r-4w) *
       one (r8 + 0xCw,h (r3+4w)) * stack_slots (r8 + 0x10w) (LDEPTH a1))
        (fun2set (h2,dh DIFF d))` by
        (Q.UNABBREV_TAC `h2` \\ SEP_WRITE_TAC)
  \\ `lisp_tree a1 (h r3,d,h2) sym` by
   (FULL_SIMP_TAC std_ss [lisp_tree_def]
    \\ Q.UNABBREV_TAC `h2`
    \\ `r8 + 8w IN dh DIFF d /\ r8 + 12w IN dh DIFF d` by SEP_READ_TAC
    \\ FULL_SIMP_TAC std_ss [IN_DIFF]
    \\ METIS_TAC [NOT_IN_lisp_tree])
  \\ Q.ABBREV_TAC `r73 = r72 + n2w (STRLEN s1)`
  \\ `(p * one_string r7 p1 r72 *
       one_space r73 (STRLEN ((STRCAT s3 (STRCAT s2 p2)))) c *
       one_space r72 (STRLEN s1) r73) (fun2set (f2,df))` by
   (Q.UNABBREV_TAC `r73`
    \\ FULL_SIMP_TAC (std_ss++star_ss) [one_space_ADD,LENGTH_APPEND]
    \\ FULL_SIMP_TAC std_ss [GSYM WORD_ADD_ASSOC,word_add_n2w]
    \\ FULL_SIMP_TAC std_ss [AC ADD_COMM ADD_ASSOC]
    \\ FULL_SIMP_TAC (std_ss++star_ss) [])
  \\ FULL_SIMP_TAC std_ss [LSIZE_def]
  \\ Q.PAT_X_ASSUM `CONTAINER (!m. bbb)` (fn th => let val th = RW [CONTAINER_def] th in
         (ASSUME_TAC o RW [] o Q.SPEC `F` o RW [] o Q.SPEC `a2` o
          RW [DECIDE ``n < SUC (m + n):num``] o Q.SPEC `LSIZE a2`) th
         THEN
         (ASSUME_TAC o RW [] o Q.SPEC `T` o RW [] o Q.SPEC `a1` o
          RW [DECIDE ``m < SUC (m + n):num``] o Q.SPEC `LSIZE a1`) th end)
  \\ POP_ASSUM (ASSUME_TAC o SIMP_RULE std_ss [LET_DEF])
  \\ Q.UNABBREV_TAC `s1`
  \\ POP_ASSUM (ASSUME_TAC o RW [GSYM AND_IMP_INTRO] o
       RW [arm_print_loop1_def,arm_print_loop1_pre_def] o
       Q.SPECL [`p * one_string r7 p1 r72 *
         one_space r73 (STRLEN ((STRCAT s3 (STRCAT s2 p2)))) c`,
         `h (r3+4w:word32)`,`r-4w`,`h (r3:word32)`,
         `r72`,`r8+8w`,`h2`,`f2`,`q * fr * one (r8,w2) * one (r8 + 0x4w,w1)`,`r73`])
  \\ POP_ASSUM (ASSUME_TAC o SIMP_RULE std_ss [word_arith_lemma1])
  \\ REPEAT (POP_ASSUM (STRIP_ASSUME_TAC o UNDISCH))
  \\ Q.UNABBREV_TAC `f2`
  \\ ASM_SIMP_TAC std_ss [EVAL ``(w2w:word32->word8) 0x28w``]
  \\ Q.ABBREV_TAC `s1 = sexp2string_aux (a1,T)`
  \\ `(r - 4w && 4w = 0w) /\ ~(r - 4w = 0w) /\ ~(r - 4w = 3w)` by
        (Q.UNABBREV_TAC `r` \\ Cases_on `b` \\ EVAL_TAC)
  \\ ONCE_REWRITE_TAC [arm_print_loop_def,arm_print_loop_pre_def]
  \\ ASM_SIMP_TAC std_ss []
  \\ ONCE_REWRITE_TAC [WORD_AND_COMM]
  \\ ASM_SIMP_TAC std_ss []
  \\ ONCE_REWRITE_TAC [WORD_AND_COMM]
  \\ ASM_SIMP_TAC std_ss []
  \\ `fun_eq d h hi` by
   (`fun_eq d h h2` suffices_by METIS_TAC [fun_eq_def]
    \\ SIMP_TAC std_ss [fun_eq_def]
    \\ REPEAT STRIP_TAC
    \\ Q.PAT_X_ASSUM `t = Dot a1 a2` ASSUME_TAC
    \\ Q.UNABBREV_TAC `h2`
    \\ FULL_SIMP_TAC std_ss [APPLY_UPDATE_THM,IN_DIFF]
    \\ `r8 + 8w IN dh DIFF d` by SEP_READ_TAC
    \\ `r8 + 12w IN dh DIFF d` by SEP_READ_TAC
    \\ FULL_SIMP_TAC std_ss [IN_DIFF]
    \\ METIS_TAC [])
  \\ Cases_on `a2 = Sym "nil"` THEN1
   (FULL_SIMP_TAC std_ss []
    \\ Q.UNABBREV_TAC `s3` \\ Q.UNABBREV_TAC `s2`
    \\ FULL_SIMP_TAC std_ss [APPEND_NIL,APPEND,lisp_tree_def]
    \\ `h (r3 + 0x4w) = 3w` by METIS_TAC [lisp_symbol_table_consts]
    \\ ASM_SIMP_TAC std_ss [arm_print_loop_aux_pre_def,arm_print_loop_aux_def,arm_print_exit_def]
    \\ SIMP_TAC std_ss [LET_DEF,word_arith_lemma1]
    \\ `~(r - 5w = 2w) /\ ((r - 5w = 0w) = ~b)` by
        (Q.UNABBREV_TAC `r` \\ Cases_on `b` \\ EVAL_TAC)
    \\ ASM_SIMP_TAC std_ss [WORD_ADD_SUB,NOT_IF]
    \\ SIMP_TAC std_ss [EVAL ``(w2w:word32->word8) 0x29w``]
    \\ SIMP_TAC std_ss [IF_SIMPS]
    \\ Q.ABBREV_TAC `fi2 = if b then (r73 =+ 0x29w) fi else fi`
    \\ Q.ABBREV_TAC `r74 = if b then r73 + 0x1w else r73`
    \\ `(hi (r8 + 0x4w) = w1)` by SEP_READ_TAC
    \\ `(hi (r8) = w2)` by SEP_READ_TAC
    \\ ASM_SIMP_TAC std_ss []
    \\ `c = r74` by
     (Q.UNABBREV_TAC `p2` \\ Q.UNABBREV_TAC `r74`
      \\ REVERSE (Cases_on `b`)
      \\ FULL_SIMP_TAC (bool_ss++sep_cond_ss) [one_space_def,LENGTH,cond_STAR]
      \\ FULL_SIMP_TAC (std_ss++sep_cond_ss) [SEP_CLAUSES]
      \\ FULL_SIMP_TAC std_ss [SEP_EXISTS,cond_STAR])
    \\ ASM_SIMP_TAC std_ss [ALIGNED_INTRO]
    \\ `r8 IN dh DIFF d /\ r8 + 4w IN dh DIFF d` by SEP_READ_TAC
    \\ `ALIGNED (r8 + 4w)` by ALIGNED_TAC
    \\ `b ==> r73 IN df` by
     (REPEAT STRIP_TAC
      \\ Q.UNABBREV_TAC `p2`
      \\ FULL_SIMP_TAC bool_ss [one_space_def,LENGTH,SEP_CLAUSES]
      \\ FULL_SIMP_TAC std_ss [SEP_EXISTS] \\ SEP_READ_TAC)
    \\ FULL_SIMP_TAC std_ss [IN_DIFF]
    \\ Q.EXISTS_TAC `hi`
    \\ Q.EXISTS_TAC `fi2`
    \\ ASM_SIMP_TAC std_ss [arm_print_loop1_pre_def,arm_print_loop1_def]
    \\ ONCE_REWRITE_TAC [LDEPTH_def]
    \\ ASM_SIMP_TAC std_ss [stack_slots_def,SEP_CLAUSES,word_arith_lemma1]
    \\ SIMP_TAC std_ss [SEP_EXISTS,word_arith_lemma1]
    \\ REVERSE STRIP_TAC THEN1
     (Q.EXISTS_TAC `r - 4w` \\ Q.EXISTS_TAC `h (r3 + 4w)`
      \\ FULL_SIMP_TAC (std_ss++star_ss) [])
    \\ FULL_SIMP_TAC std_ss [one_string_STRCAT]
    \\ Q.UNABBREV_TAC `p1`
    \\ Q.UNABBREV_TAC `p2`
    \\ Q.UNABBREV_TAC `r72`
    \\ Q.UNABBREV_TAC `r73`
    \\ Q.UNABBREV_TAC `fi2`
    \\ Q.UNABBREV_TAC `r74`
    \\ REVERSE (Cases_on `b`) THEN1
      (FULL_SIMP_TAC std_ss [AC WORD_ADD_ASSOC WORD_ADD_COMM]
       \\ FULL_SIMP_TAC std_ss [one_string_def,one_list_def,MAP,LENGTH]
       \\ FULL_SIMP_TAC std_ss [WORD_ADD_0,SEP_CLAUSES,one_space_def,APPEND])
    \\ FULL_SIMP_TAC std_ss [LENGTH,SIMP_RULE std_ss []
        (REWRITE_CONV [one_space_def] ``one_space a (SUC 0) b``)]
    \\ FULL_SIMP_TAC std_ss [SEP_CLAUSES]
    \\ FULL_SIMP_TAC std_ss [SEP_EXISTS,LENGTH_APPEND,LENGTH,GSYM word_add_n2w]
    \\ FULL_SIMP_TAC std_ss [AC WORD_ADD_COMM WORD_ADD_ASSOC]
    \\ FULL_SIMP_TAC std_ss [one_string_def,one_list_def,MAP]
    \\ FULL_SIMP_TAC std_ss [SEP_CLAUSES,EVAL ``ORD #")"``]
    \\ FULL_SIMP_TAC std_ss [AC WORD_ADD_COMM WORD_ADD_ASSOC,SEP_CLAUSES]
    \\ SEP_WRITE_TAC)
  \\ ASM_SIMP_TAC std_ss [arm_print_loop_aux_def,arm_print_loop_aux_pre_def,arm_print_exit_def]
  \\ `~(h (r3 + 4w) = 3w)` by
   (IMP_RES_TAC builti_symbols_thm
    \\ CCONTR_TAC
    \\ FULL_SIMP_TAC std_ss [ADDR32_n2w,word_add_n2w]
    \\ Q.PAT_X_ASSUM `t = Dot a1 a2` (ASSUME_TAC)
    \\ FULL_SIMP_TAC std_ss [lisp_tree_def]
    \\ Q.PAT_X_ASSUM `!x.bbb` (K ALL_TAC)
    \\ Cases_on `a2`
    \\ FULL_SIMP_TAC std_ss [lisp_tree_def,ALIGNED_n2w]
    \\ FULL_SIMP_TAC std_ss [GSYM ADDR32_n2w,GSYM word_add_n2w,GSYM WORD_EQ_SUB_RADD]
    \\ FULL_SIMP_TAC std_ss [word_arith_lemma2,RW1 [MULT_COMM] (GSYM ADDR32_n2w)]
    \\ `ALIGNED (ADDR32 (n2w n)) /\ ~(ALIGNED (0x1w))` by
      SIMP_TAC std_ss [ALIGNED_ADDR32,ALIGNED_n2w]
    \\ FULL_SIMP_TAC std_ss [] THEN1 METIS_TAC []
    \\ METIS_TAC [lisp_symbol_table_11])
  \\ FULL_SIMP_TAC std_ss [LET_DEF,arm_set_return_def]
  \\ SIMP_TAC std_ss [ALIGNED_INTRO]
  \\ `ALIGNED (h (r3 + 0x4w)) = isDot a2` by
   (Q.PAT_X_ASSUM `t = Dot a1 a2` (ASSUME_TAC)
    \\ FULL_SIMP_TAC std_ss [lisp_tree_def]
    \\ Cases_on `a2`
    \\ FULL_SIMP_TAC std_ss [lisp_tree_def,isDot_def]
    \\ SIMP_TAC std_ss [GSYM word_add_n2w,GSYM (RW1 [MULT_COMM] ADDR32_n2w)]
    \\ SIMP_TAC std_ss [ALIGNED_ADD_EQ,ALIGNED_ADDR32,ALIGNED_n2w]
    \\ IMP_RES_TAC NOT_ALIGNED
    \\ FULL_SIMP_TAC std_ss [WORD_SUB_ADD])
  \\ ASM_SIMP_TAC std_ss [WORD_ADD_SUB]
  \\ `(r - 0x4w = 0x2w) = b` by
        (Q.UNABBREV_TAC `r` \\ Cases_on `b` \\ EVAL_TAC)
  \\ ASM_SIMP_TAC std_ss [EVAL ``(w2w:word32->word8) 0x20w``]
  \\ ASM_SIMP_TAC std_ss [EVAL ``(w2w:word32->word8) 0x2Ew``]
  \\ ASM_SIMP_TAC std_ss [arm_set_return_pre_def,LET_DEF,ALIGNED_INTRO]
  \\ `(isDot a2 ==> r73 IN df) /\
      (~(isDot a2) ==> r73 IN df /\ r73 + 1w IN df /\ r73 + 2w IN df)` by
   (REPEAT STRIP_TAC \\ Q.UNABBREV_TAC `s3`
    \\ FULL_SIMP_TAC std_ss [APPEND,LENGTH,one_space_def,SEP_CLAUSES]
    \\ FULL_SIMP_TAC std_ss [SEP_EXISTS,word_arith_lemma1] \\ SEP_READ_TAC)
  \\ ASM_SIMP_TAC std_ss []
  \\ Q.ABBREV_TAC `r8i = if b then r8 + 8w else r8`
  \\ Q.ABBREV_TAC `hi2 = if b then (r8 + 8w =+ 3w ) hi else hi`
  \\ `(if b then (5w,0x3w:word32,r8 + 0x8w,dh,(r8 + 0x8w =+ 0x3w) hi)
       else (5w,0x2w,r8,dh,hi)) =
      (5w:word32,if b then 3w else 2w, r8i, dh, hi2)` by
   (Q.UNABBREV_TAC `r8i`
    \\ Q.UNABBREV_TAC `hi2`
    \\ Q.UNABBREV_TAC `r`
    \\ Cases_on `b`
    \\ SIMP_TAC std_ss [word_add_n2w,WORD_SUB_ADD])
  \\ ASM_SIMP_TAC std_ss [] \\ POP_ASSUM (K ALL_TAC)
  \\ Q.ABBREV_TAC `r74 = r73 + if isDot a2 then 1w else 3w`
  \\ Q.ABBREV_TAC `fi2 = if isDot a2 then (r73 =+ 0x20w) fi else
       (r73 + 0x1w =+ 0x2Ew) ((r73 + 0x2w =+ 0x20w) ((r73 =+ 0x20w) fi))`
  \\ `(if isDot a2 then
        (h (r3 + 0x4w),5w:word32,r73 + 0x1w,r8i,dh,hi2,df,(r73 =+ 0x20w) fi)
      else
        (h (r3 + 0x4w),5w,r73 + 0x3w,r8i,dh,hi2,df,
         (r73 + 0x1w =+ 0x2Ew)
           ((r73 + 0x2w =+ 0x20w) ((r73 =+ 0x20w) fi)))) =
      (h (r3 + 0x4w),5w,r74,r8i,dh,hi2,df,fi2)` by
    (Q.UNABBREV_TAC `r74` \\ Q.UNABBREV_TAC `fi2`
     \\ Cases_on `isDot a2` \\ ASM_SIMP_TAC std_ss [])
  \\ ASM_SIMP_TAC std_ss [] \\ POP_ASSUM (K ALL_TAC)
  \\ Q.UNABBREV_TAC `s2`
  \\ Q.ABBREV_TAC `s2 = sexp2string_aux (a2,F)`
  \\ Q.ABBREV_TAC `r75 = r74 + n2w (LENGTH s2)`
  \\ `(p * one_string r7 p1 r72 * one_string r72 s1 r73 *
       one_string r73 s3 r74 * one_space r75 (LENGTH p2) c *
       one_space r74 (LENGTH s2) r75) (fun2set (fi2,df))` by
   (Q.UNABBREV_TAC `r73` \\ Q.UNABBREV_TAC `r74`
    \\ Q.UNABBREV_TAC `r75`
    \\ Q.UNABBREV_TAC `fi2` \\ Q.UNABBREV_TAC `s3`
    \\ Cases_on `isDot a2` THENL [
      ASM_SIMP_TAC std_ss [one_string_def,MAP,one_list_def]
      \\ FULL_SIMP_TAC std_ss [GSYM one_string_def,SEP_CLAUSES]
      \\ FULL_SIMP_TAC std_ss [EVAL ``ORD #" "``,LENGTH_APPEND]
      \\ FULL_SIMP_TAC std_ss [one_space_ADD,LENGTH]
      \\ FULL_SIMP_TAC std_ss [LENGTH,SIMP_RULE std_ss []
          (REWRITE_CONV [one_space_def] ``one_space a (SUC 0) b``)]
      \\ FULL_SIMP_TAC std_ss [SEP_CLAUSES]
      \\ FULL_SIMP_TAC std_ss [SEP_EXISTS,STAR_ASSOC]
      \\ SEP_WRITE_TAC,
      ASM_SIMP_TAC std_ss [one_string_def,MAP,one_list_def]
      \\ FULL_SIMP_TAC std_ss [GSYM one_string_def,SEP_CLAUSES]
      \\ FULL_SIMP_TAC std_ss [EVAL ``ORD #" "``,LENGTH_APPEND]
      \\ FULL_SIMP_TAC std_ss [EVAL ``ORD #"."``,LENGTH_APPEND]
      \\ FULL_SIMP_TAC std_ss [one_space_ADD,LENGTH]
      \\ FULL_SIMP_TAC std_ss [LENGTH,SIMP_RULE std_ss []
          (REWRITE_CONV [one_space_def] ``one_space a (SUC (SUC (SUC 0))) b``)]
      \\ FULL_SIMP_TAC std_ss [GSYM WORD_ADD_ASSOC,word_add_n2w]
      \\ FULL_SIMP_TAC std_ss [ADD_ASSOC,SEP_CLAUSES]
      \\ FULL_SIMP_TAC std_ss [SEP_EXISTS,STAR_ASSOC]
      \\ SEP_WRITE_TAC])
  \\ `fun_eq d h hi2` by
   (`fun_eq d hi hi2` suffices_by METIS_TAC [fun_eq_def]
    \\ SIMP_TAC std_ss [fun_eq_def]
    \\ REPEAT STRIP_TAC
    \\ Q.UNABBREV_TAC `hi2`
    \\ FULL_SIMP_TAC std_ss [APPLY_UPDATE_THM,IN_DIFF]
    \\ Cases_on `b` \\ ASM_SIMP_TAC std_ss []
    \\ `r8 + 8w IN dh DIFF d` by SEP_READ_TAC
    \\ Q.UNABBREV_TAC `r8i`
    \\ FULL_SIMP_TAC std_ss [IN_DIFF]
    \\ FULL_SIMP_TAC std_ss [APPLY_UPDATE_THM,IN_DIFF]
    \\ METIS_TAC [])
  \\ `lisp_tree a2 (h (r3 + 4w),d,h) sym` by
   (Q.PAT_X_ASSUM `t = Dot a1 a2` ASSUME_TAC
    \\ FULL_SIMP_TAC std_ss [lisp_tree_def])
  \\ `lisp_tree a2 (h (r3 + 4w),d,hi2) sym` by METIS_TAC [fun_eq_lisp_tree]
  \\ `(q * one (r8,w2) * one (r8 + 0x4w,w1) *
        one (r8 + 0x8w,r - 0x4w) * one (r8 + 0xCw,h (r3 + 0x4w)) *
        stack_slots (r8 + 0x10w) (MAX (LDEPTH a1) (LDEPTH a2)))
        (fun2set (hi,dh DIFF d))` by
           FULL_SIMP_TAC (std_ss++star_ss) []
  \\ Q.PAT_X_ASSUM `bb = bbb * fr` (fn th => REWRITE_TAC [GSYM th])
  \\ REVERSE (Cases_on `b`) THEN1
    (FULL_SIMP_TAC std_ss [] \\ Q.UNABBREV_TAC `r`
     \\ Q.UNABBREV_TAC `r8i` \\ Q.UNABBREV_TAC `hi2`
     \\ `(q * one (r8,w2) * one (r8 + 0x4w,w1) *
          stack_slots (r8+8w) (SUC (MAX (LDEPTH a1) (LDEPTH a2))))
           (fun2set (hi,dh DIFF d))` by
       (FULL_SIMP_TAC std_ss [stack_slots_def,SEP_CLAUSES]
        \\ SIMP_TAC std_ss [SEP_EXISTS,word_arith_lemma1]
        \\ Q.EXISTS_TAC `5w-4w`
        \\ Q.EXISTS_TAC `h (r3 + 4w:word32)`
        \\ FULL_SIMP_TAC (std_ss++star_ss) [])
     \\ `LDEPTH a2 <= SUC (MAX (LDEPTH a1) (LDEPTH a2))` by
         (SIMP_TAC std_ss [MAX_DEF] \\ DECIDE_TAC)
     \\ FULL_SIMP_TAC std_ss [LESS_EQ_EXISTS]
     \\ FULL_SIMP_TAC std_ss []
     \\ `?fr2. stack_slots (r8 + 8w) (LDEPTH a2 + p') =
               stack_slots (r8 + 8w) (LDEPTH a2) * fr2` by
           METIS_TAC [stack_slots_ADD]
     \\ FULL_SIMP_TAC std_ss []
     \\ `((q * fr2) * one (r8,w2) * one (r8 + 0x4w,w1) *
          stack_slots (r8 + 0x8w) (LDEPTH a2))
             (fun2set (hi,dh DIFF d))` by
                FULL_SIMP_TAC (std_ss++star_ss) []
     \\ Q.PAT_X_ASSUM `!p w1. bbb` (ASSUME_TAC o
       Q.SPECL [`p * one_string r7 p1 r72 * one_string r72 s1 r73 *
          one_string r73 s3 r74 * one_space r75 (STRLEN p2) c`,
         `w1`,`w2`,`h ((r3:word32)+4w)`,`r74`,`r8`,`hi`,`fi2`])
     \\ POP_ASSUM (ASSUME_TAC o Q.SPECL [`q * fr2`,`r75`])
     \\ POP_ASSUM (ASSUME_TAC o SIMP_RULE std_ss [GSYM AND_IMP_INTRO])
     \\ REPEAT (POP_ASSUM (STRIP_ASSUME_TAC o UNDISCH))
     \\ ASM_SIMP_TAC std_ss []
     \\ `c = r75` by
      (Q.UNABBREV_TAC `p2`
       \\ FULL_SIMP_TAC (std_ss++sep_cond_ss) [LENGTH,one_space_def,cond_STAR])
     \\ Q.EXISTS_TAC `hi'` \\ Q.EXISTS_TAC `fi'`
     \\ ASM_SIMP_TAC std_ss []
     \\ REVERSE STRIP_TAC THEN1
          (ASM_SIMP_TAC std_ss [LDEPTH_def]
           \\ FULL_SIMP_TAC (std_ss++star_ss) []
           \\ FULL_SIMP_TAC std_ss [fun_eq_def] \\ METIS_TAC [])
     \\ Q.UNABBREV_TAC `p1` \\ Q.UNABBREV_TAC `p2`
     \\ FULL_SIMP_TAC std_ss [APPEND,APPEND_NIL]
     \\ FULL_SIMP_TAC std_ss [one_string_STRCAT]
     \\ Q.UNABBREV_TAC `r75`
     \\ Q.UNABBREV_TAC `r74`
     \\ REVERSE (Cases_on `r7 = r72`)
     \\ FULL_SIMP_TAC std_ss [one_string_def,MAP,one_list_def,SEP_CLAUSES,cond_STAR]
     \\ FULL_SIMP_TAC (std_ss++star_ss) [SEP_F_def]
     \\ `(if isDot a2 then 0x1w else 0x3w) = n2w (LENGTH s3):word32` by
       (Q.UNABBREV_TAC `s3` \\ Cases_on `isDot a2` \\ ASM_SIMP_TAC std_ss [] \\ EVAL_TAC)
     \\ FULL_SIMP_TAC std_ss []
     \\ Q.UNABBREV_TAC `r73`
     \\ FULL_SIMP_TAC std_ss [word_arith_lemma1,LENGTH_APPEND]
     \\ FULL_SIMP_TAC (std_ss++star_ss) [AC WORD_ADD_ASSOC WORD_ADD_COMM,
          LENGTH,one_space_def,SEP_CLAUSES])
  \\ FULL_SIMP_TAC std_ss []
  \\ STRIP_ASSUME_TAC (Q.SPECL [`LDEPTH a2`,`LDEPTH a1`,`r8+16w`] (RW1 [MAX_COMM] stack_slots_MAX))
  \\ Q.UNABBREV_TAC `r8i`
  \\ ASM_SIMP_TAC std_ss [LDEPTH_def,stack_slots_def,word_arith_lemma1]
  \\ FULL_SIMP_TAC std_ss [SEP_CLAUSES]
  \\ `(q * fr' * one (r8,w2) * one (r8 + 0x4w,w1) *
        one (r8 + 0x8w,3w) * one (r8 + 0xCw,h (r3 + 0x4w)) *
        stack_slots (r8 + 0x10w) (LDEPTH a2))
         (fun2set (hi2,dh DIFF d))` by
     (Q.UNABBREV_TAC `hi2` \\ Q.UNABBREV_TAC `r`
      \\ FULL_SIMP_TAC std_ss [EVAL ``6w-4w:word32``]
      \\ SEP_WRITE_TAC)
  \\ Q.PAT_X_ASSUM `!p w1. bbb` (ASSUME_TAC o
       RW [arm_print_loop1_pre_def,arm_print_loop1_def] o
       Q.SPECL [`p * one_string r7 p1 r72 * one_string r72 s1 r73 *
         one_string r73 s3 r74 * one_space r75 (STRLEN p2) c`,
         `h ((r3:word32)+4w)`,`3w`,`h ((r3:word32)+4w)`,`r74`,`r8+8w`,`hi2`,`fi2`])
  \\ POP_ASSUM (ASSUME_TAC o Q.SPECL [`q * fr' * one (r8,w2) * one (r8 + 0x4w,w1)`,`r75`])
  \\ POP_ASSUM (ASSUME_TAC o SIMP_RULE std_ss [GSYM AND_IMP_INTRO])
  \\ FULL_SIMP_TAC std_ss [word_arith_lemma1]
  \\ REPEAT (POP_ASSUM (STRIP_ASSUME_TAC o UNDISCH))
  \\ ASM_SIMP_TAC std_ss []
  \\ ONCE_REWRITE_TAC [arm_print_loop_pre_def,arm_print_loop_def]
  \\ SIMP_TAC (std_ss++SIZES_ss) [n2w_11,EVAL ``3w && 4w:word32``]
  \\ SIMP_TAC std_ss [arm_print_loop_aux_def,arm_print_loop_aux_pre_def,arm_print_exit_def,LET_DEF]
  \\ SIMP_TAC (std_ss++SIZES_ss) [n2w_11,WORD_ADD_SUB]
  \\ SIMP_TAC std_ss [EVAL ``(w2w:word32->word8) 0x29w``]
  \\ ONCE_REWRITE_TAC [WORD_AND_COMM]
  \\ ASM_SIMP_TAC std_ss [EVAL ``3w && 4w:word32``]
  \\ `c = r75 + 1w` by
    (Q.UNABBREV_TAC `p2`
     \\ FULL_SIMP_TAC (bool_ss++sep_cond_ss) [one_space_def,LENGTH,SEP_CLAUSES]
     \\ FULL_SIMP_TAC std_ss [SEP_EXISTS,cond_STAR])
  \\ ASM_SIMP_TAC std_ss []
  \\ `hi' (r8 + 0x4w) = w1` by SEP_READ_TAC
  \\ `hi' (r8) = w2` by SEP_READ_TAC
  \\ ASM_SIMP_TAC std_ss []
  \\ Q.EXISTS_TAC `hi'`
  \\ Q.EXISTS_TAC `(r75 =+ 0x29w) fi'`
  \\ ASM_SIMP_TAC std_ss [arm_print_loop1_def,arm_print_loop1_pre_def]
  \\ SIMP_TAC std_ss [ALIGNED_INTRO]
  \\ `ALIGNED r8 /\ r8 IN dh DIFF d /\ ALIGNED (r8 + 0x4w) /\ r8 + 0x4w IN dh DIFF d` by
    (ALIGNED_TAC \\ SEP_READ_TAC)
  \\ `r75 IN df` by
   (Q.UNABBREV_TAC `p2`
    \\ FULL_SIMP_TAC bool_ss [one_space_def,LENGTH_APPEND,one_space_ADD,one_space_def,LENGTH]
    \\ FULL_SIMP_TAC std_ss [stack_slots_def,SEP_CLAUSES]
    \\ FULL_SIMP_TAC std_ss [SEP_EXISTS,lisp_tree_def]
    \\ SEP_READ_TAC)
  \\ FULL_SIMP_TAC std_ss [IN_DIFF]
  \\ REVERSE (REPEAT STRIP_TAC)
  THEN1 FULL_SIMP_TAC std_ss [fun_eq_def]
  THEN1
   (SIMP_TAC std_ss [SEP_EXISTS]
    \\ Q.EXISTS_TAC `3w`
    \\ Q.EXISTS_TAC `h(r3+4w:word32)`
    \\ FULL_SIMP_TAC (std_ss++star_ss) [])
  \\ Q.UNABBREV_TAC `p2`
  \\ SIMP_TAC std_ss [one_string_STRCAT]
  \\ FULL_SIMP_TAC std_ss [one_string_def,one_list_def,MAP,EVAL ``ORD #")"``]
  \\ FULL_SIMP_TAC bool_ss [LENGTH,one_space_def,SEP_CLAUSES]
  \\ FULL_SIMP_TAC std_ss [GSYM one_string_def,STAR_ASSOC,SEP_EXISTS]
  \\ Q.UNABBREV_TAC `r75`
  \\ Q.UNABBREV_TAC `r74`
  \\ Q.UNABBREV_TAC `r73`
  \\ Q.UNABBREV_TAC `r72`
  \\ `(if isDot a2 then 0x1w else 0x3w) = n2w (LENGTH s3):word32` by
    (Q.UNABBREV_TAC `s3` \\ Cases_on `isDot a2` \\ ASM_SIMP_TAC std_ss [] \\ EVAL_TAC)
  \\ FULL_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC (std_ss++star_ss) [SEP_F_def,one_space_def,LENGTH,SEP_CLAUSES]
  \\ Q.UNABBREV_TAC `p1`
  \\ FULL_SIMP_TAC std_ss [LENGTH_APPEND,word_arith_lemma1]
  \\ FULL_SIMP_TAC std_ss [AC ADD_ASSOC ADD_COMM,LENGTH,SEP_CLAUSES]
  \\ SEP_WRITE_TAC);

val arm_print_loop_sexp =
  (Q.GEN `t` o SIMP_RULE bool_ss [GSYM sexp2string_def,LET_DEF] o
   Q.SPECL [`t`,`T`]) arm_print_loop_lemma;


val (thms,arm_init_stack_def,arm_init_stack_pre_def) = compile_all ``
  arm_init_stack (r4:word32,r8:word32,r9:word32) =
    if r8 = 0w then
      let r8 = r9 in
        (r4,r8,r9)
    else
      let r8 = r9 + r4 in
      let r8 = r8 + 8w in
        (r4,r8,r9)``;

val (arm_print_sexp_thms,arm_print_sexp_def,arm_print_sexp_pre_def) = compile_all ``
  arm_print_sexp (r3,r7,r9,dh,h,df,f,dm,m,dg,g) =
    let r4 = h (r9 - 0x20w) in
    let r8 = h (r9 - 0x1Cw) in
    let (r4,r8,r9) = arm_init_stack (r4,r8,r9) in
    let r4 = r4 + r4 in
    let r4 = r4 + r9 in
    let r4 = r4 + 0x18w in
    let h = (r4 - 8w =+ r9) h in
    let h = (r4 - 4w =+ r7) h in
    let r9 = r4 in
    let r4 = 0w in
    let h = (r8 =+ r4) h in
    let r4 = 6w in
    let (r3,r4,r7,r8,r9,dh,h,dm,m,dg,g,df,f) =
      arm_print_loop (r3,r4,r7,r8,r9,dh,h,dm,m,dg,g,df,f) in
    let r3 = h (r9 - 4w) in
    let r9 = h (r9 - 8w) in
      (r3,r4,r7,r8,r9,dh,h,df,f,dm,m,dg,g)``;

val one_space_LESS_EQ = prove(
  ``!n a b df f. one_space a n b ((fun2set (f,df)):(word32 # 'a) set) ==> n <= 2**32``,
  ONCE_REWRITE_TAC [DECIDE ``n<=m = ~(m+1<=n:num)``]
  \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC bool_ss [LESS_EQ_EXISTS,GSYM ADD_ASSOC]
  \\ FULL_SIMP_TAC std_ss [one_space_ADD]
  \\ POP_ASSUM (K ALL_TAC)
  \\ POP_ASSUM MP_TAC
  \\ REWRITE_TAC [GSYM (EVAL ``SUC 4294967295``),GSYM (EVAL ``SUC 0``)]
  \\ SIMP_TAC bool_ss [one_space_def,SEP_CLAUSES]
  \\ SIMP_TAC std_ss [SEP_EXISTS]
  \\ ONCE_REWRITE_TAC [GSYM n2w_mod]
  \\ SIMP_TAC (std_ss++SIZES_ss) []
  \\ REPEAT STRIP_TAC
  \\ `~(a = a + 0w)` by SEP_NEQ_TAC
  \\ FULL_SIMP_TAC std_ss [WORD_ADD_0]);

val ch_active_set2_thm = prove(
  ``ch_active_set2 (a,i,n) = { a + n2w (4 * j) | 2 * i <= j /\ j < 2 * n }``,
  SIMP_TAC (std_ss++SIZES_ss) [ch_active_set2_def,ch_active_set_def,IN_UNION,
    IN_DELETE,WORD_EQ_ADD_CANCEL,n2w_11,GSPECIFICATION,EXTENSION]
  \\ REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC
  \\ ASM_SIMP_TAC std_ss [GSYM WORD_ADD_ASSOC,WORD_EQ_ADD_CANCEL]
  \\ ASM_SIMP_TAC std_ss [word_mul_n2w,word_add_n2w]
  THEN1 (Q.EXISTS_TAC `2*j`
    \\ SIMP_TAC std_ss [MULT_ASSOC,LEFT_ADD_DISTRIB] \\ DECIDE_TAC)
  THEN1 (Q.EXISTS_TAC `1+2*j`
    \\ SIMP_TAC std_ss [MULT_ASSOC,LEFT_ADD_DISTRIB] \\ DECIDE_TAC)
  \\ `?r q. (j = q * 2 + r) /\ r < 2` by METIS_TAC [DA,DECIDE ``0<2:num``]
  \\ Cases_on `r = 1` THENL [
    FULL_SIMP_TAC std_ss [] \\ DISJ2_TAC \\ Q.EXISTS_TAC `q`
    \\ SIMP_TAC std_ss [DECIDE ``4 * (q * 2 + 1) = 4 + 8 * q:num``] \\ DECIDE_TAC,
    `r = 0` by DECIDE_TAC \\ ASM_SIMP_TAC std_ss [DECIDE ``4 * (q * 2) = 8 * q:num``]
    \\ DISJ1_TAC \\ Q.EXISTS_TAC `q` \\ SIMP_TAC std_ss [] \\ DECIDE_TAC]);

val stack_slots_INTRO = prove(
  ``!n a. 8 * n < 2 ** 32 ==> stack_slots a n (fun2set (f,ch_active_set2 (a,0,n)))``,
  Induct
  \\ SIMP_TAC std_ss [stack_slots_def,emp_def,fun2set_EMPTY]
  THEN1 (SIMP_TAC std_ss [EXTENSION,ch_active_set_def,ch_active_set2_def]
         \\ SIMP_TAC std_ss [IN_UNION,GSPECIFICATION,NOT_IN_EMPTY])
  \\ SIMP_TAC std_ss [SEP_EXISTS]
  \\ SIMP_TAC std_ss [GSYM STAR_ASSOC,one_STAR,IN_fun2set,fun2set_DELETE]
  \\ REPEAT STRIP_TAC THENL [
    SIMP_TAC std_ss [ch_active_set2_def,ch_active_set_def,IN_UNION,GSPECIFICATION]
    \\ DISJ1_TAC \\ Q.EXISTS_TAC `0` \\ SIMP_TAC std_ss [WORD_ADD_0,word_mul_n2w],
    SIMP_TAC (std_ss++SIZES_ss) [ch_active_set2_def,ch_active_set_def,IN_UNION,
      IN_DELETE,WORD_EQ_ADD_CANCEL,n2w_11,GSPECIFICATION]
    \\ DISJ2_TAC \\ Q.EXISTS_TAC `0` \\ SIMP_TAC std_ss [WORD_ADD_0,word_mul_n2w],
    `ch_active_set2 (a,0,SUC n) DELETE a DELETE (a + 0x4w) =
     ch_active_set2 (a + 8w,0,n)` by
     (SIMP_TAC (std_ss++SIZES_ss) [ch_active_set2_thm,ch_active_set_def,IN_UNION,
        IN_DELETE,WORD_EQ_ADD_CANCEL,n2w_11,GSPECIFICATION,EXTENSION]
      \\ REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC
      \\ ASM_SIMP_TAC std_ss [GSYM WORD_ADD_ASSOC,WORD_EQ_ADD_CANCEL]
      \\ ASM_SIMP_TAC std_ss [word_mul_n2w,word_add_n2w] THENL [
        Q.EXISTS_TAC `j - 2`
        \\ Cases_on `j = 0` THEN1 FULL_SIMP_TAC std_ss [WORD_ADD_0]
        \\ Cases_on `j = 1` THEN1 FULL_SIMP_TAC std_ss [WORD_ADD_0]
        \\ `8 + 4 * (j - 2) = 4 * j` by DECIDE_TAC
        \\ ASM_SIMP_TAC std_ss [] \\ DECIDE_TAC,
        Q.EXISTS_TAC `2 + j`
        \\ SIMP_TAC std_ss [MULT_ASSOC,LEFT_ADD_DISTRIB] \\ DECIDE_TAC,
        FULL_SIMP_TAC std_ss [GSYM WORD_ADD_ASSOC,WORD_EQ_ADD_CANCEL,word_add_n2w]
        \\ `8 + 4 * j < 4294967296` by DECIDE_TAC
        \\ FULL_SIMP_TAC (std_ss++SIZES_ss) [n2w_11],
        FULL_SIMP_TAC std_ss [GSYM WORD_ADD_ASSOC,WORD_EQ_ADD_CANCEL,word_add_n2w]
        \\ `8 + 4 * j < 4294967296` by DECIDE_TAC
        \\ FULL_SIMP_TAC (std_ss++SIZES_ss) [n2w_11] \\ DECIDE_TAC])
    \\ FULL_SIMP_TAC std_ss []
    \\ `8 * n < 4294967296` by DECIDE_TAC
    \\ RES_TAC \\ FULL_SIMP_TAC std_ss []]);

val fun2set_UPDATE = prove(
  ``!a w df f. ~(a IN df) ==> (fun2set ((a =+ w) f,df) = fun2set (f,df))``,
  SIMP_TAC std_ss [fun2set_def,EXTENSION,GSPECIFICATION,APPLY_UPDATE_THM]
  \\ REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC
  \\ ASM_SIMP_TAC std_ss [] \\ METIS_TAC []);

val DIFF_DIFF_EQ = prove(
  ``!d dh. d SUBSET dh ==> (dh DIFF (dh DIFF d) = d)``,
  FULL_SIMP_TAC std_ss [EXTENSION,DISJOINT_DEF,IN_INTER,NOT_IN_EMPTY,
     SUBSET_DEF,IN_DIFF] \\ METIS_TAC []);

val arm_print_sexp_lemma = store_thm("arm_print_sexp_lemma",
  ``(one_space r7 (STRLEN (sexp2string t1) + 1) c) (fun2set (f,df)) /\
    lisp_inv (t1,t2,t3,t4,t5,t6,l) (w1,w2,w3,w4,w5,w6,r9,dh,h,sym,rest) ==>
    ?r4i r7i r8i hi fi.
      arm_print_sexp_pre (w1,r7,r9,dh,h,df,f,rest) /\
      (arm_print_sexp (w1,r7,r9,dh,h,df,f,rest) =
        (r7,r4i,r7i,r8i,r9,dh,hi,df,fi,rest)) /\
      (one_string r7 (STRCAT (sexp2string t1) null_string) c) (fun2set (fi,df))``,
  STRIP_TAC
  \\ IMP_RES_TAC one_space_LESS_EQ
  \\ REPEAT (POP_ASSUM MP_TAC)
  \\ SIMP_TAC std_ss [one_space_ADD,SEP_EXISTS]
  \\ SIMP_TAC bool_ss [GSYM (EVAL ``SUC 0``),one_space_def,SEP_CLAUSES]
  \\ SIMP_TAC bool_ss [SEP_EXISTS]
  \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC (std_ss++sep_cond_ss) [cond_STAR]
  \\ `LDEPTH t1 <= l` by IMP_RES_TAC lisp_inv_LDEPTH
  \\ `?dm m dg g. rest = (dm,m,dg,g)` by METIS_TAC [PAIR]
  \\ FULL_SIMP_TAC std_ss [lisp_inv_def,LET_DEF]
  \\ SIMP_TAC std_ss [arm_print_sexp_def,arm_print_sexp_pre_def,LET_DEF]
  \\ `ALIGNED (r9 - 0x20w) /\ ALIGNED (r9 - 0x1Cw)` by ALIGNED_TAC
  \\ ASM_SIMP_TAC std_ss [ALIGNED_INTRO]
  \\ `arm_init_stack (n2w (8 * l),if u then 0x0w else 0x1w,r9) =
        (n2w (8 * l),if u then r9 else r9 + 8w * n2w l + 8w,r9)` by
    (REVERSE (Cases_on `u`) \\ ASM_SIMP_TAC std_ss [arm_init_stack_def,LET_DEF]
     \\ SIMP_TAC (std_ss++SIZES_ss) [n2w_11,AC WORD_ADD_ASSOC WORD_ADD_COMM,GSYM word_mul_n2w])
  \\ ASM_SIMP_TAC std_ss []
  \\ Q.ABBREV_TAC `a = n2w (8 * l) + n2w (8 * l) + r9 + 0x18w`
  \\ Q.ABBREV_TAC `a1 = if u then r9 else r9 + 0x8w * n2w l + 0x8w`
  \\ `r9 + (n2w (8 * l) + n2w (8 * l)) + 0x18w = a` by
       (Q.UNABBREV_TAC `a` \\ SIMP_TAC std_ss [AC WORD_ADD_COMM WORD_ADD_ASSOC])
  \\ ASM_SIMP_TAC std_ss []
  \\ `ALIGNED a` by
   (Q.UNABBREV_TAC `a`
    \\ SIMP_TAC bool_ss [DECIDE ``8 * i = 4 * (2 * i):num``]
    \\ SIMP_TAC bool_ss [GSYM ADDR32_n2w,GSYM WORD_ADD_ASSOC]
    \\ ASM_SIMP_TAC std_ss [ALIGNED_ADD_EQ,ALIGNED_ADDR32,ALIGNED_n2w])
  \\ ASM_SIMP_TAC std_ss [ALIGNED_ADD_EQ,ALIGNED_n2w]
  \\ `r9 - 0x20w IN ref_set r9 (l + l + 1) /\
      r9 - 0x1Cw IN ref_set r9 (l + l + 1) /\
      a - 0x8w IN ref_set r9 (l + l + 1) /\
      a - 0x4w IN ref_set r9 (l + l + 1)` by
   (SIMP_TAC std_ss [ref_set_def,IN_UNION,GSPECIFICATION]
    \\ REPEAT STRIP_TAC
    THEN1 (DISJ2_TAC \\ Q.EXISTS_TAC `8` \\ SIMP_TAC std_ss [])
    THEN1 (DISJ2_TAC \\ Q.EXISTS_TAC `7` \\ SIMP_TAC std_ss [])
    \\ Q.UNABBREV_TAC `a` \\ DISJ1_TAC THENL [
      Q.EXISTS_TAC `2 * (l + l + 1) + 2`
      \\ SIMP_TAC std_ss [LEFT_ADD_DISTRIB,MULT_ASSOC]
      \\ SIMP_TAC std_ss [word_arith_lemma4]
      \\ SIMP_TAC std_ss [GSYM ADD_ASSOC]
      \\ SIMP_TAC std_ss [GSYM word_mul_n2w,GSYM word_add_n2w]
      \\ SIMP_TAC std_ss [AC WORD_ADD_ASSOC WORD_ADD_COMM],
      Q.EXISTS_TAC `2 * (l + l + 1) + 3`
      \\ SIMP_TAC std_ss [LEFT_ADD_DISTRIB,MULT_ASSOC]
      \\ SIMP_TAC std_ss [word_arith_lemma4]
      \\ SIMP_TAC std_ss [GSYM ADD_ASSOC]
      \\ SIMP_TAC std_ss [GSYM word_mul_n2w,GSYM word_add_n2w]
      \\ SIMP_TAC std_ss [AC WORD_ADD_ASSOC WORD_ADD_COMM]])
  \\ ASM_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC std_ss [DECIDE ``n + 1 <= 4294967296 = n < 4294967296:num``]
  \\ `ALIGNED a1` by
   (Q.UNABBREV_TAC `a1`
    \\ Cases_on `u` \\ ASM_SIMP_TAC std_ss []
    \\ SIMP_TAC std_ss [GSYM WORD_ADD_ASSOC,word_mul_n2w,word_add_n2w]
    \\ REWRITE_TAC [DECIDE ``8 * l + 8 = 4 * (2 * l + 2):num``,GSYM ADDR32_n2w]
    \\ ASM_SIMP_TAC std_ss [ALIGNED_ADD_EQ,ALIGNED_ADDR32])
  \\ `lisp_tree t1 (w1,ch_active_set2 (r9,if u then 1 + l else 1,i),h) sym`
       by IMP_RES_TAC lisp_x_IMP_lisp_tree
  \\ Q.ABBREV_TAC `h2 = (a1 =+ 0x0w) ((a - 0x4w =+ r7) ((a - 0x8w =+ r9) h))`
  \\ `r9 + 0x10w * n2w l + 0x18w = a` by
   (Q.UNABBREV_TAC `a`
    \\ SIMP_TAC std_ss [word_add_n2w,DECIDE ``8*l+8*l = 16 * l:num``]
    \\ SIMP_TAC std_ss [word_mul_n2w,AC WORD_ADD_COMM WORD_ADD_ASSOC])
  \\ `~(a1 = a - 0x4w) /\ ~(a1 = a - 0x8w)` by
   (POP_ASSUM (ASSUME_TAC o GSYM) \\ FULL_SIMP_TAC std_ss []
    \\ Q.UNABBREV_TAC `a1`
    \\ Cases_on `u` \\ FULL_SIMP_TAC std_ss [WORD_EQ_ADD_CANCEL]
    \\ FULL_SIMP_TAC std_ss [word_sub_def,GSYM WORD_ADD_ASSOC]
    \\ FULL_SIMP_TAC std_ss [WORD_EQ_ADD_CANCEL,GSYM word_sub_def]
    \\ SIMP_TAC std_ss [word_arith_lemma2]
    \\ SIMP_TAC std_ss [word_add_n2w,word_mul_n2w]
    \\ `16 * l + 20 < 4294967296 /\ 16 * l + 16 < 4294967296` by DECIDE_TAC
    \\ `8 * l + 8 < 4294967296` by DECIDE_TAC
    \\ ASM_SIMP_TAC (std_ss++SIZES_ss) [n2w_11]
    \\ DECIDE_TAC)
  \\ FULL_SIMP_TAC std_ss [GSYM CONJ_ASSOC]
  \\ Q.ABBREV_TAC `d = ch_active_set2 (a1,0,SUC l)`
  \\ Q.ABBREV_TAC `d2 = ch_active_set2 (r9,if u then 1 + l else 1,i)`
  \\ `DISJOINT d d2` by
   (SIMP_TAC std_ss [DISJOINT_DEF,EXTENSION,IN_INTER,NOT_IN_EMPTY]
    \\ STRIP_TAC \\ Cases_on `x IN d` \\ ASM_SIMP_TAC std_ss []
    \\ Q.UNABBREV_TAC `d` \\ Q.UNABBREV_TAC `d2`
    \\ FULL_SIMP_TAC std_ss [ch_active_set_def,ch_active_set2_def]
    \\ FULL_SIMP_TAC std_ss [IN_UNION,GSPECIFICATION]
    \\ Q.UNABBREV_TAC `a1` \\ Cases_on `u` \\ FULL_SIMP_TAC std_ss []
    \\ SIMP_TAC std_ss [GSYM WORD_ADD_ASSOC,WORD_EQ_ADD_CANCEL]
    \\ SIMP_TAC std_ss [word_mul_n2w,word_add_n2w]
    THEN1
     (REPEAT STRIP_TAC
      \\ `8 * j < 4294967296` by DECIDE_TAC
      \\ SIMP_TAC std_ss [DISJ_ASSOC]
      \\ REWRITE_TAC [METIS_PROVE [] ``c \/ ~b = (b ==> c)``]
      \\ NTAC 2 STRIP_TAC
      \\ `8 * j' < 4294967296 /\ 4 + 8 * j' < 4294967296` by DECIDE_TAC
      \\ ASM_SIMP_TAC (std_ss++SIZES_ss) [n2w_11] \\ DECIDE_TAC)
    THEN1
     (REPEAT STRIP_TAC
      \\ `8 * l + (8 + 8 * j) < 4294967296` by DECIDE_TAC
      \\ SIMP_TAC std_ss [DISJ_ASSOC]
      \\ REWRITE_TAC [METIS_PROVE [] ``c \/ ~b = (b ==> c)``]
      \\ NTAC 2 STRIP_TAC
      \\ `8 * j' < 4294967296 /\ 4 + 8 * j' < 4294967296` by DECIDE_TAC
      \\ ASM_SIMP_TAC (std_ss++SIZES_ss) [n2w_11] \\ DECIDE_TAC)
    THEN1
     (REPEAT STRIP_TAC
      \\ `4 + 8 * j < 4294967296 /\ 8 * j < 4294967296` by DECIDE_TAC
      \\ SIMP_TAC std_ss [DISJ_ASSOC]
      \\ REWRITE_TAC [METIS_PROVE [] ``c \/ ~b = (b ==> c)``]
      \\ NTAC 2 STRIP_TAC
      \\ `8 * j' < 4294967296 /\ 4 + 8 * j' < 4294967296` by DECIDE_TAC
      \\ ASM_SIMP_TAC (std_ss++SIZES_ss) [n2w_11] \\ DECIDE_TAC)
    THEN1
     (REPEAT STRIP_TAC
      \\ `8 * l + (8 + (4 + 8 * j)) < 4294967296` by DECIDE_TAC
      \\ SIMP_TAC std_ss [DISJ_ASSOC]
      \\ REWRITE_TAC [METIS_PROVE [] ``c \/ ~b = (b ==> c)``]
      \\ NTAC 2 STRIP_TAC
      \\ `8 * j' < 4294967296 /\ 4 + 8 * j' < 4294967296` by DECIDE_TAC
      \\ ASM_SIMP_TAC (std_ss++SIZES_ss) [n2w_11] \\ DECIDE_TAC))
  \\ REPEAT (Q.PAT_X_ASSUM `lisp_x tt ww sym` (K ALL_TAC))
  \\ Q.PAT_X_ASSUM `!x. bb` (K ALL_TAC)
  \\ Q.ABBREV_TAC `c2 = r7 + n2w (STRLEN (sexp2string t1))`
  \\ `d2 SUBSET ref_set r9 (l+l+1)` by
   (Q.UNABBREV_TAC `d2`
    \\ SIMP_TAC std_ss [ch_active_set2_def,SUBSET_DEF,IN_UNION]
    \\ SIMP_TAC std_ss [ref_set_def,ch_active_set_def,GSPECIFICATION,IN_UNION]
    \\ REPEAT STRIP_TAC \\ DISJ1_TAC \\ ASM_SIMP_TAC std_ss []
    \\ SIMP_TAC std_ss [GSYM WORD_ADD_ASSOC,WORD_EQ_ADD_CANCEL]
    \\ SIMP_TAC std_ss [word_mul_n2w,word_add_n2w] THENL [
      Q.EXISTS_TAC `2 * j` \\ SIMP_TAC std_ss [MULT_ASSOC]
      \\ Cases_on `u` \\ FULL_SIMP_TAC std_ss [] \\ DECIDE_TAC,
      Q.EXISTS_TAC `1 + 2 * j` \\ SIMP_TAC std_ss [MULT_ASSOC,LEFT_ADD_DISTRIB]
      \\ Cases_on `u` \\ FULL_SIMP_TAC std_ss [] \\ DECIDE_TAC])
  \\ `d SUBSET ref_set r9 (l+l+1)` by
   (Q.UNABBREV_TAC `d`
    \\ SIMP_TAC std_ss [ch_active_set2_def,SUBSET_DEF,IN_UNION]
    \\ SIMP_TAC std_ss [ref_set_def,ch_active_set_def,GSPECIFICATION,IN_UNION]
    \\ Q.UNABBREV_TAC `a1`
    \\ REPEAT STRIP_TAC \\ DISJ1_TAC \\ ASM_SIMP_TAC std_ss []
    \\ Cases_on `u` \\ FULL_SIMP_TAC std_ss []
    \\ SIMP_TAC std_ss [GSYM WORD_ADD_ASSOC,WORD_EQ_ADD_CANCEL]
    \\ SIMP_TAC std_ss [word_mul_n2w,word_add_n2w]
    THEN1 (Q.EXISTS_TAC `2 * j` \\ SIMP_TAC std_ss [MULT_ASSOC] \\ DECIDE_TAC)
    THEN1 (Q.EXISTS_TAC `2 * (l + (1 + j))`
      \\ SIMP_TAC std_ss [MULT_ASSOC,LEFT_ADD_DISTRIB] \\ DECIDE_TAC)
    THEN1 (Q.EXISTS_TAC `1 + 2 * j`
      \\ SIMP_TAC std_ss [MULT_ASSOC,LEFT_ADD_DISTRIB] \\ DECIDE_TAC)
    THEN1 (Q.EXISTS_TAC `2 * l + (2 + (1 + 2 * j))`
      \\ SIMP_TAC std_ss [MULT_ASSOC,LEFT_ADD_DISTRIB] \\ DECIDE_TAC))
  \\ Q.PAT_X_ASSUM `dh = ref_set r9 (l + l + 1)` (ASSUME_TAC o GSYM)
  \\ FULL_SIMP_TAC std_ss []
  \\ `8 * (SUC l) < 2 ** 32` by (FULL_SIMP_TAC std_ss [] \\ DECIDE_TAC)
  \\ IMP_RES_TAC stack_slots_INTRO
  \\ POP_ASSUM (ASSUME_TAC o Q.SPECL [`h`,`a1`])
  \\ Q.UNABBREV_TAC `d`
  \\ Q.ABBREV_TAC `d = ch_active_set2 (a1,0,SUC l)`
  \\ FULL_SIMP_TAC std_ss [stack_slots_def,SEP_EXISTS]
  \\ `a1 IN d` by SEP_READ_TAC
  \\ `a1 IN dh` by METIS_TAC [SUBSET_DEF]
  \\ ASM_SIMP_TAC std_ss []
  \\ `~(a - 0x4w IN d) /\ ~(a - 0x8w IN d)` by
   (Q.PAT_X_ASSUM `r9 + 0x10w * n2w l + 0x18w = a` (ASSUME_TAC o GSYM)
    \\ FULL_SIMP_TAC std_ss []
    \\ Q.UNABBREV_TAC `d` \\ Q.UNABBREV_TAC `a1`
    \\ SIMP_TAC std_ss [ch_active_set2_thm,GSPECIFICATION]
    \\ Cases_on `u` \\ FULL_SIMP_TAC std_ss []
    \\ SIMP_TAC std_ss [word_sub_def]
    \\ SIMP_TAC std_ss [GSYM WORD_ADD_ASSOC,WORD_EQ_ADD_CANCEL]
    \\ SIMP_TAC std_ss [word_mul_n2w,word_add_n2w]
    \\ REPEAT STRIP_TAC
    \\ SIMP_TAC std_ss [GSYM word_sub_def,word_arith_lemma2,word_add_n2w]
    \\ `16 * l + 20 < 4294967296 /\ 16 * l + 16 < 4294967296` by DECIDE_TAC
    \\ SIMP_TAC std_ss [DISJ_ASSOC]
    \\ REWRITE_TAC [METIS_PROVE [] ``c \/ ~b = (b ==> c)``]
    \\ STRIP_TAC THENL [
      `4 * j < 4294967296` by DECIDE_TAC
      \\ ASM_SIMP_TAC (std_ss++SIZES_ss) [MULT_ASSOC,LEFT_ADD_DISTRIB,n2w_11]
      \\ DECIDE_TAC,
      `4 * j < 4294967296` by DECIDE_TAC
      \\ ASM_SIMP_TAC (std_ss++SIZES_ss) [MULT_ASSOC,LEFT_ADD_DISTRIB,n2w_11]
      \\ DECIDE_TAC,
     `8 * l + (8 + 4 * j) < 4294967296` by DECIDE_TAC
      \\ ASM_SIMP_TAC (std_ss++SIZES_ss) [MULT_ASSOC,LEFT_ADD_DISTRIB,n2w_11]
      \\ DECIDE_TAC,
      `8 * l + (8 + 4 * j) < 4294967296` by DECIDE_TAC
      \\ ASM_SIMP_TAC (std_ss++SIZES_ss) [MULT_ASSOC,LEFT_ADD_DISTRIB,n2w_11]
      \\ DECIDE_TAC])
  \\ `(one (a1,y') * one (a1 + 0x4w,y'') * stack_slots (a1 + 0x8w) l)
         (fun2set (((a - 0x4w =+ r7) ((a - 0x8w =+ r9) h)),d))` by
    ASM_SIMP_TAC std_ss [fun2set_UPDATE]
  \\ `(one (a1,0w) * one (a1 + 0x4w,y'') * stack_slots (a1 + 0x8w) l)
         (fun2set (h2,d))` by
   (Q.UNABBREV_TAC `h2`
    \\ Q.ABBREV_TAC `h3 = (a - 0x4w =+ r7) ((a - 0x8w =+ r9) h)`
    \\ SEP_WRITE_TAC)
  \\ STRIP_ASSUME_TAC (Q.SPECL [`LDEPTH t1`,`l`,`a1+8w`] stack_slots_MAX)
  \\ `MAX (LDEPTH t1) l = l` by (ASM_SIMP_TAC std_ss [MAX_DEF] \\ DECIDE_TAC)
  \\ FULL_SIMP_TAC std_ss []
  \\ `(fr * one (a1,0w) * one (a1 + 0x4w,y'') * stack_slots (a1 + 0x8w) (LDEPTH t1))
         (fun2set (h2,d)) /\
      (one (c2,y) * one_space r7 (STRLEN (sexp2string t1)) c2)
        (fun2set (f,df))` by (FULL_SIMP_TAC (std_ss++star_ss) [] \\ DECIDE_TAC)
  \\ Q.ABBREV_TAC `d3 = dh DIFF d`
  \\ `dh DIFF d3 = d` by (Q.UNABBREV_TAC `d3` \\ ASM_SIMP_TAC std_ss [DIFF_DIFF_EQ])
  \\ `(fr * one (a1,0w) * one (a1 + 0x4w,y'') * stack_slots (a1 + 0x8w) (LDEPTH t1))
         (fun2set (h2,dh DIFF d3))` by (FULL_SIMP_TAC (std_ss++star_ss) [] \\ DECIDE_TAC)
  \\ `d3 SUBSET dh` by (Q.UNABBREV_TAC `d3` \\ SIMP_TAC std_ss [SUBSET_DEF,IN_DIFF])
  \\ `d2 SUBSET d3` by
   (Q.UNABBREV_TAC `d3`
    \\ FULL_SIMP_TAC std_ss [SUBSET_DEF,IN_DIFF,DISJOINT_DEF,IN_INTER,EXTENSION,NOT_IN_EMPTY]
    \\ METIS_TAC [])
  \\ MP_TAC ((Q.INST [`r9`|->`a`,`d`|->`d3`] o
              Q.SPECL [`t1`,`one (c2,y)`,`y''`,`0w`,`w1`,`r7`,`a1`,`h2`,`f`,`fr`,`c2`])
             arm_print_loop_sexp)
  \\ `~(a - 0x4w IN d2) /\ ~(a - 0x8w IN d2)` by
   (Q.PAT_X_ASSUM `r9 + 0x10w * n2w l + 0x18w = a` (ASSUME_TAC o GSYM)
    \\ FULL_SIMP_TAC std_ss []
    \\ Q.UNABBREV_TAC `d2` \\ Q.UNABBREV_TAC `a1`
    \\ SIMP_TAC std_ss [ch_active_set2_thm,GSPECIFICATION]
    \\ REPEAT (Q.PAT_X_ASSUM `bbb (fun2set(ff,fff))` (K ALL_TAC))
    \\ Cases_on `u` \\ FULL_SIMP_TAC std_ss []
    \\ SIMP_TAC std_ss [word_sub_def]
    \\ SIMP_TAC std_ss [GSYM WORD_ADD_ASSOC,WORD_EQ_ADD_CANCEL]
    \\ SIMP_TAC std_ss [word_mul_n2w,word_add_n2w]
    \\ REPEAT STRIP_TAC
    \\ SIMP_TAC std_ss [GSYM word_sub_def,word_arith_lemma2,word_add_n2w]
    \\ `16 * l + 20 < 4294967296 /\ 16 * l + 16 < 4294967296` by DECIDE_TAC
    \\ SIMP_TAC std_ss [DISJ_ASSOC]
    \\ REWRITE_TAC [METIS_PROVE [] ``c \/ ~b = (b ==> c)``]
    \\ STRIP_TAC \\ STRIP_TAC
    \\ `4 * j < 4294967296` by DECIDE_TAC
    \\ ASM_SIMP_TAC (std_ss++SIZES_ss) [MULT_ASSOC,LEFT_ADD_DISTRIB,n2w_11]
    \\ DECIDE_TAC)
  \\ `lisp_tree t1 (w1,d2,h2) sym` by
   (Q.UNABBREV_TAC `h2`
    \\ `~(a1 IN d2)` by METIS_TAC [DISJOINT_DEF,IN_INTER,NOT_IN_EMPTY,EXTENSION]
    \\ ASM_SIMP_TAC std_ss [NOT_IN_lisp_tree])
  \\ IMP_RES_TAC lisp_tree_SUBSET
  \\ ASM_SIMP_TAC std_ss [] \\ STRIP_TAC
  \\ ASM_SIMP_TAC std_ss []
  \\ SIMP_TAC std_ss [arm_print_loop1_pre_def,arm_print_loop1_def]
  \\ ONCE_REWRITE_TAC [arm_print_loop_pre_def,arm_print_loop_def]
  \\ ASM_SIMP_TAC std_ss [LET_DEF,w2w_0]
  \\ SIMP_TAC std_ss [one_string_STRCAT,null_string_def]
  \\ `c2 IN df` by SEP_READ_TAC
  \\ FULL_SIMP_TAC std_ss [one_string_def,one_list_def,MAP,EVAL ``ORD #"\^@"``]
  \\ SIMP_TAC std_ss [SEP_CLAUSES,CONJ_ASSOC]
  \\ REVERSE STRIP_TAC THEN1 SEP_WRITE_TAC
  \\ `a - 0x4w IN d3 /\ a - 0x8w IN d3` by
       (Q.UNABBREV_TAC `d3` \\ ASM_SIMP_TAC std_ss [IN_DIFF])
  \\ `(hi (a - 0x4w) = h2 (a - 0x4w)) /\ (hi (a - 0x8w) = h2 (a - 0x8w))` by FULL_SIMP_TAC std_ss [fun_eq_def]
  \\ ASM_SIMP_TAC std_ss []
  \\ Q.UNABBREV_TAC `h2`
  \\ REPEAT (Q.PAT_X_ASSUM `bbb (fun2set(ff,fff))` (K ALL_TAC))
  \\ SIMP_TAC std_ss [APPLY_UPDATE_THM]
  \\ ASM_SIMP_TAC std_ss [word_sub_def,word_2comp_n2w]
  \\ SIMP_TAC (std_ss++SIZES_ss) [WORD_EQ_ADD_CANCEL,n2w_11]);

(*

set_trace "Goalstack.print_goal_at_top" 1
set_trace "Goalstack.print_goal_at_top" 0

*)

val (arm_sexp2string_th,arm_sexp2string_def,arm_sexp2string_pre_def) = compile "arm" ``
  arm_sexp2string (r1,r3,r9,dh,h,df,f,dm,m,dg,g) =
    let r7 = r1 in
    let (r3,r4,r7,r8,r9,dh,h,df,f,dm,m,dg,g) =
           arm_print_sexp (r3,r7,r9,dh,h,df,f,dm,m,dg,g) in
    let r3 = r1 in
      (r3,dh,h,df,f,dm,m,dg,g)``;

val (ppc_sexp2string_th,ppc_sexp2string_def,ppc_sexp2string_pre_def) = compile "ppc" ``
  ppc_sexp2string (r1,r3,r9,dh,h,df,f,dm,m,dg,g) =
    let r7 = r1 in
    let (r3,r4,r7,r8,r9,dh,h,df,f,dm,m,dg,g) =
           arm_print_sexp (r3,r7,r9,dh,h,df,f,dm,m,dg,g) in
    let r3 = r1 in
      (r3,dh,h,df,f,dm,m,dg,g)``;

fun save_all prefix postfix =
  map (fn (n,th) => save_thm(prefix ^ n ^ postfix,th));

val _ = save_all "" "_sexp2string_thm"
  ([("arm",arm_sexp2string_th),("ppc",ppc_sexp2string_th)] @
   filter (fn (n,th) => n = "x86") arm_print_sexp_thms);


val _ = export_theory();
