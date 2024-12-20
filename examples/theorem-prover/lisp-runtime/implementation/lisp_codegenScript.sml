open HolKernel Parse boolLib bossLib; val _ = new_theory "lisp_codegen";
val _ = ParseExtras.temp_loose_equality()
open lisp_sexpTheory lisp_consTheory lisp_invTheory lisp_symbolsTheory;

(* --- *)

open wordsTheory arithmeticTheory wordsLib listTheory pred_setTheory pairTheory;
open combinTheory finite_mapTheory addressTheory helperLib;
open set_sepTheory bitTheory fcpTheory stringTheory;

val wstd_ss = std_ss ++ SIZES_ss ++ rewrites [DECIDE ``n<256 ==> (n:num)<18446744073709551616``,ORD_BOUND];

open stop_and_copyTheory;
open codegenLib decompilerLib prog_x64Lib prog_x64Theory progTheory;
open lisp_parseTheory;

val RW = REWRITE_RULE;
val RW1 = ONCE_REWRITE_RULE;
fun SUBGOAL q = REVERSE (sg q)

val _ = augment_srw_ss [rewrites [listTheory.DROP_def, listTheory.TAKE_def]]

val align_blast = blastLib.BBLAST_PROVE
  ``(a && 3w = 0w) ==> ((a - w && 3w = 0w) = (w && 3w = 0w:word64))``

val align_add_blast = blastLib.BBLAST_PROVE
  ``(a && 3w = 0w) ==> ((a + w && 3w = 0w) = (w && 3w = 0w:word64))``

val FORALL_EXISTS = METIS_PROVE [] ``(!x. P x ==> Q) = ((?x. P x) ==> Q)``
val IMP_IMP = METIS_PROVE [] ``b /\ (c ==> d) ==> ((b ==> c) ==> d)``

val LISP = lisp_inv_def |> SPEC_ALL |> concl |> dest_eq |> fst;
val REST = LISP |> cdr |> cdr |> cdr |> cdr |> cdr |> cdr |> cdr |> cdr |> cdr;
val STAT = LISP |> car |> car |> cdr;
val VAR_REST = LISP |> car |> cdr |> cdr |> cdr |> cdr |> cdr |> cdr |> cdr;


(* is_quote *)

val (thm,mc_is_quote_def) = basic_decompile_strings x64_tools "mc_is_quote"
  (SOME (``(r0:word64,r6:word64,df:word64 set,f:word64->word32)``,
         ``(r1:word64,r6:word64,df:word64 set,f:word64->word32)``))
  (assemble "x64" `
       test r0,1
       jne FALSE
       mov r1d,[r6+4*r0]
       mov r0d,[r6+4*r0+4]
       cmp r1,19
       jne FALSE
       test r0,1
       jne FALSE
       mov r1d,[r6+4*r0+4]
       cmp r1,3
       jne FALSE
TRUE:  mov r1d,1
       jmp EXIT
FALSE: xor r1,r1
EXIT:`)

val mc_is_quote_blast = blastLib.BBLAST_PROVE
  ``((31 -- 0) (w2w (w:word32)):word64 = w2w w) /\
    ((w2w w && 0x1w = 0x0w:word64) = (w && 0x1w = 0x0w))``

val mc_is_quote_thm = prove(
  ``^LISP ==>
    mc_is_quote_pre (w2w w0,bp,df,f) /\
    (mc_is_quote (w2w w0,bp,df,f) = (if isQuote x0 then 1w else 0w,bp,df,f))``,
  SIMP_TAC std_ss [isQuote_def,mc_is_quote_def,LET_DEF,mc_is_quote_blast]
  \\ STRIP_TAC \\ IMP_RES_TAC lisp_inv_type \\ ASM_SIMP_TAC std_ss []
  \\ Cases_on `isDot x0` \\ FULL_SIMP_TAC std_ss []
  \\ IMP_RES_TAC lisp_inv_car
  \\ IMP_RES_TAC (el 3 (CONJUNCTS lisp_inv_Sym))
  \\ FULL_SIMP_TAC std_ss [AC WORD_ADD_COMM WORD_ADD_ASSOC]
  \\ Cases_on `CAR x0 = Sym "QUOTE"`  \\ ASM_SIMP_TAC std_ss []
  \\ IMP_RES_TAC lisp_inv_cdr
  \\ IMP_RES_TAC lisp_inv_type \\ ASM_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC std_ss [AC WORD_ADD_COMM WORD_ADD_ASSOC]
  \\ Cases_on `isDot (CDR x0)`  \\ ASM_SIMP_TAC std_ss []
  \\ IMP_RES_TAC lisp_inv_cdr
  \\ IMP_RES_TAC (el 1 (CONJUNCTS lisp_inv_Sym))
  \\ FULL_SIMP_TAC std_ss [AC WORD_ADD_COMM WORD_ADD_ASSOC]
  \\ Cases_on `CDR (CDR x0) = Sym "NIL"`  \\ ASM_SIMP_TAC std_ss []);

val (mc_is_quote_full_spec,mc_is_quote_full_def) = basic_decompile_strings x64_tools "mc_is_quote_full"
  (SOME (``(r8:word64,r6:word64,df:word64 set,f:word64->word32)``,
         ``(r0:word64,r1:word64,r8:word64,r6:word64,df:word64 set,f:word64->word32)``))
  (assemble "x64" `
      mov r0,r8
      insert mc_is_quote
      mov r0d,3
      mov r8d,11
      test r1,r1
      cmove r8,r0
      mov r1d,1
   `)

val _ = save_thm("mc_is_quote_full_spec",mc_is_quote_full_spec);

val mc_is_quote_full_thm = prove(
  ``^LISP ==>
    ?v0. mc_is_quote_full_pre (w2w w0,bp,df,f) /\
         (mc_is_quote_full (w2w w0,bp,df,f) = (tw0,tw1,w2w v0,bp,df,f)) /\
         let (w0,x0) = (v0,LISP_TEST (isQuote x0)) in ^LISP``,
  FULL_SIMP_TAC std_ss [mc_is_quote_full_def,LET_DEF] \\ STRIP_TAC
  \\ IMP_RES_TAC mc_is_quote_thm \\ ASM_SIMP_TAC std_ss []
  \\ `(tw0 = 3w) /\ (tw1 = 1w)` by FULL_SIMP_TAC std_ss [lisp_inv_def]
  \\ Cases_on `isQuote x0` \\ FULL_SIMP_TAC wstd_ss [n2w_11,LISP_TEST_def]
  THEN1 (Q.EXISTS_TAC `0xBw` \\ FULL_SIMP_TAC wstd_ss [w2w_def,w2n_n2w]
    \\ IMP_RES_TAC (el 2 (CONJUNCTS lisp_inv_Sym)))
  THEN1 (Q.EXISTS_TAC `0x3w` \\ FULL_SIMP_TAC wstd_ss [w2w_def,w2n_n2w]
    \\ IMP_RES_TAC (el 1 (CONJUNCTS lisp_inv_Sym)))) |> SIMP_RULE std_ss [LET_DEF];

val _ = save_thm("mc_is_quote_full_thm",mc_is_quote_full_thm);


(* lookup constant *)

val (mc_const_load_spec,mc_const_load_def) = basic_decompile_strings x64_tools "mc_const_load"
  (SOME (``(r2:word64,r7:word64,r8:word64,df:word64 set,f:word64->word32)``,
         ``(r2:word64,r7:word64,r8:word64,df:word64 set,f:word64->word32)``))
  (assemble "x64" `
       mov r2,[r7-64]
       mov r8d,[r2+r8]
   `)

val PULL_EXISTS_OVER_CONJ = METIS_PROVE []
  ``((?x. P x) /\ Q = ?x. P x /\ Q) /\ (Q /\ (?x. P x) = ?x. P x /\ Q)``

val ref_heap_addr_alt = store_thm("ref_heap_addr_alt",
  ``(ref_heap_addr (H_ADDR a) = n2w a << 1) /\
    (ref_heap_addr (H_DATA (INL w)) = w2w w << 2 + 0x1w) /\
    (ref_heap_addr (H_DATA (INR v)) = w2w v << 3 + 0x3w)``,
  SIMP_TAC std_ss [ref_heap_addr_def] \\ blastLib.BBLAST_TAC);

val mc_const_load_blast = prove(
  ``w2w ((0x1w:word32) + w2w w << 2) = (0x1w:word64) + w2w (w:word30) << 2``,
  blastLib.BBLAST_TAC);

val gc_w2w_lemma = prove(
  ``!w. ((w2w:word64->word32) ((w2w:word32->word64) w) = w) /\
        ((31 -- 0) ((w2w:word32->word64) w) = w2w w) /\
        ((31 >< 0) bp = (w2w bp):word32) /\
        ((63 >< 32) bp = (w2w (bp >>> 32)):word32) /\
        (w2w ((w2w (bp >>> 32)):word32) << 32 !! w2w ((w2w bp):word32) = bp:word64)``,
  blastLib.BBLAST_TAC);

val mc_const_load_thm = prove(
  ``^LISP ==> getVal x0 < LENGTH xs1 /\ isVal x0 ==>
    ?w0i tw2i.
      mc_const_load_pre (tw2,sp,w2w w0,df,f) /\
      (mc_const_load (tw2,sp,w2w w0,df,f) = (tw2i,sp,w2w w0i,df,f)) /\
      let (x0,tw2,w0) = (EL (getVal x0) xs1, tw2i, w0i) in ^LISP``,
  FULL_SIMP_TAC std_ss [LET_DEF,mc_const_load_def] \\ REPEAT STRIP_TAC
  \\ IMP_RES_TAC lisp_inv_ds_read
  \\ FULL_SIMP_TAC std_ss [INSERT_SUBSET,EMPTY_SUBSET,gc_w2w_lemma]
  \\ `sp && 0x3w = 0x0w` by FULL_SIMP_TAC std_ss [lisp_inv_def]
  \\ FULL_SIMP_TAC std_ss [align_blast,n2w_and_3,isVal_thm,getVal_def]
  \\ Q.EXISTS_TAC `f (w2w w0 + EL 6 ds)` \\ FULL_SIMP_TAC std_ss []
  \\ Q.PAT_X_ASSUM `lisp_inv xxx yyy zzz` ASSUME_TAC
  \\ FULL_SIMP_TAC std_ss [lisp_inv_def,PULL_EXISTS_OVER_CONJ,EVERY_DEF,lisp_x_def]
  \\ Q.LIST_EXISTS_TAC [`EL a ss1`,`s1`,`s2`,`s3`,`s4`,`s5`]
  \\ Q.LIST_EXISTS_TAC [`m`,`i`,`ss`,`ss1`,`sym`,`b`]
  \\ FULL_SIMP_TAC std_ss [MAP,CONS_11,EVERY_DEF,LENGTH,ADD1,ZIP,EVERY_DEF,getVal_def]
  \\ `?ss3 s ss4. (ss1 = ss3 ++ s::ss4) /\ (LENGTH ss3 = a)` by METIS_TAC [SPLIT_LIST,APPEND_ASSOC,APPEND]
  \\ `?xs3 x xs4. (xs1 = xs3 ++ x::xs4) /\ (LENGTH xs3 = a)` by METIS_TAC [SPLIT_LIST,APPEND_ASSOC,APPEND]
  \\ FULL_SIMP_TAC std_ss [ZIP_APPEND,ZIP,EVERY_DEF,EVERY_APPEND,GSYM APPEND_ASSOC]
  \\ FULL_SIMP_TAC std_ss [ZIP,APPEND,EVERY_DEF]
  \\ FULL_SIMP_TAC std_ss [rich_listTheory.EL_APPEND2,LENGTH_APPEND,LENGTH,EL,HD]
  \\ SIMP_TAC std_ss [GSYM CONJ_ASSOC] \\ STRIP_TAC THEN1
   (FULL_SIMP_TAC std_ss [ok_split_heap_def,UNION_SUBSET,ref_heap_addr_def]
    \\ FULL_SIMP_TAC std_ss [SUBSET_DEF,ADDR_SET_def,GSPECIFICATION,lisp_x_def]
    \\ FULL_SIMP_TAC std_ss [MEM,MEM_APPEND,n2w_w2n] \\ REPEAT STRIP_TAC
    \\ Q.PAT_X_ASSUM `!x. bb \/ bbb ==> bbbb` MATCH_MP_TAC
    \\ ASM_SIMP_TAC std_ss [] \\ FULL_SIMP_TAC (srw_ss()) [])
  \\ Q.PAT_X_ASSUM `EVERY xx yy` MP_TAC
  \\ FULL_SIMP_TAC std_ss [ZIP_APPEND,EVERY_APPEND,ZIP,EVERY_DEF] \\ STRIP_TAC
  \\ Q.PAT_X_ASSUM `ref_heap_addr (H_DATA (INL (n2w a))) = w0` (MP_TAC o GSYM)
  \\ FULL_SIMP_TAC std_ss [RW1 [WORD_ADD_COMM] ref_heap_addr_alt,mc_const_load_blast]
  \\ ONCE_REWRITE_TAC [WORD_ADD_COMM]
  \\ FULL_SIMP_TAC std_ss [WORD_ADD_ASSOC,WORD_SUB_ADD] \\ STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [ref_full_stack_def,APPEND_ASSOC]
  \\ FULL_SIMP_TAC std_ss [ref_stack_def,Once ref_stack_APPEND,APPEND]
  \\ Cases_on `wsp`
  \\ FULL_SIMP_TAC std_ss [STAR_ASSOC,word_mul_n2w,word_arith_lemma1,w2n_n2w]
  \\ FULL_SIMP_TAC (std_ss++SIZES_ss) [w2w_def,w2n_n2w,WORD_MUL_LSL,word_mul_n2w]
  \\ FULL_SIMP_TAC std_ss [GSYM LEFT_ADD_DISTRIB,LENGTH_APPEND,word_arith_lemma1]
  \\ Q.PAT_X_ASSUM `LENGTH ss + n = sl` (fn th => FULL_SIMP_TAC std_ss [GSYM th])
  \\ FULL_SIMP_TAC std_ss [AC ADD_COMM ADD_ASSOC] \\ SEP_R_TAC
  \\ ASM_SIMP_TAC std_ss [align_add_blast,n2w_and_3,RW1[MULT_COMM]MOD_EQ_0])
  |> SIMP_RULE std_ss [LET_DEF];

val _ = save_thm("mc_const_load_spec",mc_const_load_spec);
val _ = save_thm("mc_const_load_thm",mc_const_load_thm);


(* store new constant *)

val (mc_const_store_spec,mc_const_store_def) = basic_decompile_strings x64_tools "mc_const_store"
  (SOME (``(r0:word64,r2:word64,r7:word64,r8:word64,df:word64 set,f:word64->word32)``,
         ``(r0:word64,r2:word64,r7:word64,r8:word64,df:word64 set,f:word64->word32)``))
  (assemble "x64" `
       mov r0,[r7-48]
       mov r2,[r7-64]
       shl r0,2
       inc r2
       dec QWORD [r7-56]
       inc QWORD [r7-48]
       mov [r0+r2],r8d
       xor r8,r8
       not r8
       mov [r0+r2+4],r8d
       inc r0
       mov r8d,r0
       mov r0d,3
   `)

val EL_UPDATE_NTH = store_thm("EL_UPDATE_NTH",
  ``!xs n k x. EL n (UPDATE_NTH k x xs) =
               if (k = n) /\ k < LENGTH xs then x else EL n xs``,
  Induct \\ Cases_on `k` \\ SIMP_TAC std_ss [LENGTH,UPDATE_NTH_def]
  THEN1 (Cases_on `n` \\ FULL_SIMP_TAC std_ss [EL,HD,TL] \\ FULL_SIMP_TAC std_ss [ADD1])
  \\ Cases_on `n'` \\ FULL_SIMP_TAC std_ss [EL,HD,TL]
  \\ FULL_SIMP_TAC std_ss [ADD1]);

val mc_const_store_blast = blastLib.BBLAST_PROVE
  ``(31 -- 0) (w:word64) = w2w ((w2w w):word32)``

val mc_const_store_thm = prove(
  ``~(EL 7 ds = 0w) /\ ^LISP ==>
    ?w0i tw2i fi.
      mc_const_store_pre (tw0,tw2,sp,w2w w0,df,f) /\
      (mc_const_store (tw0,tw2,sp,w2w w0,df,f) = (tw0,tw2i,sp,w2w w0i,df,fi)) /\
      let (x0,xs1,tw2,w0,f,ds) = (Val (LENGTH xs1), xs1 ++ [x0],
             tw2i, w0i, fi, UPDATE_NTH 7 (EL 7 ds - 1w) (UPDATE_NTH 8 (EL 8 ds + 1w) ds)) in ^LISP``,
  FULL_SIMP_TAC std_ss [LET_DEF,mc_const_store_def] \\ REPEAT STRIP_TAC
  \\ IMP_RES_TAC lisp_inv_ds_read
  \\ FULL_SIMP_TAC std_ss [INSERT_SUBSET,EMPTY_SUBSET,gc_w2w_lemma]
  \\ `sp && 0x3w = 0x0w` by FULL_SIMP_TAC std_ss [lisp_inv_def]
  \\ FULL_SIMP_TAC std_ss [align_blast,n2w_and_3,isVal_thm,getVal_def]
  \\ Q.EXISTS_TAC `w2w (EL 8 ds) << 2 + 0x1w` \\ FULL_SIMP_TAC std_ss []
  \\ Q.PAT_X_ASSUM `lisp_inv xxx yyy zzz` ASSUME_TAC
  \\ FULL_SIMP_TAC std_ss [lisp_inv_def,PULL_EXISTS_OVER_CONJ,EVERY_DEF,lisp_x_def]
  \\ Q.LIST_EXISTS_TAC [`s1`,`s2`,`s3`,`s4`,`s5`]
  \\ Q.LIST_EXISTS_TAC [`m`,`i`,`ss`,`ss1 ++ [s0]`,`sym`,`b`]
  \\ FULL_SIMP_TAC std_ss [LENGTH_UPDATE_NTH,EL_UPDATE_NTH]
  \\ FULL_SIMP_TAC std_ss [word_arith_lemma1,LENGTH_APPEND,WORD_SUB_ADD,LENGTH]
  \\ FULL_SIMP_TAC std_ss [n2w_11,MAP,CONS_11,ref_heap_addr_alt,word_arith_lemma2]
  \\ `(sl1 - LENGTH ss1) < 18446744073709551616` by DECIDE_TAC
  \\ FULL_SIMP_TAC (std_ss++SIZES_ss) []
  \\ `~(sl1 < LENGTH ss1 + 1) /\ LENGTH ss1 + 1 <= sl1` by DECIDE_TAC
  \\ Q.PAT_X_ASSUM `LENGTH xs = LENGTH ss` ASSUME_TAC
  \\ FULL_SIMP_TAC std_ss [SUB_PLUS,ZIP_APPEND,EVERY_APPEND,EVERY_DEF,ZIP]
  \\ `sp + n2w (4 * sl) - 0x1w + n2w (LENGTH ss1) << 2 + 0x1w =
      sp + n2w (4 * sl) + n2w (LENGTH ss1) << 2` by WORD_DECIDE_TAC
  \\ `LENGTH ss1 < 1073741824 /\ LENGTH ss1 < 18446744073709551616` by DECIDE_TAC
  \\ `(4 * LENGTH ss1 + 1) < 18446744073709551616` by DECIDE_TAC
  \\ `0xFFFFFFFFFFFFFFFFw = 0xFFFFFFFFw:word32` by EVAL_TAC
  \\ FULL_SIMP_TAC (std_ss++SIZES_ss) [w2w_def,w2n_n2w,GSYM LEFT_ADD_DISTRIB,
       align_add_blast,n2w_and_3,RW1[MULT_COMM]MOD_EQ_0,GSYM CONJ_ASSOC,
       EVAL ``w2n (~0x0w:word64)``,WORD_MUL_LSL,word_mul_n2w,word_arith_lemma1,
       mc_const_store_blast] \\ STRIP_TAC THEN1
   (FULL_SIMP_TAC std_ss [ok_split_heap_def,UNION_SUBSET,ref_heap_addr_def]
    \\ FULL_SIMP_TAC std_ss [SUBSET_DEF,ADDR_SET_def,GSPECIFICATION,lisp_x_def]
    \\ FULL_SIMP_TAC std_ss [MEM,MEM_APPEND,n2w_w2n] \\ REPEAT STRIP_TAC
    \\ Q.PAT_X_ASSUM `!x. bb \/ bbb ==> bbbb` MATCH_MP_TAC
    \\ ASM_SIMP_TAC std_ss [] \\ FULL_SIMP_TAC (srw_ss()) [])
  \\ Q.PAT_X_ASSUM `LENGTH cs = 10` MP_TAC
  \\ IMP_RES_TAC expand_list
  \\ FULL_SIMP_TAC std_ss [UPDATE_NTH_CONS,
       GSYM (SIMP_RULE std_ss [word_mul_n2w] (Q.SPECL [`n2w a`,`32`] WORD_MUL_LSL))]
  \\ `(sl1 - LENGTH ss1 - 1) < 18446744073709551616` by DECIDE_TAC
  \\ FULL_SIMP_TAC std_ss [GSYM w2w_def]
  \\ Q.PAT_X_ASSUM `xxx (fun2set (f,df))` MP_TAC
  \\ FULL_SIMP_TAC std_ss [EL_CONS] \\ NTAC 2 STRIP_TAC
  \\ Q.ABBREV_TAC `aa = [a1; a2; n2w e; bp2; sa1; sa2; sa3; ex]`
  \\ `LENGTH aa = 8` by (Q.UNABBREV_TAC `aa` \\ EVAL_TAC)
  \\ FULL_SIMP_TAC std_ss [ref_full_stack_def,ref_static_APPEND,LENGTH_APPEND]
  \\ FULL_SIMP_TAC std_ss [word_arith_lemma3,ref_static_def,LET_DEF,word64_3232_def,STAR_ASSOC]
  \\ FULL_SIMP_TAC std_ss [APPEND_ASSOC]
  \\ Q.ABBREV_TAC `ss2 = ss ++ ss1`
  \\ SIMP_TAC std_ss [ref_stack_APPEND,ref_stack_def,STAR_ASSOC]
  \\ FULL_SIMP_TAC std_ss [RW [APPEND_NIL,ref_stack_def] (Q.SPECL [`xs`,`[]`] ref_stack_APPEND)]
  \\ FULL_SIMP_TAC std_ss [SEP_CLAUSES,STAR_ASSOC]
  \\ ASM_SIMP_TAC (std_ss++SIZES_ss)
      [APPLY_UPDATE_THM,RW [GSYM word_sub_def] (Q.SPECL [`w`,`-x`,`-y`] WORD_EQ_ADD_LCANCEL),
       WORD_EQ_NEG,n2w_11,word_add_n2w]
  \\ Cases_on `sl1 - LENGTH ss1` THEN1 (`F` by DECIDE_TAC)
  \\ FULL_SIMP_TAC std_ss []
  \\ `sp + 0x4w * wsp + n2w (4 * LENGTH ss2) =
      sp + n2w (4 * (sl + LENGTH ss1))` by
   (Cases_on `wsp` \\ FULL_SIMP_TAC std_ss [word_mul_n2w,w2n_n2w]
    \\ Q.UNABBREV_TAC `ss2`
    \\ FULL_SIMP_TAC std_ss [word_arith_lemma1,LENGTH_APPEND,GSYM LEFT_ADD_DISTRIB]
    \\ NTAC 3 AP_TERM_TAC \\ DECIDE_TAC)
  \\ Q.UNABBREV_TAC `ss2`
  \\ FULL_SIMP_TAC std_ss [ref_stack_space_above_def,STAR_ASSOC,
       SEP_CLAUSES,LEFT_ADD_DISTRIB,SEP_EXISTS_THM,LENGTH_APPEND]
  \\ FULL_SIMP_TAC std_ss [word_arith_lemma1]
  \\ REVERSE STRIP_TAC THEN1 SEP_READ_TAC
  \\ FULL_SIMP_TAC std_ss [LENGTH,ADD_ASSOC,GSYM word_add_n2w,WORD_ADD_ASSOC]
  \\ SEP_W_TAC
  \\ FULL_SIMP_TAC (std_ss++star_ss) []
  \\ FULL_SIMP_TAC std_ss [STAR_ASSOC]
  \\ POP_ASSUM MP_TAC
  \\ FULL_SIMP_TAC (std_ss++SIZES_ss) [w2w_def,w2n_n2w]
  \\ `n < 18446744073709551616` by DECIDE_TAC
  \\ FULL_SIMP_TAC (std_ss++star_ss) []
  \\ FULL_SIMP_TAC std_ss [STAR_ASSOC])
  |> SIMP_RULE std_ss [LET_DEF];

val _ = save_thm("mc_const_store_spec",mc_const_store_spec);
val _ = save_thm("mc_const_store_thm",mc_const_store_thm);


(* xbp set *)

val (mc_xbp_set_spec,mc_xbp_set_def) = basic_decompile_strings x64_tools "mc_xbp_set"
  (SOME (``(r2:word64,r3:word64,r7:word64,df:word64 set,f:word64->word32)``,
         ``(r2:word64,r3:word64,r7:word64,df:word64 set,f:word64->word32)``))
  (assemble "x64" `
       lea r2,[4*r3+r7-1]
       mov [r7-104],r2
   `)

val UPDATE_NTH_1 = prove(``UPDATE_NTH 1 x (y1::y2::ys) = y1::x::ys``, EVAL_TAC);

val mc_xbp_set_thm = prove(
  ``^LISP ==>
    ?tw2i fi.
      mc_xbp_set_pre (tw2,wsp,sp,df,f) /\
      (mc_xbp_set (tw2,wsp,sp,df,f) = (tw2i,wsp,sp,df,fi)) /\
      let (xbp,tw2,ds,f) = (LENGTH xs, tw2i, UPDATE_NTH 1 (sp + 4w * wsp - 1w) ds, fi) in ^LISP``,
  SIMP_TAC std_ss [mc_xbp_set_def,LET_DEF,INSERT_SUBSET,EMPTY_SUBSET] \\ STRIP_TAC
  \\ `(sp - 0x64w IN df /\ sp - 0x68w IN df)` by
      (IMP_RES_TAC lisp_inv_ds_read \\ ASM_SIMP_TAC std_ss [])
  \\ FULL_SIMP_TAC std_ss [LET_DEF,lisp_inv_def]
  \\ ASM_SIMP_TAC std_ss [align_blast,n2w_and_3]
  \\ ASM_SIMP_TAC std_ss []
  \\ Q.LIST_EXISTS_TAC [`s0`,`s1`,`s2`,`s3`,`s4`,`s5`]
  \\ Q.LIST_EXISTS_TAC [`m`,`i`,`ss`,`ss1`,`sym`,`b`]
  \\ FULL_SIMP_TAC std_ss [LENGTH_UPDATE_NTH,EL_UPDATE_NTH]
  \\ Q.PAT_X_ASSUM `xxx = sl` (ASSUME_TAC o GSYM o RW1[ADD_COMM])
  \\ FULL_SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC THEN1
   (FULL_SIMP_TAC std_ss [LEFT_ADD_DISTRIB,GSYM word_add_n2w,
      WORD_ADD_ASSOC,WORD_ADD_SUB,WORD_EQ_ADD_LCANCEL,WORD_EQ_ADD_RCANCEL]
    \\ FULL_SIMP_TAC std_ss [GSYM word_mul_n2w,n2w_w2n])
  \\ Cases_on `ds` \\ FULL_SIMP_TAC std_ss [LENGTH,ADD1]
  \\ Cases_on `t` \\ FULL_SIMP_TAC std_ss [LENGTH,ADD1]
  \\ Q.PAT_X_ASSUM `xxx (fun2set (f,df))` MP_TAC
  \\ FULL_SIMP_TAC std_ss [ref_full_stack_def,ref_static_APPEND,LENGTH,LENGTH_APPEND]
  \\ FULL_SIMP_TAC std_ss [word_arith_lemma3,UPDATE_NTH_1]
  \\ Q.ABBREV_TAC `xssss = [a1; a2; n2w e; bp2; sa1; sa2; sa3; ex]`
  \\ FULL_SIMP_TAC std_ss [ref_static_def,word64_3232_def,LET_DEF]
  \\ FULL_SIMP_TAC std_ss [word_arith_lemma3,word_arith_lemma2,word_arith_lemma1,
       STAR_ASSOC,gc_w2w_lemma]
  \\ FULL_SIMP_TAC std_ss [AC WORD_ADD_ASSOC WORD_ADD_COMM]
  \\ REPEAT STRIP_TAC \\ SEP_WRITE_TAC) |> SIMP_RULE std_ss [LET_DEF];

val _ = save_thm("mc_xbp_set_spec",mc_xbp_set_spec);
val _ = save_thm("mc_xbp_set_thm",mc_xbp_set_thm);


(* load based on xbp *)

val (mc_xbp_load_spec,mc_xbp_load_def) = basic_decompile_strings x64_tools "mc_xbp_load"
  (SOME (``(r2:word64,r7:word64,r9:word64,df:word64 set,f:word64->word32)``,
         ``(r2:word64,r7:word64,r9:word64,r12:word64,df:word64 set,f:word64->word32)``))
  (assemble "x64" `
       mov r2,[r7-104]
       mov r12d,[r2+r9]
   `)

val BLAST_LEMMA = prove(``w << 2 !! 1w = w << 2 + 1w:word32``,blastLib.BBLAST_TAC);

val UPDATE_NTH_1 = prove(``UPDATE_NTH 1 x (y1::y2::ys) = y1::x::ys``, EVAL_TAC);

val mc_xbp_load_blast = blastLib.BBLAST_PROVE
  ``((31 -- 0) (w2w w1) = (w2w w2):word64) = (w1 = w2:word32)``

val mc_xbp_load_thm = prove(
  ``^LISP ==> isVal x1 /\ getVal x1 < xbp /\ xbp <= LENGTH xs ==>
    ?tw2i w4i.
      mc_xbp_load_pre (tw2,sp,w2w w1,df,f) /\
      (mc_xbp_load (tw2,sp,w2w w1,df,f) = (tw2i,sp,w2w w1,w2w w4i,df,f)) /\
      let (x4,tw2,w4) = (EL ((LENGTH xs + getVal x1) - xbp) xs,tw2i,w4i) in ^LISP``,
  Cases_on `isVal x1` \\ FULL_SIMP_TAC std_ss [LET_DEF]
  \\ FULL_SIMP_TAC std_ss [isVal_thm,getVal_def] \\ STRIP_TAC
  \\ SIMP_TAC std_ss [mc_xbp_load_def,LET_DEF,INSERT_SUBSET,EMPTY_SUBSET]
  \\ IMP_RES_TAC lisp_inv_ds_read \\ ASM_SIMP_TAC std_ss []
  \\ Q.PAT_X_ASSUM `lisp_inv xxx yyy zzz` MP_TAC \\ REPEAT (POP_ASSUM (K ALL_TAC))
  \\ NTAC 2 STRIP_TAC \\ FULL_SIMP_TAC std_ss [mc_xbp_load_blast]
  \\ Q.ABBREV_TAC `n = LENGTH xs + a - xbp`
  \\ `EL 1 ds + w2w w1 = sp + 0x4w * wsp + 0x4w * n2w n` by
   (FULL_SIMP_TAC std_ss [lisp_inv_def,MAP,CONS_11,EVERY_DEF,lisp_x_def]
    \\ Q.PAT_X_ASSUM `ref_heap_addr s1 = w1` (MP_TAC o GSYM)
    \\ FULL_SIMP_TAC std_ss [ref_heap_addr_def,BLAST_LEMMA]
    \\ REPEAT STRIP_TAC
    \\ FULL_SIMP_TAC (std_ss++SIZES_ss) [w2w_def,w2n_n2w,WORD_MUL_LSL]
    \\ `(4 * a + 1) < 4294967296` by DECIDE_TAC
    \\ FULL_SIMP_TAC (std_ss++SIZES_ss) [word_mul_n2w,word_add_n2w,w2n_n2w]
    \\ ONCE_REWRITE_TAC [ADD_COMM]
    \\ SIMP_TAC std_ss [GSYM word_add_n2w,WORD_SUB_ADD,WORD_ADD_ASSOC]
    \\ ASM_SIMP_TAC std_ss [word_arith_lemma3]
    \\ Q.PAT_X_ASSUM `LENGTH ss + w2n wsp = sl` (MP_TAC o GSYM)
    \\ ASM_SIMP_TAC std_ss [] \\ Q.SPEC_TAC (`wsp`,`w`)
    \\ Cases \\ ASM_SIMP_TAC std_ss [word_arith_lemma1,word_mul_n2w,w2n_n2w]
    \\ `~(4 * (LENGTH ss + n') < 4 * xbp - 4 * a)` by DECIDE_TAC
    \\ ASM_SIMP_TAC std_ss [WORD_EQ_ADD_LCANCEL,word_arith_lemma4]
    \\ REPEAT STRIP_TAC \\ AP_TERM_TAC \\ Q.UNABBREV_TAC `n` \\ DECIDE_TAC)
  \\ ASM_SIMP_TAC std_ss []
  \\ `n < LENGTH xs` by (Q.UNABBREV_TAC `n` \\ DECIDE_TAC)
  \\ IMP_RES_TAC lisp_inv_swap4
  \\ IMP_RES_TAC (RW[AND_IMP_INTRO]lisp_inv_load_lemma)
  \\ ASM_SIMP_TAC std_ss []
  \\ `sp && 3w = 0w` by FULL_SIMP_TAC std_ss [lisp_inv_def]
  \\ FULL_SIMP_TAC std_ss [AC WORD_ADD_ASSOC WORD_ADD_COMM]
  \\ FULL_SIMP_TAC std_ss [align_blast,n2w_and_3]
  \\ MATCH_MP_TAC lisp_inv_swap4
  \\ MATCH_MP_TAC (GEN_ALL lisp_inv_ignore_tw2) \\ ASM_SIMP_TAC std_ss []
  \\ Q.EXISTS_TAC `tw2` \\ ASM_SIMP_TAC std_ss [])
  |> SIMP_RULE std_ss [LET_DEF];

val _ = save_thm("mc_xbp_load_spec",mc_xbp_load_spec);
val _ = save_thm("mc_xbp_load_thm",mc_xbp_load_thm);


(* load amnt *)

val (mc_load_amnt_spec,mc_load_amnt_def) = basic_decompile_strings x64_tools "mc_load_amnt"
  (SOME (``(r7:word64,df:word64 set,f:word64->word32)``,
         ``(r7:word64,r9:word64,df:word64 set,f:word64->word32)``))
  (assemble "x64" `
       mov r9d,[r7-40]
       shl r9d,2
       inc r9d
   `)

val mc_load_amnt_thm = prove(
  ``^LISP ==>
    ?w1i.
      mc_load_amnt_pre (sp,df,f) /\
      (mc_load_amnt (sp,df,f) = (sp,w2w w1i,df,f)) /\
      let (x1,w1) = (Val amnt,w1i) in ^LISP``,
  FULL_SIMP_TAC std_ss [mc_load_amnt_def,LET_DEF,mc_xbp_load_blast] \\ STRIP_TAC
  \\ IMP_RES_TAC lisp_inv_swap1
  \\ IMP_RES_TAC lisp_inv_amnt_read
  \\ Q.EXISTS_TAC `w2w ((w2w (f (sp - 0x24w)) << 32 !! (w2w:word32->word64) (f (sp - 0x28w))) << 2 + 0x1w)`
  \\ IMP_RES_TAC lisp_inv_swap1
  \\ FULL_SIMP_TAC std_ss [WORD_MUL_LSL]
  \\ Q.SPEC_TAC (`f (sp - 0x24w)`,`w`)
  \\ Q.SPEC_TAC (`f (sp - 0x28w)`,`w1`)
  \\ blastLib.BBLAST_TAC);

val _ = save_thm("mc_load_amnt_spec",mc_load_amnt_spec);
val _ = save_thm("mc_load_amnt_thm",mc_load_amnt_thm);


(* pops by x1 *)

val (mc_pops_by_var_spec,mc_pops_by_var_def) = basic_decompile_strings x64_tools "mc_pops_by_var"
  (SOME (``(r2:word64,r3:word64,r9:word64)``,
         ``(r2:word64,r3:word64,r9:word64)``))
  (assemble "x64" `
       mov r2,r9
       shr r2,2
       add r3,r2
   `)

val mc_pops_by_var_thm = prove(
  ``^LISP ==> isVal x1 /\ getVal x1 <= LENGTH xs ==>
    ?tw2i wspi.
      mc_pops_by_var_pre (tw2,wsp,w2w w1) /\
      (mc_pops_by_var (tw2,wsp,w2w w1) = (tw2i,wspi,w2w w1)) /\
      let (xs,wsp,tw2) = (DROP (getVal x1) xs,wspi,tw2i) in ^LISP``,
  Cases_on `isVal x1` \\ FULL_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC std_ss [isVal_thm,getVal_def,LET_DEF,mc_pops_by_var_def]
  \\ REPEAT STRIP_TAC
  \\ MATCH_MP_TAC (GEN_ALL lisp_inv_ignore_tw2) \\ ASM_SIMP_TAC std_ss []
  \\ Q.EXISTS_TAC `tw2` \\ ASM_SIMP_TAC std_ss []
  \\ SUBGOAL `wsp + w2w w1 >>> 2 = wsp + n2w a` THEN1
   (ASM_SIMP_TAC std_ss []
    \\ MATCH_MP_TAC(RW[AND_IMP_INTRO]lisp_inv_pops_lemma)
    \\ ASM_SIMP_TAC std_ss [])
  \\ FULL_SIMP_TAC std_ss [lisp_inv_def,MAP,CONS_11,EVERY_DEF,lisp_x_def]
  \\ Q.PAT_X_ASSUM `xxx = w1` (MP_TAC o GSYM)
  \\ FULL_SIMP_TAC std_ss [ref_heap_addr_def]
  \\ SUBGOAL `n2w a = (w2w:word30->word64) (n2w a)` THEN1
   (FULL_SIMP_TAC std_ss []
    \\ Q.SPEC_TAC (`(n2w a):word30`,`w`) \\ blastLib.BBLAST_TAC)
  \\ FULL_SIMP_TAC wstd_ss [w2w_def,w2n_n2w]);

val _ = save_thm("mc_pops_by_var_spec",mc_pops_by_var_spec);
val _ = save_thm("mc_pops_by_var_thm",mc_pops_by_var_thm);


(* store based on xbp *)

val (mc_xbp_store_spec,mc_xbp_store_def) = basic_decompile_strings x64_tools "mc_xbp_store"
  (SOME (``(r2:word64,r7:word64,r8:word64,r9:word64,df:word64 set,f:word64->word32)``,
         ``(r2:word64,r7:word64,r8:word64,r9:word64,df:word64 set,f:word64->word32)``))
  (assemble "x64" `
       mov r2,[r7-104]
       mov [r2+r9],r8d
   `)

val mc_xbp_store_blast = blastLib.BBLAST_PROVE
  ``w2w ((w2w w):word64) = (w:word32)``

val mc_xbp_store_thm = prove(
  ``^LISP ==> isVal x1 /\ getVal x1 < xbp /\ xbp <= LENGTH xs ==>
    ?tw2i fi.
      mc_xbp_store_pre (tw2,sp,w2w w0,w2w w1,df,f) /\
      (mc_xbp_store (tw2,sp,w2w w0,w2w w1,df,f) = (tw2i,sp,w2w w0,w2w w1,df,fi)) /\
      let (xs,tw2,f) = (UPDATE_NTH ((LENGTH xs + getVal x1) - xbp) x0 xs,tw2i,fi) in ^LISP``,
  Cases_on `isVal x1` \\ FULL_SIMP_TAC std_ss [LET_DEF]
  \\ FULL_SIMP_TAC std_ss [isVal_thm,getVal_def] \\ STRIP_TAC
  \\ SIMP_TAC std_ss [mc_xbp_store_def,LET_DEF,INSERT_SUBSET,EMPTY_SUBSET]
  \\ IMP_RES_TAC lisp_inv_ds_read \\ ASM_SIMP_TAC std_ss []
  \\ Q.PAT_X_ASSUM `lisp_inv xxx yyy zzz` MP_TAC \\ REPEAT (POP_ASSUM (K ALL_TAC))
  \\ NTAC 2 STRIP_TAC \\ FULL_SIMP_TAC std_ss [mc_xbp_load_blast]
  \\ Q.ABBREV_TAC `n = LENGTH xs + a - xbp`
  \\ `EL 1 ds + w2w w1 = sp + 0x4w * wsp + 0x4w * n2w n` by
   (FULL_SIMP_TAC std_ss [lisp_inv_def,MAP,CONS_11,EVERY_DEF,lisp_x_def]
    \\ Q.PAT_X_ASSUM `ref_heap_addr s1 = w1` (MP_TAC o GSYM)
    \\ FULL_SIMP_TAC std_ss [ref_heap_addr_def,BLAST_LEMMA]
    \\ REPEAT STRIP_TAC
    \\ FULL_SIMP_TAC (std_ss++SIZES_ss) [w2w_def,w2n_n2w,WORD_MUL_LSL]
    \\ `(4 * a + 1) < 4294967296` by DECIDE_TAC
    \\ FULL_SIMP_TAC (std_ss++SIZES_ss) [word_mul_n2w,word_add_n2w,w2n_n2w]
    \\ ONCE_REWRITE_TAC [ADD_COMM]
    \\ SIMP_TAC std_ss [GSYM word_add_n2w,WORD_SUB_ADD,WORD_ADD_ASSOC]
    \\ ASM_SIMP_TAC std_ss [word_arith_lemma3]
    \\ Q.PAT_X_ASSUM `LENGTH ss + w2n wsp = sl` (MP_TAC o GSYM)
    \\ ASM_SIMP_TAC std_ss [] \\ Q.SPEC_TAC (`wsp`,`w`)
    \\ Cases \\ ASM_SIMP_TAC std_ss [word_arith_lemma1,word_mul_n2w,w2n_n2w]
    \\ `~(4 * (LENGTH ss + n') < 4 * xbp - 4 * a)` by DECIDE_TAC
    \\ ASM_SIMP_TAC std_ss [WORD_EQ_ADD_LCANCEL,word_arith_lemma4]
    \\ REPEAT STRIP_TAC \\ AP_TERM_TAC \\ Q.UNABBREV_TAC `n` \\ DECIDE_TAC)
  \\ ASM_SIMP_TAC std_ss []
  \\ `n < LENGTH xs` by (Q.UNABBREV_TAC `n` \\ DECIDE_TAC)
  \\ IMP_RES_TAC (RW[AND_IMP_INTRO]lisp_inv_store_lemma)
  \\ ASM_SIMP_TAC std_ss []
  \\ `sp && 3w = 0w` by FULL_SIMP_TAC std_ss [lisp_inv_def]
  \\ FULL_SIMP_TAC std_ss [AC WORD_ADD_ASSOC WORD_ADD_COMM]
  \\ FULL_SIMP_TAC std_ss [align_blast,n2w_and_3,mc_xbp_store_blast]
  \\ MATCH_MP_TAC (GEN_ALL lisp_inv_ignore_tw2) \\ ASM_SIMP_TAC std_ss []
  \\ Q.EXISTS_TAC `tw2` \\ ASM_SIMP_TAC std_ss [])
  |> SIMP_RULE std_ss [LET_DEF];

val _ = save_thm("mc_xbp_store_spec",mc_xbp_store_spec);
val _ = save_thm("mc_xbp_store_thm",mc_xbp_store_thm);


(* read code_ptr code *)

val (mc_read_snd_code_spec,mc_read_snd_code_def) = basic_decompile_strings x64_tools "mc_read_snd_code"
  (SOME (``(r7:word64,r8:word64,df:word64 set,f:word64->word32)``,
         ``(r7:word64,r8:word64,df:word64 set,f:word64->word32)``))
  (assemble "x64" `
       mov r8,[r7-96]
       sub r8,[r7-160]
       shl r8,2
       inc r8
   `)

val mc_read_snd_code_thm = prove(
  ``^LISP ==>
    ?v0.
      mc_read_snd_code_pre (sp,w2w w0,df,f) /\
      (mc_read_snd_code (sp,w2w w0,df,f) = (sp,w2w v0,df,f)) /\
      let (x0,w0) = (Val (code_ptr code),v0) in ^LISP``,
  REPEAT STRIP_TAC \\ SIMP_TAC std_ss [mc_read_snd_code_def,LET_DEF]
  \\ IMP_RES_TAC lisp_inv_cs_read \\ IMP_RES_TAC lisp_inv_ds_read
  \\ ASM_SIMP_TAC std_ss [INSERT_SUBSET,EMPTY_SUBSET]
  \\ `sp && 3w = 0w` by FULL_SIMP_TAC std_ss [lisp_inv_def]
  \\ ASM_SIMP_TAC std_ss [align_blast,n2w_and_3]
  \\ Q.EXISTS_TAC `n2w (4 * (code_ptr code) + 1)`
  \\ `code_ptr code < 1073741824` by
      (FULL_SIMP_TAC std_ss [lisp_inv_def,code_heap_def] \\ DECIDE_TAC)
  \\ REVERSE STRIP_TAC
  THEN1 (MATCH_MP_TAC lisp_inv_Val_n2w \\ ASM_SIMP_TAC std_ss [])
  \\ `EL 2 ds - EL 4 cs = n2w (code_ptr code)` by
    (FULL_SIMP_TAC std_ss [lisp_inv_def,code_heap_def]
     \\ ONCE_REWRITE_TAC [WORD_ADD_COMM] \\ SIMP_TAC std_ss [WORD_ADD_SUB])
  \\ FULL_SIMP_TAC std_ss [WORD_MUL_LSL,word_mul_n2w,word_add_n2w]
  \\ `(4 * code_ptr code + 1) < 4294967296` by DECIDE_TAC
  \\ ASM_SIMP_TAC wstd_ss [w2w_def,w2n_n2w])
  |> SIMP_RULE std_ss [LET_DEF];

val _ = save_thm("mc_read_snd_code_spec",mc_read_snd_code_spec);
val _ = save_thm("mc_read_snd_code_thm",mc_read_snd_code_thm);


(* safe versions of car and cdr, i.e. total versions *)

val SAFE_CAR_def = Define `SAFE_CAR x = CAR x`;
val SAFE_CDR_def = Define `SAFE_CDR x = CDR x`;

val (mc_safe_car_spec,mc_safe_car_def) = basic_decompile_strings x64_tools "mc_safe_car"
  (SOME (``(r0:word64,r6:word64,r8:word64,df:word64 set,f:word64->word32)``,
         ``(r0:word64,r6:word64,r8:word64,df:word64 set,f:word64->word32)``))
  (assemble "x64" `
       test r8,1
       cmovne r8,r0
       jne L
       mov r8d, [r6+4*r8]
L: `)

val (mc_safe_cdr_spec,mc_safe_cdr_def) = basic_decompile_strings x64_tools "mc_safe_cdr"
  (SOME (``(r0:word64,r6:word64,r8:word64,df:word64 set,f:word64->word32)``,
         ``(r0:word64,r6:word64,r8:word64,df:word64 set,f:word64->word32)``))
  (assemble "x64" `
       test r8,1
       cmovne r8,r0
       jne L
       mov r8d, [r6+4*r8+4]
L: `)

val mc_safe_car_pre_def = CONJUNCT2 mc_safe_car_def
val mc_safe_cdr_pre_def = CONJUNCT2 mc_safe_cdr_def

val mc_safe_car_blast = blastLib.BBLAST_PROVE
  ``((w2w (w0:word32) && 0x1w = 0x0w:word64) = (w0 && 1w = 0w)) /\
    ((((31 -- 0) ((w2w w))) = (w2w (v:word32)):word64) = (w = v))``

val mc_safe_car_lemma = prove(
  ``^LISP ==>
    ?w0i.
      mc_safe_car_pre (tw0,bp,w2w w0,df,f) /\
      (mc_safe_car (tw0,bp,w2w w0,df,f) = (tw0,bp,w2w w0i,df,f)) /\
      let (x0,w0) = (SAFE_CAR x0,w0i) in ^LISP``,
  FULL_SIMP_TAC std_ss [SAFE_CAR_def,SAFE_CDR_def]
  \\ FULL_SIMP_TAC std_ss [mc_safe_car_def,mc_safe_cdr_def,LET_DEF]
  \\ FULL_SIMP_TAC std_ss [mc_safe_car_blast] \\ STRIP_TAC
  \\ IMP_RES_TAC lisp_inv_type \\ ASM_SIMP_TAC std_ss []
  \\ Cases_on `isDot x0` \\ ASM_SIMP_TAC std_ss [] THEN1
   (IMP_RES_TAC lisp_inv_car \\ IMP_RES_TAC lisp_inv_cdr
    \\ FULL_SIMP_TAC std_ss [AC WORD_ADD_ASSOC WORD_ADD_COMM,mc_safe_car_blast])
  \\ `(CAR x0 = Sym "NIL") /\ (CDR x0 = Sym "NIL")` by
    (Cases_on `x0` \\ FULL_SIMP_TAC std_ss [isDot_def,CAR_def,CDR_def])
  \\ ASM_SIMP_TAC std_ss [] \\ Q.EXISTS_TAC `3w`
  \\ `tw0 = 3w` by FULL_SIMP_TAC std_ss [lisp_inv_def]
  \\ IMP_RES_TAC lisp_inv_nil
  \\ POP_ASSUM MP_TAC \\ FULL_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC wstd_ss [w2w_def,w2n_n2w])
  |> SIMP_RULE std_ss [LET_DEF];

val mc_safe_car_thm = prove(
  ``^LISP ==>
    (?w0i.
      mc_safe_car_pre (tw0,bp,w2w w0,df,f) /\
      (mc_safe_car (tw0,bp,w2w w0,df,f) = (tw0,bp,w2w w0i,df,f)) /\
      let (x0,w0) = (SAFE_CAR x0,w0i) in ^LISP) /\
    (?w1i.
      mc_safe_car_pre (tw0,bp,w2w w1,df,f) /\
      (mc_safe_car (tw0,bp,w2w w1,df,f) = (tw0,bp,w2w w1i,df,f)) /\
      let (x1,w1) = (SAFE_CAR x1,w1i) in ^LISP) /\
    (?w2i.
      mc_safe_car_pre (tw0,bp,w2w w2,df,f) /\
      (mc_safe_car (tw0,bp,w2w w2,df,f) = (tw0,bp,w2w w2i,df,f)) /\
      let (x2,w2) = (SAFE_CAR x2,w2i) in ^LISP) /\
    (?w3i.
      mc_safe_car_pre (tw0,bp,w2w w3,df,f) /\
      (mc_safe_car (tw0,bp,w2w w3,df,f) = (tw0,bp,w2w w3i,df,f)) /\
      let (x3,w3) = (SAFE_CAR x3,w3i) in ^LISP) /\
    (?w4i.
      mc_safe_car_pre (tw0,bp,w2w w4,df,f) /\
      (mc_safe_car (tw0,bp,w2w w4,df,f) = (tw0,bp,w2w w4i,df,f)) /\
      let (x4,w4) = (SAFE_CAR x4,w4i) in ^LISP) /\
    (?w5i.
      mc_safe_car_pre (tw0,bp,w2w w5,df,f) /\
      (mc_safe_car (tw0,bp,w2w w5,df,f) = (tw0,bp,w2w w5i,df,f)) /\
      let (x5,w5) = (SAFE_CAR x5,w5i) in ^LISP)``,
  REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [LET_DEF]
  THEN1 (IMP_RES_TAC mc_safe_car_lemma \\ METIS_TAC [])
  THEN1 (IMP_RES_TAC lisp_inv_swap1 \\ IMP_RES_TAC mc_safe_car_lemma
         \\ METIS_TAC [lisp_inv_swap1])
  THEN1 (IMP_RES_TAC lisp_inv_swap2 \\ IMP_RES_TAC mc_safe_car_lemma
         \\ METIS_TAC [lisp_inv_swap2])
  THEN1 (IMP_RES_TAC lisp_inv_swap3 \\ IMP_RES_TAC mc_safe_car_lemma
         \\ METIS_TAC [lisp_inv_swap3])
  THEN1 (IMP_RES_TAC lisp_inv_swap4 \\ IMP_RES_TAC mc_safe_car_lemma
         \\ METIS_TAC [lisp_inv_swap4])
  THEN1 (IMP_RES_TAC lisp_inv_swap5 \\ IMP_RES_TAC mc_safe_car_lemma
         \\ METIS_TAC [lisp_inv_swap5]))
  |> SIMP_RULE std_ss [LET_DEF];

val mc_safe_cdr_lemma = prove(
  ``^LISP ==>
    ?w0i.
      mc_safe_cdr_pre (tw0,bp,w2w w0,df,f) /\
      (mc_safe_cdr (tw0,bp,w2w w0,df,f) = (tw0,bp,w2w w0i,df,f)) /\
      let (x0,w0) = (SAFE_CDR x0,w0i) in ^LISP``,
  FULL_SIMP_TAC std_ss [SAFE_CAR_def,SAFE_CDR_def]
  \\ FULL_SIMP_TAC std_ss [mc_safe_car_def,mc_safe_cdr_def,LET_DEF]
  \\ FULL_SIMP_TAC std_ss [mc_safe_car_blast] \\ STRIP_TAC
  \\ IMP_RES_TAC lisp_inv_type \\ ASM_SIMP_TAC std_ss []
  \\ Cases_on `isDot x0` \\ ASM_SIMP_TAC std_ss [] THEN1
   (IMP_RES_TAC lisp_inv_car \\ IMP_RES_TAC lisp_inv_cdr
    \\ FULL_SIMP_TAC std_ss [AC WORD_ADD_ASSOC WORD_ADD_COMM,mc_safe_car_blast])
  \\ `(CAR x0 = Sym "NIL") /\ (CDR x0 = Sym "NIL")` by
    (Cases_on `x0` \\ FULL_SIMP_TAC std_ss [isDot_def,CAR_def,CDR_def])
  \\ ASM_SIMP_TAC std_ss [] \\ Q.EXISTS_TAC `3w`
  \\ `tw0 = 3w` by FULL_SIMP_TAC std_ss [lisp_inv_def]
  \\ IMP_RES_TAC lisp_inv_nil
  \\ POP_ASSUM MP_TAC \\ FULL_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC wstd_ss [w2w_def,w2n_n2w])
  |> SIMP_RULE std_ss [LET_DEF];

val mc_safe_cdr_thm = prove(
  ``^LISP ==>
    (?w0i.
      mc_safe_cdr_pre (tw0,bp,w2w w0,df,f) /\
      (mc_safe_cdr (tw0,bp,w2w w0,df,f) = (tw0,bp,w2w w0i,df,f)) /\
      let (x0,w0) = (SAFE_CDR x0,w0i) in ^LISP) /\
    (?w1i.
      mc_safe_cdr_pre (tw0,bp,w2w w1,df,f) /\
      (mc_safe_cdr (tw0,bp,w2w w1,df,f) = (tw0,bp,w2w w1i,df,f)) /\
      let (x1,w1) = (SAFE_CDR x1,w1i) in ^LISP) /\
    (?w2i.
      mc_safe_cdr_pre (tw0,bp,w2w w2,df,f) /\
      (mc_safe_cdr (tw0,bp,w2w w2,df,f) = (tw0,bp,w2w w2i,df,f)) /\
      let (x2,w2) = (SAFE_CDR x2,w2i) in ^LISP) /\
    (?w3i.
      mc_safe_cdr_pre (tw0,bp,w2w w3,df,f) /\
      (mc_safe_cdr (tw0,bp,w2w w3,df,f) = (tw0,bp,w2w w3i,df,f)) /\
      let (x3,w3) = (SAFE_CDR x3,w3i) in ^LISP) /\
    (?w4i.
      mc_safe_cdr_pre (tw0,bp,w2w w4,df,f) /\
      (mc_safe_cdr (tw0,bp,w2w w4,df,f) = (tw0,bp,w2w w4i,df,f)) /\
      let (x4,w4) = (SAFE_CDR x4,w4i) in ^LISP) /\
    (?w5i.
      mc_safe_cdr_pre (tw0,bp,w2w w5,df,f) /\
      (mc_safe_cdr (tw0,bp,w2w w5,df,f) = (tw0,bp,w2w w5i,df,f)) /\
      let (x5,w5) = (SAFE_CDR x5,w5i) in ^LISP)``,
  REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [LET_DEF]
  THEN1 (IMP_RES_TAC mc_safe_cdr_lemma \\ METIS_TAC [])
  THEN1 (IMP_RES_TAC lisp_inv_swap1 \\ IMP_RES_TAC mc_safe_cdr_lemma
         \\ METIS_TAC [lisp_inv_swap1])
  THEN1 (IMP_RES_TAC lisp_inv_swap2 \\ IMP_RES_TAC mc_safe_cdr_lemma
         \\ METIS_TAC [lisp_inv_swap2])
  THEN1 (IMP_RES_TAC lisp_inv_swap3 \\ IMP_RES_TAC mc_safe_cdr_lemma
         \\ METIS_TAC [lisp_inv_swap3])
  THEN1 (IMP_RES_TAC lisp_inv_swap4 \\ IMP_RES_TAC mc_safe_cdr_lemma
         \\ METIS_TAC [lisp_inv_swap4])
  THEN1 (IMP_RES_TAC lisp_inv_swap5 \\ IMP_RES_TAC mc_safe_cdr_lemma
         \\ METIS_TAC [lisp_inv_swap5]))
  |> SIMP_RULE std_ss [LET_DEF];

val _ = save_thm("mc_safe_car_spec",mc_safe_car_spec);
val _ = save_thm("mc_safe_cdr_spec",mc_safe_cdr_spec);
val _ = save_thm("mc_safe_car_thm",mc_safe_car_thm);
val _ = save_thm("mc_safe_cdr_thm",mc_safe_cdr_thm);


(* code heap space test *)

val mc_code_heap_space_thm = prove(
  ``^LISP ==>
    (let tw2 = 3w in ^LISP) /\
    ((w2w (f (sp - 0x54w)) << 32 !! w2w (f (sp - 0x58w))) = EL 3 ds) /\
    {sp - 0x54w; sp - 0x58w} SUBSET df /\ (sp - 0x54w && 0x3w = 0x0w) /\
    (sp - 0x58w && 0x3w = 0x0w)``,
  STRIP_TAC \\ SIMP_TAC std_ss [LET_DEF]
  \\ IMP_RES_TAC lisp_inv_cs_read \\ IMP_RES_TAC lisp_inv_ds_read
  \\ ASM_SIMP_TAC std_ss [INSERT_SUBSET,EMPTY_SUBSET]
  \\ `sp && 3w = 0w` by FULL_SIMP_TAC std_ss [lisp_inv_def]
  \\ ASM_SIMP_TAC std_ss [align_blast,n2w_and_3]
  \\ MATCH_MP_TAC lisp_inv_ignore_tw2 \\ METIS_TAC [])
  |> SIMP_RULE std_ss [LET_DEF];

val _ = save_thm("mc_code_heap_space_thm",mc_code_heap_space_thm);


(* lemmas for code heap write *)

val expand_list = prove(
  ``!cs. (LENGTH cs = 10) ==>
         ?c0 c1 c2 c3 c4 c5 c6 c7 c8 c9. cs = [c0;c1;c2;c3;c4;c5;c6;c7;c8;c9]``,
  Cases \\ SIMP_TAC std_ss [LENGTH,ADD1,CONS_11]
  \\ Cases_on `t` \\ SIMP_TAC std_ss [LENGTH,ADD1,CONS_11]
  \\ Cases_on `t'` \\ SIMP_TAC std_ss [LENGTH,ADD1,CONS_11]
  \\ Cases_on `t` \\ SIMP_TAC std_ss [LENGTH,ADD1,CONS_11]
  \\ Cases_on `t'` \\ SIMP_TAC std_ss [LENGTH,ADD1,CONS_11]
  \\ Cases_on `t` \\ SIMP_TAC std_ss [LENGTH,ADD1,CONS_11]
  \\ Cases_on `t'` \\ SIMP_TAC std_ss [LENGTH,ADD1,CONS_11]
  \\ Cases_on `t` \\ SIMP_TAC std_ss [LENGTH,ADD1,CONS_11]
  \\ Cases_on `t'` \\ SIMP_TAC std_ss [LENGTH,ADD1,CONS_11]
  \\ Cases_on `t` \\ SIMP_TAC std_ss [LENGTH,ADD1,CONS_11]
  \\ Cases_on `t'` \\ SIMP_TAC std_ss [LENGTH,ADD1,CONS_11,NOT_CONS_NIL]
  \\ DECIDE_TAC);

val expand_list2 = prove(
  ``!cs. (LENGTH cs = 10) ==> ?c0 c1 c2 c3 cs2. cs = (c0::c1::c2::c3::cs2)``,
  REPEAT STRIP_TAC \\ IMP_RES_TAC expand_list \\ FULL_SIMP_TAC std_ss [CONS_11]);

val WRITE_CODE_APPEND = prove(
  ``!xs ys code.
       WRITE_CODE code (xs ++ ys) = WRITE_CODE (WRITE_CODE code xs) ys``,
  Induct \\ Cases_on `code` \\ Cases_on `p` \\ ASM_SIMP_TAC std_ss [WRITE_CODE_def,APPEND]);

val SND_WRITE_CODE = prove(
  ``!code x. code_ptr (WRITE_CODE code [x]) = code_ptr code + bc_length x``,
  Cases \\ Cases \\ Cases_on `p` \\ SIMP_TAC std_ss [WRITE_CODE_def,code_ptr_def]);

val bc_symbols_ok_APPEND = prove(
  ``!xs ys. bc_symbols_ok sym (xs ++ ys) =
            bc_symbols_ok sym xs /\ bc_symbols_ok sym ys``,
  Induct \\ SIMP_TAC std_ss [APPEND,bc_symbols_ok_def] \\ Cases_on `h`
  \\ ASM_SIMP_TAC std_ss [APPEND,bc_symbols_ok_def,CONJ_ASSOC]);

val code_length_def = Define `
  (code_length [] = 0) /\
  (code_length (x::xs) = bc_length x + code_length xs)`;

val bs2bytes_APPEND = prove(
  ``!xs ys k sym.
      bs2bytes (k,sym) (xs ++ ys) =
      bs2bytes (k,sym) xs ++ bs2bytes (k + code_length xs,sym) ys``,
  Induct \\ ASM_SIMP_TAC std_ss [APPEND,bs2bytes_def,code_length_def]
  \\ FULL_SIMP_TAC std_ss [APPEND_ASSOC,ADD_ASSOC]);

val bc_length_lemma = prove(
  ``0x100w <+ w /\ (LENGTH hs = w2n w) /\ n + w2n (w:word64) < 1073741824 ==>
    bc_length x <= LENGTH hs``,
  SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC \\ `w2n w < 1073741824` by DECIDE_TAC
  \\ Cases_on `w` \\ FULL_SIMP_TAC wstd_ss [w2n_n2w,word_lo_n2w]
  \\ Cases_on `x` \\ REPEAT (Cases_on `l`)
  \\ FULL_SIMP_TAC std_ss [bc_length_def,LENGTH,bc_ref_def,
        IMMEDIATE32_def,APPEND] \\ REPEAT DECIDE_TAC);

val SUC_EQ_LENGTH = prove(
  ``(SUC n <= LENGTH xs) = ?y ys. (xs = (y::ys)) /\ (n <= LENGTH ys)``,
  Cases_on `xs` \\ FULL_SIMP_TAC std_ss [LENGTH,ADD1,NOT_CONS_NIL,CONS_11]);

val DROP_CONS = prove(
  ``DROP n (x::xs) = if n = 0 then x::xs else DROP (n-1) xs``,
  SRW_TAC [] []);

val LENGTH_bs2bytes = prove(
  ``!bs code.
       (WRITE_CODE (BC_CODE ((\x. NONE),0)) bs = code) ==>
       (LENGTH (bs2bytes (0,sym) bs) = code_ptr code)``,
  HO_MATCH_MP_TAC rich_listTheory.SNOC_INDUCT
  \\ SIMP_TAC std_ss [bs2bytes_def,WRITE_CODE_def,LENGTH,SNOC_APPEND]
  \\ SIMP_TAC std_ss [WRITE_CODE_APPEND,SND_WRITE_CODE]
  \\ SIMP_TAC std_ss [bs2bytes_APPEND,LENGTH_APPEND,bs2bytes_def,LENGTH,code_ptr_def]
  \\ REPEAT STRIP_TAC \\ Cases_on `x` \\ REPEAT (Cases_on `l`) \\ EVAL_TAC);

val write_lemma = prove(
  ``!w ys. (w2n w = LENGTH ys + k) /\ n + (LENGTH ys + k) < 1073741824 ==>
           (w2n (w - n2w k) = LENGTH ys)``,
  Cases \\ FULL_SIMP_TAC wstd_ss [w2n_n2w]
  \\ ASM_SIMP_TAC wstd_ss [GSYM word_add_n2w,WORD_ADD_SUB,w2n_n2w]
  \\ REPEAT STRIP_TAC \\ `LENGTH ys < dimword (:'a)` by DECIDE_TAC
  \\ ASM_SIMP_TAC std_ss []);

val mc_code_heap_blast = blastLib.BBLAST_PROVE
  ``(w2w ((w2w (w >>> 32)):word32) << 32 !! w2w ((w2w (w:word64)):word32) = w) /\
    ((63 >< 32) w = (w2w (w >>> 32)):word32) /\ ((31 >< 0) w = (w2w w):word32)``;

val WRITE_CODE_IMP_code_length = prove(
  ``!bs code k m.
      (WRITE_CODE (BC_CODE (m,k)) bs = code) ==>
      (code_length bs + k = code_ptr code)``,
  SIMP_TAC std_ss [] \\ ONCE_REWRITE_TAC [EQ_SYM_EQ]
  \\ Induct \\ ASM_SIMP_TAC std_ss [WRITE_CODE_def,code_length_def,code_ptr_def]
  \\ REPEAT STRIP_TAC \\ DECIDE_TAC);


(* generate approximate code for a few of the bytecode instructions *)

fun approx_code inst = let
  val xs = EVAL (mk_comb(``bc_ref (i,sym)``,inst))
           |> concl |> dest_eq |> snd |> listSyntax.dest_list |> fst
           |> map (fn tm => if can (numSyntax.int_of_term o cdr) tm then tm else ``0w:word64``)
           |> map (numSyntax.int_of_term o cdr)
           |> map (fn n => n mod 256)
           |> map (fn x => if x < 128 then x else x - 256)
  val enc = x64_encodeLib.x64_encode
  fun my_int_to_string n = if n < 0 then "-" ^ int_to_string (0-n) else int_to_string n
  fun encs (i,[]) = []
    | encs (i,(x::xs)) = ("mov BYTE [r2+"^ int_to_string i ^"]," ^ my_int_to_string x)
                         :: encs (i+1,xs)
  val l = length xs
  val code = (["mov r2,[r7-96]"] @ encs (0,xs) @
              ["mov r2,[r7-88]"] @
              ["sub r2," ^ int_to_string l] @
              ["add QWORD [r7-96]," ^ int_to_string l] @
              ["mov [r7-88],r2"])
  val _ = print "\n\n"
  val _ = map (fn x => print ("       " ^ x ^ "\n")) code
  val _ = print "\n\n"
  in () end


(* code heap -- write iCONST_NUM, same as iCONST_SYM *)

val (mc_write_num_spec,mc_write_num_def) = basic_decompile_strings x64_tools "mc_write_num"
  (SOME (``(r1:word64,r2:word64,r7:word64,r8:word64,df:word64 set,f:word64->word32,dg:word64 set,g:word64->word8)``,
         ``(r1:word64,r2:word64,r7:word64,r8:word64,df:word64 set,f:word64->word32,dg:word64 set,g:word64->word8)``))
  (assemble "x64" `
       mov r2,[r7-96]
       mov r1,r8
       mov BYTE [r2+0],72
       mov BYTE [r2+1],-123
       mov BYTE [r2+2],-37
       mov BYTE [r2+3],62
       mov BYTE [r2+4],72
       mov BYTE [r2+5],117
       mov BYTE [r2+6],9
       mov BYTE [r2+7],-117
       mov BYTE [r2+8],-47
       mov BYTE [r2+9],72
       mov BYTE [r2+10],-1
       mov BYTE [r2+11],-89
       mov BYTE [r2+12],56
       mov BYTE [r2+13],-1
       mov BYTE [r2+14],-1
       mov BYTE [r2+15],-1
       mov BYTE [r2+16],72
       mov BYTE [r2+17],-1
       mov BYTE [r2+18],-53
       mov BYTE [r2+19],68
       mov BYTE [r2+20],-119
       mov BYTE [r2+21],4
       mov BYTE [r2+22],-97
       mov BYTE [r2+23],65
       mov BYTE [r2+24],-72
       mov BYTE [r2+25],r1b
       shr r1,8
       mov BYTE [r2+26],r1b
       shr r1,8
       mov BYTE [r2+27],r1b
       shr r1,8
       mov BYTE [r2+28],r1b
       mov r2,[r7-88]
       sub r2,29
       add QWORD [r7-96],29
       mov [r7-88],r2
       mov r1d,1
   `)

val const_num_blast = blastLib.BBLAST_PROVE
  ``(w2w (w2w (w:word30) << 2 + 0x1w:word32) = w2w w << 2 + 0x1w:word64) /\
    (w2w (w2w (v:29 word) << 3 + 0x3w:word32) = w2w v << 3 + 0x3w:word64) /\
    (w2w ((ww:word32) >>> 8) = (w2w ((w2w ww >>> 8):word64)):word8) /\
    (w2w ((ww:word32) >>> 16) = (w2w ((w2w ww >>> 16):word64)):word8) /\
    (w2w ((ww:word32) >>> 24) = (w2w ((w2w ww >>> 24):word64)):word8)``

val inst = ``iCONST_NUM (getVal x0)``
val mc_write_num_thm = prove(
  ``^LISP /\ 0x100w <+ EL 3 ds ==> isVal x0 ==>
    ?fi di tw2i.
        mc_write_num_pre (tw1,tw2,sp,w2w w0,df,f,dd,d) /\
        (mc_write_num (tw1,tw2,sp,w2w w0,df,f,dd,d) = (tw1,tw2i,sp,w2w w0,df,fi,dd,di)) /\
         let (code,f,d,tw2,ds) = (WRITE_CODE code [^inst],fi,di,tw2i,UPDATE_NTH 2 (EL 2 ds + n2w (bc_length ^inst)) (UPDATE_NTH 3 (EL 3 ds - n2w (bc_length ^inst)) ds)) in ^LISP``,
  REPEAT STRIP_TAC \\ SIMP_TAC std_ss [mc_write_num_def,LET_DEF]
  \\ IMP_RES_TAC lisp_inv_ds_read
  \\ ASM_SIMP_TAC std_ss [INSERT_SUBSET,EMPTY_SUBSET]
  \\ `sp && 3w = 0w` by FULL_SIMP_TAC std_ss [lisp_inv_def]
  \\ ASM_SIMP_TAC std_ss [align_blast,n2w_and_3]
  \\ SIMP_TAC std_ss [CONJ_ASSOC]
  \\ FULL_SIMP_TAC std_ss [lisp_inv_def]
  \\ SIMP_TAC std_ss [PULL_EXISTS_OVER_CONJ]
  \\ Q.LIST_EXISTS_TAC [`s0`,`s1`,`s2`,`s3`,`s4`,`s5`,`m`,`i`,`ss`,`ss1`,`sym`,`b`]
  \\ ASM_SIMP_TAC std_ss [EL_UPDATE_NTH,LENGTH_UPDATE_NTH]
  \\ ASM_SIMP_TAC std_ss [bc_length_def,LENGTH,bc_ref_def,GSYM CONJ_ASSOC]
  \\ STRIP_TAC THEN1
   (Q.ABBREV_TAC `cs2 = [a1; a2; n2w e; bp2; sa1; sa2; sa3; ex] ++ cs`
    \\ `LENGTH cs2 = 18` by
       (Q.UNABBREV_TAC `cs2` \\ FULL_SIMP_TAC std_ss [LENGTH,LENGTH_APPEND])
    \\ IMP_RES_TAC expand_list2
    \\ REPEAT (Q.PAT_X_ASSUM `EL yyy ds = xxxx` (K ALL_TAC))
    \\ FULL_SIMP_TAC std_ss [EL_CONS,UPDATE_NTH_CONS]
    \\ FULL_SIMP_TAC std_ss [ref_static_def,LET_DEF,APPEND,ref_full_stack_def,
         word_arith_lemma1,word64_3232_def,word_arith_lemma1,STAR_ASSOC,word_mul_n2w,
         word_arith_lemma3,word_arith_lemma4,WORD_ADD_0,ref_stack_def,SEP_EXISTS_THM,
         ref_static_APPEND,ref_static_def,LENGTH,mc_code_heap_blast,IMMEDIATE32_def]
    \\ FULL_SIMP_TAC std_ss [GSYM word_add_n2w]
    \\ FULL_SIMP_TAC std_ss [AC WORD_ADD_COMM WORD_ADD_ASSOC]
    \\ SEP_WRITE_TAC)
  \\ ASM_SIMP_TAC std_ss [IMMEDIATE32_def,APPEND,LENGTH,LSR_ADD]
  \\ FULL_SIMP_TAC std_ss [code_heap_def,PULL_EXISTS_OVER_CONJ]
  \\ EXISTS_TAC ``bs ++ [^inst]``
  \\ EXISTS_TAC ``DROP (bc_length ^inst) (hs:word8 list)``
  \\ FULL_SIMP_TAC std_ss [bc_length_def,LENGTH,bc_ref_def,IMMEDIATE32_def,APPEND]
  \\ FULL_SIMP_TAC std_ss [WRITE_CODE_APPEND,bc_symbols_ok_APPEND,bc_ref_def,
       bc_symbols_ok_def,SND_WRITE_CODE,bc_length_def,word_arith_lemma1]
  \\ FULL_SIMP_TAC std_ss [LENGTH,bs2bytes_APPEND]
  \\ FULL_SIMP_TAC std_ss [bs2bytes_def,APPEND_NIL,bc_ref_def,IMMEDIATE32_def,APPEND]
  \\ Q.PAT_X_ASSUM `MAP ref_heap_addr xssss = yssss` (ASSUME_TAC o GSYM)
  \\ FULL_SIMP_TAC std_ss [EVERY_DEF,MAP,CONS_11]
  \\ Q.PAT_X_ASSUM `isVal x0` ASSUME_TAC \\ FULL_SIMP_TAC std_ss [isVal_thm]
  \\ FULL_SIMP_TAC std_ss [ref_heap_addr_alt,lisp_x_def,getVal_def]
  \\ FULL_SIMP_TAC std_ss [const_num_blast]
  \\ `w2w ((n2w a):word30) = (n2w a):word64` by
       (ASM_SIMP_TAC wstd_ss [w2w_def,w2n_n2w])
  \\ FULL_SIMP_TAC std_ss []
  \\ IMP_RES_TAC bc_length_lemma
  \\ POP_ASSUM (STRIP_ASSUME_TAC o RW [bc_length_def,bc_ref_def,
        LENGTH,SUC_EQ_LENGTH,APPEND,IMMEDIATE32_def] o SPEC inst)
  \\ FULL_SIMP_TAC std_ss [DROP_CONS,DROP_0]
  \\ Q.PAT_X_ASSUM `xxx = w2n (EL 3 ds)` (ASSUME_TAC o GSYM)
  \\ FULL_SIMP_TAC std_ss [LENGTH,ADD1,GSYM ADD_ASSOC]
  \\ IMP_RES_TAC write_lemma \\ ASM_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC std_ss [AC ADD_ASSOC ADD_COMM]
  \\ FULL_SIMP_TAC std_ss [one_byte_list_APPEND,one_byte_list_def]
  \\ FULL_SIMP_TAC std_ss [SEP_CLAUSES,STAR_ASSOC,LENGTH_APPEND,LENGTH,GSYM ADD_ASSOC,
       word_arith_lemma1]
  \\ IMP_RES_TAC LENGTH_bs2bytes \\ FULL_SIMP_TAC std_ss []
  \\ Q.PAT_X_ASSUM `xxx (fun2set (d,dd))` ASSUME_TAC
  \\ SEP_R_TAC \\ ASM_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC std_ss [WORD_MUL_LSL,word_mul_n2w,word_add_n2w]
  \\ FULL_SIMP_TAC std_ss [AC ADD_ASSOC ADD_COMM]
  \\ `(1 + 4 * a) < 2**32` by (FULL_SIMP_TAC wstd_ss [] \\ DECIDE_TAC)
  \\ FULL_SIMP_TAC std_ss []
  \\ `w2w ((n2w (1 + 4 * a)):word32) = (n2w (1 + 4 * a)):word64` by
       (ASM_SIMP_TAC wstd_ss [w2w_def,w2n_n2w])
  \\ ASM_SIMP_TAC std_ss []
  \\ SEP_W_TAC
  \\ `(1 + 4 * a) < 2**64` by (FULL_SIMP_TAC wstd_ss [] \\ DECIDE_TAC)
  \\ FULL_SIMP_TAC wstd_ss [w2w_def,w2n_n2w])
  |> SIMP_RULE std_ss [];

val LIST_FIND_SOME_IMP = prove(
  ``!xs x a i. (LIST_FIND x a xs = SOME i) ==> MEM a xs``,
  Induct \\ SRW_TAC [] [LIST_FIND_def,MEM] \\ RES_TAC \\ ASM_SIMP_TAC std_ss []);

val inst = ``iCONST_SYM (getSym x0)``
val mc_write_sym_thm = prove(
  ``^LISP /\ 0x100w <+ EL 3 ds ==> isSym x0 ==>
    ?fi di tw2i.
        mc_write_num_pre (tw1,tw2,sp,w2w w0,df,f,dd,d) /\
        (mc_write_num (tw1,tw2,sp,w2w w0,df,f,dd,d) = (tw1,tw2i,sp,w2w w0,df,fi,dd,di)) /\
         let (code,f,d,tw2,ds) = (WRITE_CODE code [^inst],fi,di,tw2i,UPDATE_NTH 2 (EL 2 ds + n2w (bc_length ^inst)) (UPDATE_NTH 3 (EL 3 ds - n2w (bc_length ^inst)) ds)) in ^LISP``,
  REPEAT STRIP_TAC \\ SIMP_TAC std_ss [mc_write_num_def,LET_DEF]
  \\ IMP_RES_TAC lisp_inv_ds_read
  \\ ASM_SIMP_TAC std_ss [INSERT_SUBSET,EMPTY_SUBSET]
  \\ `sp && 3w = 0w` by FULL_SIMP_TAC std_ss [lisp_inv_def]
  \\ ASM_SIMP_TAC std_ss [align_blast,n2w_and_3]
  \\ SIMP_TAC std_ss [CONJ_ASSOC]
  \\ FULL_SIMP_TAC std_ss [lisp_inv_def]
  \\ SIMP_TAC std_ss [PULL_EXISTS_OVER_CONJ]
  \\ Q.LIST_EXISTS_TAC [`s0`,`s1`,`s2`,`s3`,`s4`,`s5`,`m`,`i`,`ss`,`ss1`,`sym`,`b`]
  \\ ASM_SIMP_TAC std_ss [EL_UPDATE_NTH,LENGTH_UPDATE_NTH]
  \\ ASM_SIMP_TAC std_ss [bc_length_def,LENGTH,bc_ref_def,GSYM CONJ_ASSOC]
  \\ STRIP_TAC THEN1
   (Q.ABBREV_TAC `cs2 = [a1; a2; n2w e; bp2; sa1; sa2; sa3; ex] ++ cs`
    \\ `LENGTH cs2 = 18` by
       (Q.UNABBREV_TAC `cs2` \\ FULL_SIMP_TAC std_ss [LENGTH,LENGTH_APPEND])
    \\ IMP_RES_TAC expand_list2
    \\ REPEAT (Q.PAT_X_ASSUM `EL yyy ds = xxxx` (K ALL_TAC))
    \\ FULL_SIMP_TAC std_ss [EL_CONS,UPDATE_NTH_CONS]
    \\ FULL_SIMP_TAC std_ss [ref_static_def,LET_DEF,APPEND,ref_full_stack_def,
         word_arith_lemma1,word64_3232_def,word_arith_lemma1,STAR_ASSOC,word_mul_n2w,
         word_arith_lemma3,word_arith_lemma4,WORD_ADD_0,ref_stack_def,SEP_EXISTS_THM,
         ref_static_APPEND,ref_static_def,LENGTH,mc_code_heap_blast,IMMEDIATE32_def]
    \\ FULL_SIMP_TAC std_ss [GSYM word_add_n2w]
    \\ FULL_SIMP_TAC std_ss [AC WORD_ADD_COMM WORD_ADD_ASSOC]
    \\ SEP_WRITE_TAC)
  \\ ASM_SIMP_TAC std_ss [IMMEDIATE32_def,APPEND,LENGTH,LSR_ADD]
  \\ FULL_SIMP_TAC std_ss [code_heap_def,PULL_EXISTS_OVER_CONJ]
  \\ EXISTS_TAC ``bs ++ [^inst]``
  \\ EXISTS_TAC ``DROP (bc_length ^inst) (hs:word8 list)``
  \\ FULL_SIMP_TAC std_ss [bc_length_def,LENGTH,bc_ref_def,IMMEDIATE32_def,APPEND]
  \\ FULL_SIMP_TAC std_ss [WRITE_CODE_APPEND,bc_symbols_ok_APPEND,bc_ref_def,
       bc_symbols_ok_def,SND_WRITE_CODE,bc_length_def,word_arith_lemma1]
  \\ FULL_SIMP_TAC std_ss [LENGTH,bs2bytes_APPEND]
  \\ FULL_SIMP_TAC std_ss [bs2bytes_def,APPEND_NIL,bc_ref_def,IMMEDIATE32_def,APPEND]
  \\ Q.PAT_X_ASSUM `MAP ref_heap_addr xssss = yssss` (ASSUME_TAC o GSYM)
  \\ FULL_SIMP_TAC std_ss [EVERY_DEF,MAP,CONS_11]
  \\ Q.PAT_X_ASSUM `isSym x0` ASSUME_TAC \\ FULL_SIMP_TAC std_ss [isSym_thm]
  \\ FULL_SIMP_TAC std_ss [ref_heap_addr_alt,lisp_x_def,getSym_def]
  \\ IMP_RES_TAC LIST_FIND_SOME_IMP
  \\ FULL_SIMP_TAC std_ss [const_num_blast]
  \\ `w2w ((n2w k):29 word) = (n2w k):word64` by
       (ASM_SIMP_TAC wstd_ss [w2w_def,w2n_n2w])
  \\ FULL_SIMP_TAC std_ss []
  \\ IMP_RES_TAC bc_length_lemma
  \\ POP_ASSUM (STRIP_ASSUME_TAC o RW [bc_length_def,bc_ref_def,
        LENGTH,SUC_EQ_LENGTH,APPEND,IMMEDIATE32_def] o SPEC inst)
  \\ FULL_SIMP_TAC std_ss [DROP_CONS,DROP_0]
  \\ Q.PAT_X_ASSUM `xxx = w2n (EL 3 ds)` (ASSUME_TAC o GSYM)
  \\ FULL_SIMP_TAC std_ss [LENGTH,ADD1,GSYM ADD_ASSOC]
  \\ IMP_RES_TAC write_lemma \\ ASM_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC std_ss [AC ADD_ASSOC ADD_COMM]
  \\ FULL_SIMP_TAC std_ss [one_byte_list_APPEND,one_byte_list_def]
  \\ FULL_SIMP_TAC std_ss [SEP_CLAUSES,STAR_ASSOC,LENGTH_APPEND,LENGTH,GSYM ADD_ASSOC,
       word_arith_lemma1]
  \\ IMP_RES_TAC LENGTH_bs2bytes \\ FULL_SIMP_TAC std_ss []
  \\ Q.PAT_X_ASSUM `xxx (fun2set (d,dd))` ASSUME_TAC
  \\ SEP_R_TAC \\ ASM_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC std_ss [WORD_MUL_LSL,word_mul_n2w,word_add_n2w]
  \\ FULL_SIMP_TAC std_ss [AC ADD_ASSOC ADD_COMM]
  \\ `(3 + 8 * k) < 2**32` by (FULL_SIMP_TAC wstd_ss [] \\ DECIDE_TAC)
  \\ FULL_SIMP_TAC std_ss []
  \\ `w2w ((n2w (3 + 8 * k)):word32) = (n2w (3 + 8 * k)):word64` by
       (ASM_SIMP_TAC wstd_ss [w2w_def,w2n_n2w])
  \\ ASM_SIMP_TAC std_ss [] \\ SEP_W_TAC
  \\ `(3 + 8 * k) < 2**64` by (FULL_SIMP_TAC wstd_ss [] \\ DECIDE_TAC)
  \\ FULL_SIMP_TAC wstd_ss [w2w_def,w2n_n2w])
  |> SIMP_RULE std_ss [];


(* code heap -- write iJUMP, iJNIL, iCALL *)

val (mc_write_jump_spec,mc_write_jump_def) = basic_decompile_strings x64_tools "mc_write_jump"
  (SOME (``(r1:word64,r2:word64,r7:word64,r8:word64,df:word64 set,f:word64->word32,dg:word64 set,g:word64->word8)``,
         ``(r1:word64,r2:word64,r7:word64,r8:word64,df:word64 set,f:word64->word32,dg:word64 set,g:word64->word8)``))
  (assemble "x64" `
       mov r2,[r7-96]
       mov r1,r8
       shr r1,2
       add r1,[r7-160]
       sub r1,r2
       sub r1,6
       mov BYTE [r2],72
       mov BYTE [r2+1],-23
       mov BYTE [r2+2],r1b
       shr r1,8
       mov BYTE [r2+3],r1b
       shr r1,8
       mov BYTE [r2+4],r1b
       shr r1,8
       mov BYTE [r2+5],r1b
       mov r2,[r7-88]
       sub r2,6
       add QWORD [r7-96],6
       mov [r7-88],r2
       mov r1d,1
   `)

val (mc_write_call_spec,mc_write_call_def) = basic_decompile_strings x64_tools "mc_write_call"
  (SOME (``(r1:word64,r2:word64,r7:word64,r8:word64,df:word64 set,f:word64->word32,dg:word64 set,g:word64->word8)``,
         ``(r1:word64,r2:word64,r7:word64,r8:word64,df:word64 set,f:word64->word32,dg:word64 set,g:word64->word8)``))
  (assemble "x64" `
       mov r2,[r7-96]
       mov r1,r8
       shr r1,2
       add r1,[r7-160]
       sub r1,r2
       sub r1,6
       mov BYTE [r2],72
       mov BYTE [r2+1],-24
       mov BYTE [r2+2],r1b
       shr r1,8
       mov BYTE [r2+3],r1b
       shr r1,8
       mov BYTE [r2+4],r1b
       shr r1,8
       mov BYTE [r2+5],r1b
       mov r2,[r7-88]
       sub r2,6
       add QWORD [r7-96],6
       mov [r7-88],r2
       mov r1d,1
   `)

val (mc_write_jnil_spec,mc_write_jnil_def) = basic_decompile_strings x64_tools "mc_write_jnil"
  (SOME (``(r1:word64,r2:word64,r7:word64,r8:word64,df:word64 set,f:word64->word32,dg:word64 set,g:word64->word8)``,
         ``(r1:word64,r2:word64,r7:word64,r8:word64,df:word64 set,f:word64->word32,dg:word64 set,g:word64->word8)``))
  (assemble "x64" `
       mov r2,[r7-96]
       mov r1,r8
       shr r1,2
       add r1,[r7-160]
       sub r1,r2
       sub r1,21
       mov BYTE [r2+0],77
       mov BYTE [r2+1],-117
       mov BYTE [r2+2],-56
       mov BYTE [r2+3],68
       mov BYTE [r2+4],-117
       mov BYTE [r2+5],4
       mov BYTE [r2+6],-97
       mov BYTE [r2+7],72
       mov BYTE [r2+8],-1
       mov BYTE [r2+9],-61
       mov BYTE [r2+10],73
       mov BYTE [r2+11],-125
       mov BYTE [r2+12],-7
       mov BYTE [r2+13],3
       mov BYTE [r2+14],72
       mov BYTE [r2+15],15
       mov BYTE [r2+16],-124
       mov BYTE [r2+17],r1b
       shr r1,8
       mov BYTE [r2+18],r1b
       shr r1,8
       mov BYTE [r2+19],r1b
       shr r1,8
       mov BYTE [r2+20],r1b
       mov r2,[r7-88]
       sub r2,21
       add QWORD [r7-96],21
       mov [r7-88],r2
       mov r1d,1
   `)

val mc_write_jump_blast = blastLib.BBLAST_PROVE
  ``((w2w:word64->word8) ((w2w:word32->word64) (w - v) >>> 24) = w2w ((w2w w - (w2w:word32->word64) v) >>> 24)) /\
    ((w2w:word64->word8) ((w2w:word32->word64) (w - v) >>> 16) = w2w ((w2w w - (w2w:word32->word64) v) >>> 16)) /\
    ((w2w:word64->word8) ((w2w:word32->word64) (w - v) >>> 8) = w2w ((w2w w - (w2w:word32->word64) v) >>> 8)) /\
    ((w2w:word64->word8) ((w2w:word32->word64) (w - v)) = w2w ((w2w w - (w2w:word32->word64) v))) /\
    ((w2w:word32->word8) (x - y) = (w2w:word64->word8) (w2w x - w2w y))``

fun iJUMP_TAC inst =
  REPEAT STRIP_TAC \\ SIMP_TAC std_ss [mc_write_jump_def,mc_write_call_def,mc_write_jnil_def,LET_DEF]
  \\ IMP_RES_TAC lisp_inv_ds_read
  \\ IMP_RES_TAC lisp_inv_cs_read
  \\ ASM_SIMP_TAC std_ss [INSERT_SUBSET,EMPTY_SUBSET]
  \\ `sp && 3w = 0w` by FULL_SIMP_TAC std_ss [lisp_inv_def]
  \\ ASM_SIMP_TAC std_ss [align_blast,n2w_and_3]
  \\ SIMP_TAC std_ss [CONJ_ASSOC]
  \\ FULL_SIMP_TAC std_ss [lisp_inv_def]
  \\ SIMP_TAC std_ss [PULL_EXISTS_OVER_CONJ]
  \\ Q.LIST_EXISTS_TAC [`s0`,`s1`,`s2`,`s3`,`s4`,`s5`,`m`,`i`,`ss`,`ss1`,`sym`,`b`]
  \\ ASM_SIMP_TAC std_ss [EL_UPDATE_NTH,LENGTH_UPDATE_NTH]
  \\ ASM_SIMP_TAC std_ss [bc_length_def,LENGTH,bc_ref_def,GSYM CONJ_ASSOC]
  \\ STRIP_TAC THEN1
   (Q.ABBREV_TAC `cs2 = [a1; a2; n2w e; bp2; sa1; sa2; sa3; ex] ++ cs`
    \\ `LENGTH cs2 = 18` by
       (Q.UNABBREV_TAC `cs2` \\ FULL_SIMP_TAC std_ss [LENGTH,LENGTH_APPEND])
    \\ IMP_RES_TAC expand_list2
    \\ REPEAT (Q.PAT_X_ASSUM `EL yyy ds = xxxx` (K ALL_TAC))
    \\ FULL_SIMP_TAC std_ss [EL_CONS,UPDATE_NTH_CONS]
    \\ FULL_SIMP_TAC std_ss [ref_static_def,LET_DEF,APPEND,ref_full_stack_def,
         word_arith_lemma1,word64_3232_def,word_arith_lemma1,STAR_ASSOC,word_mul_n2w,
         word_arith_lemma3,word_arith_lemma4,WORD_ADD_0,ref_stack_def,SEP_EXISTS_THM,
         ref_static_APPEND,ref_static_def,LENGTH,mc_code_heap_blast,IMMEDIATE32_def]
    \\ FULL_SIMP_TAC std_ss [GSYM word_add_n2w]
    \\ FULL_SIMP_TAC std_ss [AC WORD_ADD_COMM WORD_ADD_ASSOC]
    \\ SEP_WRITE_TAC)
  \\ ASM_SIMP_TAC std_ss [IMMEDIATE32_def,APPEND,LENGTH,LSR_ADD]
  \\ FULL_SIMP_TAC std_ss [code_heap_def,PULL_EXISTS_OVER_CONJ]
  \\ EXISTS_TAC ``bs ++ [^inst]``
  \\ EXISTS_TAC ``DROP (bc_length ^inst) (hs:word8 list)``
  \\ FULL_SIMP_TAC std_ss [bc_length_def,LENGTH,bc_ref_def,IMMEDIATE32_def,APPEND]
  \\ FULL_SIMP_TAC std_ss [WRITE_CODE_APPEND,bc_symbols_ok_APPEND,bc_ref_def,
       bc_symbols_ok_def,SND_WRITE_CODE,bc_length_def,word_arith_lemma1]
  \\ FULL_SIMP_TAC std_ss [LENGTH,bs2bytes_APPEND]
  \\ FULL_SIMP_TAC std_ss [bs2bytes_def,APPEND_NIL,bc_ref_def,IMMEDIATE32_def,APPEND]
  \\ Q.PAT_X_ASSUM `MAP ref_heap_addr xssss = yssss` (ASSUME_TAC o GSYM)
  \\ FULL_SIMP_TAC std_ss [EVERY_DEF,MAP,CONS_11]
  \\ Q.PAT_X_ASSUM `isVal x0` ASSUME_TAC \\ FULL_SIMP_TAC std_ss [isVal_thm]
  \\ FULL_SIMP_TAC std_ss [ref_heap_addr_alt,lisp_x_def,getVal_def]
  \\ FULL_SIMP_TAC std_ss [const_num_blast]
  \\ `w2w ((n2w a):word30) = (n2w a):word64` by
       (ASM_SIMP_TAC wstd_ss [w2w_def,w2n_n2w])
  \\ FULL_SIMP_TAC std_ss []
  \\ IMP_RES_TAC bc_length_lemma
  \\ POP_ASSUM (STRIP_ASSUME_TAC o RW [bc_length_def,bc_ref_def,
        LENGTH,SUC_EQ_LENGTH,APPEND,IMMEDIATE32_def] o SPEC inst)
  \\ FULL_SIMP_TAC std_ss [DROP_CONS,DROP_0]
  \\ Q.PAT_X_ASSUM `xxx = w2n (EL 3 ds)` (ASSUME_TAC o GSYM)
  \\ FULL_SIMP_TAC std_ss [LENGTH,ADD1,GSYM ADD_ASSOC]
  \\ IMP_RES_TAC write_lemma \\ ASM_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC std_ss [AC ADD_ASSOC ADD_COMM]
  \\ `(n2w a << 2 + 0x1w) >>> 2 = (n2w a):word64` by
   (ONCE_REWRITE_TAC [WORD_ADD_COMM] \\ SIMP_TAC std_ss [WORD_ADD_SUB]
    \\ `n2w a <+ n2w (2**30):word64` by
      (`a < (2**64)` by (FULL_SIMP_TAC std_ss [] \\ DECIDE_TAC)
       \\ FULL_SIMP_TAC wstd_ss [word_lo_n2w])
    \\ POP_ASSUM MP_TAC \\ Q.SPEC_TAC (`(n2w a):word64`,`w`)
    \\ blastLib.BBLAST_TAC)
  \\ ASM_SIMP_TAC std_ss [WORD_SUB_PLUS,WORD_ADD_SUB]
  \\ `code_length bs = code_ptr code` by METIS_TAC [WRITE_CODE_IMP_code_length,ADD_0]
  \\ FULL_SIMP_TAC std_ss [one_byte_list_APPEND,one_byte_list_def]
  \\ FULL_SIMP_TAC std_ss [SEP_CLAUSES,STAR_ASSOC,LENGTH_APPEND,LENGTH,GSYM ADD_ASSOC,
       word_arith_lemma1]
  \\ IMP_RES_TAC LENGTH_bs2bytes \\ FULL_SIMP_TAC std_ss []
  \\ Q.PAT_X_ASSUM `xxx (fun2set (d,dd))` ASSUME_TAC
  \\ SEP_R_TAC \\ ASM_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC std_ss [WORD_MUL_LSL,word_mul_n2w,word_add_n2w]
  \\ FULL_SIMP_TAC std_ss [AC ADD_ASSOC ADD_COMM]
  \\ FULL_SIMP_TAC std_ss [mc_write_jump_blast]
  \\ `((w2w:word32->word64) (n2w a) = n2w a) /\
      ((w2w:word32->word64) (n2w (code_ptr code)) = n2w (code_ptr code)) /\
      ((w2w:word32->word64) (n2w (code_ptr code + 6)) = n2w (code_ptr code + 6)) /\
      ((w2w:word32->word64) (n2w (code_ptr code + 21)) = n2w (code_ptr code + 21))` by
   (`a < 4294967296 /\ code_ptr code < 4294967296 /\
     code_ptr code + 6 < 4294967296 /\ code_ptr code + 21 < 4294967296` by DECIDE_TAC
    \\ FULL_SIMP_TAC wstd_ss [w2w_def,w2n_n2w,n2w_11])
  \\ ASM_SIMP_TAC std_ss []
  \\ SEP_WRITE_TAC

val inst = ``iJUMP (getVal x0)``
val mc_write_jump_thm = prove(
  ``^LISP /\ 0x100w <+ EL 3 ds ==> isVal x0 ==>
    ?fi di tw2i.
        mc_write_jump_pre (tw1,tw2,sp,w2w w0,df,f,dd,d) /\
        (mc_write_jump (tw1,tw2,sp,w2w w0,df,f,dd,d) = (tw1,tw2i,sp,w2w w0,df,fi,dd,di)) /\
         let (code,f,d,tw2,ds) = (WRITE_CODE code [^inst],fi,di,tw2i,UPDATE_NTH 2 (EL 2 ds + n2w (bc_length ^inst)) (UPDATE_NTH 3 (EL 3 ds - n2w (bc_length ^inst)) ds)) in ^LISP``,
  iJUMP_TAC inst) |> SIMP_RULE std_ss [];

val inst = ``iCALL (getVal x0)``
val mc_write_call_thm = prove(
  ``^LISP /\ 0x100w <+ EL 3 ds ==> isVal x0 ==>
    ?fi di tw2i.
        mc_write_call_pre (tw1,tw2,sp,w2w w0,df,f,dd,d) /\
        (mc_write_call (tw1,tw2,sp,w2w w0,df,f,dd,d) = (tw1,tw2i,sp,w2w w0,df,fi,dd,di)) /\
         let (code,f,d,tw2,ds) = (WRITE_CODE code [^inst],fi,di,tw2i,UPDATE_NTH 2 (EL 2 ds + n2w (bc_length ^inst)) (UPDATE_NTH 3 (EL 3 ds - n2w (bc_length ^inst)) ds)) in ^LISP``,
  iJUMP_TAC inst) |> SIMP_RULE std_ss [];

val inst = ``iJNIL (getVal x0)``
val mc_write_jnil_thm = prove(
  ``^LISP /\ 0x100w <+ EL 3 ds ==> isVal x0 ==>
    ?fi di tw2i.
        mc_write_jnil_pre (tw1,tw2,sp,w2w w0,df,f,dd,d) /\
        (mc_write_jnil (tw1,tw2,sp,w2w w0,df,f,dd,d) = (tw1,tw2i,sp,w2w w0,df,fi,dd,di)) /\
         let (code,f,d,tw2,ds) = (WRITE_CODE code [^inst],fi,di,tw2i,UPDATE_NTH 2 (EL 2 ds + n2w (bc_length ^inst)) (UPDATE_NTH 3 (EL 3 ds - n2w (bc_length ^inst)) ds)) in ^LISP``,
  iJUMP_TAC inst) |> SIMP_RULE std_ss [];


(* code heap -- write iPOPS, iSTORE, iLOAD *)

val (mc_write_pops_spec,mc_write_pops_def) = basic_decompile_strings x64_tools "mc_write_pops"
  (SOME (``(r1:word64,r2:word64,r7:word64,r8:word64,df:word64 set,f:word64->word32,dg:word64 set,g:word64->word8)``,
         ``(r1:word64,r2:word64,r7:word64,r8:word64,df:word64 set,f:word64->word32,dg:word64 set,g:word64->word8)``))
  (assemble "x64" `
       mov r2,[r7-96]
       mov r1,r8
       shr r1,2
       mov BYTE [r2+0],72
       mov BYTE [r2+1],-127
       mov BYTE [r2+2],-61
       mov BYTE [r2+3],r1b
       shr r1,8
       mov BYTE [r2+4],r1b
       shr r1,8
       mov BYTE [r2+5],r1b
       shr r1,8
       mov BYTE [r2+6],r1b
       mov r2,[r7-88]
       sub r2,7
       add QWORD [r7-96],7
       mov [r7-88],r2
       mov r1d,1
   `)

val (mc_write_store_spec,mc_write_store_def) = basic_decompile_strings x64_tools "mc_write_store"
  (SOME (``(r1:word64,r2:word64,r7:word64,r8:word64,df:word64 set,f:word64->word32,dg:word64 set,g:word64->word8)``,
         ``(r1:word64,r2:word64,r7:word64,r8:word64,df:word64 set,f:word64->word32,dg:word64 set,g:word64->word8)``))
  (assemble "x64" `
       mov r2,[r7-96]
       mov r1,r8
       sub r1,1
       mov BYTE [r2+0],68
       mov BYTE [r2+1],-119
       mov BYTE [r2+2],-124
       mov BYTE [r2+3],-97
       mov BYTE [r2+4],r1b
       shr r1,8
       mov BYTE [r2+5],r1b
       shr r1,8
       mov BYTE [r2+6],r1b
       shr r1,8
       mov BYTE [r2+7],r1b
       mov BYTE [r2+8],68
       mov BYTE [r2+9],-117
       mov BYTE [r2+10],4
       mov BYTE [r2+11],-97
       mov BYTE [r2+12],72
       mov BYTE [r2+13],-1
       mov BYTE [r2+14],-61
       mov r2,[r7-88]
       sub r2,15
       add QWORD [r7-96],15
       mov [r7-88],r2
       mov r1d,1
   `)

val (mc_write_load_spec,mc_write_load_def) = basic_decompile_strings x64_tools "mc_write_load"
  (SOME (``(r1:word64,r2:word64,r7:word64,r8:word64,df:word64 set,f:word64->word32,dg:word64 set,g:word64->word8)``,
         ``(r1:word64,r2:word64,r7:word64,r8:word64,df:word64 set,f:word64->word32,dg:word64 set,g:word64->word8)``))
  (assemble "x64" `
       mov r2,[r7-96]
       mov r1,r8
       sub r1,1
       mov BYTE [r2+0],72
       mov BYTE [r2+1],-123
       mov BYTE [r2+2],-37
       mov BYTE [r2+3],62
       mov BYTE [r2+4],72
       mov BYTE [r2+5],117
       mov BYTE [r2+6],9
       mov BYTE [r2+7],-117
       mov BYTE [r2+8],-47
       mov BYTE [r2+9],72
       mov BYTE [r2+10],-1
       mov BYTE [r2+11],-89
       mov BYTE [r2+12],56
       mov BYTE [r2+13],-1
       mov BYTE [r2+14],-1
       mov BYTE [r2+15],-1
       mov BYTE [r2+16],72
       mov BYTE [r2+17],-1
       mov BYTE [r2+18],-53
       mov BYTE [r2+19],68
       mov BYTE [r2+20],-119
       mov BYTE [r2+21],4
       mov BYTE [r2+22],-97
       mov BYTE [r2+23],68
       mov BYTE [r2+24],-117
       mov BYTE [r2+25],-124
       mov BYTE [r2+26],-97
       mov BYTE [r2+27],r1b
       shr r1,8
       mov BYTE [r2+28],r1b
       shr r1,8
       mov BYTE [r2+29],r1b
       shr r1,8
       mov BYTE [r2+30],r1b
       mov r2,[r7-88]
       sub r2,31
       add QWORD [r7-96],31
       mov [r7-88],r2
       mov r1d,1
   `)

val mc_write_pops_blast = blastLib.BBLAST_PROVE
  ``((w2w:word32->word8) x = (w2w:word64->word8) (w2w x))``

fun iPOPS_TAC inst =
  REPEAT STRIP_TAC \\ SIMP_TAC std_ss [mc_write_pops_def,mc_write_load_def,mc_write_store_def,LET_DEF]
  \\ IMP_RES_TAC lisp_inv_ds_read
  \\ IMP_RES_TAC lisp_inv_cs_read
  \\ ASM_SIMP_TAC std_ss [INSERT_SUBSET,EMPTY_SUBSET]
  \\ `sp && 3w = 0w` by FULL_SIMP_TAC std_ss [lisp_inv_def]
  \\ ASM_SIMP_TAC std_ss [align_blast,n2w_and_3]
  \\ SIMP_TAC std_ss [CONJ_ASSOC]
  \\ FULL_SIMP_TAC std_ss [lisp_inv_def]
  \\ SIMP_TAC std_ss [PULL_EXISTS_OVER_CONJ]
  \\ Q.LIST_EXISTS_TAC [`s0`,`s1`,`s2`,`s3`,`s4`,`s5`,`m`,`i`,`ss`,`ss1`,`sym`,`b`]
  \\ ASM_SIMP_TAC std_ss [EL_UPDATE_NTH,LENGTH_UPDATE_NTH]
  \\ ASM_SIMP_TAC std_ss [bc_length_def,LENGTH,bc_ref_def,GSYM CONJ_ASSOC]
  \\ STRIP_TAC THEN1
   (Q.ABBREV_TAC `cs2 = [a1; a2; n2w e; bp2; sa1; sa2; sa3; ex] ++ cs`
    \\ `LENGTH cs2 = 18` by
       (Q.UNABBREV_TAC `cs2` \\ FULL_SIMP_TAC std_ss [LENGTH,LENGTH_APPEND])
    \\ IMP_RES_TAC expand_list2
    \\ REPEAT (Q.PAT_X_ASSUM `EL yyy ds = xxxx` (K ALL_TAC))
    \\ FULL_SIMP_TAC std_ss [EL_CONS,UPDATE_NTH_CONS]
    \\ FULL_SIMP_TAC std_ss [ref_static_def,LET_DEF,APPEND,ref_full_stack_def,
         word_arith_lemma1,word64_3232_def,word_arith_lemma1,STAR_ASSOC,word_mul_n2w,
         word_arith_lemma3,word_arith_lemma4,WORD_ADD_0,ref_stack_def,SEP_EXISTS_THM,
         ref_static_APPEND,ref_static_def,LENGTH,mc_code_heap_blast,IMMEDIATE32_def]
    \\ FULL_SIMP_TAC std_ss [GSYM word_add_n2w]
    \\ FULL_SIMP_TAC std_ss [AC WORD_ADD_COMM WORD_ADD_ASSOC]
    \\ SEP_WRITE_TAC)
  \\ ASM_SIMP_TAC std_ss [IMMEDIATE32_def,APPEND,LENGTH,
       Q.SPECL [`w`,`8`,`8`] LSR_ADD, Q.SPECL [`w`,`8`,`16`] LSR_ADD]
  \\ FULL_SIMP_TAC std_ss [code_heap_def,PULL_EXISTS_OVER_CONJ]
  \\ EXISTS_TAC ``bs ++ [^inst]``
  \\ EXISTS_TAC ``DROP (bc_length ^inst) (hs:word8 list)``
  \\ FULL_SIMP_TAC std_ss [bc_length_def,LENGTH,bc_ref_def,IMMEDIATE32_def,APPEND]
  \\ FULL_SIMP_TAC std_ss [WRITE_CODE_APPEND,bc_symbols_ok_APPEND,bc_ref_def,
       bc_symbols_ok_def,SND_WRITE_CODE,bc_length_def,word_arith_lemma1]
  \\ FULL_SIMP_TAC std_ss [LENGTH,bs2bytes_APPEND]
  \\ FULL_SIMP_TAC std_ss [bs2bytes_def,APPEND_NIL,bc_ref_def,IMMEDIATE32_def,APPEND]
  \\ Q.PAT_X_ASSUM `MAP ref_heap_addr xssss = yssss` (ASSUME_TAC o GSYM)
  \\ FULL_SIMP_TAC std_ss [EVERY_DEF,MAP,CONS_11]
  \\ Q.PAT_X_ASSUM `isVal x0` ASSUME_TAC \\ FULL_SIMP_TAC std_ss [isVal_thm]
  \\ FULL_SIMP_TAC std_ss [ref_heap_addr_alt,lisp_x_def,getVal_def]
  \\ FULL_SIMP_TAC std_ss [const_num_blast]
  \\ `w2w ((n2w a):word30) = (n2w a):word64` by
       (ASM_SIMP_TAC wstd_ss [w2w_def,w2n_n2w])
  \\ FULL_SIMP_TAC std_ss []
  \\ IMP_RES_TAC bc_length_lemma
  \\ POP_ASSUM (STRIP_ASSUME_TAC o RW [bc_length_def,bc_ref_def,
        LENGTH,SUC_EQ_LENGTH,APPEND,IMMEDIATE32_def] o SPEC inst)
  \\ FULL_SIMP_TAC std_ss [DROP_CONS,DROP_0]
  \\ Q.PAT_X_ASSUM `xxx = w2n (EL 3 ds)` (ASSUME_TAC o GSYM)
  \\ FULL_SIMP_TAC std_ss [LENGTH,ADD1,GSYM ADD_ASSOC]
  \\ IMP_RES_TAC write_lemma \\ ASM_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC std_ss [AC ADD_ASSOC ADD_COMM]
  \\ `(n2w a << 2 + 0x1w) >>> 2 = (n2w a):word64` by
   (ONCE_REWRITE_TAC [WORD_ADD_COMM] \\ SIMP_TAC std_ss [WORD_ADD_SUB]
    \\ `n2w a <+ n2w (2**30):word64` by
      (`a < (2**64)` by (FULL_SIMP_TAC std_ss [] \\ DECIDE_TAC)
       \\ FULL_SIMP_TAC wstd_ss [word_lo_n2w])
    \\ POP_ASSUM MP_TAC \\ Q.SPEC_TAC (`(n2w a):word64`,`w`)
    \\ blastLib.BBLAST_TAC)
  \\ ASM_SIMP_TAC std_ss [WORD_SUB_PLUS,WORD_ADD_SUB]
  \\ SIMP_TAC std_ss [WORD_MUL_LSL,word_mul_n2w]
  \\ `(w2w:word32->word64) (n2w (4 * a)) = n2w (4 * a)` by
     (`(4 * a) < 4294967296` by DECIDE_TAC
      \\ FULL_SIMP_TAC wstd_ss [w2w_def,w2n_n2w,n2w_11])
  \\ ASM_SIMP_TAC std_ss []
  \\ `code_length bs = code_ptr code` by METIS_TAC [WRITE_CODE_IMP_code_length,ADD_0]
  \\ FULL_SIMP_TAC std_ss [one_byte_list_APPEND,one_byte_list_def]
  \\ FULL_SIMP_TAC std_ss [SEP_CLAUSES,STAR_ASSOC,LENGTH_APPEND,LENGTH,GSYM ADD_ASSOC,
       word_arith_lemma1]
  \\ IMP_RES_TAC LENGTH_bs2bytes \\ FULL_SIMP_TAC std_ss []
  \\ Q.PAT_X_ASSUM `xxx (fun2set (d,dd))` ASSUME_TAC
  \\ SEP_R_TAC \\ ASM_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC std_ss [WORD_MUL_LSL,word_mul_n2w,word_add_n2w]
  \\ FULL_SIMP_TAC std_ss [AC ADD_ASSOC ADD_COMM]
  \\ FULL_SIMP_TAC std_ss [mc_write_jump_blast]
  \\ `((w2w:word32->word64) (n2w a) = n2w a) /\
      ((w2w:word32->word64) (n2w (code_ptr code)) = n2w (code_ptr code))` by
   (`a < 4294967296 /\ code_ptr code < 4294967296` by DECIDE_TAC
    \\ FULL_SIMP_TAC wstd_ss [w2w_def,w2n_n2w,n2w_11])
  \\ ASM_SIMP_TAC std_ss [mc_write_pops_blast]
  \\ SEP_WRITE_TAC


val inst = ``iPOPS (getVal x0)``
val mc_write_pops_thm = prove(
  ``^LISP /\ 0x100w <+ EL 3 ds ==> isVal x0 ==>
    ?fi di tw2i.
        mc_write_pops_pre (tw1,tw2,sp,w2w w0,df,f,dd,d) /\
        (mc_write_pops (tw1,tw2,sp,w2w w0,df,f,dd,d) = (tw1,tw2i,sp,w2w w0,df,fi,dd,di)) /\
         let (code,f,d,tw2,ds) = (WRITE_CODE code [^inst],fi,di,tw2i,UPDATE_NTH 2 (EL 2 ds + n2w (bc_length ^inst)) (UPDATE_NTH 3 (EL 3 ds - n2w (bc_length ^inst)) ds)) in ^LISP``,
  iPOPS_TAC inst) |> SIMP_RULE std_ss [];

val inst = ``iSTORE (getVal x0)``
val mc_write_store_thm = prove(
  ``^LISP /\ 0x100w <+ EL 3 ds ==> isVal x0 /\ getVal x0 < 536870912 ==>
    ?fi di tw2i.
        mc_write_store_pre (tw1,tw2,sp,w2w w0,df,f,dd,d) /\
        (mc_write_store (tw1,tw2,sp,w2w w0,df,f,dd,d) = (tw1,tw2i,sp,w2w w0,df,fi,dd,di)) /\
         let (code,f,d,tw2,ds) = (WRITE_CODE code [^inst],fi,di,tw2i,UPDATE_NTH 2 (EL 2 ds + n2w (bc_length ^inst)) (UPDATE_NTH 3 (EL 3 ds - n2w (bc_length ^inst)) ds)) in ^LISP``,
  iPOPS_TAC inst) |> SIMP_RULE std_ss [];

val inst = ``iLOAD (getVal x0)``
val mc_write_load_thm = prove(
  ``^LISP /\ 0x100w <+ EL 3 ds ==> isVal x0 /\ getVal x0 < 536870912 ==>
    ?fi di tw2i.
        mc_write_load_pre (tw1,tw2,sp,w2w w0,df,f,dd,d) /\
        (mc_write_load (tw1,tw2,sp,w2w w0,df,f,dd,d) = (tw1,tw2i,sp,w2w w0,df,fi,dd,di)) /\
         let (code,f,d,tw2,ds) = (WRITE_CODE code [^inst],fi,di,tw2i,UPDATE_NTH 2 (EL 2 ds + n2w (bc_length ^inst)) (UPDATE_NTH 3 (EL 3 ds - n2w (bc_length ^inst)) ds)) in ^LISP``,
  iPOPS_TAC inst) |> SIMP_RULE std_ss [];


(* code heap -- write const instructions *)

local
val ready_formats = let (* derive Hoare triples for mov BYTE [r2+???],??? *)
  fun foo i = let
    val e = x64_encodeLib.x64_encode ("mov BYTE [r2+"^(int_to_string i)^"],34")
    val e = String.substring(e,0,size(e)-2)
    val (x,_) = x64_spec e
    in (e,x) end
  fun genlist i n f = if i = n then [] else
                        (print (int_to_string (256-i) ^ " "); f i :: genlist (i+1) n f)
  in genlist 0 256 foo end
in
fun instantiate_ready_format s = let
  val e = String.substring(s,0,size(s)-2)
  val t = String.substring(s,size(s)-2,2)
  fun list_find x [] = fail()
    | list_find x ((y,z)::xs) = if x = y then z else list_find x xs
  val (th,i,j) = list_find e ready_formats
  val n = numSyntax.mk_numeral(Arbnum.fromHexString t)
  val th = INST [mk_var("imm8",``:word8``)|->``(n2w ^n):word8``] th
  val tm = find_term (can (match_term ``SIGN_EXTEND x y z MOD 256``)) (concl th)
  val th = RW [EVAL tm] th
  in (th,i,j) end handle Subsript => fail()
end;

fun get_code_for_bc_inst inst = let
  val ys = EVAL (mk_comb(``bc_ref (i,sym)``,inst))
           |> concl |> dest_eq |> snd |> listSyntax.dest_list |> fst
           |> map (fn tm => if wordsSyntax.is_w2w tm then ``0w:word64`` else tm)
           |> map (numSyntax.int_of_term o cdr)
           |> map (fn n => n mod 256)
  val xs = ys |> map (fn x => if x < 128 then x else x - 256)
  val enc = x64_encodeLib.x64_encode
  fun my_int_to_string n = if n < 0 then "-" ^ int_to_string (0-n) else int_to_string n
  fun encs (i,[]) = []
    | encs (i,(x::xs)) = ("mov BYTE [r2+"^ int_to_string i ^"]," ^ my_int_to_string x)
                         :: encs (i+1,xs)
  val l = length xs
  val (c1,c2,c3) = (["mov r2,[r7-96]"], encs (0,xs),
              ["mov r2,[r7-88]"] @
              ["sub r2," ^ int_to_string l] @
              ["add QWORD [r7-96]," ^ int_to_string l] @
              ["mov [r7-88],r2"])
  in (map enc c1 @ map enc c2 @ map enc c3,ys) end

fun straight_line_decompile func_name code in_out_vars = let
  val _ = print "\nStraight-line decompile, "
  val (spec,_,sts,pc) = x64_tools
  fun my_spec s = (instantiate_ready_format s,NONE) handle HOL_ERR _ => spec s
  fun simple_spec s = let val ((th,_,_),_) = my_spec s in HIDE_STATUS_RULE true sts th end;
  val counter = ref 0
  val total = length code
  fun next x = (counter := 1+(!counter); print ("\n" ^ int_to_string (!counter) ^ " of " ^ int_to_string total ^ " "); x)
  val thms = map simple_spec code
  val th = SPEC_COMPOSE_RULE thms
  val th = SIMP_RULE (std_ss++sep_cond_ss) [] th
  val th = Q.INST [`rip`|->`p`] th
  val (_,p,_,q) = dest_spec (concl (UNDISCH_ALL (RW [progTheory.SPEC_MOVE_COND] th)))
  val ps = filter (not o can dest_sep_hide) (list_dest dest_star p)
  val qs = filter (not o can dest_sep_hide) (list_dest dest_star q)
  val ps = filter (fn tm => (car tm !~ pc) handle HOL_ERR _ => true) ps
  val qs = filter (fn tm => (car tm !~ pc) handle HOL_ERR _ => true) qs
  fun safe_car tm = car tm handle HOL_ERR _ => tm
  val sorter = sort (fn t1 => fn t2 => term_to_string (safe_car t1) <= term_to_string (safe_car t2))
  val ps = sorter ps
  val qs = sorter qs
  val px = list_mk_star(ps)(type_of (hd ps))
  val qx = list_mk_star(qs)(type_of (hd qs))
  val s = fst (match_term px qx)
  val result = subst s in_out_vars
  val ty = type_of (pairSyntax.mk_pabs(in_out_vars,in_out_vars))
  val def = new_definition(func_name,mk_eq(mk_comb(mk_var(func_name,ty),in_out_vars),result))
  val ty = type_of (pairSyntax.mk_pabs(in_out_vars,``T:bool``))
  val pre_result = th |> RW [progTheory.SPEC_MOVE_COND] |> concl |> dest_imp |> fst
                   handle HOL_ERR _ => ``T``
  val pre = new_definition(func_name ^ "_pre",mk_eq(mk_comb(mk_var(func_name ^ "_pre",ty),in_out_vars),pre_result))
  val th = RW [GSYM pre] th
  val new_q = subst (map (fn {redex= x, residue=y} => y |-> x) s) q
  val rhs = def |> SPEC_ALL |> concl |> dest_eq |> fst
  val new_q = pairSyntax.mk_anylet([(in_out_vars,rhs)],new_q)
  val (th,goal) = SPEC_WEAKEN_RULE th new_q
  val lemma = prove(goal,SIMP_TAC (std_ss++star_ss) [LET_DEF,def,SEP_IMP_REFL])
  val th = MP th lemma
  val x = CONJ (SPEC_ALL def) (SPEC_ALL pre)
  val _ = print "done!\n"
  in (th,x) end;

val one_write_list_def = Define `
  (one_write_list a [] f = f) /\
  (one_write_list (a:word64) (x::xs) f = one_write_list (a + 1w) xs ((a =+ x) f))`;

val one_address_list_def = Define `
  (one_address_list a [] = []) /\
  (one_address_list (a:word64) (x::xs) = a::one_address_list (a+1w) xs)`;

val STAR5_LEMMA = prove(
  ``STAR x1 x2 * x3 * x4 * x5 = x1 * x3 * x2 * x4 * x5``,
  SIMP_TAC (std_ss++star_ss) []);

val one_write_list_lemma = prove(
  ``!xs b a x y p q d.
      (p * one (a,x) * one_byte_list b (MAP FST xs) * q)
          (fun2set (one_write_list b (MAP FST xs) d,dd)) ==>
      (p * one (a,y) * one_byte_list b (MAP FST xs) * q)
          (fun2set (one_write_list b (MAP FST xs) ((a =+ y) d),dd))``,
  Induct \\ SIMP_TAC std_ss [MAP,one_write_list_def]
  THEN1 (REPEAT STRIP_TAC \\ SEP_WRITE_TAC)
  \\ FULL_SIMP_TAC std_ss [one_write_list_def,one_byte_list_def,STAR_ASSOC]
  \\ REPEAT STRIP_TAC \\ POP_ASSUM MP_TAC
  \\ ONCE_REWRITE_TAC [STAR5_LEMMA]
  \\ REPEAT STRIP_TAC \\ RES_TAC \\ POP_ASSUM (ASSUME_TAC o Q.SPEC `y`)
  \\ `~(b = a)` by SEP_NEQ_TAC \\ METIS_TAC [UPDATE_COMMUTES]);

val one_write_list_thm = prove(
  ``!xs p q d a.
      (p * one_byte_list a (MAP SND xs) * q) (fun2set (d,dd)) ==>
      (p * one_byte_list a (MAP FST xs) * q)
         (fun2set (one_write_list a (MAP FST xs) d,dd)) /\
      EVERY (\a. a IN dd) (one_address_list a xs)``,
  Induct \\ SIMP_TAC std_ss [MAP,one_byte_list_def,one_write_list_def,
    STAR_ASSOC,one_address_list_def,EVERY_DEF] \\ REPEAT STRIP_TAC \\ RES_TAC
  \\ SEP_R_TAC \\ IMP_RES_TAC one_write_list_lemma \\ FULL_SIMP_TAC std_ss []);


fun generate_and_verify_write_const (name,inst) = let
  val _ = print ("\n\n"^name^"\n\n")
  val (code,ys) = get_code_for_bc_inst inst
  val func_name = ("mc_write_" ^ name)
  val in_out_vars =
    ``(r2:word64,r7:word64,df:word64 set,f:word64->word32,dg:word64 set,g:word64->word8)``
  val (spec_thm,def_thm) = straight_line_decompile name code in_out_vars
  val ds = map (car o fst o dest_eq o concl) (CONJUNCTS def_thm)
  val def = el 1 ds
  val pre = el 2 ds
  val goal =
    ``^LISP /\ 0x100w <+ EL 3 ds ==>
     ?fi di tw2i.
        pre (tw2,sp,df,f,dd,d) /\
        (def (tw2,sp,df,f,dd,d) = (tw2i,sp,df,fi,dd,di)) /\
         let (code,f,d,tw2,ds) = (WRITE_CODE code [inst],fi,di,tw2i,UPDATE_NTH 2 (EL 2 ds + n2w (bc_length inst)) (UPDATE_NTH 3 (EL 3 ds - n2w (bc_length inst)) ds)) in ^LISP``
    |> subst [mk_var("inst",type_of inst)|->inst]
    |> subst [mk_var("pre",type_of pre)|->pre]
    |> subst [mk_var("def",type_of def)|->def]
  val write_list_th =
    map (fn x => pairSyntax.mk_pair(genvar(``:word8``),genvar(``:word8``))) ys
    |> (fn xs => listSyntax.mk_list(xs,type_of (hd xs)))
    |> (fn tm => Q.SPECL [`p`,`q`,`d`,`a + n2w n`] (SPEC tm one_write_list_thm))
    |> SIMP_RULE std_ss [EVERY_DEF,MAP,one_address_list_def,word_arith_lemma1,
         one_write_list_def,one_byte_list_def,STAR_ASSOC,SEP_CLAUSES]
(*
set_goal([],goal)
*)
  val tac =
 (REPEAT STRIP_TAC \\ SIMP_TAC std_ss [def_thm,LET_DEF]
  \\ IMP_RES_TAC lisp_inv_ds_read
  \\ ASM_SIMP_TAC std_ss [INSERT_SUBSET,EMPTY_SUBSET]
  \\ `sp && 3w = 0w` by FULL_SIMP_TAC std_ss [lisp_inv_def]
  \\ ASM_SIMP_TAC std_ss [align_blast,n2w_and_3]
  \\ SIMP_TAC std_ss [CONJ_ASSOC]
  \\ FULL_SIMP_TAC std_ss [lisp_inv_def]
  \\ SIMP_TAC std_ss [PULL_EXISTS_OVER_CONJ]
  \\ Q.LIST_EXISTS_TAC [`s0`,`s1`,`s2`,`s3`,`s4`,`s5`,`m`,`i`,`ss`,`ss1`,`sym`,`b`]
  \\ ASM_SIMP_TAC std_ss [EL_UPDATE_NTH,LENGTH_UPDATE_NTH]
  \\ ASM_SIMP_TAC std_ss [bc_length_def,LENGTH,bc_ref_def,GSYM CONJ_ASSOC]
  \\ STRIP_TAC THEN1
   (Q.ABBREV_TAC `cs2 = [a1; a2; n2w e; bp2; sa1; sa2; sa3; ex] ++ cs`
    \\ `LENGTH cs2 = 18` by
       (Q.UNABBREV_TAC `cs2` \\ FULL_SIMP_TAC std_ss [LENGTH,LENGTH_APPEND])
    \\ IMP_RES_TAC expand_list2
    \\ REPEAT (Q.PAT_X_ASSUM `EL yyy ds = xxxx` (K ALL_TAC))
    \\ FULL_SIMP_TAC std_ss [EL_CONS,UPDATE_NTH_CONS]
    \\ FULL_SIMP_TAC std_ss [ref_static_def,LET_DEF,APPEND,ref_full_stack_def,
         word_arith_lemma1,word64_3232_def,word_arith_lemma1,STAR_ASSOC,word_mul_n2w,
         word_arith_lemma3,word_arith_lemma4,WORD_ADD_0,ref_stack_def,SEP_EXISTS_THM,
         ref_static_APPEND,ref_static_def,LENGTH,mc_code_heap_blast]
    \\ FULL_SIMP_TAC std_ss [GSYM word_add_n2w]
    \\ FULL_SIMP_TAC std_ss [AC WORD_ADD_COMM WORD_ADD_ASSOC]
    \\ SEP_WRITE_TAC)
  \\ FULL_SIMP_TAC std_ss [code_heap_def,PULL_EXISTS_OVER_CONJ]
  \\ EXISTS_TAC ``bs ++ [^inst]``
  \\ EXISTS_TAC ``DROP (bc_length ^inst) (hs:word8 list)``
  \\ FULL_SIMP_TAC std_ss [bc_length_def,LENGTH,bc_ref_def]
  \\ FULL_SIMP_TAC std_ss [WRITE_CODE_APPEND,bc_symbols_ok_APPEND,bc_ref_def,
       bc_symbols_ok_def,SND_WRITE_CODE,bc_length_def,word_arith_lemma1]
  \\ FULL_SIMP_TAC std_ss [LENGTH,bs2bytes_APPEND]
  \\ FULL_SIMP_TAC std_ss [bs2bytes_def,APPEND_NIL,bc_ref_def]
  \\ IMP_RES_TAC bc_length_lemma
  \\ POP_ASSUM (STRIP_ASSUME_TAC o RW [bc_length_def,bc_ref_def,
        LENGTH,SUC_EQ_LENGTH] o SPEC inst)
  \\ FULL_SIMP_TAC std_ss [DROP_CONS,DROP_0]
  \\ Q.PAT_X_ASSUM `xxx = w2n (EL 3 ds)` (ASSUME_TAC o GSYM)
  \\ FULL_SIMP_TAC std_ss [LENGTH,ADD1,GSYM ADD_ASSOC]
  \\ IMP_RES_TAC write_lemma \\ ASM_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC std_ss [AC ADD_ASSOC ADD_COMM]
  \\ Q.PAT_X_ASSUM `xxx (fun2set (d,dd))` ASSUME_TAC
  \\ FULL_SIMP_TAC std_ss [one_byte_list_APPEND,one_byte_list_def]
  \\ FULL_SIMP_TAC std_ss [SEP_CLAUSES,STAR_ASSOC,LENGTH_APPEND,LENGTH,GSYM ADD_ASSOC,
       word_arith_lemma1]
  \\ IMP_RES_TAC LENGTH_bs2bytes \\ FULL_SIMP_TAC std_ss []
  \\ IMP_RES_TAC (GEN_ALL write_list_th) \\ ASM_SIMP_TAC std_ss [])
  val correct_thm = prove(goal,tac) |> SIMP_RULE std_ss [LET_DEF];
  in CONJ spec_thm correct_thm end

(*

val my_consts = LIST_CONJ (map generate_and_verify_write_const
  [("isymbol_less",``iDATA (opSYMBOL_LESS)``)])

*)

val all_const_insts =
  [("ipop",``iPOP``),
   ("isymbol_less",``iDATA (opSYMBOL_LESS)``),
   ("ijump_sym",``iJUMP_SYM``),
   ("icall_sym",``iCALL_SYM``),
   ("ireturn",``iRETURN``),
   ("ifail",``iFAIL``),
   ("icompile",``iCOMPILE``),
   ("iprint",``iPRINT``),
   ("icons",``iDATA (opCONS)``),
   ("iequal",``iDATA (opEQUAL)``),
   ("iless",``iDATA (opLESS)``),
   ("iadd",``iDATA (opADD)``),
   ("isub",``iDATA (opSUB)``),
   ("iconsp",``iDATA (opCONSP)``),
   ("inatp",``iDATA (opNATP)``),
   ("isymbolp",``iDATA (opSYMBOLP)``),
   ("icar",``iDATA (opCAR)``),
   ("icdr",``iDATA (opCDR)``),
   ("ilookup",``iCONST_LOOKUP``)]

val consts = LIST_CONJ (map generate_and_verify_write_const all_const_insts);


(* code heap -- update iJUMP, iJNIL *)

val (mc_update_jump_spec,mc_update_jump_def) = basic_decompile_strings x64_tools "mc_update_jump"
  (SOME (``(r1:word64,r2:word64,r7:word64,r8:word64,r9:word64,df:word64 set,f:word64->word32,dg:word64 set,g:word64->word8)``,
         ``(r1:word64,r2:word64,r7:word64,r8:word64,r9:word64,df:word64 set,f:word64->word32,dg:word64 set,g:word64->word8)``))
  (assemble "x64" `
       mov r1,r8
       mov r2,r9
       shr r1,2
       shr r2,2
       sub r1,r2
       sub r1,6
       add r2,[r7-160]
       mov BYTE [r2+2],r1b
       shr r1,8
       mov BYTE [r2+3],r1b
       shr r1,8
       mov BYTE [r2+4],r1b
       shr r1,8
       mov BYTE [r2+5],r1b
       mov r1d,1
   `)

val (mc_update_jnil_spec,mc_update_jnil_def) = basic_decompile_strings x64_tools "mc_update_jnil"
  (SOME (``(r1:word64,r2:word64,r7:word64,r8:word64,r9:word64,df:word64 set,f:word64->word32,dg:word64 set,g:word64->word8)``,
         ``(r1:word64,r2:word64,r7:word64,r8:word64,r9:word64,df:word64 set,f:word64->word32,dg:word64 set,g:word64->word8)``))
  (assemble "x64" `
       mov r1,r8
       mov r2,r9
       shr r1,2
       shr r2,2
       sub r1,r2
       sub r1,21
       add r2,[r7-160]
       mov BYTE [r2+17],r1b
       shr r1,8
       mov BYTE [r2+18],r1b
       shr r1,8
       mov BYTE [r2+19],r1b
       shr r1,8
       mov BYTE [r2+20],r1b
       mov r1d,1
   `)

val REPLACE_CODE_def = Define `
  REPLACE_CODE (BC_CODE (c1,c2)) p x = BC_CODE ((p =+ SOME x) c1,c2)`;

val SND_REPLACE_CODE = prove(
  ``!code p x. code_ptr (REPLACE_CODE code p x) = code_ptr code``,
  Cases \\ Cases_on `p` \\ FULL_SIMP_TAC std_ss [REPLACE_CODE_def,code_ptr_def]);

val CODE_UPDATE_def = Define `
  CODE_UPDATE x (BC_CODE (c,n)) = BC_CODE ((n =+ SOME x) c, n + bc_length x)`;

val WRITE_CODE_SNOC = prove(
  ``!xs x c. WRITE_CODE c (xs ++ [x]) = CODE_UPDATE x (WRITE_CODE c xs)``,
  Induct \\ Cases_on `c` \\ Cases_on `p`
  \\ ASM_SIMP_TAC std_ss [APPEND,WRITE_CODE_def,CODE_UPDATE_def]);

val WRITE_CODE_code_length = prove(
  ``!bs m k q.
      (WRITE_CODE (BC_CODE (m,k)) bs = BC_CODE (q,n)) ==>
      (code_length bs = n - k) /\ k <= n``,
  Induct \\ SIMP_TAC (srw_ss()) [WRITE_CODE_def,code_length_def]
  \\ REPEAT STRIP_TAC \\ RES_TAC
  \\ ASM_SIMP_TAC std_ss [] \\ DECIDE_TAC);

val code_length_IM_SPLIT = prove(
  ``!bs n code x.
      (code_mem code n = SOME x) /\
      (WRITE_CODE (BC_CODE ((\x.NONE),0)) bs = code) ==>
      ?bs1 bs2. (bs = bs1 ++ [x] ++ bs2) /\ (code_length bs1 = n)``,
  HO_MATCH_MP_TAC SNOC_INDUCT
  \\ SIMP_TAC std_ss [code_length_def,WRITE_CODE_def,code_mem_def]
  \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [WRITE_CODE_SNOC,SNOC_APPEND]
  \\ Cases_on `WRITE_CODE (BC_CODE ((\x. NONE),0)) bs` \\ Cases_on `p`
  \\ FULL_SIMP_TAC std_ss [code_mem_def,CODE_UPDATE_def,APPLY_UPDATE_THM]
  \\ Cases_on `r = n` \\ FULL_SIMP_TAC std_ss [] THEN1
   (IMP_RES_TAC WRITE_CODE_code_length \\ Q.LIST_EXISTS_TAC [`bs`,`[]`]
    \\ FULL_SIMP_TAC std_ss [APPEND_NIL])
  \\ RES_TAC \\ Q.LIST_EXISTS_TAC [`bs1`,`bs2 ++ [x]`]
  \\ FULL_SIMP_TAC std_ss [APPEND_ASSOC]);

val code_length_APPEND = prove(
  ``!xs ys. code_length (xs ++ ys) = code_length xs + code_length ys``,
  Induct \\ EVAL_TAC \\ ASM_SIMP_TAC std_ss [ADD_ASSOC]);

val bc_length_NOT_ZERO = prove(
  ``!x. 0 < bc_length x``,
  Cases \\ EVAL_TAC \\ Cases_on `l` \\ EVAL_TAC);

val WRITE_CODE_REPLACE_CODE_IMP = prove(
  ``!bs2 bs1 code m.
      (bc_length x = bc_length y) /\
      (WRITE_CODE (BC_CODE (m,0)) (bs1 ++ [x] ++ bs2) = code) ==>
      (WRITE_CODE (BC_CODE (m,0)) (bs1 ++ [y] ++ bs2) =
       REPLACE_CODE code (code_length bs1) y)``,
  HO_MATCH_MP_TAC SNOC_INDUCT
  \\ SIMP_TAC std_ss [code_length_def,WRITE_CODE_def,code_mem_def]
  \\ REVERSE (REPEAT STRIP_TAC) THEN1
   (FULL_SIMP_TAC std_ss [SNOC_APPEND,APPEND_ASSOC,WRITE_CODE_SNOC]
    \\ Q.PAT_X_ASSUM `!x.b` (ASSUME_TAC o Q.SPECL [`bs1`,`m`])
    \\ ASM_SIMP_TAC std_ss []
    \\ Cases_on `WRITE_CODE (BC_CODE (m,0)) (bs1 ++ [x] ++ bs2)`
    \\ Cases_on `p`
    \\ IMP_RES_TAC WRITE_CODE_code_length
    \\ FULL_SIMP_TAC std_ss [code_length_APPEND,code_length_def]
    \\ `0 < bc_length x` by FULL_SIMP_TAC std_ss [bc_length_NOT_ZERO]
    \\ `~(r = code_length bs1)` by DECIDE_TAC
    \\ EVAL_TAC \\ FULL_SIMP_TAC std_ss [FUN_EQ_THM,APPLY_UPDATE_THM]
    \\ METIS_TAC [])
  \\ FULL_SIMP_TAC std_ss [APPEND_NIL,WRITE_CODE_SNOC]
  \\ Cases_on `WRITE_CODE (BC_CODE (m,0)) bs1` \\ Cases_on `p`
  \\ IMP_RES_TAC WRITE_CODE_code_length
  \\ FULL_SIMP_TAC std_ss [REPLACE_CODE_def,CODE_UPDATE_def]
  \\ FULL_SIMP_TAC std_ss [combinTheory.UPDATE_EQ]);

val LENGTH_bs2bytes_EQ = prove(
  ``!bs k sym. LENGTH (bs2bytes (k,sym) bs) = code_length bs``,
  Induct \\ ASM_SIMP_TAC std_ss [bs2bytes_def,LENGTH,code_length_def,LENGTH_APPEND]
  \\ Cases \\ EVAL_TAC \\ SIMP_TAC std_ss []
  \\ Cases_on `l` \\ EVAL_TAC \\ SIMP_TAC std_ss []);

val code_length_APPEND = prove(
  ``!xs ys. code_length (xs ++ ys) = code_length xs + code_length ys``,
  Induct \\ ASM_SIMP_TAC std_ss [APPEND,code_length_def,ADD_ASSOC]);

val replace_jump_balst = blastLib.BBLAST_PROVE
  ``(w2w:word32->word64) (w2w (w:30 word) << 2 !! 1w) >>> 2 = w2w w``

val replace_jump_balst2 = blastLib.BBLAST_PROVE
  ``((w2w:word32->word8) ((w - v) >>> 24) = w2w ((w2w w - (w2w:word32->word64) v) >>> 24)) /\
    ((w2w:word32->word8) ((w - v) >>> 16) = w2w ((w2w w - (w2w:word32->word64) v) >>> 16)) /\
    ((w2w:word32->word8) ((w - v) >>> 8) = w2w ((w2w w - (w2w:word32->word64) v) >>> 8)) /\
    ((w2w:word32->word8) ((w - v)) = w2w ((w2w w - (w2w:word32->word64) v)))``

fun REPLACE_JUMP_TAC inst =
  REPEAT STRIP_TAC \\ SIMP_TAC std_ss [mc_update_jump_def,mc_update_jnil_def,LET_DEF]
  \\ IMP_RES_TAC lisp_inv_ds_read
  \\ IMP_RES_TAC lisp_inv_cs_read
  \\ ASM_SIMP_TAC std_ss [INSERT_SUBSET,EMPTY_SUBSET]
  \\ `sp && 3w = 0w` by FULL_SIMP_TAC std_ss [lisp_inv_def]
  \\ ASM_SIMP_TAC std_ss [align_blast,n2w_and_3]
  \\ SIMP_TAC std_ss [CONJ_ASSOC]
  \\ FULL_SIMP_TAC std_ss [lisp_inv_def]
  \\ SIMP_TAC std_ss [PULL_EXISTS_OVER_CONJ]
  \\ Q.LIST_EXISTS_TAC [`s0`,`s1`,`s2`,`s3`,`s4`,`s5`,`m`,`i`,`ss`,`ss1`,`sym`,`b`]
  \\ ASM_SIMP_TAC std_ss [EL_UPDATE_NTH,LENGTH_UPDATE_NTH]
  \\ ASM_SIMP_TAC std_ss [bc_length_def,LENGTH,bc_ref_def,GSYM CONJ_ASSOC]
  \\ ASM_SIMP_TAC std_ss [IMMEDIATE32_def,APPEND,LENGTH,LSR_ADD]
  \\ FULL_SIMP_TAC std_ss [code_heap_def,PULL_EXISTS_OVER_CONJ,SND_REPLACE_CODE]
  \\ `?bs1 bs2. (bs = bs1 ++ [^(car inst) 0] ++ bs2) /\ (code_length bs1 = getVal x1)` by METIS_TAC [code_length_IM_SPLIT]
  \\ FULL_SIMP_TAC std_ss []
  \\ Q.EXISTS_TAC `bs1 ++ [^inst] ++ bs2` \\ Q.EXISTS_TAC `hs`
  \\ IMP_RES_TAC WRITE_CODE_REPLACE_CODE_IMP
  \\ FULL_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC std_ss [bc_symbols_ok_APPEND,bs2bytes_APPEND,bs2bytes_def,
        bc_symbols_ok_def,APPEND_NIL,bc_ref_def,IMMEDIATE32_def,one_byte_list_def,
        one_byte_list_APPEND,APPEND,LENGTH_APPEND,LENGTH,SEP_CLAUSES,STAR_ASSOC,
        word_arith_lemma1,GSYM ADD_ASSOC,LENGTH_bs2bytes_EQ,code_length_APPEND,
        code_length_def,bc_length_def]
  \\ `(w2w w0 >>> 2 = (n2w (getVal x0)):word64) /\ getVal x0 < 2**30 /\
      (w2w w1 >>> 2 = (n2w (getVal x1)):word64) /\ getVal x1 < 2**30` by
   (FULL_SIMP_TAC std_ss [isVal_thm,getVal_def]
    \\ Q.PAT_X_ASSUM `MAP ref_heap_addr [s0; s1; s2; s3; s4; s5] = xx` (ASSUME_TAC o GSYM)
    \\ FULL_SIMP_TAC std_ss [EVERY_DEF,CONS_11,MAP,lisp_x_def,ref_heap_addr_def]
    \\ FULL_SIMP_TAC std_ss [replace_jump_balst]
    \\ FULL_SIMP_TAC wstd_ss [w2w_def,w2n_n2w,WORD_MUL_LSL,word_add_n2w,word_mul_n2w])
  \\ ASM_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC std_ss [GSYM word_add_n2w,AC WORD_ADD_ASSOC WORD_ADD_COMM]
  \\ ASM_SIMP_TAC std_ss [GSYM WORD_SUB_PLUS,word_add_n2w]
  \\ SEP_R_TAC \\ FULL_SIMP_TAC std_ss [replace_jump_balst2]
  \\ `(((w2w:word32->word64) (n2w (getVal x0)) = n2w (getVal x0))) /\
      (((w2w:word32->word64) (n2w (getVal x1)) = n2w (getVal x1))) /\
      (((w2w:word32->word64) (n2w (getVal x1 + 6)) = n2w (getVal x1 + 6))) /\
      (((w2w:word32->word64) (n2w (getVal x1 + 21)) = n2w (getVal x1 + 21)))` by
   (IMP_RES_TAC (DECIDE ``n < 1073741824 ==> (n:num) < 4294967296 /\ n+6 < 4294967296 /\ n+21 < 4294967296``)
    \\ ASM_SIMP_TAC wstd_ss [w2w_def,w2n_n2w])
  \\ ASM_SIMP_TAC std_ss []
  \\ SEP_WRITE_TAC

val inst = ``iJUMP (getVal x0)``
val mc_update_jump_thm = prove(
  ``^LISP /\ 0x100w <+ EL 3 ds ==>
    isVal x0 /\ isVal x1 /\ (code_mem code (getVal x1) = SOME (^(car inst) 0)) ==>
    ?di tw2i.
        mc_update_jump_pre (tw1,tw2,sp,w2w w0,w2w w1,df,f,dd,d) /\
        (mc_update_jump (tw1,tw2,sp,w2w w0,w2w w1,df,f,dd,d) = (tw1,tw2i,sp,w2w w0,w2w w1,df,f,dd,di)) /\
         let (code,d,tw2) = (REPLACE_CODE code (getVal x1) ^inst,di,tw2i) in ^LISP``,
  REPLACE_JUMP_TAC inst) |> SIMP_RULE std_ss [LET_DEF];

val inst = ``iJNIL (getVal x0)``
val mc_update_jnil_thm = prove(
  ``^LISP /\ 0x100w <+ EL 3 ds ==>
    isVal x0 /\ isVal x1 /\ (code_mem code (getVal x1) = SOME (^(car inst) 0)) ==>
    ?di tw2i.
        mc_update_jnil_pre (tw1,tw2,sp,w2w w0,w2w w1,df,f,dd,d) /\
        (mc_update_jnil (tw1,tw2,sp,w2w w0,w2w w1,df,f,dd,d) = (tw1,tw2i,sp,w2w w0,w2w w1,df,f,dd,di)) /\
         let (code,d,tw2) = (REPLACE_CODE code (getVal x1) ^inst,di,tw2i) in ^LISP``,
  REPLACE_JUMP_TAC inst) |> SIMP_RULE std_ss [LET_DEF];


(* store all code heap write/replace *)

val numsym  = LIST_CONJ [CONJ (mc_write_num_spec) (mc_write_num_thm),
                         CONJ (mc_write_num_spec) (mc_write_sym_thm)];
val pops  = LIST_CONJ [CONJ (mc_write_pops_spec) (mc_write_pops_thm),
                       CONJ (mc_write_load_spec) (mc_write_load_thm),
                       CONJ (mc_write_store_spec) (mc_write_store_thm)];
val calls = LIST_CONJ [CONJ (mc_write_call_spec) (mc_write_call_thm),
                       CONJ (mc_write_jump_spec) (mc_write_jump_thm),
                       CONJ (mc_write_jnil_spec) (mc_write_jnil_thm)];
val updates = LIST_CONJ [CONJ mc_update_jump_spec mc_update_jump_thm,
                         CONJ mc_update_jnil_spec mc_update_jnil_thm]

val lisp_inv_write_consts_thm = save_thm("lisp_inv_write_consts_thm",
  LIST_CONJ [numsym,updates,pops,calls,consts]);


(* load pointer into code (used by eval) *)

val (mc_calc_addr_spec,mc_calc_addr_def) = basic_decompile_strings x64_tools "mc_calc_addr"
  (SOME (``(r2:word64,r7:word64,r10:word64,df:word64 set,f:word64->word32)``,
         ``(r2:word64,r7:word64,r10:word64,df:word64 set,f:word64->word32)``))
  (assemble "x64" `
       mov r2,r10
       shr r2,2
       add r2,[r7-160]
   `)

val _ = save_thm("mc_calc_addr_spec",mc_calc_addr_spec);

val mc_calc_addr_thm = store_thm("mc_calc_addr_thm",
  ``^LISP ==> isVal x2 ==>
    ?tw2i. mc_calc_addr_pre (tw2,sp,w2w w2,df,f) /\
           (mc_calc_addr (tw2,sp,w2w w2,df,f) = (tw2i,sp,w2w w2,df,f)) /\
           (tw2i = EL 4 cs + n2w (getVal x2)) /\
           let tw2 = tw2i in ^LISP``,
  FULL_SIMP_TAC std_ss [LET_DEF,mc_calc_addr_def] \\ NTAC 2 STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [isVal_thm,getVal_def,INSERT_SUBSET,EMPTY_SUBSET]
  \\ IMP_RES_TAC lisp_inv_cs_read \\ FULL_SIMP_TAC std_ss []
  \\ `sp && 3w = 0w` by FULL_SIMP_TAC std_ss [lisp_inv_def]
  \\ STRIP_TAC THEN1 (POP_ASSUM MP_TAC THEN blastLib.BBLAST_TAC)
  \\ `w2w w2 >>> 2 = (n2w a):word64` by
   (FULL_SIMP_TAC std_ss [lisp_inv_def,EVERY_DEF,MAP,CONS_11]
    \\ Q.PAT_X_ASSUM `ref_heap_addr s2 = w2` (fn th => FULL_SIMP_TAC std_ss [GSYM th])
    \\ FULL_SIMP_TAC std_ss [lisp_x_def,ref_heap_addr_alt]
    \\ FULL_SIMP_TAC (std_ss++SIZES_ss) [w2w_def,w2n_n2w,WORD_MUL_LSL,word_mul_n2w,
         word_add_n2w,GSYM w2n_11,w2n_lsr]
    \\ `4 * a + 1 < 4294967296` by DECIDE_TAC
    \\ `(4 * a + 1) < 18446744073709551616` by DECIDE_TAC
    \\ `a < 18446744073709551616` by DECIDE_TAC
    \\ ASM_SIMP_TAC std_ss [DIV_EQ_X] \\ DECIDE_TAC)
  \\ ASM_SIMP_TAC std_ss [AC WORD_ADD_ASSOC WORD_ADD_COMM]
  \\ MATCH_MP_TAC (GEN_ALL lisp_inv_ignore_tw2) \\ METIS_TAC []);


(* return stack *)

val stack_tm =
 [``SPEC X64_MODEL
      (zPC p * zR 0x2w r2 * stack (rbp:word64) qs)
      {(p,[0x48w; 0xFFw; 0xD2w])}
      (zPC r2 * zR 0x2w r2 * stack (rbp:word64) ((p+3w)::qs))``,
  ``SPEC X64_MODEL
      (zPC p * zR 0x2w r2 * stack (rbp:word64) qs)
      {(p,[0x48w; 0x52w])}
      (zPC (p+2w) * zR 0x2w r2 * stack (rbp:word64) (r2::qs))``,
  ``SPEC X64_MODEL
      (zPC p * stack (rbp:word64) qs * cond ~(qs = []))
      {(p,[0x48w; 0xC3w])}
      (zPC (HD qs) * stack (rbp:word64) (TL qs))``,
  ``SPEC X64_MODEL
      (zPC p * zR 0x2w r2 * stack (rbp:word64) qs * cond ~(qs = []))
      {(p,[0x48w; 0x5Aw])}
      (zPC (p+2w) * zR 0x2w (HD qs) * stack (rbp:word64) (TL qs))``,
  ``SPEC X64_MODEL
      (zPC p * stack (rbp:word64) qs)
      {(p,[0x48w; 0xE8w; w2w imm32; w2w (imm32 >>> 8); w2w (imm32 >>> 16); w2w (imm32 >>> 24)])}
      (zPC (p + n2w (6 + SIGN_EXTEND 32 64 (w2n (imm32:word32)))) *
       stack (rbp:word64) ((p + 0x6w)::qs))``]
  |> list_mk_conj
  |> (fn tm => list_mk_forall (filter (fn v => fst (dest_var v) <> "stack")
                                 (free_vars tm), tm));

val zSTACK_def = Define ` (* improve at some point... *)
  zSTACK rbp xs = SEP_EXISTS stack. stack rbp xs * cond ^stack_tm`

val zSTACK_PROPS = store_thm("zSTACK_PROPS",
  subst [hd (free_vars stack_tm)|->``zSTACK``] stack_tm,
  REPEAT STRIP_TAC \\ SIMP_TAC std_ss [zSTACK_def,SEP_CLAUSES]
  \\ HO_MATCH_MP_TAC SPEC_EXISTS_EXISTS
  \\ FULL_SIMP_TAC std_ss [SPEC_MOVE_COND,STAR_ASSOC,SEP_CLAUSES]);

val lisp_inv_stack = prove(
  ``!qs2 tw3. ^LISP ==> let qs = qs2 in let tw2 = tw3 in ^LISP``,
  SIMP_TAC std_ss [lisp_inv_def,LET_DEF]) |> SIMP_RULE std_ss [LET_DEF];

val _ = save_thm("lisp_inv_stack",lisp_inv_stack);


val _ = export_theory();
