
open HolKernel Parse boolLib bossLib; val _ = new_theory "lisp_equal";
val _ = ParseExtras.temp_loose_equality()
open lisp_sexpTheory lisp_invTheory;

(* --- *)

open wordsTheory arithmeticTheory wordsLib listTheory pred_setTheory pairTheory;
open combinTheory finite_mapTheory addressTheory helperLib;
open set_sepTheory bitTheory fcpTheory stringTheory;

open codegenLib decompilerLib prog_x64Lib;
open lisp_consTheory stop_and_copyTheory;

val RW = REWRITE_RULE;
val RW1 = ONCE_REWRITE_RULE;
fun SUBGOAL q = REVERSE (sg q)



(* equality test - main loop

  r8 - sexp1
  r9 - sexp2
  r15 - base pointer for "other" heap half
  r0 - index pointer for "other" heap half

*)

val (thm,mc_equal_def) = basic_decompile_strings x64_tools "mc_equal"
  (SOME (``(r8:word64,r9:word64,r0:word64,r15:word64,r6:word64,df:word64 set,f:word64->word32)``,
         ``(r0:word64,r6:word64,df:word64 set,f:word64->word32)``))
  (assemble "x64" `
START: cmp r8,r9
       je NEXT
       test r8,1
       jne FALSE
       test r9,1
       jne FALSE
       mov r8,[r6+4*r8]
       mov r9,[r6+4*r9]
       mov [r15+8*r0],r8d
       mov [r15+8*r0+4],r9d
       shr r8,32
       shr r9,32
       inc r0
       jmp START
NEXT:  cmp r0,0
       je TRUE
       dec r0
       mov r8d,[r15+8*r0]
       mov r9d,[r15+8*r0+4]
       jmp START
TRUE:  mov r0d,11
       jmp EXIT
FALSE: mov r0d,3
EXIT:`)

(* equality test *)

val (thm,mc_full_equal_def) = decompile_io_strings x64_tools "mc_full_equal"
  (SOME (``(r6:word64,r7:word64,r8:word64,r9:word64,df:word64 set,f:word64->word32)``,
         ``(r0:word64,r6:word64,r7:word64,r8:word64,r9:word64,r15:word64,df:word64 set,f:word64->word32)``))
  (assemble "x64" `
     mov r15,[r7-232]
     xor r0,r0
     insert mc_equal
     mov r15,[r7-240]
     mov r8,r0
     mov r0d,3
     mov r9,r0
     add r15,r15
     `);

val mc_full_equal_spec = thm;
val _ = save_thm("mc_full_equal_spec",thm);

val LISP = lisp_inv_def |> SPEC_ALL |> concl |> dest_eq |> fst;
val REST = LISP |> cdr |> cdr |> cdr |> cdr |> cdr |> cdr |> cdr |> cdr |> cdr;
val STAT = LISP |> car |> car |> cdr;
val VAR_REST = LISP |> car |> cdr |> cdr |> cdr |> cdr |> cdr |> cdr |> cdr;

val lisp_equal_stack_def = Define `
  (lisp_equal_stack [] xx yy zz = T) /\
  (lisp_equal_stack ((w0,x0,w1,x1)::ys) ^STAT (x2,x3,x4,x5,^VAR_REST) (w2,w3,w4,w5,df,f,^REST) =
     LDEPTH x0 + LENGTH ys <= e /\ LDEPTH x1 + LENGTH ys <= e /\
     lisp_inv ^STAT (x0,x1,x2,x3,x4,x5,^VAR_REST) (w0,w1,w2,w3,w4,w5,df,f,^REST) /\
     lisp_equal_stack ys ^STAT (x2,x3,x4,x5,^VAR_REST) (w2,w3,w4,w5,df,f,^REST))`;

val one_eq_stack_def = Define `
  (one_eq_stack bp [] = emp) /\
  (one_eq_stack bp ((w0,x0,w1,x1)::ys) =
     one (bp + n2w (8 * LENGTH ys), w0) *
     one (bp + n2w (8 * LENGTH ys + 4), w1) *
     one_eq_stack bp ys)`;

val lisp_eq_measure_def = Define `
  (lisp_eq_measure [] = 0) /\
  (lisp_eq_measure ((w0:word32,x0,w1:word32,x1)::ys) = 3*LSIZE x0 + 3*LSIZE x1 + lisp_eq_measure ys)`;

val w2w_lemma = prove(
  ``!w v. ((w2w w = (w2w v):word64) = (w = v:word32)) /\
          ((w2w w && 1w = 0w:word64) = (w && 1w = 0w)) /\
          ((31 -- 0) (w2w w) = (w2w w):word64) /\
          ((w2w w << 32 !! w2w v) >>> 32 = (w2w w):word64) /\
          (w2w (w2w w << 32 !! (w2w v):word64) = v)``,
  blastLib.BBLAST_TAC);

val RANGE_TAC = FULL_SIMP_TAC std_ss [RANGE_def,IN_DEF] \\ DECIDE_TAC

val ref_mem_REFL = prove(
  ``ref_mem a m n n = emp``,
  Cases_on `n` \\ ASM_SIMP_TAC std_ss [ref_mem_def]);

val lisp_equal_stack_ignore1 = prove(
  ``!ys.
      lisp_equal_stack ys ^STAT (x2,x3,x4,x5,^VAR_REST)
        (w2,w3,w4,w5,df,f,^REST) /\ RANGE (0,e) j ==>
      lisp_equal_stack ys ^STAT (x2,x3,x4,x5,^VAR_REST)
        (w2,w3,w4,w5,df,(n2w (8 * j) + bp2 =+ w) f,^REST)``,
  Induct \\ SIMP_TAC std_ss [lisp_equal_stack_def]
  \\ Cases \\ Cases_on `r` \\ Cases_on `r'`
  \\ ASM_SIMP_TAC std_ss [lisp_equal_stack_def] \\ REPEAT STRIP_TAC
  \\ IMP_RES_TAC (SIMP_RULE std_ss [LET_DEF] lisp_inv_ignore_write1)
  \\ FULL_SIMP_TAC std_ss [AC WORD_ADD_ASSOC WORD_ADD_COMM]);

val lisp_equal_stack_ignore2 = prove(
  ``!ys.
      lisp_equal_stack ys ^STAT (x2,x3,x4,x5,^VAR_REST)
        (w2,w3,w4,w5,df,f,^REST) /\ RANGE (0,e) j ==>
      lisp_equal_stack ys ^STAT (x2,x3,x4,x5,^VAR_REST)
        (w2,w3,w4,w5,df,(n2w (8 * j) + bp2 + 4w =+ w) f,^REST)``,
  Induct \\ SIMP_TAC std_ss [lisp_equal_stack_def]
  \\ Cases \\ Cases_on `r` \\ Cases_on `r'`
  \\ ASM_SIMP_TAC std_ss [lisp_equal_stack_def] \\ REPEAT STRIP_TAC
  \\ IMP_RES_TAC (SIMP_RULE std_ss [LET_DEF] lisp_inv_ignore_write2)
  \\ FULL_SIMP_TAC std_ss [AC WORD_ADD_ASSOC WORD_ADD_COMM]);

val addr_lemma = prove(
  ``((w2w (w && 3w) = 0w:word32) = (w && 3w = 0w:word64)) /\
    (((w + 4w) && 3w = 0w) = (w && 3w = 0w:word64)) /\
    (((w - 0x34w) && 3w = 0w) = (w && 3w = 0w:word64)) /\
    (((w - 0x38w) && 3w = 0w) = (w && 3w = 0w:word64)) /\
    (((w - 0x3Cw) && 3w = 0w) = (w && 3w = 0w:word64)) /\
    (((w - 0x40w) && 3w = 0w) = (w && 3w = 0w:word64)) /\
    (((w - 0xE8w) && 3w = 0w) = (w && 3w = 0w:word64)) /\
    (((w - 0xE4w) && 3w = 0w) = (w && 3w = 0w:word64)) /\
    (((w - 0xECw) && 3w = 0w) = (w && 3w = 0w:word64)) /\
    (((w - 0xF0w) && 3w = 0w) = (w && 3w = 0w:word64)) /\
    (((w + 8w * x) && 3w = 0w) = (w && 3w = 0w:word64)) /\
    (((4w * x + w) && 3w = 0w) = (w && 3w = 0w:word64)) /\
    (((8w * x + w) && 3w = 0w) = (w && 3w = 0w:word64))``,
  blastLib.BBLAST_TAC);

val lisp_inv_Sym_NIL =
  lisp_inv_Sym |> CONJUNCTS |> hd |> UNDISCH |> CONJUNCT1 |> DISCH_ALL

val lisp_inv_Sym_T =
  lisp_inv_Sym |> CONJUNCTS |> el 2 |> UNDISCH |> CONJUNCT1 |> DISCH_ALL

val mc_equal_lemma = prove(
  ``!ys w0 x0 w1 x1 f.
      lisp_equal_stack ((w0,x0,w1,x1)::ys) ^STAT
         (x2,x3,x4,x5,^VAR_REST) (w2,w3,w4,w5,df,f,^REST) /\
      LENGTH ys <= e /\
      (one_eq_stack bp2 ys * ref_mem bp2 (\x. H_EMP) (LENGTH ys) e * p) (fun2set (f,df)) ==>
      ?fi. mc_equal_pre(w2w w0,w2w w1,n2w (LENGTH ys),bp2,bp,df,f) /\
           (mc_equal(w2w w0,w2w w1,n2w (LENGTH ys),bp2,bp,df,f) =
             (if (x0 = x1) /\ EVERY (\(w0,x0,w1,x1). x0 = x1) ys then 11w else 3w,bp,df,fi)) /\
           lisp_inv ^STAT (Sym "NIL",Sym "NIL",x2,x3,x4,x5,^VAR_REST)
             (3w,3w,w2,w3,w4,w5,df,fi,^REST)``,
  NTAC 5 STRIP_TAC
  \\ completeInduct_on `lisp_eq_measure ((w0,x0,w1,x1)::ys) + LENGTH ys`
  \\ REPEAT STRIP_TAC \\ ONCE_REWRITE_TAC [mc_equal_def]
  \\ ASM_SIMP_TAC std_ss [w2w_lemma]
  \\ Cases_on `w0 = w1` \\ ASM_SIMP_TAC std_ss [w2w_lemma] THEN1
   (`LENGTH ys < 18446744073709551616` by
       (FULL_SIMP_TAC std_ss [lisp_equal_stack_def,lisp_inv_def] \\ DECIDE_TAC)
    \\ ASM_SIMP_TAC (std_ss++SIZES_ss) [n2w_11,LENGTH_NIL]
    \\ Cases_on `ys = []` \\ ASM_SIMP_TAC std_ss [] THEN1
     (FULL_SIMP_TAC std_ss [LET_DEF,EVERY_DEF]
      \\ FULL_SIMP_TAC std_ss [lisp_equal_stack_def]
      \\ IMP_RES_TAC (SIMP_RULE std_ss [] lisp_inv_eq_lucky)
      \\ ASM_SIMP_TAC std_ss []
      \\ MATCH_MP_TAC (GEN_ALL lisp_inv_Sym_NIL)
      \\ Q.LIST_EXISTS_TAC [`x1`,`w1`]
      \\ MATCH_MP_TAC lisp_inv_swap1
      \\ MATCH_MP_TAC (GEN_ALL lisp_inv_Sym_NIL)
      \\ Q.LIST_EXISTS_TAC [`x0`,`w0`]
      \\ FULL_SIMP_TAC std_ss [])
    \\ Cases_on `ys` \\ FULL_SIMP_TAC std_ss []
    \\ FULL_SIMP_TAC std_ss [LENGTH,ADD1,GSYM word_add_n2w,WORD_ADD_SUB]
    \\ FULL_SIMP_TAC std_ss [lisp_equal_stack_def]
    \\ `?w0n x0n w1n x1n. h = (w0n,x0n,w1n,x1n)` by METIS_TAC [PAIR]
    \\ FULL_SIMP_TAC std_ss []
    \\ Q.PAT_X_ASSUM `!m.bbb` (MP_TAC o Q.SPEC `lisp_eq_measure ((w0n,x0n,w1n,x1n)::t) + (LENGTH t)`)
    \\ MATCH_MP_TAC (METIS_PROVE [] ``b1 /\ (b2 ==> b3) ==> ((b1 ==> b2) ==> b3)``)
    \\ STRIP_TAC THEN1 (SIMP_TAC std_ss [lisp_eq_measure_def,ADD_ASSOC] \\ DECIDE_TAC)
    \\ STRIP_TAC \\ POP_ASSUM (MP_TAC o Q.SPECL [`w0n`,`x0n`,`w1n`,`x1n`,`t`])
    \\ ASM_SIMP_TAC std_ss [] \\ `LENGTH t <= e` by DECIDE_TAC
    \\ STRIP_TAC \\ POP_ASSUM (MP_TAC o Q.SPECL [`f`])
    \\ FULL_SIMP_TAC std_ss [lisp_equal_stack_def]
    \\ MATCH_MP_TAC (METIS_PROVE [] ``b1 /\ (b2 ==> b3) ==> ((b1 ==> b2) ==> b3)``)
    \\ STRIP_TAC THEN1
     (FULL_SIMP_TAC std_ss [one_eq_stack_def]
      \\ `RANGE(LENGTH t,e)(LENGTH t)` by RANGE_TAC
      \\ IMP_RES_TAC ref_mem_RANGE
      \\ FULL_SIMP_TAC std_ss [ref_aux_def,SEP_CLAUSES,SEP_EXISTS_THM,STAR_ASSOC,ref_mem_REFL]
      \\ Q.LIST_EXISTS_TAC [`w0n`,`w1n`]
      \\ FULL_SIMP_TAC (std_ss++star_ss) [ADD1,word_arith_lemma1])
    \\ REPEAT STRIP_TAC \\ ASM_SIMP_TAC std_ss [LET_DEF]
    \\ FULL_SIMP_TAC std_ss [one_eq_stack_def,word_mul_n2w,AC ADD_COMM ADD_ASSOC,
         AC WORD_ADD_COMM WORD_ADD_ASSOC,word_add_n2w,EVERY_DEF]
    \\ SEP_R_TAC \\ IMP_RES_TAC lisp_inv_eq_lucky
    \\ FULL_SIMP_TAC std_ss []
    \\ FULL_SIMP_TAC std_ss [addr_lemma,GSYM word_add_n2w,GSYM word_mul_n2w,WORD_ADD_ASSOC]
    \\ FULL_SIMP_TAC std_ss [lisp_inv_def])
  \\ REVERSE (Cases_on `isDot x0`) THEN1
   (FULL_SIMP_TAC std_ss [lisp_equal_stack_def]
    \\ `~(w0 && 0x1w = 0x0w)` by METIS_TAC [lisp_inv_type]
    \\ `~(x0 = x1)` by METIS_TAC [lisp_inv_eq]
    \\ ASM_SIMP_TAC std_ss [LET_DEF]
    \\ METIS_TAC [lisp_inv_Sym_T,lisp_inv_Sym_NIL,lisp_inv_swap1])
  \\ REVERSE (Cases_on `isDot x1`) THEN1
   (FULL_SIMP_TAC std_ss [lisp_equal_stack_def]
    \\ `~(w1 && 0x1w = 0x0w)` by METIS_TAC [lisp_inv_type,lisp_inv_swap1]
    \\ `~(x0 = x1)` by METIS_TAC [lisp_inv_eq]
    \\ ASM_SIMP_TAC std_ss [LET_DEF]
    \\ METIS_TAC [lisp_inv_Sym_T,lisp_inv_Sym_NIL,lisp_inv_swap1])
  \\ `(w0 && 0x1w = 0x0w) /\ (w1 && 0x1w = 0x0w)` by
   (FULL_SIMP_TAC std_ss [lisp_equal_stack_def]
    \\ METIS_TAC [lisp_inv_type,lisp_inv_swap1])
  \\ ASM_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC std_ss [lisp_equal_stack_def]
  \\ Q.ABBREV_TAC `w04 = f (0x4w * w2w w0 + bp + 0x4w)`
  \\ Q.ABBREV_TAC `w00 = f (0x4w * w2w w0 + bp)`
  \\ Q.ABBREV_TAC `w14 = f (0x4w * w2w w1 + bp + 0x4w)`
  \\ Q.ABBREV_TAC `w10 = f (0x4w * w2w w1 + bp)`
  \\ `f (bp + 0x4w * w2w w1 + 0x4w) = w14` by FULL_SIMP_TAC std_ss [AC WORD_ADD_ASSOC WORD_ADD_COMM]
  \\ `f (bp + 0x4w * w2w w0 + 0x4w) = w04` by FULL_SIMP_TAC std_ss [AC WORD_ADD_ASSOC WORD_ADD_COMM]
  \\ `f (bp + 0x4w * w2w w1) = w10` by FULL_SIMP_TAC std_ss [AC WORD_ADD_ASSOC WORD_ADD_COMM]
  \\ `f (bp + 0x4w * w2w w0) = w00` by FULL_SIMP_TAC std_ss [AC WORD_ADD_ASSOC WORD_ADD_COMM]
  \\ FULL_SIMP_TAC std_ss [LET_DEF,word_mul_n2w,w2w_lemma]
  \\ `lisp_equal_stack ((w00,CAR x0,w10,CAR x1)::ys) ^STAT (x2,x3,x4,x5,^VAR_REST)
        (w2,w3,w4,w5,df,f,^REST)` by
   (FULL_SIMP_TAC std_ss [lisp_equal_stack_def,CONJ_ASSOC]
    \\ STRIP_TAC THEN1
     (FULL_SIMP_TAC std_ss [isDot_thm,CAR_def,LDEPTH_def,MAX_DEF]
      \\ FULL_SIMP_TAC std_ss [isDot_thm,CAR_def,LDEPTH_def,MAX_DEF]
      \\ DECIDE_TAC)
    \\ IMP_RES_TAC lisp_inv_car \\ REPEAT (Q.PAT_X_ASSUM `!xs xx xxxx. bbb` (K ALL_TAC))
    \\ IMP_RES_TAC lisp_inv_swap1
    \\ IMP_RES_TAC lisp_inv_car \\ REPEAT (Q.PAT_X_ASSUM `!xs xx xxxx. bbb` (K ALL_TAC))
    \\ IMP_RES_TAC lisp_inv_swap1 \\ METIS_TAC [])
  \\ `lisp_equal_stack ((w04,CDR x0,w14,CDR x1)::(w00,CAR x0,w10,CAR x1)::ys) ^STAT (x2,x3,x4,x5,^VAR_REST)
        (w2,w3,w4,w5,df,f,^REST)` by
   (ONCE_REWRITE_TAC [lisp_equal_stack_def] \\ ASM_SIMP_TAC std_ss []
    \\ FULL_SIMP_TAC std_ss [lisp_equal_stack_def,CONJ_ASSOC]
    \\ STRIP_TAC THEN1
     (FULL_SIMP_TAC std_ss [isDot_thm,CDR_def,LDEPTH_def,MAX_DEF,LENGTH]
      \\ FULL_SIMP_TAC std_ss [isDot_thm,CDR_def,LDEPTH_def,MAX_DEF]
      \\ DECIDE_TAC)
    \\ IMP_RES_TAC lisp_inv_cdr \\ REPEAT (Q.PAT_X_ASSUM `!xs xx xxxx. bbb` (K ALL_TAC))
    \\ IMP_RES_TAC lisp_inv_swap1
    \\ IMP_RES_TAC lisp_inv_cdr \\ REPEAT (Q.PAT_X_ASSUM `!xs xx xxxx. bbb` (K ALL_TAC))
    \\ IMP_RES_TAC lisp_inv_swap1 \\ METIS_TAC [])
  \\ Q.ABBREV_TAC `fj = (n2w (8 * LENGTH ys) + bp2 + 0x4w =+ w10)
                          ((n2w (8 * LENGTH ys) + bp2 =+ w00) f)`
  \\ FULL_SIMP_TAC std_ss [GSYM lisp_equal_stack_def]
  \\ Q.PAT_X_ASSUM `!m.bbb` (MP_TAC o Q.SPEC `lisp_eq_measure ((w04,CDR x0,w14,CDR x1)::(w00,CAR x0,w10,CAR x1)::ys) + LENGTH ((w00,CAR x0,w10,CAR x1)::ys)`)
  \\ MATCH_MP_TAC (METIS_PROVE [] ``b1 /\ (b2 ==> b3) ==> ((b1 ==> b2) ==> b3)``)
  \\ STRIP_TAC THEN1
   (FULL_SIMP_TAC std_ss [isDot_thm]
    \\ SIMP_TAC std_ss [lisp_eq_measure_def,LENGTH,CAR_def,CDR_def,LSIZE_def]
    \\ DECIDE_TAC)
  \\ STRIP_TAC \\ POP_ASSUM (MP_TAC o Q.SPECL [`w04`,`CDR x0`,`w14`,`CDR x1`,`(w00,CAR x0,w10,CAR x1)::ys`])
  \\ ASM_SIMP_TAC std_ss []
  \\ STRIP_TAC \\ POP_ASSUM (MP_TAC o Q.SPEC `fj`)
  \\ MATCH_MP_TAC (METIS_PROVE [] ``b1 /\ (b2 ==> b3) ==> ((b1 ==> b2) ==> b3)``)
  \\ STRIP_TAC THEN1
   (SIMP_TAC std_ss [LENGTH,one_eq_stack_def]
    \\ `SUC (LENGTH ys) <= e` by
     (FULL_SIMP_TAC std_ss [isDot_thm] \\ FULL_SIMP_TAC std_ss [LDEPTH_def,MAX_DEF]
      \\ DECIDE_TAC) \\ ASM_SIMP_TAC std_ss []
    \\ REVERSE (REPEAT STRIP_TAC) THEN1
     (`RANGE(LENGTH ys,e)(LENGTH ys)` by RANGE_TAC
      \\ IMP_RES_TAC ref_mem_RANGE
      \\ FULL_SIMP_TAC std_ss [ref_mem_REFL,SEP_CLAUSES,STAR_ASSOC,ref_aux_def,SEP_EXISTS_THM]
      \\ Q.UNABBREV_TAC `fj`
      \\ FULL_SIMP_TAC std_ss [AC WORD_ADD_ASSOC WORD_ADD_COMM,GSYM word_add_n2w]
      \\ SEP_WRITE_TAC)
    \\ Q.UNABBREV_TAC `fj` \\ `RANGE(0,e)(LENGTH ys)` by RANGE_TAC
    \\ MATCH_MP_TAC lisp_equal_stack_ignore2 \\ ASM_SIMP_TAC std_ss []
    \\ MATCH_MP_TAC lisp_equal_stack_ignore1 \\ ASM_SIMP_TAC std_ss [])
  \\ SIMP_TAC std_ss [LENGTH,word_add_n2w,EVERY_DEF,ADD1]
  \\ REPEAT STRIP_TAC \\ ASM_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC std_ss [isDot_thm,CDR_def,CAR_def,SExp_11,AC CONJ_ASSOC CONJ_COMM]
  \\ FULL_SIMP_TAC std_ss [addr_lemma,INSERT_SUBSET,EMPTY_SUBSET,GSYM word_mul_n2w]
  \\ `(bp && 0x3w = 0x0w) /\ (bp2 && 0x3w = 0x0w)` by FULL_SIMP_TAC std_ss [lisp_inv_def]
  \\ ASM_SIMP_TAC std_ss []
  \\ `RANGE(0,e)(LENGTH ys)` by
   (SIMP_TAC std_ss [LENGTH,one_eq_stack_def]
    \\ FULL_SIMP_TAC std_ss [isDot_thm] \\ FULL_SIMP_TAC std_ss [LDEPTH_def,MAX_DEF]
    \\ RANGE_TAC)
  \\ IMP_RES_TAC lisp_inv_ignore_write1
  \\ IMP_RES_TAC lisp_inv_ignore_write2
  \\ REPEAT (Q.PAT_X_ASSUM `!x.bbb` (K ALL_TAC))
  \\ IMP_RES_TAC (RW [isDot_def] (Q.INST [`x0`|->`Dot a b`] lisp_inv_car))
  \\ IMP_RES_TAC (RW [isDot_def] (Q.INST [`x0`|->`Dot a b`] lisp_inv_cdr))
  \\ IMP_RES_TAC lisp_inv_swap1
  \\ IMP_RES_TAC (RW [isDot_def] (Q.INST [`x0`|->`Dot a b`] lisp_inv_car))
  \\ IMP_RES_TAC (RW [isDot_def] (Q.INST [`x0`|->`Dot a b`] lisp_inv_cdr))
  \\ FULL_SIMP_TAC std_ss [AC WORD_ADD_ASSOC WORD_ADD_COMM,word_mul_n2w]);

val mc_equal_thm = mc_equal_lemma
  |> Q.SPECL [`[]`,`w0`,`x0`,`w1`,`x1`,`f`]
  |> SIMP_RULE std_ss [EVERY_DEF,LENGTH,lisp_equal_stack_def,one_eq_stack_def,SEP_CLAUSES]

val mc_full_equal_thm = store_thm("mc_full_equal_thm",
  ``lisp_inv ^STAT (x0,x1,x2,x3,x4,x5,^VAR_REST)
      (w0,w1,w2,w3,w4,w5,df,f,^REST) ==>
    ?fi w0i w1i.
      mc_full_equal_pre (bp,sp,w2w w0,w2w w1,df,f) /\
      (mc_full_equal (bp,sp,w2w w0,w2w w1,df,f) = (tw0,bp,sp,w2w w0i,w2w w1i,we,df,fi)) /\
      lisp_inv ^STAT (LISP_TEST (x0 = x1),Sym "NIL",x2,x3,x4,x5,^VAR_REST)
        (w0i,w1i,w2,w3,w4,w5,df,fi,^REST)``,
  SIMP_TAC std_ss [mc_full_equal_def] \\ STRIP_TAC
  \\ `?p. (ref_mem bp2 (\x. H_EMP) 0 e * p) (fun2set (f,df))` by
    (FULL_SIMP_TAC std_ss [lisp_inv_def] \\ METIS_TAC [STAR_ASSOC,STAR_COMM])
  \\ MP_TAC mc_equal_thm \\ ASM_SIMP_TAC std_ss []
  \\ `LDEPTH x0 <= e /\ LDEPTH x1 <= e` by METIS_TAC [lisp_inv_LDEPTH,lisp_inv_swap1]
  \\ ASM_SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC
  \\ ASM_SIMP_TAC std_ss [LET_DEF]
  \\ `w2w (f (sp - 0xE4w)) << 32 !! w2w (f (sp - 0xE8w)) = bp2` by
   (FULL_SIMP_TAC std_ss [lisp_inv_def,ref_full_stack_def,ref_static_def,APPEND]
    \\ FULL_SIMP_TAC std_ss [LET_DEF,word64_3232_def,word_arith_lemma3,STAR_ASSOC,SEP_CLAUSES]
    \\ SEP_R_TAC \\ blastLib.BBLAST_TAC)
  \\ ASM_SIMP_TAC std_ss []
  \\ Q.LIST_EXISTS_TAC [`if x0 = x1 then 0xBw else 0x3w`,`3w`]
  \\ `(w2w (fi (sp - 0xECw)) << 32 !! w2w (fi (sp - 0xF0w)) = (n2w e):word64)` by
   (FULL_SIMP_TAC std_ss [lisp_inv_def,ref_full_stack_def,ref_static_def,APPEND]
    \\ FULL_SIMP_TAC std_ss [LET_DEF,word64_3232_def,word_arith_lemma3,STAR_ASSOC]
    \\ SEP_R_TAC \\ Q.SPEC_TAC (`(n2w e):word64`,`ww`) \\ blastLib.BBLAST_TAC)
  \\ ASM_SIMP_TAC std_ss []
  \\ `n2w e + n2w e = we` by
    FULL_SIMP_TAC std_ss [lisp_inv_def,word_add_n2w,DECIDE ``2*e=e+e:num``]
  \\ FULL_SIMP_TAC std_ss [INSERT_SUBSET,EMPTY_SUBSET]
  \\ FULL_SIMP_TAC std_ss [addr_lemma]
  \\ `sp && 3w = 0w` by FULL_SIMP_TAC std_ss [lisp_inv_def]
  \\ ASM_SIMP_TAC std_ss []
  \\ `(sp - 0xE4w IN df /\ sp - 0xE8w IN df) /\
      (sp - 0xECw IN df /\ sp - 0xF0w IN df)` by
   (FULL_SIMP_TAC std_ss [lisp_inv_def,ref_full_stack_def,ref_static_def,
      LET_DEF,word64_3232_def,word_arith_lemma3,STAR_ASSOC,APPEND] \\ SEP_R_TAC
    \\ ASM_SIMP_TAC std_ss []) \\ ASM_SIMP_TAC std_ss []
  \\ `tw0 = 3w` by FULL_SIMP_TAC std_ss [lisp_inv_def]
  \\ Cases_on `x0 = x1` \\ ASM_SIMP_TAC std_ss [LISP_TEST_def]
  \\ FULL_SIMP_TAC (std_ss++SIZES_ss) [w2w_def,w2n_n2w]
  \\ IMP_RES_TAC lisp_inv_Sym_T);


val _ = export_theory();
