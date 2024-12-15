
open HolKernel boolLib bossLib Parse;
open tailrecTheory mc_tailrecLib compilerLib codegen_x86Lib;
open wordsTheory addressTheory wordsLib arithmeticTheory;

open decompilerLib set_sepTheory prog_x86Lib;

val _ = new_theory "divide";


val _ = set_x86_regs
  [(3,"eax"),(4,"ecx"),(5,"edx"),(6,"ebx"),(7,"edi"),(8,"esi"),(10,"ebp")]

(* division *)

val (th1,shift_left_def,shift_left_pre_def) = compile "arm" ``
  shift_left(r5:word32,r4:word32,r2:word32) =
    if r5 <=+ r4 then (r5,r4,r2) else
      let r4 = r4 + r4 in
      let r2 = r2 + r2 in
        shift_left(r5,r4,r2)``;

val (th1,if_sub_def,if_sub_pre_def) = compile "arm" ``
  if_sub(r5:word32,r4:word32,r2:word32,r3:word32) =
    if r4 <=+ r5 then
      let r5 = r5 - r4 in
      let r3 = r3 + r2 in
        (r5,r4,r2,r3)
    else (r5,r4,r2,r3)``

val (th1,sub_and_shift_def,sub_and_shift_pre_def) = compile "arm" ``
  sub_and_shift(r5:word32,r4:word32,r2:word32,r3:word32) =
    let (r5,r4,r2,r3) = if_sub (r5,r4,r2,r3) in
    let r2 = r2 >>> 1 in
      if r2 = 0w then (r5,r4,r2,r3) else
        let r4 = r4 >>> 1 in
          sub_and_shift(r5,r4,r2,r3)``;

val (arm_div_th1,arm_div_def,arm_div_pre_def) = compile "arm" ``
  arm_div(r3:word32,r4:word32) =
    let r2 = 1w in
    let r5 = r3 in
    let (r5,r4,r2) = shift_left(r5,r4,r2) in
    let r3 = 0w in
    let (r5,r4,r2,r3) = sub_and_shift(r5,r4,r2,r3) in
      (r5,r4,r3)``

val shift_left_lemma = prove(
  ``!m n k.
      m < 2 ** 31 /\ n < 2 ** 32 /\ n <> 0 ==>
      ?i. shift_left_pre(n2w m, n2w n, n2w k) /\
          m <= n * 2 ** i /\ n * 2 ** i < 2 ** 32 /\
          (shift_left(n2w m, n2w n, n2w k) =
            (n2w m, n2w (n * 2 ** i), n2w (k * 2 ** i)))``,
  completeInduct_on `m - n:num` THEN REPEAT STRIP_TAC
  THEN Cases_on `m <= n`
  THEN ONCE_REWRITE_TAC [shift_left_pre_def,shift_left_def]
  THEN FULL_SIMP_TAC (std_ss++SIZES_ss) [word_ls_n2w,WORD_NOT_LOWER]
  THEN `m < 4294967296` by DECIDE_TAC
  THEN FULL_SIMP_TAC (std_ss++SIZES_ss) [word_ls_n2w]
  THEN1 (Q.EXISTS_TAC `0` THEN ASM_SIMP_TAC std_ss [])
  THEN REWRITE_TAC [word_add_n2w,GSYM TIMES2]
  THEN SIMP_TAC std_ss [LET_DEF]
  THEN `m - (2 * n) < m - n` by DECIDE_TAC
  THEN Q.PAT_X_ASSUM `!m.bbb` (ASSUME_TAC o UNDISCH o Q.SPEC `m - (2 * n)`)
  THEN Q.PAT_X_ASSUM `!m.bbb` (ASSUME_TAC o REWRITE_RULE [] o Q.SPECL [`m`,`2*n`])
  THEN `2 * n < 4294967296 /\ 2 * n <> 0` by DECIDE_TAC
  THEN Q.PAT_X_ASSUM `!m.bbb` (STRIP_ASSUME_TAC o UNDISCH_ALL o
         REWRITE_RULE [GSYM AND_IMP_INTRO] o Q.SPEC `2 * k`)
  THEN Q.EXISTS_TAC `SUC i`
  THEN FULL_SIMP_TAC std_ss [AC MULT_ASSOC MULT_COMM,EXP]);

val word_LSR_n2w = store_thm("word_LSR_n2w",
  ``!m n. m < dimword (:'a) ==>
          (((n2w m):'a word) >>> n = n2w (m DIV (2 ** n)))``,
  ONCE_REWRITE_TAC [GSYM n2w_w2n] THEN REWRITE_TAC [w2n_lsr]
  THEN REWRITE_TAC [n2w_w2n] THEN SIMP_TAC std_ss [w2n_n2w]);

val MULT_IMP_LESS_EQ = prove(
  ``!m n t q. t < m /\ m * n <= m * q + t ==> n <= q:num``,
  REPEAT STRIP_TAC THEN REWRITE_TAC [GSYM NOT_LESS]
  THEN CCONTR_TAC THEN FULL_SIMP_TAC bool_ss []
  THEN `q <= n /\ q <> n` by DECIDE_TAC
  THEN FULL_SIMP_TAC bool_ss [LESS_EQ_EXISTS]
  THEN FULL_SIMP_TAC bool_ss [LEFT_ADD_DISTRIB]
  THEN Cases_on `p'` THEN1 FULL_SIMP_TAC std_ss []
  THEN FULL_SIMP_TAC std_ss [MULT_CLAUSES,GSYM ADD_ASSOC]
  THEN DECIDE_TAC);

val sub_and_shift_lemma = prove(
  ``!k m l q t.
      t < m /\ q * m + t < m * 2 ** (SUC k) /\
      m * 2 ** k < 2 ** 32 /\ q * m + t < 2 ** 32 ==>
      sub_and_shift_pre(n2w (q * m + t), n2w (m * 2 ** k), n2w (2 ** k), n2w l) /\
      (sub_and_shift(n2w (q * m + t), n2w (m * 2 ** k), n2w (2 ** k), n2w l) =
        (n2w t,n2w m,0w,n2w (l + q)))``,
  Induct THEN1
   (SIMP_TAC std_ss []
    THEN ONCE_REWRITE_TAC [sub_and_shift_def,sub_and_shift_pre_def]
    THEN REWRITE_TAC [if_sub_def]
    THEN SIMP_TAC (std_ss++SIZES_ss) [word_ls_n2w]
    THEN NTAC 5 STRIP_TAC
    THEN Cases_on `m <= q * m + t`
    THEN ASM_SIMP_TAC std_ss [LET_DEF,EVAL ``(1w:word32) >>> 1``]
    THEN `m < dimword (:32)` by ASM_SIMP_TAC (std_ss++SIZES_ss) []
    THEN  IMP_RES_TAC word_LSR_n2w
    THEN ASM_SIMP_TAC std_ss []
    THENL [
      REWRITE_TAC [addressTheory.word_arith_lemma2]
      THEN FULL_SIMP_TAC std_ss [GSYM NOT_LESS]
      THEN Cases_on `q` THEN1 FULL_SIMP_TAC std_ss []
      THEN Cases_on `n` THEN1 SIMP_TAC std_ss [word_add_n2w]
      THEN FULL_SIMP_TAC std_ss [MULT,ONCE_REWRITE_RULE [MULT_COMM] TIMES2]
      THEN `F` by DECIDE_TAC,
      Cases_on `q` THEN1 FULL_SIMP_TAC std_ss []
      THEN FULL_SIMP_TAC std_ss [MULT,ONCE_REWRITE_RULE [MULT_COMM] TIMES2]
      THEN `F` by DECIDE_TAC])
  THEN SIMP_TAC std_ss []
  THEN ONCE_REWRITE_TAC [sub_and_shift_def,sub_and_shift_pre_def]
  THEN REWRITE_TAC [if_sub_def]
  THEN SIMP_TAC (std_ss++SIZES_ss) [word_ls_n2w]
  THEN NTAC 5 STRIP_TAC
  THEN REVERSE (Cases_on `m * 2 ** SUC k <= q * m + t`)
  THEN ASM_SIMP_TAC std_ss [LET_DEF]
  THEN `m * 2 ** SUC k < dimword (:32)` by ASM_SIMP_TAC (std_ss++SIZES_ss) []
  THEN `2 ** SUC k < dimword (:32)` by
   (Cases_on `m` THEN1 DECIDE_TAC
    THEN FULL_SIMP_TAC std_ss [MULT]
    THEN DECIDE_TAC)
  THEN IMP_RES_TAC word_LSR_n2w
  THEN ASM_SIMP_TAC std_ss [EXP]
  THEN ONCE_REWRITE_TAC [MULT_COMM]
  THEN SIMP_TAC std_ss [MULT_DIV]
  THEN REWRITE_TAC [GSYM MULT_ASSOC]
  THEN ONCE_REWRITE_TAC [MULT_COMM]
  THEN SIMP_TAC std_ss [MULT_DIV]
  THEN ONCE_REWRITE_TAC [MULT_COMM]
  THEN `n2w (2 ** k) <> 0x0w:word32` by
   (`2 ** k < dimword (:32)` by
      (FULL_SIMP_TAC std_ss [EXP] THEN DECIDE_TAC)
    THEN FULL_SIMP_TAC (std_ss++SIZES_ss) [n2w_11])
  THEN ASM_SIMP_TAC std_ss [] THEN1
   (`t < m /\ q * m + t < m * 2 ** SUC k /\ m * 2 ** k < 2 ** 32 /\
       q * m + t < 2 ** 32` by
      (FULL_SIMP_TAC (std_ss++SIZES_ss) [EXP,GSYM NOT_LESS] THEN DECIDE_TAC)
    THEN Q.PAT_X_ASSUM `!m l. bbb`
      (ASSUME_TAC o GSYM o UNDISCH_ALL o REWRITE_RULE [GSYM AND_IMP_INTRO] o
       Q.SPECL [`m`,`l`,`q`,`t`])
    THEN FULL_SIMP_TAC std_ss []
    THEN FULL_SIMP_TAC std_ss [AC MULT_ASSOC MULT_COMM])
  THEN `~(m * q + t < 2 * (2 ** k * m))` by
    (FULL_SIMP_TAC std_ss [EXP] THEN DECIDE_TAC)
  THEN ASM_SIMP_TAC std_ss [addressTheory.word_arith_lemma2,word_add_n2w]
  THEN FULL_SIMP_TAC std_ss [NOT_LESS,MULT_ASSOC]
  THEN `2 * 2 ** k <= q` by METIS_TAC [MULT_IMP_LESS_EQ,MULT_COMM]
  THEN `m * q + t - 2 * 2 ** k * m = m * (q - 2 * 2 ** k) + t` by
   (`2 * 2 ** k * m <= q * m` by METIS_TAC [LESS_MONO_MULT]
    THEN DECIDE_TAC)
  THEN ASM_SIMP_TAC std_ss []
  THEN `t < m /\ (q - 2 * 2 ** k) * m + t < m * 2 ** SUC k /\
          m * 2 ** k < 4294967296 /\ (q - 2 * 2 ** k) * m + t < 4294967296` by
     (FULL_SIMP_TAC (std_ss++SIZES_ss) [EXP]
      THEN REPEAT STRIP_TAC THEN REPEAT DECIDE_TAC)
  THEN Q.PAT_X_ASSUM `!m l. bbb`
    (ASSUME_TAC o UNDISCH_ALL o REWRITE_RULE [GSYM AND_IMP_INTRO] o
     Q.SPECL [`m`,`l + (2 ** k * 2)`,`q - 2 * 2 ** k`,`t`])
  THEN FULL_SIMP_TAC std_ss [AC MULT_ASSOC MULT_COMM]
  THEN MATCH_MP_TAC (METIS_PROVE [] ``(x = y) ==> (f x = f y)``)
  THEN SIMP_TAC std_ss [GSYM ADD_ASSOC]
  THEN REWRITE_TAC [SUB_LEFT_ADD]
  THEN Cases_on `2 * 2 ** k = q` THEN1 ASM_SIMP_TAC std_ss []
  THEN `~(q <= 2 * 2 ** k)` by
   (Q.PAT_X_ASSUM `2 * 2 ** k <> q` MP_TAC
    THEN Q.PAT_X_ASSUM `2 * 2 ** k <= q` MP_TAC
    THEN REPEAT (POP_ASSUM (K ALL_TAC))
    THEN DECIDE_TAC)
  THEN ASM_SIMP_TAC std_ss []);

val arm_div_lemma = store_thm("arm_div_lemma",
  ``!m n x.
      m < 2 ** 31 /\ n < 2 ** 32 /\ n <> 0 ==>
      arm_div_pre(n2w m, n2w n) /\
      (arm_div(n2w m, n2w n) = (n2w (m MOD n), n2w n, n2w (m DIV n)))``,
  SIMP_TAC bool_ss [arm_div_def,arm_div_pre_def,LET_DEF]
  THEN NTAC 3 STRIP_TAC
  THEN IMP_RES_TAC shift_left_lemma
  THEN Q.PAT_X_ASSUM `!k.bbb` (STRIP_ASSUME_TAC o Q.SPEC `1`)
  THEN ASM_SIMP_TAC std_ss []
  THEN `0 < n` by DECIDE_TAC
  THEN IMP_RES_TAC (GSYM DIVISION)
  THEN `m MOD n < n` by FULL_SIMP_TAC std_ss []
  THEN `m DIV n * n + m MOD n < 2 ** 32` by
         (FULL_SIMP_TAC std_ss [] THEN DECIDE_TAC)
  THEN `m DIV n * n + m MOD n < n * 2 ** SUC i` by
   (ASM_SIMP_TAC std_ss [EXP,TIMES2,LEFT_ADD_DISTRIB]
    THEN `~(2 ** i = 0:num)` by SIMP_TAC std_ss [EXP_EQ_0]
    THEN `n * 2 ** i <> 0:num` by ASM_SIMP_TAC std_ss [MULT_EQ_0]
    THEN DECIDE_TAC)
  THEN MP_TAC (Q.SPECL [`i`,`n`,`0`,`m DIV n`,`m MOD n`] sub_and_shift_lemma)
  THEN FULL_SIMP_TAC std_ss []
  THEN `m < 4294967296` by DECIDE_TAC
  THEN FULL_SIMP_TAC std_ss []);

val arm_div_thm = prove(
  ``!w v.
      w2n v < 2 ** 31 /\ w <> 0w ==>
      arm_div_pre(v, w) /\
      (arm_div(v, w) = (word_mod v w, w, word_div v w))``,
  Cases_word THEN Cases_word
  THEN REWRITE_TAC [word_mod_def,word_div_def]
  THEN FULL_SIMP_TAC (std_ss++SIZES_ss) [w2n_n2w,n2w_11]
  THEN STRIP_TAC THEN IMP_RES_TAC (SIMP_RULE std_ss [] arm_div_lemma)
  THEN ASM_SIMP_TAC std_ss []);

val arm_div_mod_thm = let
  val imp = Q.SPECL [`r4`,`r3`] arm_div_thm
  val th = DISCH (concl (UNDISCH imp)) arm_div_th1
  val th = SIMP_RULE std_ss [SEP_CLAUSES,LET_DEF] th
  val th = DISCH_ALL (MP th (UNDISCH imp))
  val th = REWRITE_RULE [GSYM progTheory.SPEC_MOVE_COND] th
  val (_,_,_,t) = dest_spec (concl th)
  val q = subst [``word_mod r3 r4:word32``|->``r5:word32``,
                 ``r3 // r4:word32``|->``r3:word32``] t
  val q = pairSyntax.mk_anylet([(``(r3:word32,r5:word32)``,``(r3 // r4:word32,word_mod r3 r4:word32)``)],q)
  val lemma = prove(mk_eq(t,q),
    SIMP_TAC (std_ss++SIZES_ss) [LET_DEF,w2n_n2w,
       word_div_def,word_mod_def] THEN SIMP_TAC (std_ss++star_ss) [])
  val th = REWRITE_RULE [lemma] th
  in th end

val (th,x86_div_mod_def) = decompile x86_tools "x86_div_mod" `31D2
                                                              F7F1`;
val x86_div_mod_thm = let
  val lemma = prove(
  ``((let (eax,ecx,edx) = x86_div_mod (eax,ecx) in pp eax ecx edx) =
     (let (eax,edx) = (word_div eax ecx, word_mod eax ecx) in pp eax ecx edx))``,
  SIMP_TAC (std_ss++SIZES_ss) [LET_DEF,x86_div_mod_def,w2n_n2w,
     word_div_def,word_mod_def] THEN SIMP_TAC (std_ss++star_ss) [])
  val th = SIMP_RULE std_ss [lemma] th
  val imp = Q.SPECL [`ecx`,`eax`] arm_div_thm
  val th = DISCH ((cdr o car o concl) imp) th
  val lemma = prove(
    ``ecx <> 0x0w ==> x86_div_mod_pre (eax,ecx)``,
    ASSUME_TAC (Q.SPEC `eax` (INST_TYPE [``:'a``|->``:32``] w2n_lt))
    THEN Q.SPEC_TAC (`ecx`,`ecx`) THEN Cases_word
    THEN FULL_SIMP_TAC (std_ss++SIZES_ss) [LET_DEF,x86_div_mod_def,w2n_n2w,n2w_11]
    THEN STRIP_TAC THEN `0 < n` by DECIDE_TAC
    THEN IMP_RES_TAC DIV_LT_X
    THEN ASM_SIMP_TAC std_ss []
    THEN Cases_on `n`
    THEN FULL_SIMP_TAC std_ss [MULT_CLAUSES]
    THEN DECIDE_TAC)
  val th = SIMP_RULE std_ss [lemma,SEP_CLAUSES] th
  val th = REWRITE_RULE [GSYM progTheory.SPEC_MOVE_COND] th
  in th end;

val (ppc_div_th1,ppc_div_def,ppc_div_pre_def) = compile "ppc" ``
  ppc_div (r3:word32,r4:word32) =
    let r2 = r3 in
    let r3 = word_div r3 r4 in
    let r5 = r3 * r4 in
    let r5 = r2 - r5 in
      (r3,r4,r5)``

val word_mod_thm =
  (GEN_ALL o DISCH_ALL o REWRITE_RULE [WORD_ADD_EQ_SUB] o
   ONCE_REWRITE_RULE [WORD_ADD_COMM] o UNDISCH o GSYM o SPEC_ALL) WORD_DIVISION

val ppc_div_mod_thm = let
  val lemma = prove(
  ``r4 <> 0w ==>
    ((let (r3,r4,r5) = ppc_div (r3,r4) in pp r3 r4 r5) =
     (let (r3,r5) = (word_div r3 r4, word_mod r3 r4) in pp r3 r4 r5))``,
  SIMP_TAC (std_ss++SIZES_ss) [LET_DEF,ppc_div_def,w2n_n2w,
     word_mod_thm])
  val imp = Q.SPECL [`r4`,`r3`] arm_div_thm
  val th = DISCH ((cdr o car o concl) imp) ppc_div_th1
  val th = SIMP_RULE bool_ss [lemma] th
  val th = REWRITE_RULE [GSYM progTheory.SPEC_MOVE_COND] th
  in th end;

(* compiling lisp primitives *)

val _ = codegenLib.add_compiled [arm_div_mod_thm,x86_div_mod_thm,ppc_div_mod_thm];

val (div_thms,lisp_word_div_def,lisp_word_div_pre_def) = compile_all ``
  lisp_word_div(r3:word32,r4:word32) =
    let r3 = r3 >>> 2 in
    let r4 = r4 >>> 2 in
    let (r3,r5) = (r3 // r4, word_mod r3 r4) in
    let r3 = r3 << 2 in
    let r3 = r3 + 2w in
    let r4 = 3w:word32 in
    let r5 = 3w:word32 in
      (r3,r4,r5)``

val (mod_thms,lisp_word_mod_def,lisp_word_mod_pre_def) = compile_all ``
  lisp_word_mod(r3:word32,r4:word32) =
    let r3 = r3 >>> 2 in
    let r4 = r4 >>> 2 in
    let (r3,r5) = (r3 // r4, word_mod r3 r4) in
    let r3 = r5 << 2 in
    let r3 = r3 + 2w in
    let r4 = 3w:word32 in
    let r5 = 3w:word32 in
      (r3,r4,r5)``

val (mul_thms,lisp_word_mul_def,lisp_word_mul_pre_def) = compile_all ``
  lisp_word_mul(r3:word32,r4:word32) =
    let r3 = r3 >>> 2 in
    let r4 = r4 >>> 2 in
    let r3 = r3 * r4 in
    let r3 = r3 << 2 in
    let r3 = r3 + 2w in
    let r4 = 3w:word32 in
    let r5 = 3w:word32 in
      (r3,r4,r5)``;


(* exporting the important theorems *)

fun save_all prefix postfix =
  map (fn (n,th) => save_thm(prefix ^ n ^ postfix,th));

val _ = save_all "lisp_word_mul_" "_thm" mul_thms;
val _ = save_all "lisp_word_mod_" "_thm" mod_thms;
val _ = save_all "lisp_word_div_" "_thm" div_thms;

val _ = save_thm("arm_div_mod_thm",arm_div_mod_thm);
val _ = save_thm("x86_div_mod_thm",x86_div_mod_thm);
val _ = save_thm("ppc_div_mod_thm",ppc_div_mod_thm);


val _ = export_theory();
