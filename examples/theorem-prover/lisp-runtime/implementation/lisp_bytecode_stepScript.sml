open HolKernel Parse boolLib bossLib; val _ = new_theory "lisp_bytecode_step";
val _ = ParseExtras.temp_loose_equality()

open lisp_sexpTheory lisp_invTheory lisp_opsTheory lisp_bigopsTheory;
open lisp_codegenTheory lisp_initTheory lisp_symbolsTheory;
open lisp_sexpTheory lisp_invTheory lisp_parseTheory;
open lisp_semanticsTheory lisp_compilerTheory lisp_compiler_opTheory progTheory;
open compilerLib decompilerLib codegenLib prog_x64Lib prog_x64Theory;

open wordsTheory arithmeticTheory wordsLib listTheory pred_setTheory pairTheory;
open combinTheory finite_mapTheory addressTheory helperLib sumTheory;
open set_sepTheory bitTheory fcpTheory stringTheory optionTheory relationTheory;
open stop_and_copyTheory lisp_consTheory;

val RW = REWRITE_RULE;
val RW1 = ONCE_REWRITE_RULE;


val PULL_EXISTS_IMP = METIS_PROVE [] ``((?x. P x) ==> Q) = (!x. P x ==> Q)``;
val PULL_FORALL_IMP = METIS_PROVE [] ``(Q ==> !x. P x) = (!x. Q ==> P x)``;

fun MERGE_CODE th = let
  val th = MATCH_MP SPEC_X64_MERGE_CODE th
  val th = CONV_RULE (RATOR_CONV (SIMP_CONV std_ss [LENGTH,ADD1])) th
  val th = RW [APPEND] th
  val _ = not (is_imp (concl th)) orelse fail()
  in MERGE_CODE th end handle HOL_ERR _ => th;


val zLISP_BYTECODE_def = Define `
  zLISP_BYTECODE (a1,a2,sl,sl1,e,ex,cs,rbp,ddd,cu) (xs,p,rs,bc) (stack,input,xbp,rstack,amnt,w) =
    (SEP_EXISTS x1 x2 x3 x4.
      zLISP (a1,a2,sl,sl1,e,ex,cs,rbp,ddd,cu)
              (HD (xs ++ Sym "NIL"::stack),x1,x2,x3,x4,bc_state_tree bc,
               TL (xs ++ Sym "NIL"::stack),bc.consts,
               IO_STREAMS input bc.io_out,xbp,rs ++ rstack,
               BC_CODE (bc.code,bc.code_end),amnt,bc.ok) * zPC p * ~zS *
      cond (bc_inv bc)) \/ zLISP_FAIL (a1,a2,sl,sl1,e,ex,cs,rbp,ddd,cu)`;

val SPEC_PULL_EXISTS = prove(
  ``(?x. SPEC m p c (q x)) ==> SPEC m p c (SEP_EXISTS x. q x)``,
  REPEAT STRIP_TAC \\ `SEP_IMP (q x) ((SEP_EXISTS x. q x))` suffices_by
  (STRIP_TAC THEN IMP_RES_TAC SPEC_WEAKEN)
  \\ SIMP_TAC std_ss [SEP_IMP_def,SEP_EXISTS_THM] \\ METIS_TAC []);

val SPEC_REMOVE_POST = prove(
  ``SPEC m p c q ==> SPEC m p c (q \/ q2)``,
  `SEP_IMP q (q \/ q2)` by FULL_SIMP_TAC std_ss [SEP_IMP_def,SEP_DISJ_def]
  \\ METIS_TAC [SPEC_WEAKEN]);

fun SPEC_EX q = HO_MATCH_MP_TAC SPEC_PULL_EXISTS \\ Q.EXISTS_TAC q

val BYTECODE_TAC =
  `bc1.instr_length = bc_length` by FULL_SIMP_TAC std_ss [bc_inv_def]
  \\ FULL_SIMP_TAC std_ss [bc_length_def,bc_ref_def,LENGTH,GSYM word_add_n2w,WORD_ADD_ASSOC,IMMEDIATE32_def,APPEND]
  \\ HO_MATCH_MP_TAC SPEC_PULL_EXISTS \\ Q.EXISTS_TAC `x1`
  \\ HO_MATCH_MP_TAC SPEC_PULL_EXISTS \\ Q.EXISTS_TAC `x2`
  \\ HO_MATCH_MP_TAC SPEC_PULL_EXISTS \\ Q.EXISTS_TAC `x3`
  \\ HO_MATCH_MP_TAC SPEC_PULL_EXISTS \\ Q.EXISTS_TAC `x4`
  \\ ASM_SIMP_TAC std_ss [SEP_CLAUSES]

val HD_TL = prove(
  ``HD (xs ++ y::ys)::TL (xs ++ y::ys) = xs ++ y::ys``,
  Cases_on `xs` \\ FULL_SIMP_TAC std_ss [APPEND,HD,TL]);

val UPDATE_NTH_APPEND1 = prove(
  ``!xs ys n x.
      n < LENGTH xs ==>
      (UPDATE_NTH n x (xs ++ ys) = UPDATE_NTH n x xs ++ ys)``,
  Induct \\ SIMP_TAC std_ss [LENGTH,APPEND,UPDATE_NTH_CONS]
  \\ REPEAT STRIP_TAC \\ Cases_on `n = 0`
  \\ FULL_SIMP_TAC std_ss [APPEND,CONS_11]
  \\ Q.PAT_X_ASSUM `!ys.bbb` MATCH_MP_TAC \\ DECIDE_TAC);

val code_abbrevs_def = Define `
  code_abbrevs cs =
    abbrev_code_for_compile_inst (cs,EL 9 cs) UNION
    abbrev_code_for_compile (cs,EL 8 cs) UNION
    abbrev_code_for_parse (cs,EL 3 cs) UNION
    abbrev_code_for_print (EL 7 cs) UNION
    abbrev_code_for_equal (EL 6 cs) UNION
    abbrev_code_for_cons (EL 5 cs)`;

val SPEC_CODE_ABBREV = prove(
  ``SPEC m p (c INSERT d) q ==> !d2. d SUBSET d2 ==> SPEC m p (c INSERT d2) q``,
  REPEAT STRIP_TAC \\ `(c INSERT d2) = (c INSERT d) UNION d2` suffices_by METIS_TAC [SPEC_ADD_CODE]
  \\ FULL_SIMP_TAC std_ss [EXTENSION,IN_INSERT,IN_UNION,SUBSET_DEF] \\ METIS_TAC []);

val (_,_,sts,_) = prog_x64Lib.x64_tools

fun lisp_pc_s th = let
  val (_,_,_,q) = dest_spec (concl th)
  val c = MOVE_OUT_CONV ``zPC`` THENC MOVE_OUT_CONV ``zS``
  val d = if can dest_star q then I else (RATOR_CONV o RAND_CONV)
  val c = PRE_CONV c THENC POST_CONV (d c)
  in CONV_RULE c th end

val pattern = ``(p1,xs1) INSERT (p2:word64,xs2:word8 list) INSERT s``
fun sort_swap_conv tm = let
  val m = fst (match_term pattern tm)
  val p1 = subst m (mk_var("p1",``:word64``))
  val p2 = subst m (mk_var("p2",``:word64``))
  fun foo tm = if is_var tm then 0 else tm |> cdr |> cdr |> numSyntax.int_of_term
  val _ = foo p2 < foo p1 orelse fail()
  val (x1,s1) = pred_setSyntax.dest_insert tm
  val (x2,s2) = pred_setSyntax.dest_insert s1
  in ISPECL [x1,x2,s2] INSERT_COMM end

fun SORT_CODE th = CONV_RULE (REDEPTH_CONV sort_swap_conv) th

fun fix_code th = th
            |> SIMP_RULE std_ss [INSERT_UNION_INSERT,UNION_EMPTY]
            |> SORT_CODE
            |> MERGE_CODE
            |> MATCH_MP SPEC_CODE_ABBREV |> Q.SPEC `code_abbrevs cs`
            |> CONV_RULE ((RATOR_CONV o RAND_CONV) (SIMP_CONV std_ss
                 [SUBSET_DEF,code_abbrevs_def,NOT_IN_EMPTY,IN_UNION]))
            |> RW []

fun prepare_monop th = th |> fix_code |> RW [SAFE_CAR_def,SAFE_CDR_def]
            |> HIDE_STATUS_RULE true sts |> lisp_pc_s |> DISCH T

fun prepare_binop th = th |> fix_code
            |> HIDE_STATUS_RULE true sts |> lisp_pc_s
            |> Q.INST [`xs`|->`x::xs`]
            |> SIMP_RULE std_ss [SPEC_MOVE_COND,NOT_CONS_NIL,HD,TL,SEP_CLAUSES]
            |> DISCH T;

val LENGTH_EQ_LEMMA = prove(
  ``((1 = LENGTH args) ==> ?arg1. args = [arg1]) /\
    ((2 = LENGTH args) ==> ?arg1 arg2. args = [arg1;arg2])``,
  Cases_on `args` \\ FULL_SIMP_TAC std_ss [LENGTH,ADD1,CONS_11]
  \\ FULL_SIMP_TAC std_ss [DECIDE ``(1 = n + 1) = (n = 0)``,LENGTH_NIL]
  \\ Cases_on `t` \\ FULL_SIMP_TAC std_ss [LENGTH,ADD1,CONS_11]
  \\ FULL_SIMP_TAC std_ss [DECIDE ``(2 = n + 1+1) = (n = 0)``,LENGTH_NIL]);

val X64_LISP_iSTEP_DATA = prove(
  ``!op_name xs1 p1 r1 bc1 xs2 p2 r2 bc2 syms.
      (bc1.code p1 = SOME (iDATA op_name)) /\
      iSTEP (xs1,p1,r1,bc1) (xs2,p2,r2,bc2) ==>
      SPEC X64_MODEL
        (zLISP_BYTECODE (a1,a2,sl,sl1,e,ex,cs,rbp,ddd,cu) (xs1,w + n2w p1,MAP (\n. w + n2w n) r1,bc1) (stack,input,xbp,rstack,amnt,w))
        ((w + n2w p1,bc_ref (p1,syms) (THE (bc1.code p1))) INSERT code_abbrevs cs)
        (zLISP_BYTECODE (a1,a2,sl,sl1,e,ex,cs,rbp,ddd,cu) (xs2,w + n2w p2,MAP (\n. w + n2w n) r2,bc2) (stack,input,xbp,rstack,amnt,w))``,
  ONCE_REWRITE_TAC [iSTEP_cases] \\ SIMP_TAC std_ss []
  \\ REVERSE (REPEAT STRIP_TAC)
  \\ FULL_SIMP_TAC (srw_ss()) [CONTAINS_BYTECODE_def]
  THEN1 (FULL_SIMP_TAC std_ss [zLISP_BYTECODE_def,zLISP_def,
            lisp_inv_def,IS_TRUE_def,SEP_CLAUSES,SPEC_REFL])
  \\ Q.PAT_X_ASSUM `op_name' = op_name` (fn th => FULL_SIMP_TAC std_ss [th])
  \\ FULL_SIMP_TAC std_ss [zLISP_BYTECODE_def] \\ MATCH_MP_TAC SPEC_PRE_DISJ_INTRO
  \\ FULL_SIMP_TAC std_ss [GSYM SPEC_PRE_EXISTS,SEP_CLAUSES,SPEC_MOVE_COND]
  \\ REPEAT STRIP_TAC
  \\ `bc1.instr_length = bc_length` by FULL_SIMP_TAC std_ss [bc_inv_def]
  \\ Cases_on `op_name`
  \\ ASM_SIMP_TAC std_ss [bc_ref_def,BC_STEP_def,bc_length_def,LENGTH,
       GSYM word_add_n2w,WORD_ADD_ASSOC]
  \\ FULL_SIMP_TAC std_ss [EVAL_DATA_OP_def]
  \\ Q.PAT_X_ASSUM `xxx = f` (fn th => FULL_SIMP_TAC std_ss [GSYM th])
  \\ IMP_RES_TAC LENGTH_EQ_LEMMA
  \\ FULL_SIMP_TAC std_ss [REVERSE_DEF,LENGTH,APPEND,HD,TL,EL_CONS]
  THEN1
   (SPEC_EX `arg2` \\ SPEC_EX `x2` \\ SPEC_EX `x3` \\ SPEC_EX `x4`
    \\ MATCH_MP_TAC (prepare_binop X64_BYTECODE_CONS) \\ SIMP_TAC std_ss [])
  THEN1
   (SPEC_EX `Sym "NIL"` \\ SPEC_EX `x2` \\ SPEC_EX `x3` \\ SPEC_EX `x4`
    \\ MATCH_MP_TAC SPEC_REMOVE_POST
    \\ SIMP_TAC std_ss [LISP_EQUAL_def] \\ ONCE_REWRITE_TAC [EQ_SYM_EQ]
    \\ MATCH_MP_TAC (prepare_binop X64_BYTECODE_EQUAL) \\ SIMP_TAC std_ss [])
  THEN1
   (SPEC_EX `NFIX arg2` \\ SPEC_EX `x2` \\ SPEC_EX `x3` \\ SPEC_EX `x4`
    \\ MATCH_MP_TAC SPEC_REMOVE_POST
    \\ MATCH_MP_TAC (prepare_binop X64_BYTECODE_LESS) \\ SIMP_TAC std_ss [])
  THEN1
   (SPEC_EX `Sym "NIL"` \\ SPEC_EX `Sym "NIL"`
    \\ SPEC_EX `Sym "NIL"` \\ SPEC_EX `x4`
    \\ MATCH_MP_TAC SPEC_REMOVE_POST
    \\ MATCH_MP_TAC (prepare_binop X64_BYTECODE_SYMBOL_LESS)
    \\ SIMP_TAC std_ss [])
  THEN1
   (SPEC_EX `NFIX arg1` \\ SPEC_EX `x2` \\ SPEC_EX `x3` \\ SPEC_EX `x4`
    \\ MATCH_MP_TAC (prepare_binop X64_BYTECODE_ADD) \\ SIMP_TAC std_ss [])
  THEN1
   (SPEC_EX `NFIX arg2` \\ SPEC_EX `x2` \\ SPEC_EX `x3` \\ SPEC_EX `x4`
    \\ MATCH_MP_TAC SPEC_REMOVE_POST
    \\ MATCH_MP_TAC (prepare_binop X64_BYTECODE_SUB) \\ SIMP_TAC std_ss [])
  THEN1
   (SPEC_EX `x1` \\ SPEC_EX `x2` \\ SPEC_EX `x3` \\ SPEC_EX `x4`
    \\ MATCH_MP_TAC SPEC_REMOVE_POST
    \\ MATCH_MP_TAC (prepare_monop X64_BYTECODE_CONSP) \\ SIMP_TAC std_ss [])
  THEN1
   (SPEC_EX `x1` \\ SPEC_EX `x2` \\ SPEC_EX `x3` \\ SPEC_EX `x4`
    \\ MATCH_MP_TAC SPEC_REMOVE_POST
    \\ MATCH_MP_TAC (prepare_monop X64_BYTECODE_NATP) \\ SIMP_TAC std_ss [])
  THEN1
   (SPEC_EX `x1` \\ SPEC_EX `x2` \\ SPEC_EX `x3` \\ SPEC_EX `x4`
    \\ MATCH_MP_TAC SPEC_REMOVE_POST
    \\ MATCH_MP_TAC (prepare_monop X64_BYTECODE_SYMBOLP) \\ SIMP_TAC std_ss [])
  THEN1
   (SPEC_EX `x1` \\ SPEC_EX `x2` \\ SPEC_EX `x3` \\ SPEC_EX `x4`
    \\ MATCH_MP_TAC SPEC_REMOVE_POST
    \\ MATCH_MP_TAC (prepare_monop X64_BYTECODE_CAR) \\ SIMP_TAC std_ss [])
  THEN1
   (SPEC_EX `x1` \\ SPEC_EX `x2` \\ SPEC_EX `x3` \\ SPEC_EX `x4`
    \\ MATCH_MP_TAC SPEC_REMOVE_POST
    \\ MATCH_MP_TAC (prepare_monop X64_BYTECODE_CDR) \\ SIMP_TAC std_ss []));

val ipop = X64_BYTECODE_POP
           |> fix_code |> SIMP_RULE (std_ss++sep_cond_ss) [SPEC_MOVE_COND];

val ipops = X64_BYTECODE_POPS
            |> fix_code |> SIMP_RULE (std_ss++sep_cond_ss) [SPEC_MOVE_COND]
            |> SIMP_RULE std_ss [w2w_def] |> DISCH ``w2n (j:word30) = LENGTH (ys:SExp list)``
            |> SIMP_RULE std_ss [] |> SIMP_RULE std_ss [GSYM w2w_def]
            |> Q.INST [`xs`|->`ys++zs`] |> SIMP_RULE std_ss [LENGTH_APPEND]
            |> RW [rich_listTheory.BUTFIRSTN_LENGTH_APPEND]
            |> Q.INST [`j`|->`n2w (LENGTH (ys:SExp list))`]

val iload = X64_BYTECODE_LOAD
            |> fix_code |> SIMP_RULE (std_ss++sep_cond_ss) [SPEC_MOVE_COND]
            |> DISCH ``(w2w:29 word->word32) j = n2w i``
            |> SIMP_RULE std_ss [word_mul_n2w,AND_IMP_INTRO]
            |> Q.INST [`j`|->`n2w i`,`x0`|->`HD (xs++y::ys)`,`xs`|->`TL (xs++y::ys)`]
            |> RW [HD_TL]
            |> DISCH ``EL (w2n ((n2w i):29 word)) (xs ++ y::ys:SExp list) = EL i xs``
            |> SIMP_RULE std_ss [word_mul_n2w,AND_IMP_INTRO]

val istore = X64_BYTECODE_STORE
            |> fix_code |> SIMP_RULE (std_ss++sep_cond_ss) [SPEC_MOVE_COND]
            |> DISCH ``(w2w:29 word->word32) j = n2w i``
            |> DISCH ``(w2n:29 word->num) j = i``
            |> SIMP_RULE std_ss [word_mul_n2w,GSYM AND_IMP_INTRO]
            |> Q.INST [`j`|->`n2w i`,`xs`|->`xs++y::ys`]
            |> SIMP_RULE std_ss [word_mul_n2w,AND_IMP_INTRO,GSYM LENGTH_NIL]
            |> DISCH ``UPDATE_NTH i x0 (xs ++ y::ys) = UPDATE_NTH i x0 xs ++ y::ys:SExp list``
            |> SIMP_RULE std_ss [word_mul_n2w,AND_IMP_INTRO,GSYM LENGTH_NIL]

val ireturn = X64_LISP_RET |> fix_code
            |> (fn th => SPEC_FRAME_RULE th ``~zS``) |> DISCH T

val ifail = X64_LISP_RAW_RUNTIME_ERROR |> fix_code |> DISCH T

val iprint =
  SPEC_COMPOSE_RULE [X64_LISP_PRINT_SEXP,X64_LISP_PRINT_NEWLINE]
  |> fix_code |> SIMP_RULE std_ss [IO_WRITE_APPEND]
  |> Q.INST [`io`|->`IO_STREAMS input bc1.io_out`]
  |> SIMP_RULE std_ss [IO_WRITE_def,APPEND_ASSOC]
  |> DISCH T

val sw2sw_2compl = blastLib.BBLAST_PROVE
  ``!w:word32. w <+ 0x80000000w ==> (sw2sw (-w) = -(sw2sw w):word64)``;

val IGNORE_SIGN_EXTEND = prove(
  ``!m n k. k < 2**n /\ n <= m ==> (SIGN_EXTEND (SUC n) m k = k)``,
  SIMP_TAC std_ss [SIGN_EXTEND_def,LET_DEF] \\ REPEAT STRIP_TAC
  \\ ASM_SIMP_TAC std_ss [bitTheory.BIT_def,bitTheory.BITS_THM]
  \\ ASM_SIMP_TAC std_ss [LESS_DIV_EQ_ZERO]
  \\ ASM_SIMP_TAC std_ss [EXP] \\ DECIDE_TAC);

val ADDRESS_LEMMA = prove(
  ``!k. k < 1000 ==>
    p1 < 1073741824 /\ p2 < 1073741824 ==>
    (w + n2w p1 + n2w (k + SIGN_EXTEND 32 64 (w2n (n2w p2 - n2w p1 - (n2w k):word32))) =
     w + n2w p2:word64)``,
  STRIP_TAC \\ STRIP_TAC \\ SIMP_TAC std_ss [GSYM WORD_SUB_PLUS,word_add_n2w]
  \\ SIMP_TAC std_ss [word_arith_lemma2]
  \\ REVERSE (Cases_on `p2 < p1 + k`) \\ ASM_SIMP_TAC std_ss [] THEN1
   (REPEAT STRIP_TAC \\ SIMP_TAC (std_ss++SIZES_ss) [w2n_n2w]
    \\ `(p2 - (p1 + k)) < 4294967296` by DECIDE_TAC
    \\ ASM_SIMP_TAC std_ss [GSYM word_add_n2w]
    \\ `p2 - (p1 + k) < 2**31` by (SIMP_TAC std_ss [] \\ DECIDE_TAC)
    \\ IMP_RES_TAC (Q.SPEC `64` IGNORE_SIGN_EXTEND)
    \\ FULL_SIMP_TAC std_ss [ADD1,word_arith_lemma1]
    \\ AP_TERM_TAC \\ AP_TERM_TAC \\ DECIDE_TAC)
  \\ REPEAT STRIP_TAC
  \\ ASM_SIMP_TAC std_ss [GSYM word_add_n2w,
      INST_TYPE [``:'a``|->``:32``,``:'b``|->``:64``] sw2sw_def
      |> SIMP_RULE (std_ss++SIZES_ss) [] |> GSYM]
  \\ `p1 + k - p2 < 2**31 /\ (p1 + k - p2) < 4294967296` by (SIMP_TAC std_ss [] \\ DECIDE_TAC)
  \\ `n2w (p1 + k - p2) <+ 0x80000000w:word32` by
         (FULL_SIMP_TAC (std_ss++SIZES_ss) [word_lo_n2w])
  \\ IMP_RES_TAC sw2sw_2compl \\ ASM_SIMP_TAC std_ss []
  \\ IMP_RES_TAC (Q.SPEC `64` IGNORE_SIGN_EXTEND)
  \\ FULL_SIMP_TAC std_ss [ADD1,word_arith_lemma1]
  \\ ASM_SIMP_TAC (std_ss++SIZES_ss) [sw2sw_def,w2n_n2w]
  \\ SIMP_TAC std_ss [GSYM WORD_ADD_ASSOC] \\ AP_TERM_TAC
  \\ SIMP_TAC std_ss [WORD_ADD_ASSOC,word_add_n2w]
  \\ SIMP_TAC std_ss [GSYM word_sub_def]
  \\ `~(p1 + k < p1 + k - p2)`by DECIDE_TAC
  \\ ASM_SIMP_TAC std_ss [word_arith_lemma2]
  \\ AP_TERM_TAC \\ DECIDE_TAC);

val JUMP_ADDRESS_LEMMA = SIMP_RULE std_ss [] (Q.SPEC `6` ADDRESS_LEMMA);
val JNIL_ADDRESS_LEMMA = SIMP_RULE std_ss [] (Q.SPEC `21` ADDRESS_LEMMA);
val JNIL_ADDRESS_LEMMA2 = SIMP_RULE std_ss [] (Q.SPEC `14` ADDRESS_LEMMA);

val (ijump_raw,ijump) = let
  val ((th,_,_),_) = prog_x64Lib.x64_spec "48E9"
  val th = Q.INST [`imm32`|->`n2w p2 - n2w p1 - 6w`,`rip`|->`w + n2w p1`] th
           |> DISCH ``p1 < 1073741824 /\ p2 < 1073741824``
           |> SIMP_RULE std_ss [JUMP_ADDRESS_LEMMA]
           |> RW [GSYM SPEC_MOVE_COND]
           |> MATCH_MP SPEC_FRAME
           |> Q.SPEC `zLISP (a1,a2,sl,sl1,e,ex,cs,ok,rbp,ddd)
                        (x0,x1,x2,x3,x4,x5,xs,io,xbp,qs,code,amnt) * ~zS`
           |> lisp_pc_s |> SIMP_RULE (std_ss++sep_cond_ss) [SPEC_MOVE_COND]
  val th2 = DISCH_ALL (fix_code (UNDISCH th))
  in (th,th2) end

val icall = let
  val th = X64_LISP_CALL_IMM
  val th = fix_code th
  val th = Q.INST [`imm32`|->`n2w p2 - n2w p1 - 6w`,`p`|->`w + n2w p1`] th
           |> DISCH ``p1 < 1073741824 /\ p2 < 1073741824``
           |> SIMP_RULE std_ss [JUMP_ADDRESS_LEMMA]
           |> RW [GSYM SPEC_MOVE_COND]
           |> MATCH_MP SPEC_FRAME
           |> Q.SPEC `~zS`
           |> lisp_pc_s |> SIMP_RULE (std_ss++sep_cond_ss) [SPEC_MOVE_COND]
  in th end;

val inum = SPEC_COMPOSE_RULE [X64_LISP_PUSH_0,X64_LISP_ASSIGN_ANY_VAL]
  |> fix_code |> RW [SPEC_MOVE_COND]

val ilookup = X64_LISP_CONST_LOAD
              |> MATCH_MP SPEC_FRAME |> Q.SPEC `~zS`
              |> fix_code |> lisp_pc_s
              |> SIMP_RULE (std_ss++sep_cond_ss) [SPEC_MOVE_COND]
              |> Q.INST [`x0`|->`Val x`] |> SIMP_RULE std_ss [getVal_def,isVal_def]

val icall_sym = X64_BYTECODE_CALL_SYM |> fix_code |> lisp_pc_s
              |> Q.INST [`p`|->`w + n2w p1`]
              |> SIMP_RULE (std_ss++sep_cond_ss) [SPEC_MOVE_COND]
              |> DISCH_ALL |> RW [AND_IMP_INTRO]

val ijump_sym = X64_BYTECODE_JUMP_SYM |> fix_code |> lisp_pc_s
              |> Q.INST [`p`|->`w + n2w p1`]
              |> SIMP_RULE (std_ss++sep_cond_ss) [SPEC_MOVE_COND]

val (ijnil1,ijnil2) = let
  fun the (SOME x) = x | the _ = fail()
  val ((th1,_,_),x) = x64_spec "480F84"
  val (th2,_,_) = the x
  val th1 = SPEC_COMPOSE_RULE [X64_LISP_MOVE10, X64_BYTECODE_POP,
                               X64_LISP_TEST_SYM_0_1,th1]
  val th1 = RW [precond_def] th1 |> Q.INST [`xs`|->`x::xs`]
            |> HIDE_STATUS_RULE true sts |> lisp_pc_s |> fix_code
            |> SIMP_RULE std_ss [HD,TL,NOT_CONS_NIL,SEP_CLAUSES,ADD_ASSOC]
            |> Q.INST [`imm32`|->`n2w p2 - n2w p1 - 21w`,`p`|->`w + n2w p1`]
            |> DISCH ``p1 < 1073741824 /\ p2 < 1073741824``
            |> SIMP_RULE (std_ss++sep_cond_ss) [JNIL_ADDRESS_LEMMA,SPEC_MOVE_COND]
            |> RW [AND_IMP_INTRO]
  val th2 = SPEC_COMPOSE_RULE [X64_LISP_MOVE10, X64_BYTECODE_POP,
                               X64_LISP_TEST_SYM_0_1,th2]
  val th2 = RW [precond_def] th2 |> Q.INST [`xs`|->`x::xs`]
            |> HIDE_STATUS_RULE true sts |> lisp_pc_s |> fix_code
            |> SIMP_RULE std_ss [HD,TL,NOT_CONS_NIL,SEP_CLAUSES,ADD_ASSOC]
            |> Q.INST [`imm32`|->`n2w p2 - n2w p1 - 21w`,`p`|->`w + n2w p1`]
            |> SIMP_RULE (std_ss++sep_cond_ss) [JNIL_ADDRESS_LEMMA,SPEC_MOVE_COND]
  in (th1,th2) end;

val BC_PRINT_LEMMA = prove(
  ``(bc_state_tree (BC_PRINT bc s) = bc_state_tree bc) /\
    ((BC_PRINT bc s).code = bc.code) /\
    ((BC_PRINT bc s).code_end = bc.code_end) /\
    (bc_inv (BC_PRINT bc s) = bc_inv bc)``,
  SIMP_TAC (srw_ss()) [bc_state_tree_def,BC_PRINT_def,const_tree_def,
    bc_inv_def,BC_CODE_OK_def]);

val X64_LISP_iSTEP_MOST_CASES = prove(
  ``bc_symbols_ok syms [THE (bc1.code p1)] /\
    ~(bc1.code p1 = SOME iCOMPILE) /\
    (!s. ~(bc1.code p1 = SOME (iCONST_SYM s))) /\
    p1 < 1073741824 /\
    iSTEP (xs1,p1,r1,bc1) (xs2,p2,r2,bc2) ==>
    SPEC X64_MODEL
      (zLISP_BYTECODE (a1,a2,sl,sl1,e,ex,cs,rbp,ddd,cu) (xs1,EL 4 cs + n2w p1,MAP (\n. EL 4 cs + n2w n) r1,bc1) (stack,input,xbp,rstack,amnt,EL 4 cs))
      ((EL 4 cs + n2w p1,bc_ref (p1,syms) (THE (bc1.code p1))) INSERT code_abbrevs cs)
      (zLISP_BYTECODE (a1,a2,sl,sl1,e,ex,cs,rbp,ddd,cu) (xs2,EL 4 cs + n2w p2,MAP (\n. EL 4 cs + n2w n) r2,bc2) (stack,input,xbp,rstack,amnt,EL 4 cs))``,
  Cases_on `?op_name. bc1.code p1 = SOME (iDATA op_name)`
  THEN1 (METIS_TAC [X64_LISP_iSTEP_DATA])
  \\ ONCE_REWRITE_TAC [iSTEP_cases] \\ SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [BC_STEP_def,CONTAINS_BYTECODE_def,bc_ref_def]
  \\ SIMP_TAC std_ss [zLISP_BYTECODE_def]
  \\ REPEAT STRIP_TAC \\ MATCH_MP_TAC SPEC_PRE_DISJ_INTRO
  \\ SIMP_TAC std_ss [GSYM SPEC_PRE_EXISTS,HD,TL,APPEND,SPEC_MOVE_COND]
  \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [bc_symbols_ok_def,SEP_CLAUSES]
  THEN1 (* pop *)
   (BYTECODE_TAC \\ MATCH_MP_TAC SPEC_REMOVE_POST \\ MATCH_MP_TAC ipop
    \\ Cases_on `xs2` \\ SIMP_TAC (srw_ss()) [])
  THEN1 (* pops *)
   (BYTECODE_TAC \\ SIMP_TAC std_ss [GSYM APPEND_ASSOC]
    \\ MATCH_MP_TAC SPEC_REMOVE_POST \\ MATCH_MP_TAC ipops
    \\ FULL_SIMP_TAC (std_ss++SIZES_ss) [w2n_n2w])
  THEN1 (* num *)
   (BYTECODE_TAC \\ SIMP_TAC std_ss [word_add_n2w]
    \\ Cases_on `xs1 ++ Sym "NIL"::stack`
    THEN1 (Cases_on `xs1` \\ FULL_SIMP_TAC (srw_ss()) [])
    \\ FULL_SIMP_TAC std_ss [HD,TL]
    \\ MATCH_MP_TAC inum \\ ASM_SIMP_TAC std_ss [])
  THEN1 (* sym *)
   (FULL_SIMP_TAC (srw_ss()) [])
  THEN1 (* lookup *)
   (BYTECODE_TAC \\ MATCH_MP_TAC SPEC_REMOVE_POST
    \\ MATCH_MP_TAC ilookup \\ ASM_SIMP_TAC std_ss [])
  THEN1 (* data *)
   (FULL_SIMP_TAC (srw_ss()) [])
  THEN1 (* iload *)
   (BYTECODE_TAC \\ MATCH_MP_TAC iload
    \\ ASM_SIMP_TAC (std_ss++SIZES_ss) [w2w_def,w2n_n2w,LENGTH_APPEND]
    \\ ASM_SIMP_TAC std_ss [rich_listTheory.EL_APPEND1] \\ DECIDE_TAC)
  THEN1 (* istore *)
   (BYTECODE_TAC \\ MATCH_MP_TAC SPEC_REMOVE_POST \\ MATCH_MP_TAC istore
    \\ ASM_SIMP_TAC (std_ss++SIZES_ss) [w2w_def,w2n_n2w,LENGTH_APPEND]
    \\ ASM_SIMP_TAC std_ss [LENGTH_UPDATE_NTH,LENGTH_APPEND,LENGTH,ADD1]
    \\ ASM_SIMP_TAC std_ss [UPDATE_NTH_APPEND1] \\ DECIDE_TAC)
  THEN1 (* ijump *)
   (BYTECODE_TAC \\ MATCH_MP_TAC SPEC_REMOVE_POST
    \\ MATCH_MP_TAC ijump \\ ASM_SIMP_TAC std_ss [])
  THEN1 (* icall *)
   (BYTECODE_TAC \\ MATCH_MP_TAC SPEC_REMOVE_POST
    \\ SIMP_TAC std_ss [MAP,GSYM word_add_n2w,WORD_ADD_ASSOC,APPEND]
    \\ MATCH_MP_TAC icall \\ ASM_SIMP_TAC std_ss [])
  THEN1 (* ireturn *)
   (BYTECODE_TAC \\ MATCH_MP_TAC SPEC_REMOVE_POST
    \\ FULL_SIMP_TAC std_ss [MAP,APPEND]
    \\ MATCH_MP_TAC ireturn \\ SIMP_TAC std_ss [])
  THEN1 (* ijnil *)
   (`bc1.instr_length = bc_length` by FULL_SIMP_TAC std_ss [bc_inv_def]
    \\ FULL_SIMP_TAC std_ss [bc_length_def,bc_ref_def,LENGTH,GSYM word_add_n2w,WORD_ADD_ASSOC,IMMEDIATE32_def,APPEND]
    \\ HO_MATCH_MP_TAC SPEC_PULL_EXISTS \\ Q.EXISTS_TAC `x`
    \\ HO_MATCH_MP_TAC SPEC_PULL_EXISTS \\ Q.EXISTS_TAC `x2`
    \\ HO_MATCH_MP_TAC SPEC_PULL_EXISTS \\ Q.EXISTS_TAC `x3`
    \\ HO_MATCH_MP_TAC SPEC_PULL_EXISTS \\ Q.EXISTS_TAC `x4`
    \\ Cases_on `xs2 ++ Sym "NIL"::stack`
    THEN1 (Cases_on `xs2` \\ FULL_SIMP_TAC (srw_ss()) [])
    \\ FULL_SIMP_TAC std_ss [HD,TL,MAP,GSYM word_add_n2w,WORD_ADD_ASSOC]
    \\ MATCH_MP_TAC SPEC_REMOVE_POST
    \\ Cases_on `x = Sym "NIL"` \\ FULL_SIMP_TAC std_ss []
    THEN1 (MATCH_MP_TAC (GEN_ALL ijnil1) \\ ASM_SIMP_TAC std_ss [])
    \\ FULL_SIMP_TAC std_ss [GSYM word_add_n2w,WORD_ADD_ASSOC]
    \\ MATCH_MP_TAC (GEN_ALL ijnil2) \\ ASM_SIMP_TAC std_ss [])
  THEN1 (* ijump_sym *)
   (`bc1.instr_length = bc_length` by FULL_SIMP_TAC std_ss [bc_inv_def]
    \\ FULL_SIMP_TAC std_ss [bc_length_def,bc_ref_def,LENGTH,GSYM word_add_n2w,WORD_ADD_ASSOC,IMMEDIATE32_def,APPEND]
    \\ HO_MATCH_MP_TAC SPEC_PULL_EXISTS \\ Q.EXISTS_TAC `Val p2`
    \\ HO_MATCH_MP_TAC SPEC_PULL_EXISTS \\ Q.EXISTS_TAC `Val p2`
    \\ HO_MATCH_MP_TAC SPEC_PULL_EXISTS \\ Q.EXISTS_TAC `Val n`
    \\ HO_MATCH_MP_TAC SPEC_PULL_EXISTS \\ Q.EXISTS_TAC `x4`
    \\ Cases_on `xs2 ++ Sym "NIL"::stack`
    THEN1 (Cases_on `xs2` \\ FULL_SIMP_TAC (srw_ss()) [])
    \\ FULL_SIMP_TAC std_ss [HD,TL,MAP,GSYM word_add_n2w,WORD_ADD_ASSOC]
    \\ MATCH_MP_TAC (GEN_ALL ijump_sym) \\ ASM_SIMP_TAC std_ss [])
  THEN1 (* icall_sym *)
   (`bc1.instr_length = bc_length` by FULL_SIMP_TAC std_ss [bc_inv_def]
    \\ FULL_SIMP_TAC std_ss [bc_length_def,bc_ref_def,LENGTH,GSYM word_add_n2w,WORD_ADD_ASSOC,IMMEDIATE32_def,APPEND]
    \\ HO_MATCH_MP_TAC SPEC_PULL_EXISTS \\ Q.EXISTS_TAC `Val p2`
    \\ HO_MATCH_MP_TAC SPEC_PULL_EXISTS \\ Q.EXISTS_TAC `Val p2`
    \\ HO_MATCH_MP_TAC SPEC_PULL_EXISTS \\ Q.EXISTS_TAC `Val n`
    \\ HO_MATCH_MP_TAC SPEC_PULL_EXISTS \\ Q.EXISTS_TAC `x4`
    \\ Cases_on `xs2 ++ Sym "NIL"::stack`
    THEN1 (Cases_on `xs2` \\ FULL_SIMP_TAC (srw_ss()) [])
    \\ FULL_SIMP_TAC std_ss [HD,TL,MAP,GSYM word_add_n2w,WORD_ADD_ASSOC,APPEND]
    \\ MATCH_MP_TAC (GEN_ALL icall_sym) \\ ASM_SIMP_TAC std_ss [])
  THEN1 (* ifail *)
   (BYTECODE_TAC \\ ONCE_REWRITE_TAC [SEP_DISJ_COMM]
    \\ MATCH_MP_TAC SPEC_REMOVE_POST
    \\ MATCH_MP_TAC ifail \\ SIMP_TAC std_ss [])
  THEN1 (* iprint *)
   (BYTECODE_TAC \\ ASM_SIMP_TAC std_ss [BC_PRINT_LEMMA,SEP_CLAUSES]
    \\ SIMP_TAC (srw_ss()) [BC_PRINT_def] \\ MATCH_MP_TAC iprint
    \\ SIMP_TAC std_ss [])
  THEN1 (* ok false *)
   (FULL_SIMP_TAC std_ss [zLISP_BYTECODE_def,zLISP_def,
      lisp_inv_def,IS_TRUE_def,SEP_CLAUSES,SPEC_REFL,SPEC_FALSE_PRE]));

val X64_LISP_iSTEP_LAST_RETURN_LEMMA = prove(
  ``(bc1.code 0 = SOME iRETURN) ==>
    SPEC X64_MODEL
      (zLISP_BYTECODE (a1,a2,sl,sl1,e,ex,cs,rbp,ddd,cu) (xs1,EL 4 cs + 0w,[],bc1) (stack,input,xbp,r::rstack,amnt,EL 4 cs))
      ((EL 4 cs + 0w,bc_ref (p1,syms) (THE (bc1.code 0))) INSERT code_abbrevs cs)
      (zLISP_BYTECODE (a1,a2,sl,sl1,e,ex,cs,rbp,ddd,cu) (xs1,r,[],bc1) (stack,input,xbp,rstack,amnt,EL 4 cs))``,
  FULL_SIMP_TAC std_ss [BC_STEP_def,CONTAINS_BYTECODE_def,bc_ref_def]
  \\ SIMP_TAC std_ss [zLISP_BYTECODE_def]
  \\ REPEAT STRIP_TAC \\ MATCH_MP_TAC SPEC_PRE_DISJ_INTRO
  \\ SIMP_TAC std_ss [GSYM SPEC_PRE_EXISTS,HD,TL,APPEND,SPEC_MOVE_COND]
  \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [bc_symbols_ok_def,SEP_CLAUSES]
  \\ BYTECODE_TAC \\ MATCH_MP_TAC SPEC_REMOVE_POST
  \\ FULL_SIMP_TAC std_ss [MAP,APPEND]
  \\ MATCH_MP_TAC ireturn \\ SIMP_TAC std_ss []);

val SPEC_X64_STRENGTHEN_CODE = prove(
  ``SPEC X64_MODEL p ((w,xs) INSERT dd) q ==>
    SPEC X64_MODEL p ((w,xs) INSERT dd) q``,
  SIMP_TAC std_ss []);

val SPEC_PRE_DISJ_REMOVE = prove(
  ``SPEC x (p \/ r) c (q \/ r) = SPEC x p c (q \/ r)``,
  SIMP_TAC std_ss [SPEC_PRE_DISJ] \\ REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC
  \\ ASM_SIMP_TAC std_ss []
  \\ MATCH_MP_TAC (SIMP_RULE std_ss [PULL_FORALL_IMP,AND_IMP_INTRO] SPEC_WEAKEN)
  \\ Q.EXISTS_TAC `r` \\ SIMP_TAC std_ss [SPEC_REFL]
  \\ SIMP_TAC std_ss [SEP_IMP_def,SEP_DISJ_def]);

val cond_EXISTS = prove(
  ``cond (?x. P x) = SEP_EXISTS x. cond (P x)``,
  SIMP_TAC std_ss [cond_def,SEP_EXISTS,FUN_EQ_THM] \\ METIS_TAC []);

val code_mem_BOUND = prove(
  ``!bs bc n. code_ptr bc + code_length bs <= n ==>
              (code_mem (WRITE_CODE bc bs) n = code_mem bc n)``,
  Induct \\ Cases_on `bc` \\ Cases_on `p`
  \\ SIMP_TAC std_ss [code_length_def,WRITE_CODE_def,code_ptr_def] \\ STRIP_TAC
  \\ POP_ASSUM (ASSUME_TAC o Q.SPEC `BC_CODE ((r =+ SOME h) q,r + bc_length h)`)
  \\ FULL_SIMP_TAC std_ss [code_ptr_def,ADD_ASSOC] \\ REPEAT STRIP_TAC
  \\ RES_TAC \\ SIMP_TAC std_ss [code_mem_def,APPLY_UPDATE_THM]
  \\ `0 < bc_length h` by
       (Cases_on `h` \\ EVAL_TAC \\ Cases_on `l` \\ EVAL_TAC)
  \\ `~(r = n)` by DECIDE_TAC \\ FULL_SIMP_TAC std_ss []);

val code_length_LESS = prove(
  ``!bs. (code_mem (WRITE_CODE (BC_CODE ((\x. NONE),0)) bs) p = SOME x) ==>
         p < code_length bs``,
  REPEAT STRIP_TAC \\ CCONTR_TAC \\ Q.PAT_X_ASSUM `xx = yy` MP_TAC
  \\ `code_ptr (BC_CODE ((\x. NONE),0)) + code_length bs <= p` by
        (FULL_SIMP_TAC std_ss [code_ptr_def] \\ DECIDE_TAC)
  \\ IMP_RES_TAC code_mem_BOUND \\ ASM_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC std_ss [code_mem_def]);

val WRITE_CODE_APPEND = prove(
  ``!xs ys x. WRITE_CODE x (xs ++ ys) = WRITE_CODE (WRITE_CODE x xs) ys``,
  Induct \\ Cases_on `x` \\ Cases_on `p`
  \\ ASM_SIMP_TAC std_ss [WRITE_CODE_def,APPEND]);

val WRITE_CODE_MEM_LEMMA = prove(
  ``!bs m l m1 l1.
       (WRITE_CODE (BC_CODE (m,l)) bs = BC_CODE (m1,l1)) ==>
       !p x. (m1 p = SOME x) ==> MEM x bs \/ (m p = SOME x)``,
  Induct \\ SIMP_TAC (srw_ss()) [MEM,WRITE_CODE_def]
  \\ REPEAT STRIP_TAC \\ RES_TAC \\ FULL_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC std_ss [APPLY_UPDATE_THM]
  \\ Cases_on `l = p` \\ FULL_SIMP_TAC std_ss []);

val WRITE_CODE_MEM = prove(
  ``!bs. (code_mem (WRITE_CODE (BC_CODE ((\x. NONE),0)) bs) p = SOME x) ==> MEM x bs``,
  REPEAT STRIP_TAC
  \\ Cases_on `WRITE_CODE (BC_CODE ((\x. NONE),0)) bs` \\ Cases_on `p'`
  \\ MP_TAC (Q.SPECL [`bs`,`\x.NONE`,`0`,`q`,`r`] WRITE_CODE_MEM_LEMMA)
  \\ FULL_SIMP_TAC std_ss [code_mem_def] \\ METIS_TAC []);

val MEM_bc_symbols_ok = prove(
  ``!xs. MEM x xs /\ bc_symbols_ok sym xs ==> bc_symbols_ok sym [x]``,
  Induct \\ SIMP_TAC std_ss [MEM] \\ REPEAT STRIP_TAC
  \\ Cases_on `h` \\ FULL_SIMP_TAC std_ss [bc_symbols_ok_def]);

val bc_symbols_ok_IMP = prove(
  ``bc_symbols_ok sym bs /\
    (WRITE_CODE (BC_CODE ((\x. NONE),0)) bs = BC_CODE (bc1.code,bc1.code_end)) /\
    (bc1.code p1 = SOME x) ==>
    bc_symbols_ok sym [x]``,
  REPEAT STRIP_TAC \\ MP_TAC (Q.INST [`p`|->`p1`] (SPEC_ALL WRITE_CODE_MEM))
  \\ ASM_SIMP_TAC std_ss [code_mem_def] \\ METIS_TAC [MEM_bc_symbols_ok]);

val SPEC_SUBSET_CODE_UNION = prove(
  ``!x p c q. SPEC x p (c UNION d) q ==>
              !c'. c SUBSET c' ==> SPEC x p (c' UNION d) q``,
  REPEAT STRIP_TAC
  \\ `(c UNION d) SUBSET (c' UNION d)` by
     (FULL_SIMP_TAC std_ss [SUBSET_DEF,IN_UNION] \\ METIS_TAC [])
  \\ METIS_TAC [SPEC_SUBSET_CODE]);

val CODE_POOL_UNION_LEMMA = prove(
  ``!c1 c2 i.
       ?r. CODE_POOL i c1 * CODE_POOL i c2 = CODE_POOL i (c1 UNION c2) * r``,
  REPEAT STRIP_TAC \\ REWRITE_TAC [CODE_POOL_def,IMAGE_UNION,BIGUNION_UNION,STAR_def]
  \\ Q.EXISTS_TAC `cond (DISJOINT (BIGUNION (IMAGE i c1)) (BIGUNION (IMAGE i c2)))`
  \\ SIMP_TAC std_ss [SPLIT_def,cond_def,UNION_EMPTY,DISJOINT_EMPTY]
  \\ FULL_SIMP_TAC std_ss [FUN_EQ_THM] \\ METIS_TAC []);

val SPEC_CODE_UNION = store_thm("SPEC_CODE_UNION",
  ``!x p c d q. SPEC x p (c UNION d) q ==>
                SPEC x (CODE_POOL ((FST (SND (SND x))):'a -> 'b -> bool) c * p) d
                       (CODE_POOL (FST (SND (SND x))) c * q)``,
  STRIP_TAC \\ `?x1 x2 x3 x4 x5. x = (x1,x2,x3,x4,x5)` by METIS_TAC [PAIR]
  \\ FULL_SIMP_TAC std_ss [SPEC_def,RUN_def] \\ REPEAT STRIP_TAC
  \\ MP_TAC (Q.ISPEC `x3:'a->'b->bool` (Q.SPECL [`c`,`d`] (GSYM CODE_POOL_UNION_LEMMA)))
  \\ REPEAT STRIP_TAC
  \\ Q.PAT_X_ASSUM `!state. bbb` (MP_TAC o Q.SPECL [`state`,`r * r'`])
  \\ FULL_SIMP_TAC std_ss [AC STAR_ASSOC STAR_COMM]);

val SPEC_zCODE_SPLIT_UNION = prove(
  ``SPEC X64_MODEL p (c UNION d) q ==>
    SPEC X64_MODEL (p * zCODE c) d (q * zCODE c)``,
  SIMP_TAC std_ss [X64_MODEL_def,zCODE_def] \\ REPEAT STRIP_TAC
  \\ IMP_RES_TAC SPEC_CODE_UNION \\ FULL_SIMP_TAC (std_ss++star_ss) []);

val SPEC_DERIVE = prove(
  ``SPEC m p c q /\ SEP_IMP p1 p /\ SEP_IMP q q1 ==> SPEC m p1 c q1``,
  METIS_TAC [SPEC_STRENGTHEN,SPEC_WEAKEN]);

fun INST_EXISTS_TAC (hyps,goal) = let
  val (v,tm) = dest_exists goal
  val w = mk_var(implode (filter (fn x => x <> #"'") (explode (fst (dest_var v)))), type_of v)
  in EXISTS_TAC w (hyps,goal) end handle HOL_ERR _ => NO_TAC (hyps,goal)

val SEP_IMP_LEMMA = prove(
  ``SEP_IMP (p1 * m) q1 /\ SEP_IMP (p2 * m) q2 ==>
    SEP_IMP ((p1 \/ p2) * m) (q1 \/ q2)``,
  SIMP_TAC std_ss [SEP_CLAUSES]
  \\ SIMP_TAC std_ss [SEP_IMP_def,SEP_DISJ_def] \\ METIS_TAC []);

val SEP_EXISTS_DISJ_REV = prove(
  ``(SEP_EXISTS x. p x \/ q) = (SEP_EXISTS x. p x) \/ q``,
  SIMP_TAC std_ss [SEP_CLAUSES]);

val WRITE_CODE_IMP_LENGTH = prove(
  ``!bs n x. (WRITE_CODE (BC_CODE (x,n)) bs = BC_CODE (q,p)) ==>
             (p = n + code_length bs)``,
  Induct \\ SIMP_TAC (srw_ss()) [WRITE_CODE_def,code_length_def]
  \\ REPEAT STRIP_TAC \\ RES_TAC \\ DECIDE_TAC);

val code_mem_SPLIT = prove(
  ``!bs n p1.
      ((code_mem (WRITE_CODE (BC_CODE ((\x.NONE),n)) bs)) p1 = SOME x) ==>
      ?bs1 bs2. (bs = bs1 ++ [x] ++ bs2) /\ (p1 = code_length bs1 + n)``,
  HO_MATCH_MP_TAC SNOC_INDUCT
  \\ SIMP_TAC std_ss [WRITE_CODE_def,MEM,code_mem_def]
  \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [SNOC_APPEND]
  \\ FULL_SIMP_TAC std_ss [WRITE_CODE_APPEND]
  \\ Cases_on `(WRITE_CODE (BC_CODE ((\x. NONE),n)) bs)`
  \\ Cases_on `p` \\ FULL_SIMP_TAC std_ss [WRITE_CODE_def,code_mem_def]
  \\ FULL_SIMP_TAC std_ss [APPLY_UPDATE_THM]
  \\ Cases_on `r = p1` \\ FULL_SIMP_TAC std_ss [] THEN1
   (Q.LIST_EXISTS_TAC [`bs`,`[]`] \\ FULL_SIMP_TAC std_ss [APPEND_NIL]
    \\ IMP_RES_TAC WRITE_CODE_IMP_LENGTH \\ DECIDE_TAC)
  \\ Q.PAT_X_ASSUM `!xx.bbb` (MP_TAC o Q.SPECL [`n`,`p1`])
  \\ FULL_SIMP_TAC std_ss [code_mem_def]
  \\ REPEAT STRIP_TAC
  \\ Q.LIST_EXISTS_TAC [`bs1`,`bs2 ++ [x']`]
  \\ FULL_SIMP_TAC std_ss [APPEND_ASSOC]);

val WRITE_CODE_NONE_LEMMA = prove(
  ``(WRITE_CODE (BC_CODE ((\x.NONE),n)) bs = BC_CODE (c,m)) ==>
    !p1. (c p1 = SOME x) ==> ?bs1 bs2. (bs = bs1 ++ [x] ++ bs2) /\
                                       (p1 = code_length bs1 + n)``,
  REPEAT STRIP_TAC \\ MP_TAC (SPEC_ALL code_mem_SPLIT)
  \\ FULL_SIMP_TAC std_ss [code_mem_def]);

val bs2bytes_APPEND = prove(
  ``!xs ys i. bs2bytes (i,sym) (xs ++ ys) =
              bs2bytes (i,sym) xs ++ bs2bytes (code_length xs + i,sym) ys``,
  Induct \\ ASM_SIMP_TAC std_ss [APPEND,bs2bytes_def,code_length_def]
  \\ SIMP_TAC std_ss [APPEND_ASSOC,AC ADD_COMM ADD_ASSOC]);

val bs_symbol_ok_APPEND = prove(
  ``!xs ys. bc_symbols_ok sym (xs ++ ys) = bc_symbols_ok sym xs /\ bc_symbols_ok sym ys``,
  Induct \\ SIMP_TAC std_ss [APPEND,bc_symbols_ok_def] \\ Cases_on `h`
  \\ FULL_SIMP_TAC std_ss [APPEND,bc_symbols_ok_def,CONJ_ASSOC]);

val LENGTH_bs2bytes = prove(
  ``!bs sym n. LENGTH (bs2bytes (n,sym) bs) = code_length bs``,
  Induct \\ ASM_SIMP_TAC std_ss [bs2bytes_def,code_length_def,LENGTH,
    bc_length_def,LENGTH_APPEND]
  \\ Cases \\ EVAL_TAC \\ SIMP_TAC std_ss []
  \\ Cases_on `l` \\ EVAL_TAC \\ SIMP_TAC std_ss []);

val code_heap_IMP = prove(
  ``code_heap (BC_CODE (bc1.code,bc1.code_end)) (sym,w1,w2,w3,dd,d) /\
    (bc1.code p1 = SOME x) ==>
    bc_symbols_ok sym [x] /\
    ?xx. (one_byte_list (w1 + n2w p1) (bc_ref (p1,sym) x) * xx) (fun2set (d,dd))``,
  SIMP_TAC std_ss [code_heap_def] \\ STRIP_TAC
  \\ IMP_RES_TAC WRITE_CODE_NONE_LEMMA
  \\ FULL_SIMP_TAC std_ss [bs2bytes_APPEND,bs_symbol_ok_APPEND]
  \\ FULL_SIMP_TAC std_ss [one_byte_list_APPEND,LENGTH_APPEND,GSYM word_add_n2w]
  \\ FULL_SIMP_TAC std_ss [WORD_ADD_ASSOC,bs2bytes_def,APPEND_NIL,LENGTH_bs2bytes]
  \\ Q.PAT_X_ASSUM `ddd (fun2set (d,dd))` MP_TAC
  \\ SIMP_TAC std_ss [GSYM STAR_ASSOC]
  \\ ONCE_REWRITE_TAC [STAR_COMM]
  \\ SIMP_TAC std_ss [GSYM STAR_ASSOC]
  \\ REPEAT STRIP_TAC
  \\ ONCE_REWRITE_TAC [STAR_COMM]
  \\ METIS_TAC []);

val zLISP_BYTECODE_MOVE_CODE = prove(
  ``(!ddd syms cu.
      (bc1.code p1 = SOME x) /\ bc_symbols_ok syms [x] ==>
      SPEC X64_MODEL
        (zLISP_BYTECODE (a1,a2,sl,sl1,e,ex,cs,rbp,ddd,cu) (xs1,pp1,r1,bc1) (stack,input,xbp,rstack1,amnt,EL 4 cs))
        ((EL 4 cs + n2w p1,bc_ref (p1,syms) x) INSERT code_abbrevs cs)
        (zLISP_BYTECODE (a1,a2,sl,sl1,e,ex,cs,rbp,ddd,cu) (xs2,pp2,r2,bc2) (stack,input,xbp,rstack2,amnt,EL 4 cs))) ==>
      (bc1.code p1 = SOME x) ==>
      SPEC X64_MODEL
        (zLISP_BYTECODE (a1,a2,sl,sl1,e,ex,cs,rbp,SOME T,NONE) (xs1,pp1,r1,bc1) (stack,input,xbp,rstack1,amnt,EL 4 cs))
        (code_abbrevs cs)
        (zLISP_BYTECODE (a1,a2,sl,sl1,e,ex,cs,rbp,SOME T,NONE) (xs2,pp2,r2,bc2) (stack,input,xbp,rstack2,amnt,EL 4 cs))``,
  REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss []
  \\ Q.PAT_X_ASSUM `!ddd.bb` (ASSUME_TAC o Q.SPEC `NONE`)
  \\ FULL_SIMP_TAC std_ss [zLISP_BYTECODE_def,SPEC_PRE_DISJ_REMOVE]
  \\ SIMP_TAC std_ss [Once zLISP_def,Once zCODE_MEMORY_def,Once lisp_inv_def]
  \\ FULL_SIMP_TAC std_ss [SEP_CLAUSES,zCODE_UNCHANGED_def,cond_EXISTS]
  \\ SIMP_TAC std_ss [GSYM SPEC_PRE_EXISTS] \\ REPEAT STRIP_TAC
  \\ SIMP_TAC (std_ss++sep_cond_ss) [SPEC_MOVE_COND] \\ REPEAT STRIP_TAC
  \\ Q.PAT_X_ASSUM `!xx.bb` (MP_TAC o Q.SPECL [`INIT_SYMBOLS ++ sym`,`SOME (dd,d)`])
  \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC
  THEN1 (FULL_SIMP_TAC std_ss [code_heap_def] \\ METIS_TAC [bc_symbols_ok_IMP])
  \\ STRIP_TAC \\ FULL_SIMP_TAC std_ss [X64_SPEC_EXLPODE_CODE_LEMMA]
  \\ IMP_RES_TAC SPEC_SUBSET_CODE_UNION
  \\ POP_ASSUM (MP_TAC o Q.SPEC `zCODE_SET dd d`)
  \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
   (SIMP_TAC std_ss [zCODE_SET_def,SUBSET_DEF,GSPECIFICATION]
    \\ SIMP_TAC std_ss [PULL_EXISTS_IMP,CONS_11]
    \\ IMP_RES_TAC code_heap_IMP
    \\ POP_ASSUM (K ALL_TAC)
    \\ POP_ASSUM MP_TAC
    \\ Q.SPEC_TAC (`bc_ref (p1,INIT_SYMBOLS ++ sym) x`,`xs`)
    \\ Q.SPEC_TAC (`xx`,`res`)
    \\ Q.SPEC_TAC (`p1`,`i`)
    \\ Induct_on `xs` \\ SIMP_TAC std_ss [LENGTH]
    \\ SIMP_TAC std_ss [one_byte_list_def]
    \\ NTAC 4 STRIP_TAC \\ Cases
    THEN1 (FULL_SIMP_TAC std_ss [EL,HD,WORD_ADD_0] \\ SEP_R_TAC \\ SIMP_TAC std_ss [])
    \\ SIMP_TAC std_ss [EL,TL] \\ POP_ASSUM MP_TAC
    \\ ONCE_REWRITE_TAC [STAR_COMM]
    \\ SIMP_TAC std_ss [STAR_ASSOC]
    \\ ONCE_REWRITE_TAC [STAR_COMM]
    \\ SIMP_TAC std_ss [word_add_n2w,GSYM WORD_ADD_ASSOC]
    \\ STRIP_TAC \\ RES_TAC
    \\ STRIP_TAC \\ RES_TAC
    \\ ASM_SIMP_TAC std_ss [] \\ FULL_SIMP_TAC std_ss [word_arith_lemma1]
    \\ FULL_SIMP_TAC std_ss [AC ADD_ASSOC ADD_COMM,ADD1])
  \\ POP_ASSUM (K ALL_TAC) \\ REPEAT STRIP_TAC
  \\ IMP_RES_TAC SPEC_zCODE_SPLIT_UNION
  \\ POP_ASSUM MP_TAC  \\ POP_ASSUM (K ALL_TAC)
  \\ REPEAT STRIP_TAC
  \\ IMP_RES_TAC SPEC_DERIVE
  \\ FULL_SIMP_TAC std_ss [PULL_FORALL_IMP,AND_IMP_INTRO]
  \\ POP_ASSUM MATCH_MP_TAC
  \\ REPEAT STRIP_TAC THEN1
   (SIMP_TAC std_ss [SEP_EXISTS_DISJ_REV] \\ MATCH_MP_TAC SEP_IMP_LEMMA
    \\ SIMP_TAC std_ss [zLISP_def,zCODE_UNCHANGED_def,SEP_CLAUSES,zCODE_MEMORY_def]
    \\ REPEAT STRIP_TAC THEN1
     (REPEAT (POP_ASSUM (K ALL_TAC))
      \\ SIMP_TAC std_ss [SEP_IMP_def,SEP_EXISTS_THM] \\ REPEAT STRIP_TAC
      \\ FULL_SIMP_TAC (std_ss++sep_cond_ss) [cond_STAR]
      \\ REPEAT (Q.PAT_X_ASSUM `dddd = ddddd` (fn th => FULL_SIMP_TAC std_ss [GSYM th]))
      \\ REPEAT INST_EXISTS_TAC
      \\ FULL_SIMP_TAC (std_ss++star_ss) [SEP_CLAUSES,zCODE_MEMORY_def])
    \\ FULL_SIMP_TAC std_ss [zLISP_FAIL_def]
    \\ SIMP_TAC std_ss [zLISP_def,zCODE_UNCHANGED_def,SEP_CLAUSES,zCODE_MEMORY_def]
    \\ REPEAT (POP_ASSUM (K ALL_TAC))
    \\ SIMP_TAC std_ss [SEP_IMP_def,SEP_EXISTS_THM] \\ REPEAT STRIP_TAC
    \\ FULL_SIMP_TAC (std_ss++sep_cond_ss) [cond_STAR]
    \\ REPEAT (Q.PAT_X_ASSUM `dddd = ddddd` (fn th => FULL_SIMP_TAC std_ss [th]))
    \\ Q.LIST_EXISTS_TAC [`SOME T`,`vars`]
    \\ POP_ASSUM MP_TAC \\ Q.SPEC_TAC (`vars`,`x`)
    \\ SIMP_TAC std_ss [FORALL_PROD,zLISP_def,SEP_CLAUSES,SEP_EXISTS_THM]
    \\ REPEAT STRIP_TAC
    \\ FULL_SIMP_TAC (std_ss++sep_cond_ss) [cond_STAR,zCODE_UNCHANGED_def]
    \\ REPEAT (Q.PAT_X_ASSUM `dddd = ddddd` (fn th => FULL_SIMP_TAC std_ss [GSYM th]))
    \\ REPEAT INST_EXISTS_TAC
    \\ FULL_SIMP_TAC (std_ss++star_ss) [SEP_CLAUSES,zCODE_MEMORY_def])
  \\ SIMP_TAC std_ss [SEP_CLAUSES,zLISP_def,zCODE_UNCHANGED_def]
  \\ SIMP_TAC std_ss [lisp_inv_def,cond_EXISTS,SEP_CLAUSES]
  \\ SIMP_TAC std_ss [SEP_IMP_def,SEP_EXISTS_THM]
  \\ REPEAT STRIP_TAC
  \\ REPEAT INST_EXISTS_TAC
  \\ FULL_SIMP_TAC (std_ss++sep_cond_ss) [cond_STAR,zCODE_UNCHANGED_def]
  \\ FULL_SIMP_TAC (std_ss++star_ss) [SEP_CLAUSES,zCODE_MEMORY_def]);

val X64_LISP_iSTEP_LAST_RETURN = prove(
  ``(bc1.code 0 = SOME iRETURN) ==>
    SPEC X64_MODEL
      (zLISP_BYTECODE (a1,a2,sl,sl1,e,ex,cs,rbp,SOME T,NONE) (xs1,EL 4 cs,[],bc1) (stack,input,xbp,r::rstack,amnt,EL 4 cs))
      (code_abbrevs cs)
      (zLISP_BYTECODE (a1,a2,sl,sl1,e,ex,cs,rbp,SOME T,NONE) (xs1,r,[],bc1) (stack,input,xbp,rstack,amnt,EL 4 cs))``,
  FULL_SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC \\ POP_ASSUM MP_TAC
  \\ MATCH_MP_TAC zLISP_BYTECODE_MOVE_CODE \\ REPEAT STRIP_TAC
  \\ IMP_RES_TAC X64_LISP_iSTEP_LAST_RETURN_LEMMA
  \\ POP_ASSUM MP_TAC \\ FULL_SIMP_TAC std_ss [WORD_ADD_0,bc_ref_def]);

val icompile =
   X64_LISP_COMPILE_INST |> lisp_pc_s
   |> Q.INST [`p`|->`EL 9 cs`] |> MATCH_MP SPEC_SUBSET_CODE
   |> Q.SPEC `(code_abbrevs cs)`
   |> CONV_RULE ((RATOR_CONV o RAND_CONV) (SIMP_CONV std_ss
                 [SUBSET_DEF,code_abbrevs_def,NOT_IN_EMPTY,IN_UNION])) |> RW []
   |> SIMP_RULE (std_ss++sep_cond_ss) [SPEC_MOVE_COND]

val icompile_fail =
   X64_LISP_COMPILE_INST_FAIL |> lisp_pc_s
   |> Q.INST [`p`|->`EL 9 cs`] |> MATCH_MP SPEC_SUBSET_CODE
   |> Q.SPEC `(code_abbrevs cs)`
   |> CONV_RULE ((RATOR_CONV o RAND_CONV) (SIMP_CONV std_ss
                 [SUBSET_DEF,code_abbrevs_def,NOT_IN_EMPTY,IN_UNION])) |> RW []
   |> SIMP_RULE (std_ss++sep_cond_ss) [SPEC_MOVE_COND]
   |> CONV_RULE ((RAND_CONV o RAND_CONV)
                 (SIMP_CONV std_ss [zLISP_def,lisp_inv_def,IS_TRUE_def,SEP_CLAUSES]))

val X64_LISP_iSTEP_COMPILE_PART2 = prove(
  ``(bc1.code p1 = SOME iCOMPILE) /\
    iSTEP (xs1,p1,r1,bc1) (xs2,p2,r2,bc2) ==>
    SPEC X64_MODEL
      (zLISP_BYTECODE (a1,a2,sl,sl1,e,ex,cs,rbp,SOME T,NONE) (xs1,EL 9 cs,r::MAP (\n. w + n2w n) r1,bc1) (stack,input,xbp,rstack,amnt,EL 4 cs))
      (code_abbrevs cs)
      (zLISP_BYTECODE (a1,a2,sl,sl1,e,ex,cs,rbp,SOME T,NONE) (xs2,r,MAP (\n. w + n2w n) r2,bc2) (stack,input,xbp,rstack,amnt,EL 4 cs))``,
  ONCE_REWRITE_TAC [iSTEP_cases] \\ SIMP_TAC std_ss [] \\ REVERSE (REPEAT STRIP_TAC)
  \\ FULL_SIMP_TAC (srw_ss()) [BC_STEP_def,CONTAINS_BYTECODE_def,bc_ref_def]
  THEN1 (FULL_SIMP_TAC std_ss [zLISP_BYTECODE_def,zLISP_def,
          lisp_inv_def,IS_TRUE_def,SEP_CLAUSES,SPEC_REFL,SPEC_FALSE_PRE])
  THEN1
   (FULL_SIMP_TAC std_ss [zLISP_BYTECODE_def,HD,TL,APPEND]
    \\ REPEAT STRIP_TAC \\ MATCH_MP_TAC SPEC_PRE_DISJ_INTRO
    \\ SIMP_TAC std_ss [GSYM SPEC_PRE_EXISTS,HD,TL,APPEND,SPEC_MOVE_COND]
    \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [bc_inv_BC_COMPILE,SEP_CLAUSES]
    \\ HO_MATCH_MP_TAC SPEC_PULL_EXISTS \\ Q.EXISTS_TAC `Sym "NIL"`
    \\ HO_MATCH_MP_TAC SPEC_PULL_EXISTS \\ Q.EXISTS_TAC `Sym "NIL"`
    \\ HO_MATCH_MP_TAC SPEC_PULL_EXISTS \\ Q.EXISTS_TAC `Sym "NIL"`
    \\ HO_MATCH_MP_TAC SPEC_PULL_EXISTS \\ Q.EXISTS_TAC `Sym "NIL"`
    \\ CONV_TAC ((RAND_CONV)
         (SIMP_CONV (srw_ss()) [zLISP_def,lisp_inv_def,IS_TRUE_def,SEP_CLAUSES,BC_FAIL_def]))
    \\ MATCH_MP_TAC icompile_fail \\ ASM_SIMP_TAC std_ss [])
  \\ FULL_SIMP_TAC std_ss [zLISP_BYTECODE_def,HD,TL,APPEND]
  \\ REPEAT STRIP_TAC \\ MATCH_MP_TAC SPEC_PRE_DISJ_INTRO
  \\ SIMP_TAC std_ss [GSYM SPEC_PRE_EXISTS,HD,TL,APPEND,SPEC_MOVE_COND]
  \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [bc_inv_BC_COMPILE,SEP_CLAUSES]
  \\ HO_MATCH_MP_TAC SPEC_PULL_EXISTS \\ Q.EXISTS_TAC `Sym "NIL"`
  \\ HO_MATCH_MP_TAC SPEC_PULL_EXISTS \\ Q.EXISTS_TAC `Sym "NIL"`
  \\ HO_MATCH_MP_TAC SPEC_PULL_EXISTS \\ Q.EXISTS_TAC `Sym "NIL"`
  \\ HO_MATCH_MP_TAC SPEC_PULL_EXISTS \\ Q.EXISTS_TAC `Sym "T"`
  \\ ASM_SIMP_TAC std_ss [BC_COMPILE_io_out]
  \\ MATCH_MP_TAC icompile \\ ASM_SIMP_TAC std_ss []);

val icompile_part1 =
  X64_LISP_CALL_EL9 |> fix_code |> Q.INST [`p`|->`n2w p1 + EL 4 cs`]
  |> SIMP_RULE std_ss [AC WORD_ADD_ASSOC WORD_ADD_COMM]
  |> MATCH_MP SPEC_FRAME |> Q.SPEC `~zS`

val X64_LISP_iSTEP_COMPILE_PART1 = prove(
  ``iSTEP (xs1,p1,r1,bc1) (xs2,p2,r2,bc2) ==>
    (bc1.code p1 = SOME iCOMPILE) ==>
    SPEC X64_MODEL
      (zLISP_BYTECODE (a1,a2,sl,sl1,e,ex,cs,rbp,SOME T,NONE) (xs1,EL 4 cs + n2w p1,MAP (\n. w + n2w n) r1,bc1) (stack,input,xbp,rstack,amnt,EL 4 cs))
      (code_abbrevs cs)
      (zLISP_BYTECODE (a1,a2,sl,sl1,e,ex,cs,rbp,SOME T,NONE) (xs1,EL 9 cs, (EL 4 cs + n2w p2)::MAP (\n. w + n2w n) r1,bc1) (stack,input,xbp,rstack,amnt,EL 4 cs))``,
  STRIP_TAC \\ MATCH_MP_TAC zLISP_BYTECODE_MOVE_CODE \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [bc_ref_def]
  \\ REVERSE (FULL_SIMP_TAC std_ss [iSTEP_cases,CONTAINS_BYTECODE_def])
  \\ FULL_SIMP_TAC (srw_ss()) [BC_STEP_def,bc_ref_def,LENGTH]
  THEN1 (FULL_SIMP_TAC std_ss [zLISP_BYTECODE_def,zLISP_def,
          lisp_inv_def,IS_TRUE_def,SEP_CLAUSES,SPEC_REFL,SPEC_FALSE_PRE])
  \\ SIMP_TAC std_ss [zLISP_BYTECODE_def]
  \\ REPEAT STRIP_TAC \\ MATCH_MP_TAC SPEC_PRE_DISJ_INTRO
  \\ SIMP_TAC std_ss [GSYM SPEC_PRE_EXISTS,HD,TL,APPEND,SPEC_MOVE_COND]
  \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [bc_symbols_ok_def,SEP_CLAUSES]
  \\ BYTECODE_TAC \\ MATCH_MP_TAC SPEC_REMOVE_POST
  \\ FULL_SIMP_TAC std_ss [AC WORD_ADD_ASSOC WORD_ADD_COMM]
  \\ FULL_SIMP_TAC std_ss [icompile_part1]);

val X64_LISP_iSTEP_COMPILE = let
  val th1 = UNDISCH_ALL X64_LISP_iSTEP_COMPILE_PART1
  val th2 = UNDISCH X64_LISP_iSTEP_COMPILE_PART2 |> Q.INST [`r`|->`EL 4 cs + n2w p2`]
  val th = DISCH_ALL (SPEC_COMPOSE_RULE [th1,th2]) |> RW [AND_IMP_INTRO]
  in th end;

val X64_LISP_iSTEP_CONST_SYM_PART1 = prove(
  ``iSTEP (xs1,p1,r1,bc1) (xs2,p2,r2,bc2) ==>
    (bc1.code p1 = SOME (iCONST_SYM s)) ==>
    SPEC X64_MODEL
      (zLISP_BYTECODE (a1,a2,sl,sl1,e,ex,cs,rbp,SOME T,NONE) (xs1,EL 4 cs + n2w p1,MAP (\n. EL 4 cs + n2w n) r1,bc1) (stack,input,xbp,rstack,amnt,EL 4 cs))
      (code_abbrevs cs)
      (zLISP_BYTECODE (a1,a2,sl,sl1,e,ex,cs,rbp,SOME T,NONE) ((if xs1 = [] then Sym "NIL" else HD xs1)::xs1,EL 4 cs + n2w p1 + 23w,MAP (\n. EL 4 cs + n2w n) r1,bc1) (stack,input,xbp,rstack,amnt,EL 4 cs))``,
  STRIP_TAC \\ MATCH_MP_TAC zLISP_BYTECODE_MOVE_CODE \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [bc_ref_def]
  \\ REVERSE (FULL_SIMP_TAC std_ss [iSTEP_cases,CONTAINS_BYTECODE_def])
  \\ FULL_SIMP_TAC (srw_ss()) [BC_STEP_def,bc_ref_def,LENGTH]
  THEN1 (FULL_SIMP_TAC std_ss [zLISP_BYTECODE_def,zLISP_def,
          lisp_inv_def,IS_TRUE_def,SEP_CLAUSES,SPEC_REFL,SPEC_FALSE_PRE])
  \\ `0x48w::0x85w::0xDBw::0x3Ew::0x48w::0x75w::0x9w::0x8Bw::0xD1w::
        0x48w::0xFFw::0xA7w::0x38w::0xFFw::0xFFw::0xFFw::0x48w::0xFFw::
        0xCBw::0x44w::0x89w::0x4w::0x9Fw::0x41w::0xB8w::
        IMMEDIATE32 (n2w (8 * THE (LIST_FIND 0 x syms) + 3)) =
      0x48w::0x85w::0xDBw::0x3Ew::0x48w::0x75w::0x9w::0x8Bw::0xD1w::
       0x48w::0xFFw::0xA7w::0x38w::0xFFw::0xFFw::0xFFw::0x48w::0xFFw::
        0xCBw::0x44w::0x89w::0x4w::0x9Fw::[] ++ 0x41w::0xB8w::
        IMMEDIATE32 (n2w (8 * THE (LIST_FIND 0 x syms) + 3))` by
          FULL_SIMP_TAC std_ss [APPEND]
  \\ FULL_SIMP_TAC std_ss []
  \\ MATCH_MP_TAC (GEN_ALL (RW [AND_IMP_INTRO] SPEC_X64_MERGE_CODE))
  \\ FULL_SIMP_TAC std_ss [LENGTH]
  \\ MATCH_MP_TAC (SPEC_SUBSET_CODE |> SPEC_ALL |> UNDISCH
        |> Q.INST [`c`|->`x1 INSERT s`] |> Q.SPEC `x1 INSERT y1 INSERT s`
        |> SIMP_RULE std_ss [INSERT_SUBSET]
        |> SIMP_RULE std_ss [SUBSET_DEF,IN_INSERT] |> DISCH_ALL)
  \\ SIMP_TAC std_ss [zLISP_BYTECODE_def]
  \\ REPEAT STRIP_TAC \\ MATCH_MP_TAC SPEC_PRE_DISJ_INTRO
  \\ SIMP_TAC std_ss [GSYM SPEC_PRE_EXISTS,HD,TL,APPEND,SPEC_MOVE_COND]
  \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [bc_symbols_ok_def,SEP_CLAUSES]
  \\ BYTECODE_TAC
  \\ Cases_on `xs1` \\ FULL_SIMP_TAC std_ss [HD,TL,APPEND,NOT_CONS_NIL]
  \\ FULL_SIMP_TAC std_ss [fix_code X64_LISP_PUSH_0]);

fun str_remove_primes v = (implode o filter (fn x => not (x = #"'")) o explode) v
fun EX_TAC (hs,goal) = let
  val v = fst (dest_exists goal)
  val v = mk_var(str_remove_primes (fst (dest_var v)), type_of v)
  in EXISTS_TAC v (hs,goal) end;

val DIFF_DELETE = prove(
  ``s DIFF t DELETE x = s DIFF (x INSERT t)``,
  SIMP_TAC std_ss [EXTENSION,IN_DIFF,IN_DELETE,IN_INSERT] \\ METIS_TAC []);

val SPEC_zCODE_SET_LEMMA = prove(
  ``SPEC X64_MODEL p {(w,xs)} q /\ one_byte_list w xs (fun2set (d,dd DIFF dx)) ==>
    SPEC X64_MODEL p (zCODE_SET dd d) q``,
  REPEAT STRIP_TAC \\ IMP_RES_TAC X64_SPEC_EXLPODE_CODE
  \\ SIMP_TAC std_ss [zCODE_SET_def]
  \\ MATCH_MP_TAC (SIMP_RULE std_ss [PULL_FORALL_IMP,AND_IMP_INTRO] SPEC_SUBSET_CODE)
  \\ Q.EXISTS_TAC `{(w + n2w n,[EL n xs]) | n | n < LENGTH xs}`
  \\ ASM_SIMP_TAC std_ss []
  \\ Q.PAT_X_ASSUM `one_byte_list w xs (fun2set (d,dd DIFF dx))` MP_TAC
  \\ REPEAT (POP_ASSUM (K ALL_TAC))
  \\ Q.SPEC_TAC (`w`,`w`) \\ Q.SPEC_TAC (`dx`,`dx`) \\ Q.SPEC_TAC (`xs`,`xs`)
  \\ Induct \\ FULL_SIMP_TAC std_ss [LENGTH,GSPECIFICATION,SUBSET_DEF]
  \\ FULL_SIMP_TAC std_ss [PULL_EXISTS_IMP,CONS_11,PULL_FORALL_IMP]
  \\ SIMP_TAC std_ss [one_byte_list_def,one_fun2set,IN_DIFF]
  \\ NTAC 4 STRIP_TAC \\ Cases_on `n`
  \\ ASM_SIMP_TAC std_ss [WORD_ADD_0,EL,HD,TL] \\ STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [DIFF_DELETE] \\ RES_TAC
  \\ FULL_SIMP_TAC std_ss [word_arith_lemma1,ADD1,AC ADD_COMM ADD_ASSOC]);

val SPEC_zCODE_SET = prove(
  ``SPEC X64_MODEL p {(w,xs)} q /\ one_byte_list w xs (fun2set (d,dd DIFF dx)) ==>
    SPEC X64_MODEL p (zCODE_SET dd d) q``,
  METIS_TAC [SPEC_zCODE_SET_LEMMA,SPEC_X64_STRENGTHEN_CODE]);

val X64_ASSIGN = let
  val ((th,_,_),_) = x64_spec "41B8"
  in RW [SIGN_EXTEND_MOD,GSYM w2w_def] th |> Q.INST [`imm32` |-> `w0n`] end;

val MEM_IMP_LIST_FIND = prove(
  ``!xs n x. MEM x xs ==> ?k. (LIST_FIND n x xs = SOME k) /\ k - n < LENGTH xs``,
  Induct \\ SIMP_TAC std_ss [MEM,LIST_FIND_def] \\ NTAC 3 STRIP_TAC
  \\ Cases_on `x = h` \\ FULL_SIMP_TAC std_ss [LENGTH]
  \\ REPEAT STRIP_TAC \\ RES_TAC
  \\ POP_ASSUM (MP_TAC o Q.SPEC `n+1`) \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss []
  \\ DECIDE_TAC);

val X64_LISP_iSTEP_CONST_SYM_PART2 = prove(
  ``iSTEP (xs1,p1,r1,bc1) (xs2,p2,r2,bc2) ==>
    (bc1.code p1 = SOME (iCONST_SYM s)) ==>
    SPEC X64_MODEL
      (zLISP_BYTECODE (a1,a2,sl,sl1,e,ex,cs,rbp,SOME T,NONE) (y::xs1,EL 4 cs + n2w p1 + 23w,MAP (\n. EL 4 cs + n2w n) r1,bc1) (stack,input,xbp,rstack,amnt,EL 4 cs))
      (code_abbrevs cs)
      (zLISP_BYTECODE (a1,a2,sl,sl1,e,ex,cs,rbp,SOME T,NONE) (Sym s::xs1,EL 4 cs + n2w p2,MAP (\n. EL 4 cs + n2w n) r1,bc1) (stack,input,xbp,rstack,amnt,EL 4 cs))``,
  REPEAT STRIP_TAC \\ SIMP_TAC std_ss [zLISP_BYTECODE_def]
  \\ REPEAT STRIP_TAC \\ MATCH_MP_TAC SPEC_PRE_DISJ_INTRO
  \\ SIMP_TAC std_ss [GSYM SPEC_PRE_EXISTS,HD,TL,APPEND,SPEC_MOVE_COND]
  \\ REPEAT STRIP_TAC \\ MATCH_MP_TAC SPEC_REMOVE_POST
  \\ FULL_SIMP_TAC std_ss [bc_symbols_ok_def,SEP_CLAUSES]
  \\ Q.SPEC_TAC (`xs1 ++ Sym "NIL"::stack`,`stack1`) \\ REPEAT STRIP_TAC
  \\ BYTECODE_TAC
  \\ REVERSE (FULL_SIMP_TAC (srw_ss()) [iSTEP_cases,CONTAINS_BYTECODE_def])
  THEN1 (FULL_SIMP_TAC std_ss [zLISP_BYTECODE_def,zLISP_def,
          lisp_inv_def,IS_TRUE_def,SEP_CLAUSES,SPEC_REFL,SPEC_FALSE_PRE])
  \\ FULL_SIMP_TAC std_ss [BC_STEP_def,bc_length_def,bc_ref_def,LENGTH_APPEND,
       LENGTH,APPEND,IMMEDIATE32_def] \\ FULL_SIMP_TAC std_ss [GSYM word_add_n2w]
  \\ Q.SPEC_TAC (`MAP (\n. n2w n + EL 4 cs) r1`,`rs2`) \\ STRIP_TAC
  \\ Q.SPEC_TAC (`IO_STREAMS input bc1.io_out`,`io2`) \\ STRIP_TAC
  \\ Q.SPEC_TAC (`bc_state_tree bc1`,`x5`) \\ STRIP_TAC
  \\ ASM_SIMP_TAC std_ss [AC WORD_ADD_ASSOC WORD_ADD_COMM]
  \\ ASM_SIMP_TAC std_ss [WORD_ADD_ASSOC]
  \\ Q.ABBREV_TAC `p = n2w p1 + EL 4 cs`
  \\ SIMP_TAC (std_ss++sep_cond_ss) [zLISP_def,SEP_CLAUSES,GSYM SPEC_PRE_EXISTS,
       SPEC_MOVE_COND,zCODE_MEMORY_def] \\ REPEAT STRIP_TAC
  \\ MATCH_MP_TAC (SPEC_SUBSET_CODE |> SPEC_ALL |> UNDISCH_ALL |> SPEC_ALL
       |> DISCH_ALL |> RW [AND_IMP_INTRO] |> GEN_ALL)
  \\ Q.EXISTS_TAC `{}` \\ FULL_SIMP_TAC std_ss [EMPTY_SUBSET]
  \\ POP_ASSUM (STRIP_ASSUME_TAC o RW [lisp_inv_def])
  \\ `?k. (LIST_FIND 0 s (INIT_SYMBOLS ++ sym) = SOME k) /\ k < 536870912 /\
      ?dx. (one_byte_list (p + 0x17w)
              ([0x41w; 0xB8w] ++ IMMEDIATE32 (n2w (8 * THE (LIST_FIND 0 s ((INIT_SYMBOLS ++ sym))) + 3))))
          (fun2set (d,dd DIFF dx))` by
   (IMP_RES_TAC code_heap_IMP \\ POP_ASSUM (K ALL_TAC)
    \\ FULL_SIMP_TAC std_ss [bc_symbols_ok_def]
    \\ `?k. (LIST_FIND 0 s (INIT_SYMBOLS ++ sym) = SOME k) /\
            (k - 0 < LENGTH (INIT_SYMBOLS ++ sym))` by METIS_TAC [MEM_IMP_LIST_FIND]
    \\ FULL_SIMP_TAC std_ss [symtable_inv_def]
    \\ FULL_SIMP_TAC std_ss [symtable_inv_def,one_symbol_list_def,
         SEP_CLAUSES,SEP_EXISTS_THM,cond_STAR]
    \\ STRIP_TAC THEN1 DECIDE_TAC
    \\ FULL_SIMP_TAC std_ss [bc_ref_def,APPEND]
    \\ Q.PAT_X_ASSUM `ddd (fun2set (d,dd))` MP_TAC
    \\ ONCE_REWRITE_TAC [STAR_COMM] \\ Q.UNABBREV_TAC `p`
    \\ NTAC 23 (SIMP_TAC std_ss [Once one_byte_list_def,word_arith_lemma1,GSYM ADD_ASSOC])
    \\ SIMP_TAC std_ss [STAR_ASSOC]
    \\ `n2w p1 + EL 4 cs + 0x17w = EL 4 cs + n2w p1 + 0x17w` by
          SIMP_TAC std_ss [AC WORD_ADD_COMM WORD_ADD_ASSOC]
    \\ ASM_SIMP_TAC std_ss [word_arith_lemma1]
    \\ METIS_TAC [fun2set_STAR_IMP])
  \\ Q.ABBREV_TAC `w0n = n2w (8 * THE (LIST_FIND 0 s (INIT_SYMBOLS ++ sym)) + 3):word32`
  \\ NTAC 6 (HO_MATCH_MP_TAC SPEC_PULL_EXISTS \\ EX_TAC)
  \\ HO_MATCH_MP_TAC SPEC_PULL_EXISTS \\ Q.EXISTS_TAC `w0n`
  \\ REPEAT (HO_MATCH_MP_TAC SPEC_PULL_EXISTS \\ EX_TAC)
  \\ Q.PAT_ABBREV_TAC `ii = lisp_inv zzz zzzz zzzzzz`
  \\ `ii` by
   (Q.UNABBREV_TAC `ii` \\ FULL_SIMP_TAC std_ss [lisp_inv_def]
    \\ Q.EXISTS_TAC `H_DATA (INR (n2w (THE (LIST_FIND 0 s (INIT_SYMBOLS ++ sym)))))`
    \\ REPEAT EX_TAC \\ FULL_SIMP_TAC std_ss []
    \\ FULL_SIMP_TAC std_ss [APPEND,EVERY_DEF,stop_and_copyTheory.lisp_x_def]
    \\ Q.UNABBREV_TAC `w0n`
    \\ FULL_SIMP_TAC std_ss [MAP,CONS_11,ref_heap_addr_alt]
    \\ STRIP_TAC THEN1 (Cases_on `s0`
      \\ FULL_SIMP_TAC std_ss [ok_split_heap_def,UNION_SUBSET,ADDR_SET_THM,INSERT_SUBSET])
    \\ FULL_SIMP_TAC std_ss [w2w_def,GSYM word_add_n2w,WORD_EQ_ADD_CANCEL]
    \\ FULL_SIMP_TAC (std_ss++SIZES_ss) [WORD_MUL_LSL,word_mul_n2w,w2n_n2w])
  \\ ASM_SIMP_TAC std_ss [SEP_CLAUSES] \\ Q.UNABBREV_TAC `ii`
  \\ CONV_TAC (PRE_CONV (MOVE_OUT_CONV ``zCODE``))
  \\ CONV_TAC (POST_CONV (MOVE_OUT_CONV ``zCODE``))
  \\ FULL_SIMP_TAC std_ss [RW1 [STAR_COMM] X64_SPEC_CODE]
  \\ MATCH_MP_TAC (GEN_ALL SPEC_zCODE_SET)
  \\ Q.LIST_EXISTS_TAC [`[0x41w; 0xB8w] ++ IMMEDIATE32 w0n`,`p + 0x17w`,`dx`]
  \\ FULL_SIMP_TAC std_ss [APPEND,IMMEDIATE32_def]
  \\ (fn (hs,goal) => let
        val (_,p,_,_) = dest_spec goal
        val lemma = GEN_ALL (Q.SPECL [`p`,`{}`] (Q.ISPEC `X64_MODEL` SPEC_REFL))
        in ASSUME_TAC (SPEC p lemma) (hs,goal) end)
  \\ POP_ASSUM (fn th => ASSUME_TAC (SPEC_COMPOSE_RULE [th,X64_ASSIGN]))
  \\ FULL_SIMP_TAC (std_ss++star_ss) []);

val X64_LISP_iSTEP_CONST_SYM = let
  val th1 = UNDISCH_ALL X64_LISP_iSTEP_CONST_SYM_PART1
  val th2 = UNDISCH_ALL X64_LISP_iSTEP_CONST_SYM_PART2
            |> Q.INST [`y`|->`(if xs1 = [] then Sym "NIL" else HD xs1)`]
  val th = DISCH_ALL (SPEC_COMPOSE_RULE [th1,th2]) |> RW [AND_IMP_INTRO]
  in th end;

val code_ptr_WRITE_CODE = prove(
  ``!bs bc. code_ptr (WRITE_CODE bc bs) = code_ptr bc + code_length bs``,
  Induct \\ Cases_on `bc` \\ Cases_on `p`
  \\ ASM_SIMP_TAC std_ss [WRITE_CODE_def,code_length_def,code_ptr_def]
  \\ DECIDE_TAC);

val code_heap_IMP = prove(
  ``!code. code_heap code (sym,base_ptr,curr_ptr,space_left,dh,h) /\
    ~(code_mem code p = NONE) ==> p < 2**30``,
  SIMP_TAC std_ss [code_heap_def,PULL_EXISTS_IMP,GSYM AND_IMP_INTRO]
  \\ REPEAT STRIP_TAC
  \\ Cases_on `code_mem (WRITE_CODE (BC_CODE ((\x. NONE),0)) bs) p`
  \\ FULL_SIMP_TAC std_ss []
  \\ IMP_RES_TAC code_length_LESS
  \\ FULL_SIMP_TAC std_ss [code_ptr_WRITE_CODE,code_ptr_def] \\ DECIDE_TAC);

val LISP = lisp_inv_def |> SPEC_ALL |> concl |> dest_eq |> fst
val lisp_inv_IMP = prove(
  ``^LISP ==> !p. ~(code_mem code p = NONE) ==> p < 2**30``,
  SIMP_TAC bool_ss [lisp_inv_def] \\ REPEAT STRIP_TAC \\ METIS_TAC [code_heap_IMP]);

val zLISP = zLISP_def |> SPEC_ALL |> concl |> dest_eq |> fst
val zLISP_IMP = prove(
  ``^zLISP s ==> !p. ~(code_mem code p = NONE) ==> p < 2**30``,
  SIMP_TAC bool_ss [zLISP_def,cond_STAR,SEP_EXISTS_THM] \\ METIS_TAC [lisp_inv_IMP]);

val zLISP_BOUND = prove(
  ``~(code_mem code p = NONE) ==> (^zLISP = ^zLISP * cond (p < 2**30))``,
  SIMP_TAC std_ss [cond_STAR,FUN_EQ_THM] \\ METIS_TAC [SIMP_RULE std_ss[]zLISP_IMP]);

val zLISP_BYTECODE_PC_BOUND = prove(
  ``(~(bc1.code p = NONE) /\ p < 2**30 ==>
     SPEC X64_MODEL
      (zLISP_BYTECODE (a1,a2,sl,sl1,e,ex,cs,rbp,ddd,cu) (xs1,wp1,r1,bc1) (stack1,input1,xbp1,rstack1,amnt1,w)) c
      (zLISP_BYTECODE (a1,a2,sl,sl1,e,ex,cs,rbp,ddd,cu) (xs2,wp2,r2,bc2) (stack2,input2,xbp2,rstack2,amnt2,w))) ==>
    ~(bc1.code p = NONE) ==>
    SPEC X64_MODEL
      (zLISP_BYTECODE (a1,a2,sl,sl1,e,ex,cs,rbp,ddd,cu) (xs1,wp1,r1,bc1) (stack1,input1,xbp1,rstack1,amnt1,w)) c
      (zLISP_BYTECODE (a1,a2,sl,sl1,e,ex,cs,rbp,ddd,cu) (xs2,wp2,r2,bc2) (stack2,input2,xbp2,rstack2,amnt2,w))``,
  SIMP_TAC std_ss [zLISP_BYTECODE_def,GSYM SPEC_PRE_EXISTS]
  \\ REPEAT STRIP_TAC \\ MATCH_MP_TAC SPEC_PRE_DISJ_INTRO
  \\ FULL_SIMP_TAC std_ss [SPEC_PRE_DISJ]
  \\ FULL_SIMP_TAC std_ss [GSYM SPEC_PRE_EXISTS] \\ REPEAT STRIP_TAC
  \\ `~(code_mem (BC_CODE (bc1.code,bc1.code_end)) p = NONE)` by
       ASM_SIMP_TAC std_ss [code_mem_def]
  \\ IMP_RES_TAC zLISP_BOUND \\ POP_ASSUM (fn th => SIMP_TAC std_ss [Once th])
  \\ FULL_SIMP_TAC (std_ss++sep_cond_ss) [SPEC_MOVE_COND]);

val X64_LISP_iSTEP = store_thm("X64_LISP_iSTEP",
  ``!xs1 p1 r1 bc1 xs2 p2 r2 bc2.
      iSTEP (xs1,p1,r1,bc1) (xs2,p2,r2,bc2) ==>
      SPEC X64_MODEL
        (zLISP_BYTECODE (a1,a2,sl,sl1,e,ex,cs,rbp,SOME T,NONE) (xs1,EL 4 cs + n2w p1,MAP (\n. EL 4 cs + n2w n) r1,bc1) (stack,input,xbp,rstack,amnt,EL 4 cs))
        (code_abbrevs cs)
        (zLISP_BYTECODE (a1,a2,sl,sl1,e,ex,cs,rbp,SOME T,NONE) (xs2,EL 4 cs + n2w p2,MAP (\n. EL 4 cs + n2w n) r2,bc2) (stack,input,xbp,rstack,amnt,EL 4 cs))``,
  NTAC 8 STRIP_TAC \\ Cases_on `bc1.code p1 = SOME iCOMPILE`
  THEN1 (STRIP_TAC \\ MATCH_MP_TAC X64_LISP_iSTEP_COMPILE \\ ASM_SIMP_TAC std_ss [])
  \\ Cases_on `?s. bc1.code p1 = SOME (iCONST_SYM s)` THEN1
   (REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss []
    \\ REVERSE (FULL_SIMP_TAC (srw_ss()) [iSTEP_cases,CONTAINS_BYTECODE_def])
    \\ REVERSE (FULL_SIMP_TAC (srw_ss()) [iSTEP_cases,CONTAINS_BYTECODE_def])
    THEN1 (FULL_SIMP_TAC std_ss [zLISP_BYTECODE_def,zLISP_def,
             lisp_inv_def,IS_TRUE_def,SEP_CLAUSES,SPEC_REFL,SPEC_FALSE_PRE])
    \\ MP_TAC X64_LISP_iSTEP_CONST_SYM
    \\ FULL_SIMP_TAC (srw_ss()) [iSTEP_cases,CONTAINS_BYTECODE_def])
  \\ FULL_SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC
  \\ REVERSE (Cases_on `?xx. bc1.code p1 = SOME xx`) THEN1
   (FULL_SIMP_TAC (srw_ss()) [iSTEP_cases,CONTAINS_BYTECODE_def]
    \\ FULL_SIMP_TAC std_ss [zLISP_BYTECODE_def,zLISP_def,
         lisp_inv_def,IS_TRUE_def,SEP_CLAUSES,SPEC_REFL,SPEC_FALSE_PRE])
  \\ FULL_SIMP_TAC std_ss []
  \\ POP_ASSUM MP_TAC \\ MATCH_MP_TAC zLISP_BYTECODE_MOVE_CODE \\ REPEAT STRIP_TAC
  \\ `~(bc1.code p1 = NONE)` by (FULL_SIMP_TAC std_ss [])
  \\ POP_ASSUM MP_TAC \\ MATCH_MP_TAC zLISP_BYTECODE_PC_BOUND
  \\ FULL_SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC
  \\ `bc_ref (p1,syms) xx = bc_ref (p1,syms) (THE (bc1.code p1))` by
       FULL_SIMP_TAC std_ss []
  \\ ONCE_ASM_REWRITE_TAC []
  \\ MATCH_MP_TAC X64_LISP_iSTEP_MOST_CASES \\ ASM_SIMP_TAC std_ss []);

val X64_LISP_RTC_iSTEP = prove(
  ``!x y. RTC iSTEP x y ==>
    !xs1 p1 r1 bc1 xs2 p2 r2 bc2.
      (x = (xs1,p1,r1,bc1)) /\ (y = (xs2,p2,r2,bc2)) ==>
      SPEC X64_MODEL
        (zLISP_BYTECODE (a1,a2,sl,sl1,e,ex,cs,rbp,SOME T,NONE) (xs1,EL 4 cs + n2w p1,MAP (\n. EL 4 cs + n2w n) r1,bc1) (stack,input,xbp,rstack,amnt,EL 4 cs))
        (code_abbrevs cs)
        (zLISP_BYTECODE (a1,a2,sl,sl1,e,ex,cs,rbp,SOME T,NONE) (xs2,EL 4 cs + n2w p2,MAP (\n. EL 4 cs + n2w n) r2,bc2) (stack,input,xbp,rstack,amnt,EL 4 cs))``,
  HO_MATCH_MP_TAC RTC_INDUCT
  \\ SIMP_TAC std_ss [SPEC_REFL,PULL_FORALL_IMP,GSYM AND_IMP_INTRO,FORALL_PROD]
  \\ REPEAT STRIP_TAC \\ IMP_RES_TAC X64_LISP_iSTEP
  \\ POP_ASSUM (IMP_RES_TAC o MATCH_MP (RW [GSYM AND_IMP_INTRO] SPEC_COMPOSE) o SPEC_ALL)
  \\ FULL_SIMP_TAC std_ss [UNION_IDEMPOT])
  |> SIMP_RULE std_ss [PULL_FORALL_IMP];


(* composition of compile, jump-to-code and execution of code *)

val SPEC_PRE_POST_COND = prove(
  ``SPEC m (p * cond b) c q = SPEC m (p * cond b) c (q * cond b)``,
  SIMP_TAC std_ss [SPEC_MOVE_COND,SEP_CLAUSES]);

val BYTECODE = zLISP_BYTECODE_def |> SPEC_ALL |> concl |> dest_eq |> fst

val SPEC_INTRO_FAIL = prove(
  ``SPEC m (pp) c (^BYTECODE) ==>
    SPEC m (pp \/ zLISP_FAIL (a1,a2,sl,sl1,e,ex,cs,rbp,ddd,cu)) c (^BYTECODE)``,
  FULL_SIMP_TAC std_ss [SPEC_PRE_DISJ,zLISP_BYTECODE_def]
  \\ ONCE_REWRITE_TAC [SEP_DISJ_COMM] \\ REPEAT STRIP_TAC
  \\ MATCH_MP_TAC SPEC_REMOVE_POST \\ SIMP_TAC std_ss [SPEC_REFL]);

val X64_BYTECODE_POP_LEMMA = prove(
  ``SPEC X64_MODEL
      (zLISP_BYTECODE (a1,a2,sl,sl1,e,ex,cs,rbp,SOME T,NONE)
         ([result],p,[],bc)
         (Sym "NIL"::xs,input,xbp,qs,amnt,EL 4 cs))
      {(p,[0x48w; 0xFFw; 0xC3w])}
      (zLISP_BYTECODE (a1,a2,sl,sl1,e,ex,cs,rbp,SOME T,NONE)
         ([result],p + 0x3w,[],bc)
         (xs,input,xbp,qs,amnt,EL 4 cs))``,
  SIMP_TAC std_ss [zLISP_BYTECODE_def,APPEND,HD,TL]
  \\ ASM_SIMP_TAC std_ss [SEP_CLAUSES]
  \\ SIMP_TAC std_ss [GSYM SPEC_PRE_EXISTS] \\ REPEAT STRIP_TAC
  \\ HO_MATCH_MP_TAC SPEC_PULL_EXISTS \\ Q.EXISTS_TAC `x1`
  \\ HO_MATCH_MP_TAC SPEC_PULL_EXISTS \\ Q.EXISTS_TAC `x2`
  \\ HO_MATCH_MP_TAC SPEC_PULL_EXISTS \\ Q.EXISTS_TAC `x3`
  \\ HO_MATCH_MP_TAC SPEC_PULL_EXISTS \\ Q.EXISTS_TAC `x4`
  \\ Cases_on `bc_inv bc` \\ ASM_SIMP_TAC std_ss [SEP_CLAUSES,SPEC_REFL]
  \\ MATCH_MP_TAC SPEC_PRE_DISJ_INTRO \\ MATCH_MP_TAC SPEC_REMOVE_POST
  \\ MATCH_MP_TAC (DISCH T (SIMP_RULE (srw_ss()) [SEP_CLAUSES]
      (Q.INST [`xs`|->`Sym "NIL"::Sym "NIL"::xs`,
               `ddd`|->`SOME T`] X64_LISP_POP))) \\ ASM_SIMP_TAC std_ss []);

val zBYTECODE_EVAL_THM = let
  val th = SPEC_COMPOSE_RULE [X64_LISP_COMPILE_FOR_EVAL,
             Q.INST [`ddd`|->`SOME T`,`cu`|->`NONE`] X64_LISP_JUMP_TO_CODE_FOR_EVAL]
           |> SIMP_RULE std_ss [getVal_def,isVal_def,SEP_CLAUSES]
           |> RW1 [SPEC_PRE_POST_COND]
           |> Q.INST [`io`|->`IO_STREAMS input bc.io_out`,`ok`|->`bc.ok`]
  val (th,goal) = SPEC_WEAKEN_RULE th ``
    zLISP_BYTECODE (a1,a2,sl,sl1,e,ex,cs,rbp,SOME T,NONE)
       ([],EL 4 cs + n2w bc.code_end,
        MAP (\n. EL 4 cs + n2w n) [0],BC_ONLY_COMPILE ([],sexp2term body,bc))
       (xs,input,xbp,p + 0x6Cw::qs,amnt,EL 4 cs)``
  val lemma = prove(goal,
    SIMP_TAC std_ss [zLISP_BYTECODE_def,SEP_IMP_MOVE_COND,HD,APPEND,TL,MAP,
      WORD_ADD_0,BC_ONLY_COMPILE_io_out,SEP_CLAUSES,
      SIMP_RULE std_ss [LET_DEF] mc_compile_for_eval_thm]
    \\ SIMP_TAC std_ss [SEP_IMP_def,SEP_EXISTS_THM]
    \\ REPEAT STRIP_TAC \\ METIS_TAC [])
  val th = MP th lemma
  val th2 = X64_LISP_RTC_iSTEP
    |> Q.SPECL [`[]`,`bc.code_end`,`[0]`,`BC_ONLY_COMPILE ([],sexp2term body,bc)`,
                `[result]`,`0`,`[]`,`bc8`]
    |> UNDISCH |> Q.INST [`stack`|->`xs`,`rstack`|->`p + 0x6Cw::qs`]
  val th = SPEC_COMPOSE_RULE [th,th2]
  val th = RW [MAP,WORD_ADD_0] th
  val th2 = UNDISCH X64_LISP_iSTEP_LAST_RETURN
            |> Q.INST [`xs1`|->`[result]`,`stack`|->`xs`,`r`|->`p+0x6Cw`,
                       `rstack`|->`qs`,`bc1`|->`bc8`]
  val th = SPEC_COMPOSE_RULE [th,th2]
  val th = RW [UNION_IDEMPOT,GSYM UNION_ASSOC] th
  val th = RW [UNION_IDEMPOT,UNION_ASSOC] th
  val th = th |> Q.GEN `x4` |> Q.GEN `x3` |> Q.GEN `x2` |> Q.GEN `x1`
  val th = SIMP_RULE std_ss [SPEC_PRE_EXISTS] th
  val th = MATCH_MP SPEC_INTRO_FAIL th
  val th = Q.INST [`xs`|->`Sym "NIL"::xs`] th
  val (th,goal) = SPEC_STRENGTHEN_RULE th ``
    zLISP_BYTECODE (a1,a2,sl,sl1,e,ex,cs,rbp,SOME T,NONE)
       ([body],p,[],bc)
       (xs,input,xbp,qs,amnt,EL 4 cs)``
  val lemma = prove(goal,
    SIMP_TAC (std_ss++star_ss) [zLISP_BYTECODE_def,APPEND,TL,HD,SEP_IMP_REFL])
  val th = MP th lemma
  val th2 = Q.INST [`p`|->`p+0x6Cw`,`bc`|->`bc8`] X64_BYTECODE_POP_LEMMA
  val th = SPEC_COMPOSE_RULE [th,th2]
  in th end;


(* derive similar theorems for read, print, print newline etc. *)

(* print *)

val iprint =
  SPEC_COMPOSE_RULE [X64_LISP_PRINT_SEXP,X64_LISP_PRINT_NEWLINE]
  |> SIMP_RULE std_ss [IO_WRITE_APPEND]
  |> Q.INST [`io`|->`IO_STREAMS input bc1.io_out`]
  |> SIMP_RULE std_ss [IO_WRITE_def,APPEND_ASSOC]
  |> DISCH T

val code = iprint |> concl |> rand |> rator |> rand
val pc = iprint |> concl |> rand |> rand |> find_term (can (match_term ``zPC p``)) |> rand

val X64_LISP_BYTECODE_PRINT = prove(
  ``SPEC X64_MODEL
      (zLISP_BYTECODE (a1,a2,sl,sl1,e,ex,cs,rbp,ddd,cu) ([x0],p,r1,bc1) (stack,input,xbp,rstack,amnt,EL 4 cs))
      ^code
      (zLISP_BYTECODE (a1,a2,sl,sl1,e,ex,cs,rbp,ddd,cu) ([x0],^pc,r1,BC_PRINT bc1 (sexp2string x0 ++ "\n")) (stack,input,xbp,rstack,amnt,EL 4 cs))``,
  SIMP_TAC std_ss [zLISP_BYTECODE_def]
  \\ REPEAT STRIP_TAC \\ MATCH_MP_TAC SPEC_PRE_DISJ_INTRO
  \\ SIMP_TAC std_ss [GSYM SPEC_PRE_EXISTS,HD,TL,APPEND,SPEC_MOVE_COND]
  \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [bc_symbols_ok_def,SEP_CLAUSES]
  \\ BYTECODE_TAC \\ ASM_SIMP_TAC std_ss [BC_PRINT_LEMMA,SEP_CLAUSES]
  \\ SIMP_TAC (srw_ss()) [BC_PRINT_def]
  \\ MATCH_MP_TAC iprint \\ SIMP_TAC std_ss []);

(* parse *)

val iparse =
  X64_LISP_PARSE_SEXP
  |> Q.INST [`io`|->`IO_STREAMS input bc1.io_out`,`xs`|->`Sym "NIL"::stack`,`xbp`|->`SUC (LENGTH (stack:SExp list))`]
  |> RW [LENGTH] |> DISCH T

val code = iparse |> concl |> rand |> rator |> rand
val pc = iparse |> concl |> rand |> rand |> find_term (can (match_term ``zPC p``)) |> rand

val next_sexp_INTRO = prove(
  ``IO_STREAMS (getINPUT (next_sexp (IO_STREAMS input bc1.io_out))) bc1.io_out =
    next_sexp (IO_STREAMS input bc1.io_out)``,
  SIMP_TAC std_ss [next_sexp_def,IO_INPUT_APPLY_def,getINPUT_def,
    REPLACE_INPUT_IO_def]);

val X64_LISP_BYTECODE_PARSE = prove(
  ``SPEC X64_MODEL
      (zLISP_BYTECODE (a1,a2,sl,sl1,e,ex,cs,rbp,ddd,cu) ([x0],p,r1,bc1) (stack,input,SUC (LENGTH stack),rstack,amnt,EL 4 cs))
      ^code
      (zLISP_BYTECODE (a1,a2,sl,sl1,e,ex,cs,rbp,ddd,cu) ([read_sexp (IO_STREAMS input bc1.io_out)],^pc,r1,bc1) (stack,getINPUT (next_sexp (IO_STREAMS input bc1.io_out)),SUC (LENGTH stack),rstack,amnt,EL 4 cs))``,
  SIMP_TAC std_ss [zLISP_BYTECODE_def]
  \\ REPEAT STRIP_TAC \\ MATCH_MP_TAC SPEC_PRE_DISJ_INTRO
  \\ SIMP_TAC std_ss [GSYM SPEC_PRE_EXISTS,HD,TL,APPEND,SPEC_MOVE_COND]
  \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [bc_symbols_ok_def,SEP_CLAUSES]
  \\ BYTECODE_TAC \\ ASM_SIMP_TAC std_ss [next_sexp_INTRO,SEP_CLAUSES]
  \\ MATCH_MP_TAC iparse \\ ASM_SIMP_TAC std_ss []);

(* eof *)

val ieof =
  X64_LISP_TEST_EOF
  |> Q.INST [`io`|->`IO_STREAMS input bc1.io_out`]
  |> SIMP_RULE std_ss [LENGTH,getINPUT_def,IO_INPUT_APPLY_def,REPLACE_INPUT_IO_def,combinTheory.o_DEF]
  |> DISCH T

val code = ieof |> concl |> rand |> rator |> rand
val pc = ieof |> concl |> rand |> rand |> find_term (can (match_term ``zPC p``)) |> rand

val X64_LISP_BYTECODE_EOF = prove(
  ``SPEC X64_MODEL
      (zLISP_BYTECODE (a1,a2,sl,sl1,e,ex,cs,rbp,ddd,cu) ([x0],p,r1,bc1) (stack,input,xbp,rstack,amnt,EL 4 cs))
      ^code
      (zLISP_BYTECODE (a1,a2,sl,sl1,e,ex,cs,rbp,ddd,cu) ([LISP_TEST (FST (is_eof input))],^pc,r1,bc1) (stack,SND (is_eof input),xbp,rstack,amnt,EL 4 cs))``,
  SIMP_TAC std_ss [zLISP_BYTECODE_def]
  \\ REPEAT STRIP_TAC \\ MATCH_MP_TAC SPEC_PRE_DISJ_INTRO
  \\ SIMP_TAC std_ss [GSYM SPEC_PRE_EXISTS,HD,TL,APPEND,SPEC_MOVE_COND]
  \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [bc_symbols_ok_def,SEP_CLAUSES]
  \\ BYTECODE_TAC \\ ASM_SIMP_TAC std_ss [next_sexp_INTRO,SEP_CLAUSES]
  \\ MATCH_MP_TAC SPEC_REMOVE_POST
  \\ MATCH_MP_TAC ieof \\ ASM_SIMP_TAC std_ss []);


(* jump *)

val pre = ijump_raw |> concl |> dest_imp |> fst
val code = ijump_raw |> concl |> rand |> rator |> rand
val pc1 = ijump_raw |> concl |> rand |> rator |> find_term (can (match_term ``zPC p``)) |> rand
val pc2 = ijump_raw |> concl |> rand |> rand |> find_term (can (match_term ``zPC p``)) |> rand

val X64_LISP_BYTECODE_JUMP = prove(
  ``^pre ==> SPEC X64_MODEL
      (zLISP_BYTECODE (a1,a2,sl,sl1,e,ex,cs,rbp,ddd,cu) ([x0],^pc1,r1,bc1) (stack,input,xbp,rstack,amnt,EL 4 cs))
      ^code
      (zLISP_BYTECODE (a1,a2,sl,sl1,e,ex,cs,rbp,ddd,cu) ([x0],^pc2,r1,bc1) (stack,input,xbp,rstack,amnt,EL 4 cs))``,
  SIMP_TAC std_ss [zLISP_BYTECODE_def]
  \\ REPEAT STRIP_TAC \\ MATCH_MP_TAC SPEC_PRE_DISJ_INTRO
  \\ SIMP_TAC std_ss [GSYM SPEC_PRE_EXISTS,HD,TL,APPEND,SPEC_MOVE_COND]
  \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [bc_symbols_ok_def,SEP_CLAUSES]
  \\ BYTECODE_TAC \\ ASM_SIMP_TAC std_ss [next_sexp_INTRO,SEP_CLAUSES]
  \\ MATCH_MP_TAC SPEC_REMOVE_POST
  \\ MATCH_MP_TAC ijump_raw \\ ASM_SIMP_TAC std_ss []);


(* jnil *)

val (ijnil1_raw,ijnil2_raw) = let
  fun the (SOME x) = x | the _ = fail()
  val ((th1,_,_),x) = x64_spec "480F85"
  val (th2,_,_) = the x
  val th1 = SPEC_COMPOSE_RULE [X64_LISP_MOVE10,X64_LISP_TEST_SYM_0_1,th1]
  val th1 = RW [precond_def] th1 |> Q.INST [`xs`|->`x::xs`]
            |> HIDE_STATUS_RULE true sts |> lisp_pc_s
            |> SIMP_RULE std_ss [HD,TL,NOT_CONS_NIL,SEP_CLAUSES,ADD_ASSOC]
            |> Q.INST [`imm32`|->`n2w p2 - n2w p1 - 14w`,`p`|->`w + n2w p1`]
            |> DISCH ``p1 < 1073741824 /\ p2 < 1073741824``
            |> SIMP_RULE (std_ss++sep_cond_ss) [JNIL_ADDRESS_LEMMA2,SPEC_MOVE_COND]
            |> RW [AND_IMP_INTRO]
            |> Q.INST [`p1`|->`0`,`w`|->`p`,`p2`|->`p3`]
            |> SIMP_RULE (std_ss++sep_cond_ss) [WORD_ADD_0]
  val th2 = SPEC_COMPOSE_RULE [X64_LISP_MOVE10,X64_LISP_TEST_SYM_0_1,th2]
  val th2 = RW [precond_def] th2 |> Q.INST [`xs`|->`x::xs`]
            |> HIDE_STATUS_RULE true sts |> lisp_pc_s
            |> SIMP_RULE std_ss [HD,TL,NOT_CONS_NIL,SEP_CLAUSES,ADD_ASSOC]
            |> Q.INST [`imm32`|->`n2w p2 - n2w p1 - 14w`,`p`|->`w + n2w p1`]
            |> SIMP_RULE (std_ss++sep_cond_ss) [JNIL_ADDRESS_LEMMA2,SPEC_MOVE_COND]
            |> Q.INST [`p1`|->`0`,`w`|->`p`,`p2`|->`p3`]
            |> SIMP_RULE (std_ss++sep_cond_ss) [WORD_ADD_0]
  in (th1,th2) end;

val pre = ijnil1_raw |> concl |> dest_imp |> fst
val code = ijnil1_raw |> concl |> rand |> rator |> rand
val pc1 = ijnil1_raw |> concl |> rand |> rator |> find_term (can (match_term ``zPC p``)) |> rand
val pc2 = ijnil1_raw |> concl |> rand |> rand |> find_term (can (match_term ``zPC p``)) |> rand

val X64_LISP_BYTECODE_JNIL1 = prove(
  ``^pre ==> SPEC X64_MODEL
      (zLISP_BYTECODE (a1,a2,sl,sl1,e,ex,cs,rbp,ddd,cu) ([x0],^pc1,r1,bc1) (stack,input,xbp,rstack,amnt,EL 4 cs))
      ^code
      (zLISP_BYTECODE (a1,a2,sl,sl1,e,ex,cs,rbp,ddd,cu) ([x0],^pc2,r1,bc1) (stack,input,xbp,rstack,amnt,EL 4 cs))``,
  SIMP_TAC std_ss [zLISP_BYTECODE_def]
  \\ REPEAT STRIP_TAC \\ MATCH_MP_TAC SPEC_PRE_DISJ_INTRO
  \\ SIMP_TAC std_ss [GSYM SPEC_PRE_EXISTS,HD,TL,APPEND,SPEC_MOVE_COND]
  \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [bc_symbols_ok_def,SEP_CLAUSES]
  \\ `bc1.instr_length = bc_length` by FULL_SIMP_TAC std_ss [bc_inv_def]
  \\ FULL_SIMP_TAC std_ss [bc_length_def,bc_ref_def,LENGTH,GSYM word_add_n2w,WORD_ADD_ASSOC,IMMEDIATE32_def,APPEND]
  \\ HO_MATCH_MP_TAC SPEC_PULL_EXISTS \\ Q.EXISTS_TAC `x0`
  \\ HO_MATCH_MP_TAC SPEC_PULL_EXISTS \\ Q.EXISTS_TAC `x2`
  \\ HO_MATCH_MP_TAC SPEC_PULL_EXISTS \\ Q.EXISTS_TAC `x3`
  \\ HO_MATCH_MP_TAC SPEC_PULL_EXISTS \\ Q.EXISTS_TAC `x4`
  \\ ASM_SIMP_TAC std_ss [SEP_CLAUSES]
  \\ MATCH_MP_TAC SPEC_REMOVE_POST
  \\ MATCH_MP_TAC ijnil1_raw \\ ASM_SIMP_TAC std_ss []);

val pre = ijnil2_raw |> concl |> dest_imp |> fst
val code = ijnil2_raw |> concl |> rand |> rator |> rand
val pc1 = ijnil2_raw |> concl |> rand |> rator |> find_term (can (match_term ``zPC p``)) |> rand
val pc2 = ijnil2_raw |> concl |> rand |> rand |> find_term (can (match_term ``zPC p``)) |> rand

val X64_LISP_BYTECODE_JNIL2 = prove(
  ``^pre ==> SPEC X64_MODEL
      (zLISP_BYTECODE (a1,a2,sl,sl1,e,ex,cs,rbp,ddd,cu) ([x0],^pc1,r1,bc1) (stack,input,xbp,rstack,amnt,EL 4 cs))
      ^code
      (zLISP_BYTECODE (a1,a2,sl,sl1,e,ex,cs,rbp,ddd,cu) ([x0],^pc2,r1,bc1) (stack,input,xbp,rstack,amnt,EL 4 cs))``,
  SIMP_TAC std_ss [zLISP_BYTECODE_def]
  \\ REPEAT STRIP_TAC \\ MATCH_MP_TAC SPEC_PRE_DISJ_INTRO
  \\ SIMP_TAC std_ss [GSYM SPEC_PRE_EXISTS,HD,TL,APPEND,SPEC_MOVE_COND]
  \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [bc_symbols_ok_def,SEP_CLAUSES]
  \\ `bc1.instr_length = bc_length` by FULL_SIMP_TAC std_ss [bc_inv_def]
  \\ FULL_SIMP_TAC std_ss [bc_length_def,bc_ref_def,LENGTH,GSYM word_add_n2w,WORD_ADD_ASSOC,IMMEDIATE32_def,APPEND]
  \\ HO_MATCH_MP_TAC SPEC_PULL_EXISTS \\ Q.EXISTS_TAC `x0`
  \\ HO_MATCH_MP_TAC SPEC_PULL_EXISTS \\ Q.EXISTS_TAC `x2`
  \\ HO_MATCH_MP_TAC SPEC_PULL_EXISTS \\ Q.EXISTS_TAC `x3`
  \\ HO_MATCH_MP_TAC SPEC_PULL_EXISTS \\ Q.EXISTS_TAC `x4`
  \\ ASM_SIMP_TAC std_ss [SEP_CLAUSES]
  \\ MATCH_MP_TAC SPEC_REMOVE_POST
  \\ MATCH_MP_TAC ijnil2_raw \\ ASM_SIMP_TAC std_ss []);


(* compose together *)

val zLISP_BYTECODE_SHORT_def = Define `
  zLISP_BYTECODE_SHORT
    (a1,a2,sl,sl1,e,ex,cs,rbp,ddd,cu,x,p,rs,bc,stack,input,xbp,rstack,amnt,w) =
  zLISP_BYTECODE (a1,a2,sl,sl1,e,ex,cs,rbp,ddd,cu) ([x],p,rs,bc)
    (stack,input,xbp,rstack,amnt,w)`;

val f1 = PURE_REWRITE_RULE [AND_IMP_INTRO] o
         (fn th => if is_imp (concl th) then th else DISCH T th) o
         DISCH_ALL o RW [GSYM zLISP_BYTECODE_SHORT_def] o
         Q.INST [`ddd`|->`SOME T`,`cu`|->`NONE`,`r1`|->`[]`,`xbp`|->`SUC (LENGTH (stack:SExp list))`]


val case1 = SPEC_COMPOSE_RULE [
  UNDISCH (f1 X64_LISP_BYTECODE_EOF),
  UNDISCH (f1 X64_LISP_BYTECODE_JNIL1)]

val case2 = SPEC_COMPOSE_RULE [
  UNDISCH (f1 X64_LISP_BYTECODE_EOF),
  UNDISCH (f1 X64_LISP_BYTECODE_JNIL2),
  UNDISCH (f1 X64_LISP_BYTECODE_PARSE),
  UNDISCH_ALL (SIMP_RULE std_ss [] (DISCH ``term2sexp body = xxx`` (f1 zBYTECODE_EVAL_THM))),
  UNDISCH (f1 X64_LISP_BYTECODE_PRINT),
  UNDISCH (RW [WORD_ADD_0] (Q.INST [`p2`|->`0`] (f1 X64_LISP_BYTECODE_JUMP)))]

fun guess_length_of_code def = let
  val tm = def |> SPEC_ALL |> concl |> cdr
  fun dest_code_piece tm = let
    val (x,y) = pairSyntax.dest_pair tm
    (* val (y,z) = pairSyntax.dest_pair y *)
    val (v,n) = wordsSyntax.dest_word_add x
    val _ = dest_var v
    val n = (numSyntax.int_of_term o cdr) n
    in n + (y |> listSyntax.dest_list |> fst |> length) end
  val xs = map dest_code_piece (find_terms (can dest_code_piece) tm)
  val max = foldl (fn (x,y) => if x < y then y else x) 0 xs
  in max end;

val (READ_EVAL_PRINT_LOOP_BASE,READ_EVAL_PRINT_LOOP_STEP) = let
  val n = guess_length_of_code (DISCH T case2)
  val k = concl case1
          |> find_term (can (match_term ``n2w (n + p2)``))
          |> find_term (numSyntax.is_numeral) |> numSyntax.int_of_term
  val p3 = numSyntax.term_of_int (n - k)
  val th1 = INST [``p3:num``|->p3] case1
            |> SIMP_RULE (std_ss++SIZES_ss) [w2w_def,w2n_n2w,w2n_lsr]
  val th2 = INST [``p3:num``|->p3] case2
            |> SIMP_RULE (std_ss++SIZES_ss) [w2w_def,w2n_n2w,w2n_lsr,word_2comp_n2w]
            |> RW1 [GSYM n2w_mod]
            |> SIMP_RULE (std_ss++SIZES_ss) [w2w_def,w2n_n2w,w2n_lsr,word_2comp_n2w]
  val (_,_,c,_) = dest_spec (concl th2)
  val th1 = SPEC c (MATCH_MP SPEC_SUBSET_CODE th1)
  val goal = fst (dest_imp (concl th1))
  val lemma = prove(goal,
    REWRITE_TAC [INSERT_SUBSET,UNION_SUBSET,IN_INSERT,IN_UNION,EMPTY_SUBSET])
  val th1 = MP th1 lemma
  in (th1,th2) end

val _ = save_thm("READ_EVAL_PRINT_LOOP_BASE",READ_EVAL_PRINT_LOOP_BASE);
val _ = save_thm("READ_EVAL_PRINT_LOOP_STEP",READ_EVAL_PRINT_LOOP_STEP);

val _ = export_theory();
