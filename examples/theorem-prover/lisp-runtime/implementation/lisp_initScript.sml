open HolKernel Parse boolLib bossLib; val _ = new_theory "lisp_init";
open lisp_sexpTheory lisp_consTheory lisp_invTheory lisp_codegenTheory;

(* --- *)

open wordsTheory arithmeticTheory wordsLib listTheory pred_setTheory pairTheory;
open combinTheory finite_mapTheory addressTheory helperLib;
open set_sepTheory bitTheory fcpTheory stringTheory;

val wstd_ss = std_ss ++ SIZES_ss ++ rewrites [DECIDE ``n<256 ==> (n:num)<18446744073709551616``,ORD_BOUND];

open stop_and_copyTheory;
open codegenLib decompilerLib prog_x64Lib prog_x64Theory progTheory;
open lisp_parseTheory;

infix \\
val op \\ = op THEN;
val RW = REWRITE_RULE;
val RW1 = ONCE_REWRITE_RULE;
fun SUBGOAL q = REVERSE (q by ALL_TAC)

val FORALL_EXISTS = METIS_PROVE [] ``(!x. P x ==> Q) = ((?x. P x) ==> Q)``
val IMP_IMP = METIS_PROVE [] ``b /\ (c ==> d) ==> ((b ==> c) ==> d)``

val LISP = lisp_inv_def |> SPEC_ALL |> concl |> dest_eq |> fst;
val REST = LISP |> cdr |> cdr |> cdr |> cdr |> cdr |> cdr |> cdr |> cdr |> cdr;
val STAT = LISP |> car |> car |> cdr;
val VAR_REST = LISP |> car |> cdr |> cdr |> cdr |> cdr |> cdr |> cdr |> cdr;

val align_blast = blastLib.BBLAST_PROVE
  ``(a && 3w = 0w) ==> ((a - w && 3w = 0w) = (w && 3w = 0w:word64))``

val align_add_blast = blastLib.BBLAST_PROVE
  ``(a && 3w = 0w) ==> ((a + w && 3w = 0w) = (w && 3w = 0w:word64))``


(* setup symbol table *)

val bytes2words_def = tDefine "bytes2words" `
  bytes2words xs = if LENGTH xs <= 4 then [bytes2word (TAKE 4 (xs ++ [0w;0w;0w;0w]))]:word32 list else
                     bytes2word (TAKE 4 xs) :: bytes2words (DROP 4 xs)`
  (WF_REL_TAC `measure (LENGTH)` \\ SIMP_TAC std_ss [LENGTH_DROP] \\ DECIDE_TAC)

val BINIT_SYMBOLS_def = Define `BINIT_SYMBOLS = INIT_SYMBOLS ++ ["PEQUAL"]`;

val INIT_SYMBOL_ASSERTION =
  EVAL ``(FOLDR (\x y. STRLEN x + y + 1) 1 BINIT_SYMBOLS) MOD 4``
  |> concl |> dest_eq |> snd |> (fn x => if x = ``0`` then () else fail());

val (init_func_spec,init_func_def) = let
  val tm = (snd o dest_eq o concl o EVAL) ``bytes2words (symbol_list BINIT_SYMBOLS)``
  val xs = tm |> listSyntax.dest_list |> fst
  val ((th1,_,_),_) = x64_spec_byte_memory "C700"
  val ((th2,_,_),_) = x64_spec_byte_memory (x64_encodeLib.x64_encode "add r0,4")
  val th = SPEC_COMPOSE_RULE [th1,th2]
  val (_,_,sts,_) = x64_tools
  val th = HIDE_STATUS_RULE true sts th
  val tms = find_terml (can (match_term ``((7 >< 0) (w:'a word)):word8``)) (concl th)
  val imm32 = hd (free_vars (hd tms))
  fun th_inst w = RW (map (EVAL o subst [imm32|->w]) tms) (INST [imm32|->w] th)
  val res = SPEC_COMPOSE_RULE (map th_inst xs)
  val f_tm = find_term (can (match_term ``(a =+ w) f``)) (concl res)
  val lhs_tm = ``(init_func (g:word64->word8) (r0:word64)):word64->word8``
  val def = new_definition("init_func",mk_eq(lhs_tm,f_tm))
  val res = RW [GSYM def] res
  val res = SIMP_RULE wstd_ss [w2w_def,w2n_n2w,w2n_lsr] res
  val res = RW1 [GSYM n2w_mod] res
  val res = SIMP_RULE (std_ss++SIZES_ss++sep_cond_ss) [] res
  val lhs_pre = ``(init_func_pre (dg:word64 set) (r0:word64)):bool``
  val f_pre = (hd o hyp o UNDISCH o RW [progTheory.SPEC_MOVE_COND]) res
  val pre = new_definition("init_func_pre",mk_eq(lhs_pre,f_pre))
  val res = RW [GSYM pre] res
  val def = CONJ def pre
  in (res,def) end

val _ = let
  val th = init_func_spec
  val pc = find_term (can (match_term (``zPC xx``))) (cdr (concl th))
  val post = ``let (r0,g) = (r0 + n2w (LENGTH (symbol_list BINIT_SYMBOLS)),init_func g r0) in
                 x * zR 0x0w r0 * zBYTE_MEMORY dg g * ~zS``
  val post = subst [mk_var("x",type_of pc)|->pc] post
  val (th,goal) = SPEC_WEAKEN_RULE th post
  val lemma = prove(goal,
    SIMP_TAC std_ss [EVAL ``LENGTH (symbol_list BINIT_SYMBOLS)``,LET_DEF]
    \\ SIMP_TAC (std_ss++star_ss) [SEP_IMP_REFL])
  val th = MP th lemma
  val i = numSyntax.int_of_term (find_term numSyntax.is_numeral pc)
  val _ = add_decompiled ("init_func",th,i,SOME i)
  in () end;

val one_fun2set_IMP = prove(
  ``(one (a,x) * p) (fun2set (g,dg DIFF xs)) ==>
    p (fun2set (g,dg DIFF (a INSERT xs))) /\ a IN dg``,
  SIMP_TAC std_ss [one_fun2set,IN_DIFF]
  \\ `dg DIFF (a INSERT xs) = dg DIFF xs DELETE a` by ALL_TAC
  \\ FULL_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC std_ss [EXTENSION,IN_DIFF,IN_INSERT,IN_DELETE]
  \\ METIS_TAC []);

val DIFF_EMPTY_LEMMA = prove(
  ``fun2set (g,dg) = fun2set (g,dg DIFF {})``,
  SIMP_TAC std_ss [DIFF_EMPTY]);

val LENGTH_EQ_IMP = prove(
  ``!xs y ys.
      (LENGTH xs = LENGTH (y::ys)) ==> ?z zs. (xs = z::zs) /\ (LENGTH zs = LENGTH ys)``,
  Cases \\ ASM_SIMP_TAC std_ss [LENGTH,ADD1,CONS_11]);

val init_func_lemma = prove(
  ``(LENGTH xs = LENGTH (symbol_list BINIT_SYMBOLS)) ==>
    (one_byte_list a (xs ++ ys)) (fun2set(g,dg)) /\ 520 <= LENGTH ys ==>
    init_func_pre dg a /\
    (one_symbol_list a BINIT_SYMBOLS (LENGTH (symbol_list BINIT_SYMBOLS ++ ys)) (fun2set(init_func g a,dg)))``,
  SIMP_TAC std_ss [one_symbol_list_def,SEP_EXISTS_THM,cond_STAR]
  \\ REPEAT STRIP_TAC THEN1
   (POP_ASSUM MP_TAC \\ POP_ASSUM MP_TAC \\ POP_ASSUM MP_TAC
    \\ SIMP_TAC std_ss [EVAL ``symbol_list BINIT_SYMBOLS``] \\ STRIP_TAC
    \\ NTAC 500 (IMP_RES_TAC LENGTH_EQ_IMP \\ POP_ASSUM MP_TAC
          \\ ASM_SIMP_TAC std_ss [] \\ REPEAT (POP_ASSUM (K ALL_TAC)) \\ STRIP_TAC)
    \\ FULL_SIMP_TAC std_ss [LENGTH_NIL,LENGTH]
    \\ FULL_SIMP_TAC std_ss [one_byte_list_def,word_arith_lemma1,APPEND]
    \\ FULL_SIMP_TAC std_ss [init_func_def,INSERT_SUBSET,EMPTY_SUBSET]
    \\ CONV_TAC (RATOR_CONV (ONCE_REWRITE_CONV [DIFF_EMPTY_LEMMA]))
    \\ REPEAT (STRIP_TAC
        \\ IMP_RES_TAC one_fun2set_IMP
        \\ POP_ASSUM MP_TAC
        \\ POP_ASSUM MP_TAC
        \\ REPEAT (POP_ASSUM (K ALL_TAC)))
    \\ SIMP_TAC std_ss [])
  \\ Q.EXISTS_TAC `ys` \\ ASM_SIMP_TAC std_ss []
  \\ STRIP_TAC THEN1 EVAL_TAC
  \\ POP_ASSUM MP_TAC \\ POP_ASSUM MP_TAC \\ POP_ASSUM MP_TAC
  \\ SIMP_TAC std_ss [EVAL ``symbol_list BINIT_SYMBOLS``] \\ STRIP_TAC
  \\ NTAC 500 (IMP_RES_TAC LENGTH_EQ_IMP \\ POP_ASSUM MP_TAC
        \\ ASM_SIMP_TAC std_ss [] \\ REPEAT (POP_ASSUM (K ALL_TAC)) \\ STRIP_TAC)
  \\ FULL_SIMP_TAC std_ss [LENGTH_NIL,LENGTH]
  \\ FULL_SIMP_TAC std_ss [one_byte_list_def,word_arith_lemma1,APPEND]
  \\ FULL_SIMP_TAC std_ss [init_func_def]
  \\ REPEAT STRIP_TAC \\ SEP_WRITE_TAC);

val init_func_thm = prove(
  ``1024 <= LENGTH xs ==>
    (one_byte_list a xs) (fun2set(g,dg)) ==>
    ?ys.
      init_func_pre dg a /\ 520 <= LENGTH ys /\
      (one_symbol_list a BINIT_SYMBOLS (LENGTH (symbol_list BINIT_SYMBOLS ++ ys)) (fun2set(init_func g a,dg))) /\
      (LENGTH xs = LENGTH (symbol_list BINIT_SYMBOLS ++ ys))``,
  `LENGTH (symbol_list BINIT_SYMBOLS) <= 504` by EVAL_TAC \\ FULL_SIMP_TAC std_ss []
  \\ REPEAT STRIP_TAC
  \\ `LENGTH (symbol_list BINIT_SYMBOLS) <= LENGTH xs` by DECIDE_TAC
  \\ IMP_RES_TAC (Q.SPECL [`xs`,`LENGTH ys`] SPLIT_LIST_LESS_EQ)
  \\ FULL_SIMP_TAC std_ss [LENGTH_APPEND]
  \\ `520 <= LENGTH xs2` by DECIDE_TAC
  \\ IMP_RES_TAC init_func_lemma \\ Q.EXISTS_TAC `xs2`
  \\ FULL_SIMP_TAC std_ss [LENGTH_APPEND]);

val ref_stack_space_SUC = prove(
  ``!n a.
      ref_stack_space a (SUC n) =
      SEP_EXISTS w. one (a - n2w (4 * n) - 4w,w) * ref_stack_space a n``,
  Induct THEN1 SIMP_TAC std_ss [ref_stack_space_def,SEP_CLAUSES,WORD_SUB_RZERO]
  \\ ONCE_REWRITE_TAC [EQ_SYM_EQ]
  \\ SIMP_TAC std_ss [Once ref_stack_space_def,SEP_CLAUSES,STAR_ASSOC]
  \\ SIMP_TAC std_ss [Once ref_stack_space_def,SEP_CLAUSES,STAR_ASSOC]
  \\ FULL_SIMP_TAC std_ss [SEP_CLAUSES,ADD1,word_arith_lemma1,LEFT_ADD_DISTRIB,
       AC ADD_COMM ADD_ASSOC]
  \\ FULL_SIMP_TAC std_ss [FUN_EQ_THM,SEP_EXISTS_THM] \\ METIS_TAC []);

val ref_stack_space_above_ADD = prove(
  ``!n m a.
      ref_stack_space_above a (n + m) =
      ref_stack_space (a + 4w + n2w (4 * n)) n *
      ref_stack_space_above (a + n2w (4 * n)) m``,
  Induct THEN1 SIMP_TAC std_ss [ref_stack_space_def,SEP_CLAUSES,WORD_ADD_0]
  \\ ASM_SIMP_TAC std_ss [ref_stack_space_SUC,WORD_ADD_0,ADD,ref_stack_space_above_def]
  \\ SIMP_TAC std_ss [word_arith_lemma1]
  \\ SIMP_TAC std_ss [word_arith_lemma4,DECIDE ``~(SUC n < n)``,
       DECIDE ``4 + 4 * SUC n - (4 * n + 4) = 4``]
  \\ FULL_SIMP_TAC (std_ss++star_ss) [ADD1,LEFT_ADD_DISTRIB,
       AC ADD_COMM ADD_ASSOC,SEP_CLAUSES]);

val lisp_init_def = Define `
  lisp_init (a1,a2,sl,sl1,e,ex,cs) (io:io_streams) (df,f,dg,g,dd,d,sp,sa1,sa_len,ds) =
     ?x xs hs.
       (ref_mem a1 (\x. H_EMP) 0 e * ref_mem a2 (\x. H_EMP) 0 e *
        ref_static sp ([a1; a2; n2w e; n2w sl; sa1; sa_len; x; ex] ++ cs ++ ds) *
       (* ref_stack_space (sp + 256w + 4w * n2w (sl + 1)) (sl + 6 + 1) *)
        ref_stack_space_above (sp + 228w) (sl + 6 + 1 + sl1))
         (fun2set (f,df)) /\
       e < 2147483648 /\ sl + 1 < 2**64 /\ 1024 <= w2n sa_len /\ sl1 < 2**30 /\
       (LENGTH cs = 10) /\ (LENGTH ds = 10) /\ (w2n (EL 3 cs) < 2**30) /\
       (a1 && 0x3w = 0x0w) /\ (a2 && 0x3w = 0x0w) /\ (sp && 0x3w = 0x0w) /\
       (w2n sa_len = LENGTH xs) /\ (one_byte_list sa1 xs) (fun2set(g,dg)) /\
       w2n sa1 + w2n sa_len < 2**64 /\ (w2n (EL 5 cs) < 2**30) /\
       (w2n (EL 5 ds) <= e) /\ (EL 7 ds = n2w sl1) /\
       (one_byte_list (EL 4 cs) hs) (fun2set(d,dd)) /\ (LENGTH hs = w2n (EL 5 cs))`;

val (mc_full_init_spec,mc_full_init_def) = basic_decompile_strings x64_tools "mc_full_init"
  (SOME (``(r7:word64,df:word64 set,f:word64->word32,dg:word64 set,g:word64->word8)``,
         ``(r0:word64,r1:word64,r2:word64,r3:word64,r6:word64,r7:word64,r8:word64,r9:word64,r10:word64,r11:word64,r12:word64,r13:word64,r14:word64,r15:word64,df:word64 set,f:word64->word32,dg:word64 set,g:word64->word8)``))
  (assemble "x64" `
      mov r3,[r7+24]
      mov r15,[r7+16]
      mov r0,[r7+32]
      mov r1,[r7+40]
      mov r2,[r7+8]
      mov r6,[r7]
      mov r8,[r7+96]
      mov r9,[r7+104]
      mov r10,[r7+88]
      add r1,r0
      insert init_func
      mov [r7+40],r0
      mov [r7+48],r1
      mov [r7+24],r2
      mov r1d,1
      xor r14,r14
      add r15,r15
      mov r0,r3
      shl r0,2
      dec r0
      add r0,256
      lea r12,[r7+r0]
      add r0,r7
      xor r11,r11
      mov [r7+152],r0
      mov [r7+160],r8
      mov [r7+168],r9
      mov [r7+216],r10
      mov [r7+208],r11
      mov [r7+192],r12
      add r7,256
      xor r2,r2
      not r2
      mov [r7+4*r3],r2d
      mov r0d,3
      mov r2,r0
      mov r8,r0
      mov r9,r0
      mov r10,r0
      mov r11,r0
      mov r12,r0
      mov r13,r0
   `);

val _ = save_thm("mc_full_init_spec",mc_full_init_spec);

val mc_full_init_blast = blastLib.BBLAST_PROVE
  ``(w2w ((w2w (w >>> 32)):word32) << 32 !! w2w ((w2w (w:word64)):word32) = w) /\
    ((63 >< 32) w = (w2w (w >>> 32)):word32) /\ ((31 >< 0) w = (w2w w):word32)``;

val mc_full_init_blast_select = blastLib.BBLAST_PROVE
  ``(w2w (w2w w1 << 32 !! (w2w:word32->word64) w2) = w2:word32) /\
    (w2w ((w2w w1 << 32 !! (w2w:word32->word64) w2) >>> 32) = w1:word32)``;

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

val EL_LEMMA = prove(
  ``!x y zs. EL 1 (x::y::zs) = y``,
  SIMP_TAC bool_ss [GSYM (EVAL ``SUC 0``),TL,HD,EL]);

val NO_CODE_def = Define `
  NO_CODE = BC_CODE ((\x:num.(NONE:bc_inst_type option)),0)`;

val one_fun2set_IMP = prove(
  ``(one (a,x)) (fun2set (f,df)) ==> (f a = x) /\ a IN df``,
  REPEAT STRIP_TAC
  \\ IMP_RES_TAC (REWRITE_RULE [SEP_CLAUSES] (Q.SPECL [`a`,`x`,`emp`] one_fun2set)));

val mc_full_init_thm = prove(
  ``lisp_init (a1,a2,sl,sl1,e,ex,cs) (io) (df,f,dg,g,dd,d,sp,sa1,sa_len,ds) ==>
    ?w0 w1 w2 w3 w4 w5 tw0 tw1 tw2 wi we wsp bp bp2 sa2 sa3 fi gi.
      mc_full_init_pre (sp,df,f,dg,g) /\
      (mc_full_init (sp,df,f,dg,g) = (tw0,tw1,tw2,wsp,bp,sp+256w,w2w w0,w2w w1,w2w w2,w2w w3,w2w w4,w2w w5,wi,we,df,fi,dg,gi)) /\
      let (x0,x1,x2,x3,x4,x5,xs,xs1,xbp,sp,f,g,ds,code,amnt,ok) = (Sym "NIL",Sym "NIL",Sym "NIL",Sym "NIL",Sym "NIL",Sym "NIL",[],[],0,sp+256w,fi,gi,UPDATE_NTH 6 (sp + 256w + 4w * n2w sl - 1w) (UPDATE_NTH 8 0w (UPDATE_NTH 9 (EL 3 cs) (UPDATE_NTH 3 (EL 5 cs) (UPDATE_NTH 2 (EL 4 cs) (UPDATE_NTH 1 (sp + 256w + n2w (4 * sl) - 1w) ds))))),NO_CODE,w2n (EL 3 cs),T) in ^LISP``,
  SIMP_TAC std_ss [LET_DEF,lisp_init_def]
  \\ ONCE_REWRITE_TAC [ref_stack_space_above_ADD]
  \\ `sp + 0xE4w + 0x4w + n2w (4 * (sl + 6 + 1)) =
      sp + 0x100w + 4w * n2w (sl + 1)` by ALL_TAC THEN1
    (FULL_SIMP_TAC std_ss [word_arith_lemma1,word_mul_n2w,LEFT_ADD_DISTRIB]
     \\ Q.SPEC_TAC (`4*sl`,`x`) \\ FULL_SIMP_TAC std_ss [AC ADD_COMM ADD_ASSOC])
  \\ FULL_SIMP_TAC std_ss [STAR_ASSOC] \\ REPEAT STRIP_TAC
  \\ Q.LIST_EXISTS_TAC [`3w`,`3w`,`3w`,`3w`,`3w`,`3w`,`3w`,`1w`,`3w`]
  \\ Q.LIST_EXISTS_TAC [`0w`,`n2w (2 * e)`,`n2w sl`]
  \\ Q.LIST_EXISTS_TAC [`a1`,`a2`,`sa1+n2w(LENGTH(symbol_list BINIT_SYMBOLS))`,`sa1+sa_len`]
  \\ FULL_SIMP_TAC wstd_ss [w2w_def,w2n_n2w]
  \\ FULL_SIMP_TAC std_ss [mc_full_init_def,ref_full_stack_def]
  \\ FULL_SIMP_TAC std_ss [WORD_ADD_SUB]
  \\ FULL_SIMP_TAC std_ss [ref_static_def,LET_DEF,APPEND,
       word64_3232_def,word_arith_lemma1,STAR_ASSOC,INSERT_SUBSET,EMPTY_SUBSET]
  \\ FULL_SIMP_TAC std_ss [align_add_blast,n2w_and_3]
  \\ SEP_R_TAC \\ FULL_SIMP_TAC std_ss [mc_full_init_blast]
  \\ SIMP_TAC std_ss [word_add_n2w,DECIDE ``2*n = n+n``]
  \\ `init_func_pre dg sa1` by METIS_TAC [init_func_thm]
  \\ FULL_SIMP_TAC std_ss [GSYM ADD1,ref_stack_space_def]
  \\ FULL_SIMP_TAC std_ss [ADD1,GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB]
  \\ FULL_SIMP_TAC std_ss [WORD_ADD_ASSOC,WORD_ADD_SUB,SEP_CLAUSES,STAR_ASSOC,word_mul_n2w]
  \\ SIMP_TAC std_ss [CONJ_ASSOC]
  \\ STRIP_TAC THEN1
   (REVERSE STRIP_TAC THEN1
     (FULL_SIMP_TAC std_ss [GSYM word_mul_n2w] \\ Q.SPEC_TAC (`(n2w sl):word64`,`slw`)
      \\ Q.PAT_ASSUM `sp && 3w = 0w` MP_TAC \\ blastLib.BBLAST_TAC)
    \\ REVERSE STRIP_TAC THEN1
     (FULL_SIMP_TAC std_ss [SEP_EXISTS_THM,AC WORD_ADD_COMM WORD_ADD_ASSOC] \\ SEP_R_TAC)
    \\ IMP_RES_TAC expand_list
    \\ FULL_SIMP_TAC std_ss [ref_static_def,LET_DEF,SEP_EXISTS_THM,
         word64_3232_def,APPEND,word_arith_lemma1,STAR_ASSOC,SEP_CLAUSES,
         ref_static_APPEND]
    \\ REPEAT (Q.PAT_ASSUM `(p_p * q_q) (fun2set (f_f,df_df))`
       (STRIP_ASSUME_TAC o MATCH_MP fun2set_STAR_IMP))
    \\ IMP_RES_TAC one_fun2set_IMP \\ FULL_SIMP_TAC std_ss [DIFF_UNION]
    \\ FULL_SIMP_TAC std_ss [IN_DIFF])
  \\ ASM_SIMP_TAC std_ss []
  \\ `n2w (4 * sl) = (n2w sl << 2):word64` by FULL_SIMP_TAC std_ss [WORD_MUL_LSL,word_mul_n2w]
  \\ ASM_SIMP_TAC std_ss []
  \\ SIMP_TAC std_ss [lisp_inv_def,IS_TRUE_def]
  \\ NTAC 6 (Q.EXISTS_TAC `H_DATA (INR (n2w 0))`)
  \\ Q.EXISTS_TAC `\x.H_EMP`
  \\ Q.LIST_EXISTS_TAC [`0`,`[]`,`[]`,`["PEQUAL"]`,`T`]
  \\ ASM_SIMP_TAC wstd_ss [LENGTH,w2n_n2w,DECIDE ``2*n = n+n``,word_add_n2w]
  \\ `sl < 18446744073709551616` by DECIDE_TAC
  \\ ASM_SIMP_TAC std_ss [LENGTH_UPDATE_NTH]
  \\ REPEAT STRIP_TAC THEN1
   (SIMP_TAC (srw_ss()) [ok_split_heap_def,APPEND,UNION_SUBSET,
      ADDR_SET_THM,EMPTY_SUBSET,memory_ok_def,EXTENSION,NOT_IN_EMPTY]
    \\ SIMP_TAC (srw_ss()) [SUBSET_DEF,IN_DEF,D1_def,R0_def])
  THEN1
   (FULL_SIMP_TAC std_ss [EVERY_DEF,ZIP,APPEND]
    \\ FULL_SIMP_TAC std_ss [lisp_x_def] \\ Q.EXISTS_TAC `0` \\ EVAL_TAC)
  THEN1
   (FULL_SIMP_TAC std_ss [MAP,ref_heap_addr_def] \\ EVAL_TAC)
  THEN1
   (FULL_SIMP_TAC wstd_ss [align_add_blast] \\ EVAL_TAC)
  THEN1
   (IMP_RES_TAC expand_list \\ FULL_SIMP_TAC std_ss [] \\ EVAL_TAC)
  THEN1
   (IMP_RES_TAC expand_list \\ FULL_SIMP_TAC std_ss [] \\ EVAL_TAC)
  THEN1
   (IMP_RES_TAC expand_list \\ FULL_SIMP_TAC std_ss [EL_CONS] \\ EVAL_TAC)
  THEN1
   (IMP_RES_TAC expand_list \\ FULL_SIMP_TAC std_ss [EL_CONS] \\ EVAL_TAC)
  THEN1
   (FULL_SIMP_TAC std_ss [EL_UPDATE_NTH])
  THEN1
   (IMP_RES_TAC expand_list \\ FULL_SIMP_TAC std_ss [EL_CONS] \\ EVAL_TAC)
  THEN1
   (IMP_RES_TAC expand_list
    \\ FULL_SIMP_TAC std_ss [EL_CONS,UPDATE_NTH_CONS,APPEND]
    \\ FULL_SIMP_TAC std_ss [ref_static_def,LET_DEF,APPEND,ref_full_stack_def,
         word_arith_lemma1,word64_3232_def,word_arith_lemma1,STAR_ASSOC,word_mul_n2w,
         word_arith_lemma3,word_arith_lemma4,WORD_ADD_0,ref_stack_def,SEP_EXISTS_THM,
         ref_static_APPEND,ref_static_def,LENGTH]
    \\ FULL_SIMP_TAC std_ss [GSYM word_add_n2w]
    \\ FULL_SIMP_TAC std_ss [AC WORD_ADD_COMM WORD_ADD_ASSOC]
    \\ FULL_SIMP_TAC std_ss [EVAL ``(w2w (~0x0w:word64)):word32``]
    \\ FULL_SIMP_TAC wstd_ss [w2n_n2w,SEP_CLAUSES,mc_full_init_blast_select]
    \\ `f (sp + 0x6Cw) = w2w (c5' >>> 32)` by SEP_READ_TAC
    \\ `f (sp + 0x68w) = w2w (c5')` by SEP_READ_TAC
    \\ `f (sp + 0x64w) = w2w (c4' >>> 32)` by SEP_READ_TAC
    \\ `f (sp + 0x60w) = w2w (c4')` by SEP_READ_TAC
    \\ `f (sp + 0x5Cw) = w2w (c3' >>> 32)` by SEP_READ_TAC
    \\ `f (sp + 0x58w) = w2w (c3')` by SEP_READ_TAC
    \\ ASM_SIMP_TAC std_ss []
    \\ FULL_SIMP_TAC std_ss [WORD_ADD_ASSOC,word_arith_lemma4]
    \\ `sp + 0xE4w + n2w (4 * (sl + 6 + 1)) = sp + n2w sl << 2 + 0x100w` by ALL_TAC THEN1
     (SIMP_TAC std_ss [GSYM ADD_ASSOC,LEFT_ADD_DISTRIB,WORD_MUL_LSL]
      \\ SIMP_TAC bool_ss [GSYM word_add_n2w,GSYM word_mul_n2w,DECIDE ``256 = 0x1C + 0xE4:num``]
      \\ FULL_SIMP_TAC std_ss [AC WORD_ADD_COMM WORD_ADD_ASSOC])
    \\ FULL_SIMP_TAC std_ss []
    \\ SEP_WRITE_TAC)
  THEN1
   (FULL_SIMP_TAC std_ss [symtable_inv_def,GSYM BINIT_SYMBOLS_def]
    \\ IMP_RES_TAC init_func_thm
    \\ Cases_on `sa1` \\ Cases_on `sa_len`
    \\ FULL_SIMP_TAC wstd_ss [word_add_n2w,w2n_n2w]
    \\ Q.PAT_ASSUM `n' = xxx` ASSUME_TAC \\ FULL_SIMP_TAC std_ss []
    \\ NO_TAC)
  THEN1
   (IMP_RES_TAC expand_list
    \\ FULL_SIMP_TAC std_ss [EL_CONS,UPDATE_NTH_CONS,APPEND]
    \\ SIMP_TAC std_ss [code_heap_def]
    \\ Q.LIST_EXISTS_TAC [`[]`,`hs`]
    \\ ASM_SIMP_TAC std_ss [bs2bytes_def,bc_symbols_ok_def,APPEND,WRITE_CODE_def,
         NO_CODE_def,WORD_ADD_0,EL_UPDATE_NTH,code_ptr_def]))
  |> SIMP_RULE std_ss [LET_DEF];

val mc_full_init_pre_thm = store_thm("mc_full_init_pre_thm",
  ``mc_full_init_pre (sp,df,f,dg,g) /\
    lisp_init (a1,a2,sl,sl1,e,ex,cs) io (df,f,dg,g,dd,d,sp,sa1,sa_len,ds) =
    lisp_init (a1,a2,sl,sl1,e,ex,cs) io (df,f,dg,g,dd,d,sp,sa1,sa_len,ds)``,
  REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC \\ ASM_SIMP_TAC std_ss []
  \\ MP_TAC mc_full_init_thm \\ ASM_SIMP_TAC std_ss []
  \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss []);

val _ = save_thm("mc_full_init_thm",mc_full_init_thm);


val _ = export_theory();

