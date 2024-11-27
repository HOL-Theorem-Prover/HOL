open HolKernel Parse boolLib bossLib; val _ = new_theory "lisp_correctness";

open lisp_sexpTheory lisp_invTheory lisp_opsTheory lisp_bigopsTheory;
open lisp_codegenTheory lisp_initTheory lisp_symbolsTheory;
open lisp_sexpTheory lisp_invTheory lisp_parseTheory;
open lisp_semanticsTheory lisp_compilerTheory lisp_compiler_opTheory progTheory;
open compilerLib decompilerLib codegenLib prog_x64Lib lisp_bytecode_stepTheory;
open lisp_compiler_opTheory;

open wordsTheory arithmeticTheory wordsLib listTheory pred_setTheory pairTheory;
open combinTheory finite_mapTheory addressTheory helperLib sumTheory;
open set_sepTheory bitTheory fcpTheory stringTheory optionTheory relationTheory;

infix \\
val op \\ = op THEN;
val RW = REWRITE_RULE;
val RW1 = ONCE_REWRITE_RULE;

val _ = let
  val thms = DB.match [] ``SPEC X64_MODEL``
  val thms = filter (can (find_term (can (match_term ``zLISP``))) o car o concl)
                    (map (#1 o #2) thms)
  val thms = map (INST [``ddd:bool option``|->``SOME T``]) thms
  val _ = map (fn th => add_compiled [th] handle e => ()) thms
  in () end;

val _ = max_print_depth := 50;


(* semantics of the read-eval-print loop *)

(*
val (R_exec_rules,R_exec_ind,R_exec_cases) = Hol_reln `
 (!input fns io rest.
    (is_eof input = (T,rest)) ==>
    R_exec (input,fns,io,ok) (io,ok))
  /\
 (!input fns io ok input2 exp rest s fns2 io2 io3 ok2 ok3.
    (is_eof input = (F,input2)) /\
    (sexp_parse_stream input2 = (exp,rest)) /\
    R_ev (sexp2term exp,FEMPTY,fns,io,ok) (s,fns2,io2,ok2) /\
    R_exec (rest,fns2,io2 ++ sexp2string s ++ "\n",ok2) (io3,ok3) ==>
    R_exec (input,fns,io,ok) (io3,ok3))`;
*)

val zERROR_MESSAGE_def = Define `
  zERROR_MESSAGE ex =
    SEP_EXISTS a1 a2 sl sl1 e cs rbp ddd cu.
      zLISP_FAIL (a1,a2,sl,sl1,e,ex,cs,rbp,ddd,cu)`;

val zLISP_OUTPUT_def = Define `
  zLISP_OUTPUT (io,ok) =
    SEP_EXISTS a1 a2 sl sl1 e ex cs rbp ddd cu x0 x1 x2 x3 x4 x5 xs xs1 xbp qs code amnt.
      zLISP (a1,a2,sl,sl1,e,ex,cs,rbp,ddd,cu) (x0,x1,x2,x3,x4,x5,xs,xs1,io,xbp,qs,code,amnt,ok)`;

val R_exec_TERMINATES_def = Define `
  R_exec_TERMINATES input = ?y. R_exec (input,FEMPTY,"") y`;

(*  *)

val c = READ_EVAL_PRINT_LOOP_BASE |> concl |> rator |> rand
val pc = READ_EVAL_PRINT_LOOP_BASE |> concl |> rand |> find_term (can (match_term ``p + n2w n``))

val getOUTPUT_def = Define `getOUTPUT (IO_STREAMS xs ys) = ys`;

val PULL_FORALL_IMP = METIS_PROVE [] ``(Q ==> !x. P x) = !x. Q ==> P x``
val IMP_IMP = METIS_PROVE [] ``b /\ (c ==> d) ==> ((b ==> c) ==> d)``

val IO_WRITE_RW = prove(
  ``!io s. (getINPUT (IO_WRITE io s) = getINPUT io) /\
           (getOUTPUT (IO_WRITE io s) = getOUTPUT io ++ s)``,
  Cases \\ EVAL_TAC \\ SIMP_TAC std_ss []);

val LENGTH_SND_read_while = prove(
  ``!t p s. STRLEN (SND (read_while p t s)) <= STRLEN t``,
  Induct \\ SIMP_TAC std_ss [read_while_def] \\ SRW_TAC [] []
  \\ Q.PAT_X_ASSUM `!p.bbb` (ASSUME_TAC o Q.SPECL [`p`,`STRCAT s (STRING h "")`])
  \\ DECIDE_TAC);

val is_eof_T_IMP = prove(
  ``(is_eof s = (T,rest)) ==> (rest = "")``,
  completeInduct_on `LENGTH s` \\ FULL_SIMP_TAC std_ss [PULL_FORALL_IMP]
  \\ Cases \\ SIMP_TAC std_ss [is_eof_def,LET_DEF] \\ STRIP_TAC
  \\ FULL_SIMP_TAC std_ss []
  \\ Cases_on `space_char h` \\ FULL_SIMP_TAC std_ss [] THEN1
   (`STRLEN t < STRLEN (STRING h t)` by (EVAL_TAC \\ DECIDE_TAC)
    \\ RES_TAC \\ ASM_SIMP_TAC std_ss [])
  \\ Cases_on `h = #";"` \\ FULL_SIMP_TAC std_ss []
  \\ Q.PAT_X_ASSUM `!s.bbb` MATCH_MP_TAC
  \\ MATCH_MP_TAC LESS_EQ_LESS_TRANS \\ Q.EXISTS_TAC `STRLEN t`
  \\ ASM_SIMP_TAC std_ss [LENGTH_SND_read_while] \\ SIMP_TAC std_ss [LENGTH]);

val hide_code_def = Define `hide_code p cs = ^c`;

val STAR_LEMMA = prove(
  ``(STAR p1 p2) * p3 = p3 * p2 * p1``,
  SIMP_TAC (std_ss++star_ss) []);

val BC_EV_HILBERT_LEMMA = prove(
  ``BC_CODE_OK bc /\ BC_ev T (t,a,q,bc) y ==> ((@result. BC_ev T (t,a,q,bc) result) = y)``,
  METIS_TAC [BC_ev_DETERMINISTIC]);

val CONTAINS_BYTECODE_with_code_end = prove(
  ``!xs bc a. CONTAINS_BYTECODE (bc with code_end := y) a xs =
              CONTAINS_BYTECODE bc a xs``,
  Induct \\ ASM_SIMP_TAC (srw_ss()) [CONTAINS_BYTECODE_def]);

val WRITE_BYTECODE_compiled = prove(
  ``!xs bc a. (WRITE_BYTECODE bc a xs).compiled = bc.compiled``,
  Induct \\ ASM_SIMP_TAC (srw_ss()) [WRITE_BYTECODE_def]);

val BC_ONLY_COMPILE_LEMMA = prove(
  ``BC_REFINES (fns,output) bc1 /\ BC_JUMPS_OK bc1 /\
    BC_ev T (sexp2term exp,[],bc1.code_end,bc1) (code,a2,p2,bc0) ==>
    BC_REFINES (fns,output) (BC_ONLY_COMPILE ([],sexp2term exp,bc1)) /\
    BC_SUBSTATE bc0 (BC_ONLY_COMPILE ([],sexp2term exp,bc1)) /\
    CONTAINS_BYTECODE (BC_ONLY_COMPILE ([],sexp2term exp,bc1)) bc1.code_end code``,
  STRIP_TAC \\ IMP_RES_TAC BC_REFINES_ONLY_COMPILE
  \\ ASM_SIMP_TAC std_ss [] \\ POP_ASSUM (K ALL_TAC)
  \\ FULL_SIMP_TAC std_ss [BC_ONLY_COMPILE_def]
  \\ `BC_ev_fun ([],sexp2term exp,bc1) = (code,a2,p2,bc0)` by
      (FULL_SIMP_TAC std_ss [BC_ev_fun_def,BC_EV_HILBERT_LEMMA,MAP,REVERSE_DEF,BC_REFINES_def])
  \\ FULL_SIMP_TAC std_ss [LET_DEF,WRITE_BYTECODE_code_end]
  \\ IMP_RES_TAC BC_ev_fun_CONSTS \\ FULL_SIMP_TAC std_ss []
  \\ `BC_CODE_OK (WRITE_BYTECODE bc0 bc0.code_end code with
       code_end := bc0.code_end + iLENGTH bc0.instr_length code)` by
   (FULL_SIMP_TAC (srw_ss()) [BC_SUBSTATE_def,WRITE_BYTECODE_code_end,
      BC_REFINES_def,BC_CODE_OK_def] \\ REPEAT STRIP_TAC
    \\ `bc0.code_end <= i` by DECIDE_TAC \\ RES_TAC
    \\ POP_ASSUM (fn th => FULL_SIMP_TAC std_ss [GSYM th])
    \\ MATCH_MP_TAC WRITE_BYTECODE_SKIP \\ FULL_SIMP_TAC std_ss [])
  \\ REVERSE (REPEAT STRIP_TAC) THEN1
   (FULL_SIMP_TAC std_ss [CONTAINS_BYTECODE_with_code_end]
    \\ MATCH_MP_TAC CONTAINS_BYTECODE_WRITE_BYTECODE
    \\ FULL_SIMP_TAC std_ss [BC_CODE_OK_def,BC_REFINES_def])
  \\ FULL_SIMP_TAC (srw_ss()) [BC_SUBSTATE_def,WRITE_BYTECODE_code_end,
      BC_REFINES_def,WRITE_BYTECODE_compiled] \\ REPEAT STRIP_TAC
  \\ MATCH_MP_TAC WRITE_BYTECODE_SKIP_LESS
  \\ Cases_on `bc0.code_end <= i` \\ RES_TAC \\ DECIDE_TAC);

val WRITE_BYTECODE_code_IGNORE = prove(
  ``!xs n bc. 0 < n ==> ((WRITE_BYTECODE bc n xs).code 0 = bc.code 0)``,
  Induct \\ ASM_SIMP_TAC std_ss [WRITE_BYTECODE_def] \\ REPEAT STRIP_TAC
  \\ `0 < n + bc.instr_length h /\ ~(n = 0)` by DECIDE_TAC
  \\ ASM_SIMP_TAC (srw_ss()) [APPLY_UPDATE_THM]);

val BC_ONLY_COMPILE_iRETURN = prove(
  ``(bc.code 0 = SOME iRETURN) /\ BC_JUMPS_OK bc /\ BC_CODE_OK bc ==>
    ((BC_ONLY_COMPILE (x,exp,bc)).code 0 = SOME iRETURN)``,
  SIMP_TAC std_ss [BC_ONLY_COMPILE_def] \\ REPEAT STRIP_TAC
  \\ `?z1 z2 z3 z4. BC_ev_fun (x,exp,bc) = (z1,z2,z3,z4)` by METIS_TAC [PAIR]
  \\ IMP_RES_TAC BC_ev_fun_CONSTS \\ FULL_SIMP_TAC (srw_ss()) [LET_DEF]
  \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [bc_inv_def,BC_CODE_OK_def]
  \\ Cases_on `z4.code_end <= 0` THEN1 (RES_TAC \\ FULL_SIMP_TAC std_ss [])
  \\ `0 < z4.code_end` by DECIDE_TAC
  \\ FULL_SIMP_TAC std_ss [WRITE_BYTECODE_code_IGNORE]);

val iSTEP_iRETURN = prove(
  ``!x y. iSTEP^* x y ==>
          !x1 x2 x3 x4 y1 y2 y3 y4.
            (x = (x1,x2,x3,x4)) /\ (y = (y1,y2,y3,y4)) ==>
            (x4.code 0 = SOME iRETURN) /\ bc_inv x4 ==>
            (y4.code 0 = SOME iRETURN) /\ bc_inv y4``,
  HO_MATCH_MP_TAC RTC_INDUCT \\ SIMP_TAC std_ss [PULL_FORALL_IMP]
  \\ ONCE_REWRITE_TAC [iSTEP_cases] \\ NTAC 8 STRIP_TAC
  \\ POP_ASSUM MP_TAC \\ POP_ASSUM MP_TAC \\ FULL_SIMP_TAC std_ss [] \\ RES_TAC
  THEN1 (FULL_SIMP_TAC (srw_ss()) [BC_FAIL_def,bc_inv_def,BC_CODE_OK_def])
  THEN1 (FULL_SIMP_TAC (srw_ss()) [BC_PRINT_def,bc_inv_def,BC_CODE_OK_def])
  THEN1
   (NTAC 2 STRIP_TAC
    \\ `bc_inv bc1 /\ (bc1.code 0 = SOME iRETURN)` by
     (`bc_inv bc1` by METIS_TAC [bc_inv_BC_COMPILE] \\ ASM_SIMP_TAC std_ss []
      \\ Q.PAT_X_ASSUM `BC_COMPILE (getSym fname,MAP getSym (sexp2list formals),sexp2term body,bc) = bc1`
           (fn th => ONCE_REWRITE_TAC [GSYM th])
      \\ SIMP_TAC std_ss [BC_COMPILE_def,LET_DEF,LENGTH_MAP]
      \\ Q.ABBREV_TAC `bcA = BC_STORE_COMPILED bc (getSym fname) (bc.code_end,LENGTH (sexp2list formals))`
      \\ `BC_JUMPS_OK bcA` by
       (Q.UNABBREV_TAC `bcA`
        \\ FULL_SIMP_TAC (srw_ss()) [BC_STORE_COMPILED_def,BC_JUMPS_OK_def,bc_inv_def]
        \\ EVAL_TAC \\ SIMP_TAC std_ss [])
      \\ `BC_CODE_OK bcA` by
       (Q.UNABBREV_TAC `bcA`
        \\ FULL_SIMP_TAC (srw_ss()) [BC_STORE_COMPILED_def,BC_CODE_OK_def,bc_inv_def]
        \\ EVAL_TAC \\ SIMP_TAC std_ss []
        \\ Cases_on `h` \\ EVAL_TAC \\ Cases_on `l` \\ EVAL_TAC)
      \\ MATCH_MP_TAC BC_ONLY_COMPILE_iRETURN \\ ASM_SIMP_TAC std_ss []
      \\ Q.UNABBREV_TAC `bcA` \\ FULL_SIMP_TAC (srw_ss()) [BC_STORE_COMPILED_def])
    \\ METIS_TAC [])
  THEN1 (FULL_SIMP_TAC (srw_ss()) [BC_FAIL_def,bc_inv_def,BC_CODE_OK_def]))
  |> SIMP_RULE std_ss [PULL_FORALL_IMP];

val BC_ONLY_COMPILE_THM = prove(
  ``bc_inv bc1 /\ R_ev (sexp2term exp,FEMPTY,fns,output,bc1.ok) (s,fns2,io2,ok8) /\
    BC_REFINES (fns,output) bc1 /\ (bc1.code 0 = SOME iRETURN) ==>
    ?bc8.
      iSTEP^* ([],bc1.code_end,[0],BC_ONLY_COMPILE ([],sexp2term exp,bc1))
        ([s],0,[],bc8) /\ (bc8.code 0 = SOME iRETURN) /\
      BC_REFINES (fns2,io2) bc8 /\ bc_inv bc8 /\ (ok8 = bc8.ok)``,
  REPEAT STRIP_TAC
  \\ `BC_JUMPS_OK bc1` by
   (FULL_SIMP_TAC std_ss [bc_inv_def,BC_JUMPS_OK_def]
    \\ EVAL_TAC \\ SIMP_TAC std_ss [])
  \\ `?code a2 p2 bc0. BC_ev T (sexp2term exp,[],bc1.code_end,bc1) (code,a2,p2,bc0)` by METIS_TAC [BC_ev_TOTAL,PAIR]
  \\ (Q.INST [`a`|->`[]`,`env`|->`FEMPTY`,`stack`|->`[]`,`r`|->`0`,
             `rs`|->`[]`,`bc7`|->`BC_ONLY_COMPILE ([],sexp2term exp,bc1)`,`c`|->`sexp2term exp`,
             `io`|->`output`,`fns8`|->`fns2`,`io8`|->`io2`,`ret`|->`T`,
             `result`|->`s`,`p`|->`bc1.code_end`,`bc`|->`bc1`] (SPEC_ALL BC_ev_thm)
      |> RW [LENGTH,DROP_0,STACK_INV_def,VARS_IN_STACK_def,FDOM_FEMPTY,NOT_IN_EMPTY]
      |> SIMP_RULE std_ss [] |> MP_TAC)
  \\ ASM_SIMP_TAC std_ss [BC_ONLY_COMPILE_io_out]
  \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1 METIS_TAC [BC_ONLY_COMPILE_LEMMA]
  \\ REPEAT STRIP_TAC \\ Q.EXISTS_TAC `bc8` \\ ASM_SIMP_TAC std_ss []
  \\ `bc_inv (BC_ONLY_COMPILE ([],sexp2term exp,bc1))` by
        ASM_SIMP_TAC std_ss [bc_inv_BC_ONLY_COMPILE |> Q.INST [`params`|->`Sym "NIL"`]
                             |> SIMP_RULE std_ss [sexp2list_def,MAP]]
  \\ `(BC_ONLY_COMPILE ([],sexp2term exp,bc1)).code 0 = SOME iRETURN` by
       (MATCH_MP_TAC BC_ONLY_COMPILE_iRETURN \\ FULL_SIMP_TAC std_ss [bc_inv_def])
  \\ METIS_TAC [iSTEP_iRETURN]);

val BC_SUBSTATE_IGNORE_IO = prove(
  ``BC_SUBSTATE bc (bc1 with io_out := x) = BC_SUBSTATE bc bc1``,
  SIMP_TAC (srw_ss()) [BC_SUBSTATE_def,BC_CODE_OK_def]);

val CONTAINS_BYTECODE_IGNORE_IO = prove(
  ``!xs n. CONTAINS_BYTECODE (bc1 with io_out := x) n xs = CONTAINS_BYTECODE bc1 n xs``,
  Induct \\ FULL_SIMP_TAC (srw_ss()) [CONTAINS_BYTECODE_def]);

val READ_EVAL_PRINT_LOOP_THM = prove(
  ``!x y. R_exec x y ==>
    !input fns output output2 ok2. (x = (input,fns,output)) /\ (y = (output2,ok2)) ==>
    !x0 x1 x2 x3 x4 x5 xs xs1 xbp io code bc1.
      (getINPUT io = input) /\ (getOUTPUT io = output) /\ BC_REFINES (fns,output) bc1 /\
      bc_inv bc1 /\ (bc1.code 0 = SOME iRETURN) /\ bc1.ok ==>
      SPEC X64_MODEL
        (zLISP_BYTECODE_SHORT
          (a1,a2,sl,sl1,e,ex,cs,rbp,SOME T,NONE,x0,p,[],bc1,stack,input,
           SUC (LENGTH stack),rstack,amnt,EL 4 cs)) (hide_code p cs)
        (zERROR_MESSAGE ex \/ ~zS * zPC ^pc * zLISP_OUTPUT (IO_STREAMS "" output2,ok2))``,
  HO_MATCH_MP_TAC R_exec_ind \\ SIMP_TAC std_ss [PULL_FORALL_IMP]
  \\ REPEAT STRIP_TAC THEN1
   (MATCH_MP_TAC (MATCH_MP SPEC_WEAKEN READ_EVAL_PRINT_LOOP_BASE
      |> RW [GSYM hide_code_def]
      |> SPEC_ALL |> DISCH_ALL |> RW [AND_IMP_INTRO])
    \\ ASM_SIMP_TAC (srw_ss()) [LISP_TEST_def]
    \\ SIMP_TAC std_ss [zLISP_BYTECODE_SHORT_def,zLISP_BYTECODE_def,HD,TL,APPEND]
    \\ SIMP_TAC std_ss [Once SEP_DISJ_COMM]
    \\ MATCH_MP_TAC SEP_IMP_DISJ \\ STRIP_TAC
    THEN1 (SIMP_TAC std_ss [zERROR_MESSAGE_def,SEP_IMP_def,SEP_EXISTS_THM]
           \\ METIS_TAC [])
    \\ IMP_RES_TAC is_eof_T_IMP \\ FULL_SIMP_TAC std_ss []
    \\ CONV_TAC (RAND_CONV (SIMP_CONV std_ss [Once STAR_LEMMA]))
    \\ SIMP_TAC std_ss [zLISP_OUTPUT_def,SEP_IMP_def,SEP_EXISTS_THM,SEP_CLAUSES]
    \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [cond_STAR,BC_REFINES_def]
    \\ FULL_SIMP_TAC std_ss [] \\ METIS_TAC [])
  \\ MATCH_MP_TAC
     (Q.SPECL [`x`,`p`,`c`,`m`,`c`,`q`] SPEC_COMPOSE
      |> RW [UNION_IDEMPOT,GSYM AND_IMP_INTRO]
      |> (fn th => MATCH_MP th (RW [GSYM hide_code_def] READ_EVAL_PRINT_LOOP_STEP))
      |> DISCH_ALL |> RW [AND_IMP_INTRO] |> GEN_ALL)
  \\ ASM_SIMP_TAC std_ss [LISP_TEST_def,read_sexp_def,getINPUT_def]
  \\ `?bc8. iSTEP^* ([],bc1.code_end,[0],BC_ONLY_COMPILE ([],sexp2term exp,bc1))
                    ([s],0,[],bc8) /\ (bc8.code 0 = SOME iRETURN) /\
                    BC_REFINES (fns2,io2) bc8 /\ bc_inv bc8 /\ (ok2 <=> bc8.ok)` by
      (MATCH_MP_TAC (GEN_ALL BC_ONLY_COMPILE_THM) \\ ASM_SIMP_TAC std_ss []
       \\ Q.LIST_EXISTS_TAC [`getOUTPUT io'`,`fns`]
       \\ FULL_SIMP_TAC std_ss [])
  \\ Q.LIST_EXISTS_TAC [`s`,`bc8`] \\ ASM_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC std_ss [AND_IMP_INTRO,next_sexp_def,IO_INPUT_APPLY_def,
        REPLACE_INPUT_IO_def,getINPUT_def]
  \\ Cases_on `bc8.ok` \\ FULL_SIMP_TAC std_ss [] THEN1
   (Q.PAT_X_ASSUM `!x0.bbb` MATCH_MP_TAC
    \\ Q.EXISTS_TAC `IO_STREAMS rest (STRCAT (STRCAT io2 (sexp2string s)) "\n")`
    \\ FULL_SIMP_TAC (srw_ss()) [getINPUT_def,getOUTPUT_def,BC_PRINT_def]
    \\ FULL_SIMP_TAC (srw_ss()) [bc_inv_def,BC_REFINES_def,BC_CODE_OK_def,
         BC_FNS_ASSUM_def,BC_SUBSTATE_IGNORE_IO,CONTAINS_BYTECODE_IGNORE_IO]
    \\ METIS_TAC [])
  \\ ASM_SIMP_TAC (srw_ss()) [zLISP_BYTECODE_SHORT_def,zLISP_BYTECODE_def,
       BC_PRINT_def,zLISP_def,lisp_inv_def,IS_TRUE_def,SEP_CLAUSES,zLISP_OUTPUT_def,
       zERROR_MESSAGE_def]
  \\ (SPEC_WEAKEN |> SPEC_ALL |> UNDISCH_ALL |> SPEC_ALL |> DISCH_ALL
       |> SIMP_RULE std_ss [AND_IMP_INTRO] |> GEN_ALL |> MATCH_MP_TAC)
  \\ Q.EXISTS_TAC `(zLISP_FAIL (a1,a2,sl,sl1,e,ex,cs,rbp,SOME T,NONE))`
  \\ SIMP_TAC std_ss [SPEC_REFL] \\ SIMP_TAC std_ss [SEP_IMP_def,SEP_EXISTS_THM]
  \\ METIS_TAC []);

val main_loop_final = let
  val th =
    READ_EVAL_PRINT_LOOP_THM
    |> SIMP_RULE std_ss [PULL_FORALL_IMP] |> SPEC_ALL
    |> Q.INST [`io`|->`IO_STREAMS input ""`,`ok`|->`T`] |> RW [getINPUT_def,getOUTPUT_def]
    |> UNDISCH_ALL |> RW [zLISP_BYTECODE_SHORT_def,zLISP_BYTECODE_def]
    |> RW [SPEC_PRE_DISJ] |> CONJUNCT1 |> DISCH_ALL
    |> RW [GSYM SPEC_MOVE_COND,HD,TL]
    |> (fn th => SPEC_BOOL_FRAME_RULE th ``R_exec (input,fns,"") (output2,ok2)``)
    |> Q.INST [`fns`|->`FEMPTY`]
    |> SIMP_RULE std_ss [GSYM SPEC_PRE_EXISTS,SEP_CLAUSES] |> SPEC_ALL
  val pc = th |> concl |> rand |> find_term (can (match_term ``zPC x``))
  val (th,goal) = SPEC_WEAKEN_RULE th
    ``zERROR_MESSAGE ex \/
      SEP_EXISTS result. cond (R_exec (input,FEMPTY,"") (result,T)) *
                         ~zS * ^pc * zLISP_OUTPUT (IO_STREAMS "" result,T)``
  val lemma = prove(goal,
    SIMP_TAC std_ss [SEP_IMP_MOVE_COND] \\ REPEAT STRIP_TAC
    \\ MATCH_MP_TAC SEP_IMP_DISJ \\ SIMP_TAC std_ss [SEP_IMP_REFL]
    \\ SIMP_TAC (std_ss++sep_cond_ss) [SEP_IMP_def,SEP_CLAUSES,SEP_EXISTS_THM,cond_STAR]
    \\ REVERSE (Cases_on `ok2`) THEN1
     (SIMP_TAC std_ss [zLISP_OUTPUT_def,zLISP_def,lisp_inv_def,IS_TRUE_def,
        SEP_CLAUSES] \\ SIMP_TAC std_ss [SEP_F_def])
    \\ REPEAT STRIP_TAC \\ Q.EXISTS_TAC `output2` \\ FULL_SIMP_TAC std_ss [])
  val th = MP th lemma
    |> Q.GEN `output2` |> Q.GEN `ok2` |> Q.GEN `bc1`
    |> SIMP_RULE std_ss [SPEC_PRE_EXISTS,SEP_CLAUSES,HD,TL,APPEND]
  val (th,goal) = SPEC_STRENGTHEN_RULE th
    ``zLISP (a1,a2,sl,sl1,e,ex,cs,rbp,SOME T,NONE)
          (x0,x1,x2,x3,x4,Dot (Sym "NIL") (Sym "NIL"),Sym "NIL"::stack,[],
           IO_STREAMS input "",SUC (LENGTH stack),rstack,
           WRITE_CODE NO_CODE [iRETURN],amnt,T) * zPC p * ~zS *
      cond (R_exec_TERMINATES input)``
  val lemma = prove(goal,
    SIMP_TAC std_ss [SEP_IMP_def,SEP_EXISTS_THM] \\ REPEAT STRIP_TAC
    \\ FULL_SIMP_TAC std_ss [R_exec_TERMINATES_def,cond_STAR]
    \\ `?output ok. y = (output,ok)` by METIS_TAC [PAIR]
    \\ FULL_SIMP_TAC std_ss []
    \\ Q.EXISTS_TAC `<| compiled := []; consts := []; io_out := "";
           code := (0 =+ SOME iRETURN) (\x.NONE); code_end := 2;
           instr_length := bc_length; ok := T |>`
    \\ Q.EXISTS_TAC `ok`
    \\ Q.EXISTS_TAC `output`
    \\ FULL_SIMP_TAC (srw_ss()) [bc_state_tree_def,flat_alist_def,list2sexp_def,
         APPLY_UPDATE_THM,EVAL ``WRITE_CODE NO_CODE [iRETURN]``]
    \\ `!h. 0 < LENGTH (bc_ref (0,[]) h)` by
         (Cases \\ EVAL_TAC \\ Cases_on `l` \\ EVAL_TAC)
    \\ EVAL_TAC \\ ASM_SIMP_TAC std_ss []
    \\ FULL_SIMP_TAC std_ss [SUBSET_DEF,GSPECIFICATION])
  val th = MP th lemma
  in RW [hide_code_def] th end


(* new init code *)

val ff = INST [``ddd:bool option``|->``SOME T``]

fun guess_length_of_code def = let
  val tm = def |> SIMP_RULE std_ss [word_arith_lemma1] |> SPEC_ALL |> concl |> cdr
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

fun derive_cs_assign def cs_thm = let
  val n = numSyntax.term_of_int (guess_length_of_code def)
  val th = RW [w2n_lsr,w2w_def] (Q.INST [`imm32`|->`n2w ^n`] (ff X64_LISP_CALL_IMM))
  val th = SIMP_RULE (std_ss++SIZES_ss) [w2n_n2w] th
  val th = RW1 [GSYM n2w_mod] th
  val th = SIMP_RULE (std_ss++SIZES_ss) [w2n_n2w] th
  val k = find_term (can (match_term ``SIGN_EXTEND n1 n2 n3``)) (concl th)
  val th = SIMP_RULE std_ss [EVAL k] th
  val new_code = (def |> Q.SPECL [`cs`,`p+6w`] |> concl |> dest_eq |> fst)
                 handle HOL_ERR _ =>
                 (def |> Q.SPECL [`p+6w`] |> concl |> dest_eq |> fst)
  val th = SPEC new_code (MATCH_MP SPEC_ADD_CODE th)
  val th = SPEC_COMPOSE_RULE [th,cs_thm]
  in th end;

(*
val abbrev_code_for_compile_inst_def = fetch "-" "abbrev_code_for_compile_inst_def"
val abbrev_code_for_compile_def = fetch "-" "abbrev_code_for_compile_def"
*)

val assign9 = let
  val def = abbrev_code_for_compile_inst_def
  val cs_thm = ff X64_LISP_WRITE_CS9
  in derive_cs_assign def cs_thm end;

val assign8 = let
  val def = abbrev_code_for_compile_def
  val cs_thm = ff X64_LISP_WRITE_CS8
  in derive_cs_assign def cs_thm end;

val assign7 = let
  val def = abbrev_code_for_print_def
  val cs_thm = ff X64_LISP_WRITE_CS7
  in derive_cs_assign def cs_thm end;

val assign6 = let
  val def = abbrev_code_for_equal_def
  val cs_thm = ff X64_LISP_WRITE_CS6
  in derive_cs_assign def cs_thm end;

val assign5 = let
  val def = abbrev_code_for_cons_def
  val cs_thm = ff X64_LISP_WRITE_CS5
  in derive_cs_assign def cs_thm end;

val assign3 = let
  val def = abbrev_code_for_parse_def
  val cs_thm = ff X64_LISP_WRITE_CS3
  in derive_cs_assign def cs_thm end;

fun compose_assignments [] = fail()
  | compose_assignments [th] = th
  | compose_assignments (x::y::xs) = let
  val (_,_,_,q) = dest_spec (concl x)
  val (_,p,_,_) = dest_spec (concl y)
  val y = INST (fst (match_term p q)) y
  in compose_assignments (SPEC_COMPOSE_RULE [x,y]::xs) end

fun expand th = let
  val code_abbrevs = [abbrev_code_for_compile_inst_def,
                      abbrev_code_for_compile_def,
                      abbrev_code_for_print_def,
                      abbrev_code_for_equal_def,
                      abbrev_code_for_cons_def,
                      abbrev_code_for_parse_def,
                      code_abbrevs_def]
  val assum = ``LENGTH (cs:word64 list) = 10``
  val assum_lhs = fst (dest_eq assum)
  fun cs_len_conv tm = if tm ~~ assum_lhs then ASSUME assum else NO_CONV tm
  val th = th |> RW (code_abbrevs @ [EL_UPDATE_NTH,LENGTH_UPDATE_NTH,
                   word_arith_lemma1,INSERT_UNION_EQ,UNION_EMPTY])
              |> CONV_RULE (DEPTH_CONV cs_len_conv)
              |> SIMP_RULE std_ss [word_arith_lemma1]
  val _ = not (can (find_term pred_setSyntax.is_union) (concl th)) orelse fail()
  in th end;


(* top-level correctness statement *)

val jitawa_correctness_thm = save_thm("jitawa_correctness_thm",let
  val th =
    [X64_LISP_WEAKEN_CODE,X64_LISP_PUSH_0,X64_LISP_XBP_SET,X64_LISP_WRITE_12,X64_LISP_CONS_50]
    |> map (Q.INST [`ddd`|->`SOME F`,`cu`|->`NONE`])
    |> SPEC_COMPOSE_RULE |> RW [LENGTH]
    |> Q.INST [`x0`|->`Sym "NIL"`,`x5`|->`Sym "NIL"`,`code`|->`NO_CODE`]
    |> (fn th => SPEC_COMPOSE_RULE [th,Q.INST [`cu`|->`NONE`] X64_LISP_STRENGTHEN_CODE])
    |> Q.INST [`io`|->`IO_STREAMS input ""`,`xs1`|->`[]`,`ok`|->`T`]
    |> (fn th => SPEC_COMPOSE_RULE [th,main_loop_final])
  (* attach init code *)
  val th = UNDISCH (RW [SPEC_MOVE_COND] th) |> Q.INST [`ok`|->`T`]
  val init = compose_assignments [assign5,assign3,assign6,assign7,assign8,assign9]
  val init = SPEC_COMPOSE_RULE [ff X64_LISP_INIT,Q.INST [`ok`|->`T`] init]
  val init = Q.INST [`io`|->`IO_STREAMS input ""`,`cu`|->`NONE`] init
  val (_,_,_,q) = dest_spec (concl init)
  val (_,p,_,_) = dest_spec (concl th)
  val th2 = INST (fst (match_term p q)) th
  val th = SPEC_COMPOSE_RULE [init,th2]
  val th = RW [GSYM SPEC_MOVE_COND] (DISCH_ALL th)
  (* correct the postcondition *)
  val pc = th |> concl |> rand |> find_term (can (match_term ``p + n2w n``))
  val (th,goal) = SPEC_WEAKEN_RULE th
    ``zERROR_MESSAGE ex \/
      SEP_EXISTS result. cond (R_exec (input,FEMPTY,"") (result,T)) *
                         ~zS * zPC ^pc * zLISP_OUTPUT (IO_STREAMS "" result,T)``
  val lemma = prove(goal,
    SIMP_TAC std_ss [SEP_IMP_PRE_DISJ,SEP_IMP_PRE_EXISTS] \\ REPEAT STRIP_TAC
    \\ SIMP_TAC (std_ss++sep_cond_ss) [SEP_IMP_def,SEP_DISJ_def,SEP_EXISTS_THM]
    THEN1 (METIS_TAC [])
    \\ SIMP_TAC std_ss [zERROR_MESSAGE_def,SEP_EXISTS_THM] \\ METIS_TAC [])
  val th = MP th lemma
  in th end);


(* write verified code to file *)

local
val th = jitawa_correctness_thm
val filename = "../bin/verified_code.s"
val _ = print "Expanding code abbreviations, "
val th = expand th
val _ = print "done.\n"
in val _ = export_codeLib.write_code_to_file filename th end


val _ = export_theory();
