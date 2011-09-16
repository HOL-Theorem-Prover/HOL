
open HolKernel boolLib bossLib Parse;
open pred_setTheory arithmeticTheory pairTheory listTheory wordsTheory;
open addressTheory set_sepTheory progTheory prog_x86Theory;
open wordsLib x86_encodeLib helperLib;

open jit_inputTheory jit_opsTheory jit_codegenTheory;

open export_codeLib;

infix \\
val op \\ = op THEN;


val _ = new_theory "jit_basic";


val xSTACK2_def = Define `
  (xSTACK2 r ([],l) = SEP_F) /\
  (xSTACK2 r (x::xs,l) =
    SEP_EXISTS a. cond (ALIGNED a) * xR r a * xSPACE a l * xLIST a (x::xs))`;

val xSTACK2_xSTACK = let
  val (spec,_,s,_) = prog_x86Lib.x86_tools
  val ((th1,_,_),_) = spec (x86_encode "mov eax,[ebp]")
  val ((th2,_,_),_) = spec (x86_encode "lea edi,[ebp+4]")
  val th = HIDE_STATUS_RULE true s (SPEC_COMPOSE_RULE [th1,th2])
  val th = Q.INST [`df`|->`{ebp}`] (DISCH_ALL th)
  val th = INST [``f:word32->word32``|->``\y:word32.(x:word32)``] (DISCH_ALL th)
  val th = SIMP_RULE std_ss [IN_INSERT,NOT_IN_EMPTY,xM_THM] th
  val th = SIMP_RULE (bool_ss++sep_cond_ss) [SPEC_MOVE_COND,xM_THM,ALIGNED_INTRO] th
  val th = RW [GSYM SPEC_MOVE_COND] th
  val th = SPEC_BOOL_FRAME_RULE th ``ALIGNED ebp``
  val th = HIDE_POST_RULE ``xM ebp`` th
  val th = SPEC_FRAME_RULE th ``xLIST (ebp+4w) xs * xSPACE ebp l``
  val (th,goal) = SPEC_WEAKEN_RULE th ``
    xR EBP ebp * xPC (eip + 0x6w) * xSTACK (x::xs,SUC l,p,ns)``
  val lemma = prove(goal,
    SIMP_TAC std_ss [xSTACK_def,SEP_CLAUSES,xSPACE_def,SEP_IMP_def]
    \\ REPEAT STRIP_TAC
    \\ SIMP_TAC std_ss [SEP_EXISTS]
    \\ Q.EXISTS_TAC `ebp + 4w`
    \\ FULL_SIMP_TAC (std_ss++star_ss) [WORD_ADD_SUB,ALIGNED])
  val th = MP th lemma
  val th = HIDE_PRE_RULE ``xR EAX`` th
  val th = HIDE_POST_RULE ``xR EBP`` th
  val th = EXISTS_PRE `ebp` th
  val (th,goal) = SPEC_STRENGTHEN_RULE th ``
    ~xR EAX * xR EDI edi * xPC eip * xSTACK2 EBP (x::xs,l)``
  val lemma = prove(goal,
    SIMP_TAC std_ss [xSTACK2_def,xLIST_def,SEP_CLAUSES,SEP_IMP_def]
    \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [SEP_EXISTS]
    \\ FULL_SIMP_TAC (std_ss++sep_cond_ss) [cond_STAR]
    \\ Q.EXISTS_TAC `y` \\ FULL_SIMP_TAC (std_ss++star_ss) [])
  val th = MP th lemma
  val th = HIDE_PRE_RULE ``xR EDI`` th
  in th end;

val xSTACK_xSTACK2 = let
  val (spec,_,s,_) = prog_x86Lib.x86_tools
  val ((th1,_,_),_) = spec (x86_encode "mov [edi-4],eax")
  val ((th2,_,_),_) = spec (x86_encode "lea ebp,[edi-4]")
  val th = HIDE_STATUS_RULE true s (SPEC_COMPOSE_RULE [th1,th2])
  val th = Q.INST [`df`|->`{edi-4w}`] (DISCH_ALL th)
  val th = INST [``f:word32->word32``|->``\y:word32.(z:word32)``] (DISCH_ALL th)
  val th = SIMP_RULE std_ss [IN_INSERT,NOT_IN_EMPTY,xM_THM] th
  val th = SIMP_RULE (bool_ss++sep_cond_ss) [SPEC_MOVE_COND,xM_THM,ALIGNED_INTRO] th
  val th = RW [GSYM SPEC_MOVE_COND,ALIGNED] th
  val th = SPEC_BOOL_FRAME_RULE th ``ALIGNED edi``
  val th = SPEC_FRAME_RULE th ``xLIST edi xs * xSPACE (edi-4w) l``
  val th = Q.INST [`eax`|->`x`] th
  val th = HIDE_POST_RULE ``xR EDI`` th
  val th = HIDE_POST_RULE ``xR EAX`` th
  val (th,goal) = SPEC_WEAKEN_RULE th ``
    ~xR EDI * xPC (eip + 0x6w) * xSTACK2 EBP (x::xs,l) * ~xR EAX``
  val lemma = prove(goal,
    SIMP_TAC std_ss [xSTACK2_def,SEP_CLAUSES,xLIST_def,SEP_IMP_def]
    \\ SIMP_TAC std_ss [SEP_EXISTS] \\ REPEAT STRIP_TAC
    \\ Q.EXISTS_TAC `edi-4w`
    \\ FULL_SIMP_TAC (std_ss++star_ss) [ALIGNED,WORD_SUB_ADD])
  val th = MP th lemma
  val th = HIDE_PRE_RULE ``xM (edi - 4w)`` th
  val th = HIDE_PRE_RULE ``xR EBP`` th
  val th = EXISTS_PRE `edi` th
  val (th,goal) = SPEC_STRENGTHEN_RULE th ``
    xPC eip * xSTACK (x::xs,SUC l,p,ns) * ~xR EBP``
  val lemma = prove(goal,
    SIMP_TAC std_ss [xSTACK_def,SEP_CLAUSES,SEP_IMP_def]
    \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [SEP_EXISTS,xSPACE_def]
    \\ Q.EXISTS_TAC `y`
    \\ FULL_SIMP_TAC (std_ss++sep_cond_ss) []
    \\ FULL_SIMP_TAC (std_ss++star_ss) [])
  val th = MP th lemma
  val th = RW [] (DISCH_ALL th)
  in th end;

val x86_basic_jit = let
  val th1 = x86_codegen_better
  val th2 = Q.INST [`p`|->`0`] xSTACK2_xSTACK
  val th3 = Q.INST [`xs`|->`x::xs`,`l`|->`SUC l`] execute_code_and_return
  val th = SPEC_COMPOSE_RULE [th1,th2,th3]
  val th = SIMP_RULE (std_ss++sep_cond_ss) [STAR_ASSOC] th
  val th4 = Q.INST [`x`|->`y`,`xs`|->`ys`,`l`|->`l2`,`p`|->`p2`] xSTACK_xSTACK2
  val th = Q.INST [`t`|->`(y::ys,SUC l2,p2,ns)`] th
  val th = SPEC_COMPOSE_RULE [th,th4]
  val th = SIMP_RULE (std_ss++sep_cond_ss) [STAR_ASSOC] th
  in th end;

val _ = write_code_to_file "basic-jit.s" x86_basic_jit;


val _ = export_theory();
