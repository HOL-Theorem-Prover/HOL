
open HolKernel Parse boolLib bossLib;

val _ = new_theory "prog_x64_extra";

open prog_x64Theory prog_x64Lib x64_encodeLib;
open helperLib progTheory set_sepTheory;

open wordsTheory wordsLib listTheory arithmeticTheory;
open whileTheory pairTheory relationTheory combinTheory optionTheory;

infix \\ val op \\ = op THEN;

(* generic code gen infrastructure *)

val zCODE_HEAP_RAX_def = Define `
  zCODE_HEAP_RAX b a n code =
    zCODE_HEAP b a code n * zR 0w (a + n2w (LENGTH code))`;

val SNOC_R1 = let
  val (_,_,sts,_) = x64_tools
  val ((th1,_,_),_) = x64_spec (x64_encode "mov [r0],r1b")
  val ((th2,_,_),_) = x64_spec (x64_encode "inc r0")
  val th1 = th1 |> REWRITE_RULE [SIGN_EXTEND_IGNORE,n2w_w2n,
                    GSYM zBYTE_MEMORY_Z_def,zBYTE_MEMORY_def]
                |> Q.GEN `g` |> Q.GEN `dg`
                |> Q.INST [`r0`|->`a+n2w (LENGTH (code:word8 list))`]
                |> MATCH_MP zCODE_HEAP_SNOC |> Q.INST [`xs`|->`code`]
  val th = SPEC_COMPOSE_RULE [th1,th2] |> HIDE_STATUS_RULE true sts
  val (th,goal) = SPEC_WEAKEN_RULE th
    ``zCODE_HEAP_RAX F a n (SNOC (w2w r1) code) * zR 0x1w r1 *
      zPC (rip + 0x5w) * ~zS``
  val lemma = prove(goal,
    FULL_SIMP_TAC (std_ss++star_ss) [zCODE_HEAP_RAX_def,LENGTH_SNOC,ADD1,SEP_IMP_REFL]);
  val th = MP th lemma
  val (th,goal) = SPEC_STRENGTHEN_RULE th
    ``zCODE_HEAP_RAX F a n code * zR 0x1w r1 *
      zPC rip * ~zS * cond (LENGTH code < n)``
  val lemma = prove(goal,
    FULL_SIMP_TAC (std_ss++star_ss) [zCODE_HEAP_RAX_def,LENGTH_SNOC,ADD1,SEP_IMP_REFL]);
  val th = MP th lemma
  in th |> REWRITE_RULE [SNOC_APPEND] end;

val SNOC_IMM = let
  val (_,_,sts,_) = x64_tools
  val ((th1,_,_),_) = x64_spec "C600"
  val ((th2,_,_),_) = x64_spec (x64_encode "inc r0")
  val th1 = th1 |> REWRITE_RULE [SIGN_EXTEND_IGNORE,n2w_w2n,
                   GSYM zBYTE_MEMORY_Z_def,zBYTE_MEMORY_def]
                |> Q.GEN `g` |> Q.GEN `dg`
                |> Q.INST [`r0`|->`a+n2w (LENGTH (code:word8 list))`,`imm8`|->`n2w k`]
                |> MATCH_MP zCODE_HEAP_SNOC |> Q.INST [`xs`|->`code`]
  val th = SPEC_COMPOSE_RULE [th1,th2] |> HIDE_STATUS_RULE true sts
  val (th,goal) = SPEC_WEAKEN_RULE th
    ``zCODE_HEAP_RAX F a n (SNOC (n2w k) code) *
      zPC (rip + 0x6w) * ~zS``
  val lemma = prove(goal,
    FULL_SIMP_TAC (std_ss++star_ss) [zCODE_HEAP_RAX_def,LENGTH_SNOC,ADD1,SEP_IMP_REFL]);
  val th = MP th lemma
  val (th,goal) = SPEC_STRENGTHEN_RULE th
    ``zCODE_HEAP_RAX F a n code *
      zPC rip * ~zS * cond (LENGTH code < n)``
  val lemma = prove(goal,
    FULL_SIMP_TAC (std_ss++star_ss) [zCODE_HEAP_RAX_def,LENGTH_SNOC,ADD1,SEP_IMP_REFL]);
  val th = MP th lemma
  in th |> REWRITE_RULE [SNOC_APPEND] end;

val LUPDATE_R1 = let
  val ((th1,_,_),_) = x64_spec (x64_encode "mov BYTE [r2],r1b")
  val th1 = th1 |> REWRITE_RULE [SIGN_EXTEND_IGNORE,n2w_w2n,
                   GSYM zBYTE_MEMORY_Z_def,zBYTE_MEMORY_def]
                |> Q.GEN `g` |> Q.GEN `dg`
                |> Q.INST [`r2`|->`a+n2w k`,`imm8`|->`n2w k1`]
                |> MATCH_MP zCODE_HEAP_UPDATE |> Q.INST [`xs`|->`code`]
  val th1 = SPEC_FRAME_RULE th1 ``zR 0w (a + n2w (LENGTH (code:word8 list)))``
  val (th,goal) = SPEC_WEAKEN_RULE th1
    ``zCODE_HEAP_RAX F a n (LUPDATE (w2w r1) k code) * zR 0x2w (a + n2w k) *
      zR 1w r1 * zPC (rip + 0x2w)``
  val lemma = prove(goal,
    FULL_SIMP_TAC (std_ss++star_ss) [zCODE_HEAP_RAX_def,LENGTH_SNOC,ADD1,
      SEP_IMP_REFL,LENGTH_LUPDATE]);
  val th = MP th lemma
  val (th,goal) = SPEC_STRENGTHEN_RULE th
    ``zCODE_HEAP_RAX F a n code * zR 0x2w (a + n2w k) *
      zR 1w r1 * zPC rip * cond (k < LENGTH code)``
  val lemma = prove(goal,
    FULL_SIMP_TAC (std_ss++star_ss) [zCODE_HEAP_RAX_def,LENGTH_SNOC,ADD1,SEP_IMP_REFL]);
  val th = MP th lemma
  in th end;

val LUPDATE_IMM = let
  val ((th1,_,_),_) = x64_spec "C602"
  val th1 = th1 |> REWRITE_RULE [SIGN_EXTEND_IGNORE,n2w_w2n,
                   GSYM zBYTE_MEMORY_Z_def,zBYTE_MEMORY_def]
                |> Q.GEN `g` |> Q.GEN `dg`
                |> Q.INST [`r2`|->`a+n2w k`,`imm8`|->`n2w k1`]
                |> MATCH_MP zCODE_HEAP_UPDATE |> Q.INST [`xs`|->`code`]
  val th1 = SPEC_FRAME_RULE th1 ``zR 0w (a + n2w (LENGTH (code:word8 list)))``
  val (th,goal) = SPEC_WEAKEN_RULE th1
    ``zCODE_HEAP_RAX F a n (LUPDATE (n2w k1) k code) * zR 0x2w (a + n2w k) *
      zPC (rip + 0x3w)``
  val lemma = prove(goal,
    FULL_SIMP_TAC (std_ss++star_ss) [zCODE_HEAP_RAX_def,LENGTH_SNOC,ADD1,
      SEP_IMP_REFL,LENGTH_LUPDATE]);
  val th = MP th lemma
  val (th,goal) = SPEC_STRENGTHEN_RULE th
    ``zCODE_HEAP_RAX F a n code * zR 0x2w (a + n2w k) *
      zPC rip * cond (k < LENGTH code)``
  val lemma = prove(goal,
    FULL_SIMP_TAC (std_ss++star_ss) [zCODE_HEAP_RAX_def,LENGTH_SNOC,ADD1,SEP_IMP_REFL]);
  val th = MP th lemma
  in th end;

val IMM32_def = Define `
  IMM32 (w:word32) =
    [w2w w; w2w (w >>> 8); w2w (w >>> 16); w2w (w >>> 24)]:word8 list`;

val IMM32_INTRO = prove(
  ``[w2w r1; w2w (r1 >>> 8); w2w (r1 >>> 16); w2w (r1 >>> 24)] =
    IMM32 (w2w (r1:word64))``,
  FULL_SIMP_TAC (srw_ss()) [IMM32_def] \\ blastLib.BBLAST_TAC);

val SNOC_IMM32 = let
  val th0 = SNOC_R1
  val (_,_,sts,_) = x64_tools
  val ((th2,_,_),_) = x64_spec (x64_encode "mov r1,r2")
  val ((th1,_,_),_) = x64_spec (x64_encode "shr r1,8")
  val th1 = HIDE_STATUS_RULE true sts th1
  val th = SPEC_COMPOSE_RULE [th2,th0,th1,th0,th1,th0,th1,th0]
  val th = th |> SIMP_RULE (std_ss++sep_cond_ss)
             [LENGTH,LENGTH_APPEND,GSYM APPEND_ASSOC,APPEND,LSR_ADD,ADD_CLAUSES,
              DECIDE ``k < n /\ k+1 < n /\ k+1+1 < n /\ k+1+1+1 < n
                       = k + 4 <= n``,IMM32_INTRO]
  in th end;


(* simple stack assertion *)

val zSTACK_def = Define `
  zSTACK xs = SEP_EXISTS rsp. zR 4w rsp * zSS xs * cond (rsp && 7w = 0w)`;

(* push *)

val x0 = ("r0",``0w:word4``,``r0:word64``)
val x1 = ("r1",``1w:word4``,``r1:word64``)
val x2 = ("r2",``2w:word4``,``r2:word64``)
val x3 = ("r3",``3w:word4``,``r3:word64``)
val x6 = ("r6",``6w:word4``,``r6:word64``)
val x7 = ("r7",``7w:word4``,``r7:word64``)
val x8 = ("r8",``8w:word4``,``r8:word64``)
val x9 = ("r9",``9w:word4``,``r9:word64``)
val x10 = ("r10",``10w:word4``,``r10:word64``)
val x11 = ("r11",``11w:word4``,``r11:word64``)
val x12 = ("r12",``12w:word4``,``r12:word64``)
val x13 = ("r13",``13w:word4``,``r13:word64``)
val x14 = ("r14",``14w:word4``,``r14:word64``)
val x15 = ("r15",``15w:word4``,``r15:word64``)

fun x64_push (s,r,v) = save_thm("x64_push_" ^ s,let
  val ((th,_,_),_) = x64_spec (x64_encode ("push " ^ s))
  val th = SPEC_BOOL_FRAME_RULE th ``r4 && 7w = 0w:word64``
  val th = Q.INST [`x1`|->`ss`] th
  val (th,goal) = SPEC_WEAKEN_RULE th
      ``zPC (rip+2w) * zR ^r ^v * zSTACK (^v::ss)``
  val lemma = prove(goal,
    FULL_SIMP_TAC std_ss [zSTACK_def,SEP_CLAUSES,SEP_IMP_def,SEP_EXISTS_THM]
    \\ REPEAT STRIP_TAC \\ Q.EXISTS_TAC `r4-8w`
    \\ FULL_SIMP_TAC std_ss [cond_STAR,STAR_ASSOC]
    \\ POP_ASSUM (K ALL_TAC) \\ POP_ASSUM MP_TAC
    \\ blastLib.BBLAST_TAC)
  val th = MP th lemma
  val th = th |> Q.GEN `r4` |> SIMP_RULE std_ss [SPEC_PRE_EXISTS]
  val (th,goal) = SPEC_STRENGTHEN_RULE th
      ``zPC rip * zR ^r ^v * zSTACK ss``
  val lemma = prove(goal,
    FULL_SIMP_TAC std_ss [zSTACK_def,SEP_CLAUSES,SEP_IMP_def,SEP_EXISTS_THM]
    \\ FULL_SIMP_TAC std_ss [cond_STAR,STAR_ASSOC]
    \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss []
    \\ Q.EXISTS_TAC `rsp` \\ FULL_SIMP_TAC std_ss [])
  val th = MP th lemma
  in th end);

val res = map x64_push [x0,x1,x2,x3,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15];

(* pop *)

fun x64_pop (s,r,v) = save_thm("x64_pop_" ^ s,let
  val ((th,_,_),_) = x64_spec (x64_encode ("pop " ^ s))
  val th = SPEC_BOOL_FRAME_RULE th ``r4 && 7w = 0w:word64``
  val th = Q.INST [`x1`|->`ss`] th
  val (th,goal) = SPEC_WEAKEN_RULE th
      ``zPC (rip+2w) * zR ^r (HD ss) * zSTACK (TL ss)``
  val lemma = prove(goal,
    FULL_SIMP_TAC std_ss [zSTACK_def,SEP_CLAUSES,SEP_IMP_def,SEP_EXISTS_THM]
    \\ REPEAT STRIP_TAC \\ Q.EXISTS_TAC `r4+8w`
    \\ FULL_SIMP_TAC std_ss [cond_STAR,STAR_ASSOC]
    \\ POP_ASSUM (K ALL_TAC) \\ POP_ASSUM MP_TAC
    \\ blastLib.BBLAST_TAC)
  val th = MP th lemma
  val th = th |> Q.GEN `r4` |> SIMP_RULE std_ss [SPEC_PRE_EXISTS]
  val (th,goal) = SPEC_STRENGTHEN_RULE th
      ``zPC rip * zR ^r ^v * zSTACK ss * cond (ss <> [])``
  val lemma = prove(goal,
    FULL_SIMP_TAC std_ss [zSTACK_def,SEP_CLAUSES,SEP_IMP_def,SEP_EXISTS_THM]
    \\ FULL_SIMP_TAC std_ss [cond_STAR,STAR_ASSOC]
    \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss []
    \\ Q.EXISTS_TAC `rsp` \\ FULL_SIMP_TAC std_ss [])
  val th = MP th lemma
  in th end);

val res = map x64_pop [x0,x1,x2,x3,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15];

(* pops *)

val x64_pops = save_thm("x64_pops",let
  val ((pops,_,_),_) = x64_spec "4881C4"
  val pops = RW [GSYM IMM32_def] pops
  val th = Q.INST [`imm32`|->`n2w (8*k)`]  pops
  val lemma = prove(
    ``k < 2 ** 28 ==>
      (SIGN_EXTEND 32 64 (w2n ((n2w:num->word32) (8 * k))) = 8 * k)``,
    FULL_SIMP_TAC (srw_ss()) [w2n_n2w,bitTheory.SIGN_EXTEND_def,LET_DEF]
    \\ REPEAT STRIP_TAC \\ `(8 * k) < 4294967296` by DECIDE_TAC
    \\ FULL_SIMP_TAC std_ss [bitTheory.BIT_def,bitTheory.BITS_THM]
    \\ `8 * k < 2147483648` by DECIDE_TAC
    \\ FULL_SIMP_TAC std_ss [LESS_DIV_EQ_ZERO]);
  val th = DISCH ``k < 2 ** 28`` th
  val th = SIMP_RULE bool_ss [lemma] th
  val lemma2 = prove(
    ``k < 2 ** 28 ==> (8 * k) < 18446744073709551616``,
    FULL_SIMP_TAC std_ss [] \\ DECIDE_TAC);
  val th = SIMP_RULE std_ss [lemma2,RW1 [MULT_COMM] MULT_DIV,
                                    RW1 [MULT_COMM] MOD_EQ_0] th
  val th = Q.INST [`x1`|->`ss`] (RW [GSYM SPEC_MOVE_COND] th)
  val th = SPEC_BOOL_FRAME_RULE th ``r4 && 7w = 0w:word64``
  val (th,goal) = SPEC_WEAKEN_RULE th
      ``zPC (rip+7w) * zSTACK (DROP k ss)``
  val lemma = prove(goal,
    FULL_SIMP_TAC std_ss [zSTACK_def,SEP_CLAUSES,SEP_IMP_def,SEP_EXISTS_THM]
    \\ REPEAT STRIP_TAC \\ Q.EXISTS_TAC `r4+n2w (8*k)`
    \\ FULL_SIMP_TAC std_ss [cond_STAR,STAR_ASSOC]
    \\ POP_ASSUM (K ALL_TAC) \\ POP_ASSUM MP_TAC
    \\ FULL_SIMP_TAC std_ss [GSYM word_mul_n2w]
    \\ blastLib.BBLAST_TAC)
  val th = MP th lemma
  val th = th |> Q.GEN `r4` |> SIMP_RULE std_ss [SPEC_PRE_EXISTS]
  val (th,goal) = SPEC_STRENGTHEN_RULE th
      ``zPC rip * zSTACK ss * cond (k <= LENGTH ss /\ k < 268435456)``
  val lemma = prove(goal,
    FULL_SIMP_TAC std_ss [zSTACK_def,SEP_CLAUSES,SEP_IMP_def,SEP_EXISTS_THM]
    \\ FULL_SIMP_TAC std_ss [cond_STAR,STAR_ASSOC]
    \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss []
    \\ Q.EXISTS_TAC `rsp` \\ FULL_SIMP_TAC std_ss [])
  val th = MP th lemma
  in th end);

(* call *)

val x64_call_imm = save_thm("x64_call_imm",let
  val ((th,_,_),_) = x64_spec "48E8"
  val th = RW [GSYM IMM32_def,GSYM word_add_n2w,WORD_ADD_ASSOC] th
  val th = SPEC_BOOL_FRAME_RULE th ``r4 && 7w = 0w:word64``
  val ll = sw2sw_def |> INST_TYPE [``:'a``|->``:32``,``:'b``|->``:64``]
                     |> SIMP_RULE (srw_ss()) []
  val th = th |> RW [GSYM ll]
  val th = Q.INST [`x1`|->`ss`] th
  val (th,goal) = SPEC_WEAKEN_RULE th
      ``zPC (rip + 0x6w + sw2sw (imm32:word32)) * zSTACK (rip+6w::ss)``
  val lemma = prove(goal,
    FULL_SIMP_TAC std_ss [zSTACK_def,SEP_CLAUSES,SEP_IMP_def,SEP_EXISTS_THM]
    \\ REPEAT STRIP_TAC \\ Q.EXISTS_TAC `r4-8w`
    \\ FULL_SIMP_TAC std_ss [cond_STAR,STAR_ASSOC]
    \\ POP_ASSUM (K ALL_TAC) \\ POP_ASSUM MP_TAC
    \\ blastLib.BBLAST_TAC)
  val th = MP th lemma
  val th = th |> Q.GEN `r4` |> SIMP_RULE std_ss [SPEC_PRE_EXISTS]
  val (th,goal) = SPEC_STRENGTHEN_RULE th
      ``zPC rip * zSTACK ss``
  val lemma = prove(goal,
    FULL_SIMP_TAC std_ss [zSTACK_def,SEP_CLAUSES,SEP_IMP_def,SEP_EXISTS_THM]
    \\ FULL_SIMP_TAC std_ss [cond_STAR,STAR_ASSOC]
    \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss []
    \\ Q.EXISTS_TAC `rsp` \\ FULL_SIMP_TAC std_ss [])
  val th = MP th lemma
  in th end);

fun x64_call (s,r,v) = save_thm("x64_call_" ^ s,let
  val ((th,_,_),_) = x64_spec (x64_encode ("call " ^ s))
  val th = SPEC_BOOL_FRAME_RULE th ``r4 && 7w = 0w:word64``
  val th = Q.INST [`x1`|->`ss`] th
  val (th,goal) = SPEC_WEAKEN_RULE th
      ``zPC ^v * zR ^r ^v * zSTACK (rip+3w::ss)``
  val lemma = prove(goal,
    FULL_SIMP_TAC std_ss [zSTACK_def,SEP_CLAUSES,SEP_IMP_def,SEP_EXISTS_THM]
    \\ REPEAT STRIP_TAC \\ Q.EXISTS_TAC `r4-8w`
    \\ FULL_SIMP_TAC std_ss [cond_STAR,STAR_ASSOC]
    \\ POP_ASSUM (K ALL_TAC) \\ POP_ASSUM MP_TAC
    \\ blastLib.BBLAST_TAC)
  val th = MP th lemma
  val th = th |> Q.GEN `r4` |> SIMP_RULE std_ss [SPEC_PRE_EXISTS]
  val (th,goal) = SPEC_STRENGTHEN_RULE th
      ``zPC rip * zR ^r ^v * zSTACK ss``
  val lemma = prove(goal,
    FULL_SIMP_TAC std_ss [zSTACK_def,SEP_CLAUSES,SEP_IMP_def,SEP_EXISTS_THM]
    \\ FULL_SIMP_TAC std_ss [cond_STAR,STAR_ASSOC]
    \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss []
    \\ Q.EXISTS_TAC `rsp` \\ FULL_SIMP_TAC std_ss [])
  val th = MP th lemma
  in th end);

val res = map x64_call [x0,x1,x2,x3,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15];

(* ret *)

val x64_ret = save_thm("x64_ret",let
  val ((ret,_,_),_) = x64_spec (x64_encode "ret")
  val ret = SPEC_BOOL_FRAME_RULE ret ``r4 && 7w = 0w:word64``
  val ret = Q.INST [`x1`|->`ss`] ret
  val (ret,goal) = SPEC_WEAKEN_RULE ret
      ``zPC (HD ss) * zSTACK (DROP 0 (TL ss))``
  val lemma = prove(goal,
    FULL_SIMP_TAC std_ss [zSTACK_def,SEP_CLAUSES,SEP_IMP_def,SEP_EXISTS_THM]
    \\ REPEAT STRIP_TAC \\ Q.EXISTS_TAC `r4+8w`
    \\ FULL_SIMP_TAC std_ss [cond_STAR,STAR_ASSOC]
    \\ POP_ASSUM (K ALL_TAC) \\ POP_ASSUM MP_TAC
    \\ blastLib.BBLAST_TAC)
  val ret = MP ret lemma
  val ret = ret |> Q.GEN `r4` |> SIMP_RULE std_ss [SPEC_PRE_EXISTS]
  val (ret,goal) = SPEC_STRENGTHEN_RULE ret
      ``zPC rip * zSTACK ss * cond (ss <> [])``
  val lemma = prove(goal,
    FULL_SIMP_TAC std_ss [zSTACK_def,SEP_CLAUSES,SEP_IMP_def,SEP_EXISTS_THM]
    \\ FULL_SIMP_TAC std_ss [cond_STAR,STAR_ASSOC]
    \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss []
    \\ Q.EXISTS_TAC `rsp` \\ FULL_SIMP_TAC std_ss [])
  val ret = MP ret lemma
  in ret end);


(* I/O interface to C: getchar, putchar *)

val IO =
  mk_var("IO",``:word64 # word8 list # word64 # word8 list -> x64_set -> bool``);

(*
  safe approximation of calling convention:
    RBP, R12 -- R15 are callee saved
    RAX -- R11 are caller saved
*)

val caller_saver_tm =
  ``~zR1 RBX * ~zR1 RCX * ~zR1 RDX * ~zR1 RSI *
    ~zR1 zR8 * ~zR1 zR9 * ~zR1 zR10 * ~zR1 zR11``

val callee_saved_tm =
  ``zR1 zR12 r12 * zR1 zR13 r13 * zR1 zR14 r14 * zR1 zR15 r15``

val io_getchar_tm =
  ``SPEC X64_MODEL
       (zPC pi * ~zR1 RAX * ~zR1 RDI * ^caller_saver_tm * ^callee_saved_tm *
        ^IO (pi,input,po,output) * ~zS * zSTACK (x::stack)) {}
       (zPC x * zR1 RAX (w2w (HD (SNOC (-1w) input))) * ~zR1 RDI *
        ^caller_saver_tm * ^callee_saved_tm *
        ^IO (pi,DROP 1 input,po,output) * ~zS * zSTACK stack)``;

val io_putchar_tm =
  ``SPEC X64_MODEL
       (zPC po * ~zR1 RAX * zR1 RDI (w2w c) * ^caller_saver_tm * ^callee_saved_tm *
        ^IO (pi,input,po,output) * ~zS * zSTACK (x::stack)) {}
       (zPC x * ~zR1 RAX * ~zR1 RDI * ^caller_saver_tm * ^callee_saved_tm *
        ^IO (pi,input,po,output ++ [c]) * ~zS * zSTACK stack)``;

fun genall tm v = foldr mk_forall tm (filter (fn x => not (x = v)) (free_vars tm));

val IO_ASSUMS_def = Define `
  IO_ASSUMS ^IO = ^(genall io_getchar_tm IO) /\ ^(genall io_putchar_tm IO)`
  |> RW [STAR_ASSOC];

val zIO_def = Define `
  zIO x = SEP_EXISTS IO. ^IO x * cond (IO_ASSUMS ^IO)`;

val x64_putchar_thm = prove(
  io_putchar_tm |> subst [IO|->``zIO``],
  SIMP_TAC std_ss [zIO_def,SEP_CLAUSES]
  \\ HO_MATCH_MP_TAC SPEC_EXISTS_EXISTS \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC (std_ss++sep_cond_ss) [SPEC_MOVE_COND,SEP_CLAUSES]
  \\ FULL_SIMP_TAC std_ss [IO_ASSUMS_def]) |> RW [STAR_ASSOC,GSYM zR_def];

val x64_getchar_thm = prove(
  io_getchar_tm |> subst [IO|->``zIO``],
  SIMP_TAC std_ss [zIO_def,SEP_CLAUSES]
  \\ HO_MATCH_MP_TAC SPEC_EXISTS_EXISTS \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC (std_ss++sep_cond_ss) [SPEC_MOVE_COND,SEP_CLAUSES]
  \\ FULL_SIMP_TAC std_ss [IO_ASSUMS_def]) |> RW [STAR_ASSOC,GSYM zR_def];

val _ = save_thm("x64_getchar_thm",x64_getchar_thm);
val _ = save_thm("x64_putchar_thm",x64_putchar_thm);

val _ = save_thm("x64_getchar_r1_thm",
  SPEC_COMPOSE_RULE [fetch "-" "x64_call_r1",x64_getchar_thm] |> RW [STAR_ASSOC]);
val _ = save_thm("x64_putchar_r1_thm",
  SPEC_COMPOSE_RULE [fetch "-" "x64_call_r1",x64_putchar_thm] |> RW [STAR_ASSOC]);

val _ = export_theory();

