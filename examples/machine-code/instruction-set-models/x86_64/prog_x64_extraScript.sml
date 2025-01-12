
open HolKernel Parse boolLib bossLib;

val _ = new_theory "prog_x64_extra";
val _ = ParseExtras.temp_loose_equality()

open prog_x64Theory prog_x64Lib x64_encodeLib;
open helperLib progTheory set_sepTheory addressTheory temporalTheory;

open wordsTheory wordsLib listTheory arithmeticTheory;
open whileTheory pairTheory relationTheory combinTheory optionTheory;

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


(* a stack assertion:
    - RSP points at the top element in the stack,
    - the stack grows towards 0,
    - there is a Ghost_stack_top of the stack
    - SPEC is setup to say nothing if RSP hits Ghost_stack_top
 *)

val stack_list_def = Define `
  (stack_list a [] = emp) /\
  (stack_list a (x::xs) = one (a,x:word64) * stack_list (a+8w) xs)`;

val stack_list_rev_def = Define `
  (stack_list_rev a [] = emp) /\
  (stack_list_rev a (x::xs) = one (a-8w,x:word64) * stack_list_rev (a-8w) xs)`;

val stack_ok_def = Define `
  stack_ok (rsp:word64) top base stack dm m =
    (rsp && 7w = 0w) /\ (top && 7w = 0w) /\ (base && 7w = 0w) /\
    (rsp + n2w (8 * LENGTH stack) = base) /\
    ?rest. (stack_list top (rest ++ stack)) (fun2set (m,dm)) /\
           (top + n2w (8 * LENGTH (rest ++ stack)) = base) /\
           8 * LENGTH (rest ++ stack) < 2 ** 64 /\ rest <> []`;

val zSTACK_def = Define `
  zSTACK (base,stack) =
    SEP_EXISTS rsp top dm m.
      zR1 RSP rsp * zR1 zGhost_stack_top top * zR1 zGhost_stack_bottom base *
      zMEMORY64 dm m * cond (stack_ok rsp top base stack dm m)`;

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

val stack_ss = Q.INST [`stack`|->`ss`]

(* lemmas *)

val stack_list_APPEND = prove(
  ``!xs ys a. stack_list a (xs ++ ys) =
              stack_list a xs * stack_list (a + n2w (8 * LENGTH xs)) ys``,
  Induct \\ ASM_SIMP_TAC std_ss [APPEND,stack_list_def,SEP_CLAUSES,LENGTH,
    WORD_ADD_0,STAR_ASSOC,addressTheory.word_arith_lemma1,MULT_CLAUSES]);

val stack_list_REVERSE = prove(
  ``!rest. stack_list top (REVERSE rest) =
           stack_list_rev (top + n2w (8 * LENGTH rest)) rest``,
  Induct THEN1 EVAL_TAC
  \\ SRW_TAC [] [MULT_CLAUSES]
  \\ SIMP_TAC std_ss [stack_list_rev_def]
  \\ ONCE_REWRITE_TAC [ADD_COMM]
  \\ SIMP_TAC std_ss [GSYM addressTheory.word_arith_lemma1,WORD_ADD_SUB]
  \\ ASM_SIMP_TAC (std_ss++star_ss) [stack_list_APPEND,LENGTH_REVERSE,
       stack_list_def,SEP_CLAUSES])
  |> Q.SPEC `REVERSE xs`
  |> SIMP_RULE std_ss [LENGTH_REVERSE,REVERSE_REVERSE] |> GSYM;

val stack_list_rev_REVERSE =
  stack_list_REVERSE |> Q.GEN `xs`
  |> Q.SPEC `REVERSE xs` |> SIMP_RULE std_ss [LENGTH_REVERSE,REVERSE_REVERSE]

val stack_ok_thm = prove(
  ``stack_ok rsp top base stack dm m =
      (rsp && 7w = 0w) /\ (top && 7w = 0w) /\ (base && 7w = 0w) /\
      (rsp + n2w (8 * LENGTH stack) = base) /\
      ?rest. (stack_list_rev rsp rest * stack_list rsp stack) (fun2set (m,dm)) /\
             (top + n2w (8 * LENGTH (rest ++ stack)) = base) /\
             8 * LENGTH (rest ++ stack) < 2 ** 64 /\ rest <> []``,
  SIMP_TAC std_ss [stack_ok_def]
  \\ REPEAT STRIP_TAC \\ EQ_TAC \\ STRIP_TAC
  \\ FULL_SIMP_TAC std_ss []
  \\ Q.EXISTS_TAC `REVERSE rest`
  \\ FULL_SIMP_TAC std_ss [LENGTH_APPEND,LENGTH_REVERSE,REVERSE_EQ_NIL]
  \\ `rsp = top + n2w (8 * LENGTH rest)` by
   (FULL_SIMP_TAC std_ss [LEFT_ADD_DISTRIB,GSYM addressTheory.word_arith_lemma1]
    \\ Q.PAT_X_ASSUM `xx + yy = base` (ASSUME_TAC o GSYM)
    \\ FULL_SIMP_TAC std_ss [wordsTheory.WORD_EQ_ADD_RCANCEL,WORD_ADD_ASSOC])
  \\ FULL_SIMP_TAC std_ss [stack_list_REVERSE,stack_list_APPEND]
  \\ FULL_SIMP_TAC std_ss [stack_list_rev_REVERSE,LENGTH_REVERSE]);

(* pop *)

val stack_ok_POP = prove(
  ``stack_ok rsp top base stack dm m /\ stack <> [] ==>
    rsp IN dm /\ (m rsp = HD stack) /\ (rsp && 0x7w = 0x0w) /\
    stack_ok (rsp + 8w) top base (TL stack) dm m``,
  SIMP_TAC std_ss [stack_ok_thm] \\ STRIP_TAC
  \\ Cases_on `stack` \\ FULL_SIMP_TAC std_ss [HD,TL]
  \\ FULL_SIMP_TAC std_ss [PULL_EXISTS] \\ Q.EXISTS_TAC `h::rest`
  \\ FULL_SIMP_TAC std_ss [LENGTH,LENGTH_APPEND,ADD1,AC ADD_COMM ADD_ASSOC,
       LEFT_ADD_DISTRIB,addressTheory.word_arith_lemma1]
  \\ FULL_SIMP_TAC std_ss [APPEND,GSYM APPEND_ASSOC]
  \\ FULL_SIMP_TAC std_ss [stack_list_rev_def,stack_list_def,NOT_CONS_NIL]
  \\ SEP_R_TAC \\ FULL_SIMP_TAC std_ss [WORD_ADD_SUB]
  \\ FULL_SIMP_TAC (std_ss++star_ss) []
  \\ Q.PAT_X_ASSUM `rsp && 0x7w = 0x0w` MP_TAC
  \\ blastLib.BBLAST_TAC);

fun x64_pop (s,r,v) = save_thm("x64_pop_" ^ s,let
  val ((th,_,_),_) = x64_spec_memory64 (x64_encode ("pop " ^ s))
  val th = th |> Q.INST [`r4`|->`rsp`,`df`|->`dm`,`f`|->`m`,`rip`|->`p`]
  val th = SPEC_FRAME_RULE th ``
             zR1 zGhost_stack_top top * zR1 zGhost_stack_bottom base *
             cond (stack_ok rsp top base stack dm m /\ stack <> [])``
  val (th,goal) = SPEC_WEAKEN_RULE th
    ``zPC (p + 2w) * zR ^r (HD stack) * zSTACK (base,TL stack)``
  val lemma = prove(goal,
    SIMP_TAC std_ss [SEP_IMP_def,zSTACK_def,SEP_CLAUSES,SEP_EXISTS_THM]
    \\ REPEAT STRIP_TAC \\ Q.LIST_EXISTS_TAC [`rsp+8w`,`top`,`dm`,`m`]
    \\ FULL_SIMP_TAC (std_ss++sep_cond_ss) [cond_STAR]
    \\ IMP_RES_TAC stack_ok_POP
    \\ FULL_SIMP_TAC (std_ss++star_ss) [zR_def])
  val th = MP th lemma
  val th = th |> Q.GENL [`rsp`,`top`,`dm`,`m`]
              |> SIMP_RULE std_ss [SPEC_PRE_EXISTS]
  val (th,goal) = SPEC_STRENGTHEN_RULE th
    ``zPC p * zR ^r ^v * zSTACK (base,stack) * cond (stack <> [])``
  val lemma = prove(goal,
    SIMP_TAC std_ss [SEP_IMP_def,zSTACK_def,SEP_CLAUSES,SEP_EXISTS_THM]
    \\ REPEAT STRIP_TAC \\ Q.LIST_EXISTS_TAC [`rsp`,`top`,`dm`,`m`]
    \\ FULL_SIMP_TAC (std_ss++sep_cond_ss) [cond_STAR]
    \\ IMP_RES_TAC stack_ok_POP
    \\ FULL_SIMP_TAC (std_ss++star_ss) [zR_def])
  val th = MP th lemma
  in th |> stack_ss end);

val all_pops = map x64_pop [x0,x1,x2,x3,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15];

(* push *)

val stack_ok_PUSH = prove(
  ``stack_ok rsp top base stack dm m ==>
    rsp - 0x8w IN dm /\ (rsp - 0x8w && 0x7w = 0x0w) /\
    (stack_ok (rsp - 8w) top base (v::stack) dm ((rsp - 8w =+ v) m) \/
     (top = rsp - 8w))``,
  SIMP_TAC std_ss [stack_ok_thm] \\ STRIP_TAC
  \\ Cases_on `top = rsp - 8w` \\ FULL_SIMP_TAC std_ss []
  \\ Cases_on `rest` \\ FULL_SIMP_TAC std_ss [stack_list_rev_def] \\ SEP_R_TAC
  \\ SIMP_TAC std_ss [LENGTH,MULT_CLAUSES,GSYM addressTheory.word_arith_lemma1]
  \\ ASM_SIMP_TAC std_ss [WORD_SUB_ADD]
  \\ SIMP_TAC std_ss [PULL_EXISTS]
  \\ Q.EXISTS_TAC `t` \\ FULL_SIMP_TAC std_ss [LENGTH,LENGTH_APPEND]
  \\ FULL_SIMP_TAC std_ss [LEFT_ADD_DISTRIB,MULT_CLAUSES]
  \\ FULL_SIMP_TAC std_ss [AC ADD_COMM ADD_ASSOC,stack_list_def,WORD_SUB_ADD]
  \\ Cases_on `t = []` \\ FULL_SIMP_TAC std_ss [] THEN1
   (FULL_SIMP_TAC std_ss [LENGTH,GSYM word_add_n2w]
    \\ Q.ABBREV_TAC `s = 8 * LENGTH stack`
    \\ NTAC 2 (Q.PAT_X_ASSUM `x = y:word64` MP_TAC)
    \\ REPEAT (Q.PAT_X_ASSUM `x <> y:word64` MP_TAC)
    \\ blastLib.BBLAST_TAC)
  \\ FULL_SIMP_TAC (std_ss++star_ss) [WORD_ADD_ASSOC,WORD_SUB_ADD]
  \\ SIMP_TAC std_ss [CONJ_ASSOC] \\ STRIP_TAC
  THEN1 (Q.PAT_X_ASSUM `rsp && 0x7w = 0x0w` MP_TAC \\ blastLib.BBLAST_TAC)
  \\ SEP_W_TAC \\ FULL_SIMP_TAC (std_ss++star_ss) []);

val X64_SPEC_WEAKEN = prove(
  ``!p c q. SPEC X64_MODEL p EMPTY q ==>
            !r. SEP_IMP q (r \/ SEP_EXISTS x frame.
                   zR1 RSP x * zR1 zGhost_stack_top x * frame) ==>
                SPEC X64_MODEL p EMPTY r``,
  SIMP_TAC std_ss [X64_SPEC_SEMANTICS] \\ REPEAT STRIP_TAC
  \\ Q.PAT_X_ASSUM `!x.bbb` (MP_TAC o Q.SPECL [`y`,`s`,`t1`,`seq`])
  \\ FULL_SIMP_TAC std_ss [] \\ REVERSE STRIP_TAC THEN1 (METIS_TAC [])
  \\ Q.LIST_EXISTS_TAC [`k`,`t2`] \\ FULL_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC std_ss [SEP_IMP_def,SEP_DISJ_def,SEP_EXISTS_THM]
  \\ RES_TAC \\ FULL_SIMP_TAC std_ss []
  \\ `?rs st ei ms. y = (rs,st,ei,ms)` by METIS_TAC [PAIR]
  \\ `?r e s m i. t2 = (r,e,s,m,i)` by METIS_TAC [PAIR]
  \\ `?r e s m i. seq k = (r,e,s,m,i)` by METIS_TAC [PAIR]
  \\ FULL_SIMP_TAC std_ss [STAR_x64_2set,GSYM STAR_ASSOC]
  \\ FULL_SIMP_TAC std_ss [X64_STACK_FULL_def,x64_icacheTheory.X64_ICACHE_def]
  \\ SRW_TAC [] []) |> SIMP_RULE std_ss [PULL_FORALL,AND_IMP_INTRO];

val X64_SPEC_WEAKEN = prove(
  ``!p c q. SPEC X64_MODEL p c q ==>
            !r. SEP_IMP q (r \/ SEP_EXISTS x frame.
                   zR1 RSP x * zR1 zGhost_stack_top x * frame) ==>
                SPEC X64_MODEL p c r``,
  ONCE_REWRITE_TAC [GSYM X64_SPEC_CODE] \\ REPEAT STRIP_TAC
  \\ MATCH_MP_TAC X64_SPEC_WEAKEN
  \\ Q.EXISTS_TAC `zCODE c * q` \\ FULL_SIMP_TAC std_ss []
  \\ IMP_RES_TAC SEP_IMP_FRAME
  \\ POP_ASSUM (MP_TAC o Q.SPEC `zCODE c`)
  \\ SIMP_TAC (std_ss++star_ss) [SEP_CLAUSES]
  \\ SIMP_TAC std_ss [SEP_IMP_def,SEP_DISJ_def,SEP_EXISTS_THM]
  \\ REPEAT STRIP_TAC \\ RES_TAC THEN1 (METIS_TAC [])
  \\ METIS_TAC [STAR_ASSOC,STAR_COMM]);

val X64_SPEC_1_WEAKEN = prove(
  ``!p c q. SPEC_1 X64_MODEL p EMPTY q SEP_F ==>
            !r. SEP_IMP q (r \/ SEP_EXISTS x frame.
                   zR1 RSP x * zR1 zGhost_stack_top x * frame) ==>
                SPEC_1 X64_MODEL p EMPTY r SEP_F``,
  SIMP_TAC std_ss [X64_SPEC_1_SEMANTICS] \\ REPEAT STRIP_TAC
  \\ Q.PAT_X_ASSUM `!x.bbb` (MP_TAC o Q.SPECL [`y`,`s`,`t1`,`seq`])
  \\ FULL_SIMP_TAC std_ss [] \\ REVERSE STRIP_TAC THEN1 (METIS_TAC [])
  \\ Cases_on `X64_STACK_FULL (seq (k+1))` THEN1 METIS_TAC []
  \\ Cases_on `X64_STACK_FULL (seq k)` THEN1 METIS_TAC []
  \\ Q.LIST_EXISTS_TAC [`k`,`t2`] \\ FULL_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC std_ss [SEP_IMP_def,SEP_DISJ_def,SEP_EXISTS_THM]
  \\ RES_TAC \\ FULL_SIMP_TAC std_ss []
  \\ `?rs st ei ms. y = (rs,st,ei,ms)` by METIS_TAC [PAIR]
  \\ `?r e s m i. t2 = (r,e,s,m,i)` by METIS_TAC [PAIR]
  \\ `?r e s m i. seq (k+1) = (r,e,s,m,i)` by METIS_TAC [PAIR]
  \\ FULL_SIMP_TAC std_ss [STAR_x64_2set,GSYM STAR_ASSOC]
  \\ FULL_SIMP_TAC std_ss [X64_STACK_FULL_def,x64_icacheTheory.X64_ICACHE_def]
  \\ SRW_TAC [] [] \\ FULL_SIMP_TAC std_ss [])
  |> SIMP_RULE std_ss [PULL_FORALL,AND_IMP_INTRO];

val X64_SPEC_1_WEAKEN = prove(
  ``!p c q. SPEC_1 X64_MODEL p c q SEP_F ==>
            !r. SEP_IMP q (r \/ SEP_EXISTS x frame.
                   zR1 RSP x * zR1 zGhost_stack_top x * frame) ==>
                SPEC_1 X64_MODEL p c r SEP_F``,
  ONCE_REWRITE_TAC [GSYM X64_SPEC_1_CODE] \\ REPEAT STRIP_TAC
  \\ MATCH_MP_TAC X64_SPEC_1_WEAKEN
  \\ Q.EXISTS_TAC `zCODE c * q` \\ FULL_SIMP_TAC std_ss []
  \\ IMP_RES_TAC SEP_IMP_FRAME
  \\ POP_ASSUM (MP_TAC o Q.SPEC `zCODE c`)
  \\ SIMP_TAC (std_ss++star_ss) [SEP_CLAUSES]
  \\ SIMP_TAC std_ss [SEP_IMP_def,SEP_DISJ_def,SEP_EXISTS_THM]
  \\ REPEAT STRIP_TAC \\ RES_TAC THEN1 (METIS_TAC [])
  \\ METIS_TAC [STAR_ASSOC,STAR_COMM]);

fun x64_push (s,r,v) = save_thm("x64_push_" ^ s,let
  val ((th,_,_),_) = x64_spec_memory64 (x64_encode ("push " ^ s))
  val th = th |> Q.INST [`r4`|->`rsp`,`df`|->`dm`,`f`|->`m`,`rip`|->`p`]
  val th = SPEC_FRAME_RULE th ``
             zR1 zGhost_stack_top top * zR1 zGhost_stack_bottom base *
             cond (stack_ok rsp top base stack dm m)``
  val th = MATCH_MP X64_SPEC_WEAKEN th
             |> Q.SPEC `zPC (p + 2w) * zR ^r ^v * zSTACK (base,^v::stack)`
  val goal = th |> concl |> dest_imp |> fst
  val lemma = prove(goal,
    SIMP_TAC std_ss [SEP_IMP_def,zSTACK_def,SEP_CLAUSES,SEP_EXISTS_THM]
    \\ REPEAT STRIP_TAC \\ Q.LIST_EXISTS_TAC [`rsp-8w`,
         `zPC (p + 0x2w) * zR ^r ^v *
          zR1 zGhost_stack_bottom base * zMEMORY64 dm ((rsp - 0x8w =+ ^v) m)`,
         `rsp-8w`,`top`,`dm`,
         `((rsp - 0x8w =+ ^v) m)`]
    \\ FULL_SIMP_TAC (std_ss++sep_cond_ss) [cond_STAR,SEP_DISJ_def]
    \\ IMP_RES_TAC stack_ok_PUSH
    \\ POP_ASSUM (STRIP_ASSUME_TAC o SPEC v)
    \\ FULL_SIMP_TAC (std_ss++star_ss) [zR_def])
  val th = MP th lemma
  val th = th |> Q.GENL [`rsp`,`top`,`dm`,`m`]
              |> SIMP_RULE std_ss [SPEC_PRE_EXISTS]
  val (th,goal) = SPEC_STRENGTHEN_RULE th
    ``zPC p * zR ^r ^v * zSTACK (base,stack)``
  val lemma = prove(goal,
    SIMP_TAC std_ss [SEP_IMP_def,zSTACK_def,SEP_CLAUSES,SEP_EXISTS_THM]
    \\ REPEAT STRIP_TAC \\ Q.LIST_EXISTS_TAC [`rsp`,`top`,`dm`,`m`]
    \\ FULL_SIMP_TAC (std_ss++sep_cond_ss) [cond_STAR]
    \\ IMP_RES_TAC stack_ok_PUSH
    \\ FULL_SIMP_TAC (std_ss++star_ss) [zR_def])
  val th = MP th lemma
  in th |> stack_ss end);

val all_pushes = map x64_push [x0,x1,x2,x3,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15];

(* call *)

val sw2sw_64_32 =
  sw2sw_def |> INST_TYPE [``:'b``|->``:64``,``:'a``|->``:32``]
            |> SIMP_RULE std_ss [EVAL ``dimindex (:64)``,EVAL ``dimindex (:32)``]
            |> GSYM

fun SPEC_1_FRAME_RULE th tm =
  SPEC tm (MATCH_MP temporalTheory.SPEC_1_FRAME th) |> RW [SEP_CLAUSES]

val x64_call_imm_raw_spec_1 = let
  val th = x64_Lib.x64_step "48E8"
  val c = calc_code th
  val th = pre_process_thm th
  val th = RW [w2n_MOD] th
  val th = x64_prove_one_spec_1 th c
  val th = introduce_zMEMORY64 th
  in th end

val x64_call_imm_spec_1 = save_thm("x64_call_imm_spec_1",let
  val th = x64_call_imm_raw_spec_1
  val th = th |> RW [sw2sw_64_32,GSYM word_add_n2w,WORD_ADD_ASSOC]
  val th = th |> Q.INST [`r4`|->`rsp`,`df`|->`dm`,`f`|->`m`,`rip`|->`p`]
  val th = SPEC_1_FRAME_RULE th ``
             zR1 zGhost_stack_top top * zR1 zGhost_stack_bottom base *
             cond (stack_ok rsp top base stack dm m)``
  val new_p = ``(p + 6w + sw2sw (imm32:word32)):word64``
  val th = MATCH_MP X64_SPEC_1_WEAKEN th
             |> Q.SPEC `zPC ^new_p * zSTACK (base,p+6w::stack)`
  val goal = th |> concl |> dest_imp |> fst
  val lemma = prove(goal,
    SIMP_TAC std_ss [SEP_IMP_def,zSTACK_def,SEP_CLAUSES,SEP_EXISTS_THM]
    \\ REPEAT STRIP_TAC \\ Q.LIST_EXISTS_TAC [`top`,
         `zPC ^new_p *
          zR1 zGhost_stack_bottom base * zMEMORY64 dm ((rsp - 0x8w =+ p+6w) m)`,
         `rsp-8w`,`top`,`dm`,
         `((rsp - 0x8w =+ p+6w) m)`]
    \\ FULL_SIMP_TAC (std_ss++sep_cond_ss) [cond_STAR,SEP_DISJ_def]
    \\ IMP_RES_TAC stack_ok_PUSH
    \\ POP_ASSUM (STRIP_ASSUME_TAC o Q.SPEC `p+6w`)
    \\ FULL_SIMP_TAC (std_ss++star_ss) [zR_def])
  val th = MP th lemma
  val th = th |> Q.GENL [`rsp`,`top`,`dm`,`m`]
              |> SIMP_RULE std_ss [SPEC_1_PRE_EXISTS]
  val (th,goal) = SPEC_STRENGTHEN_RULE th
    ``zPC p * zSTACK (base,stack)``
  val lemma = prove(goal,
    SIMP_TAC std_ss [SEP_IMP_def,zSTACK_def,SEP_CLAUSES,SEP_EXISTS_THM]
    \\ REPEAT STRIP_TAC \\ Q.LIST_EXISTS_TAC [`rsp`,`top`,`dm`,`m`]
    \\ FULL_SIMP_TAC (std_ss++sep_cond_ss) [cond_STAR]
    \\ IMP_RES_TAC stack_ok_PUSH
    \\ FULL_SIMP_TAC (std_ss++star_ss) [zR_def])
  val th = MP th lemma
  val th = RW [GSYM IMM32_def,GSYM word_add_n2w,WORD_ADD_ASSOC] th
  in th |> stack_ss end);

val x64_call_imm = save_thm("x64_call_imm",let
  val ((th,_,_),_) = x64_spec_memory64 "48E8"
  val th = th |> RW [sw2sw_64_32,GSYM word_add_n2w,WORD_ADD_ASSOC]
  val th = th |> Q.INST [`r4`|->`rsp`,`df`|->`dm`,`f`|->`m`,`rip`|->`p`]
  val th = SPEC_FRAME_RULE th ``
             zR1 zGhost_stack_top top * zR1 zGhost_stack_bottom base *
             cond (stack_ok rsp top base stack dm m)``
  val new_p = ``(p + 6w + sw2sw (imm32:word32)):word64``
  val th = MATCH_MP X64_SPEC_WEAKEN th
             |> Q.SPEC `zPC ^new_p * zSTACK (base,p+6w::stack)`
  val goal = th |> concl |> dest_imp |> fst
  val lemma = prove(goal,
    SIMP_TAC std_ss [SEP_IMP_def,zSTACK_def,SEP_CLAUSES,SEP_EXISTS_THM]
    \\ REPEAT STRIP_TAC \\ Q.LIST_EXISTS_TAC [`top`,
         `zPC ^new_p *
          zR1 zGhost_stack_bottom base * zMEMORY64 dm ((rsp - 0x8w =+ p+6w) m)`,
         `rsp-8w`,`top`,`dm`,
         `((rsp - 0x8w =+ p+6w) m)`]
    \\ FULL_SIMP_TAC (std_ss++sep_cond_ss) [cond_STAR,SEP_DISJ_def]
    \\ IMP_RES_TAC stack_ok_PUSH
    \\ POP_ASSUM (STRIP_ASSUME_TAC o Q.SPEC `p+6w`)
    \\ FULL_SIMP_TAC (std_ss++star_ss) [zR_def])
  val th = MP th lemma
  val th = th |> Q.GENL [`rsp`,`top`,`dm`,`m`]
              |> SIMP_RULE std_ss [SPEC_PRE_EXISTS]
  val (th,goal) = SPEC_STRENGTHEN_RULE th
    ``zPC p * zSTACK (base,stack)``
  val lemma = prove(goal,
    SIMP_TAC std_ss [SEP_IMP_def,zSTACK_def,SEP_CLAUSES,SEP_EXISTS_THM]
    \\ REPEAT STRIP_TAC \\ Q.LIST_EXISTS_TAC [`rsp`,`top`,`dm`,`m`]
    \\ FULL_SIMP_TAC (std_ss++sep_cond_ss) [cond_STAR]
    \\ IMP_RES_TAC stack_ok_PUSH
    \\ FULL_SIMP_TAC (std_ss++star_ss) [zR_def])
  val th = MP th lemma
  val th = RW [GSYM IMM32_def,GSYM word_add_n2w,WORD_ADD_ASSOC] th
  in th |> stack_ss end);

fun x64_call (s,r,v) = save_thm("x64_call_" ^ s,let
  val ((th,_,_),_) = x64_spec_memory64 (x64_encode ("call " ^ s))
  val th = th |> Q.INST [`r4`|->`rsp`,`df`|->`dm`,`f`|->`m`,`rip`|->`p`]
  val th = SPEC_FRAME_RULE th ``
             zR1 zGhost_stack_top top * zR1 zGhost_stack_bottom base *
             cond (stack_ok rsp top base stack dm m)``
  val new_p = v
  val th = MATCH_MP X64_SPEC_WEAKEN th
             |> Q.SPEC `zPC ^new_p * zR ^r ^v * zSTACK (base,p+3w::stack)`
  val goal = th |> concl |> dest_imp |> fst
  val lemma = prove(goal,
    SIMP_TAC std_ss [SEP_IMP_def,zSTACK_def,SEP_CLAUSES,SEP_EXISTS_THM]
    \\ REPEAT STRIP_TAC \\ Q.LIST_EXISTS_TAC [`top`,
         `zPC ^new_p * zR ^r ^v *
          zR1 zGhost_stack_bottom base * zMEMORY64 dm ((rsp - 0x8w =+ p+3w) m)`,
         `rsp-8w`,`top`,`dm`,
         `((rsp - 0x8w =+ p+3w) m)`]
    \\ FULL_SIMP_TAC (std_ss++sep_cond_ss) [cond_STAR,SEP_DISJ_def]
    \\ IMP_RES_TAC stack_ok_PUSH
    \\ POP_ASSUM (STRIP_ASSUME_TAC o Q.SPEC `p+3w`)
    \\ FULL_SIMP_TAC (std_ss++star_ss) [zR_def])
  val th = MP th lemma
  val th = th |> Q.GENL [`rsp`,`top`,`dm`,`m`]
              |> SIMP_RULE std_ss [SPEC_PRE_EXISTS]
  val (th,goal) = SPEC_STRENGTHEN_RULE th
    ``zPC p * zR ^r ^v * zSTACK (base,stack)``
  val lemma = prove(goal,
    SIMP_TAC std_ss [SEP_IMP_def,zSTACK_def,SEP_CLAUSES,SEP_EXISTS_THM]
    \\ REPEAT STRIP_TAC \\ Q.LIST_EXISTS_TAC [`rsp`,`top`,`dm`,`m`]
    \\ FULL_SIMP_TAC (std_ss++sep_cond_ss) [cond_STAR]
    \\ IMP_RES_TAC stack_ok_PUSH
    \\ FULL_SIMP_TAC (std_ss++star_ss) [zR_def])
  val th = MP th lemma
  val th = RW [GSYM IMM32_def,GSYM word_add_n2w,WORD_ADD_ASSOC] th
  in th |> stack_ss end);

val res = map x64_call [x0,x1,x2,x3,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15];

(* pops *)

val LENGTH_LESS_EQ = prove(
  ``!xs m. m <= LENGTH xs ==> ?ys zs. (xs = ys ++ zs) /\ (LENGTH ys = m)``,
  Induct \\ SIMP_TAC (srw_ss()) [] \\ REPEAT STRIP_TAC
  \\ Cases_on `m` \\ FULL_SIMP_TAC std_ss [LENGTH_NIL,APPEND]
  \\ RES_TAC \\ Q.LIST_EXISTS_TAC [`h::ys`,`zs`]
  \\ FULL_SIMP_TAC std_ss [APPEND,LENGTH]);

val stack_list_rev_APPEND = prove(
  ``!rest ys a.
      stack_list_rev a (rest ++ ys) =
      stack_list_rev a rest *
      stack_list_rev (a - n2w (8 * LENGTH rest)) ys``,
  Induct THEN1 (FULL_SIMP_TAC (srw_ss()) [stack_list_rev_def,SEP_CLAUSES])
  \\ FULL_SIMP_TAC std_ss [stack_list_rev_def,SEP_CLAUSES,APPEND]
  \\ FULL_SIMP_TAC std_ss [AC STAR_ASSOC STAR_COMM,LENGTH,
       GSYM WORD_SUB_PLUS,word_add_n2w,MULT_CLAUSES]);

val stack_ok_POPS = store_thm("stack_ok_POPS",
  ``stack_ok rsp top base stack dm m /\ k <= LENGTH stack ==>
    stack_ok (rsp + n2w (8 * k)) top base (DROP k stack) dm m``,
  SIMP_TAC std_ss [stack_ok_thm] \\ STRIP_TAC
  \\ IMP_RES_TAC LENGTH_LESS_EQ \\ FULL_SIMP_TAC std_ss []
  \\ POP_ASSUM (ASSUME_TAC o GSYM)
  \\ FULL_SIMP_TAC std_ss [addressTheory.word_arith_lemma1,
       rich_listTheory.DROP_LENGTH_APPEND,GSYM LEFT_ADD_DISTRIB,LENGTH_APPEND]
  \\ FULL_SIMP_TAC std_ss [GSYM word_mul_n2w] \\ STRIP_TAC
  THEN1 (Q.PAT_X_ASSUM `rsp && 0x7w = 0x0w` MP_TAC \\ blastLib.BBLAST_TAC)
  \\ Q.EXISTS_TAC `REVERSE ys ++ rest`
  \\ FULL_SIMP_TAC std_ss [LENGTH_APPEND,ADD_ASSOC,APPEND_eq_NIL,LENGTH_REVERSE]
  \\ FULL_SIMP_TAC std_ss [stack_list_APPEND,STAR_ASSOC]
  \\ SIMP_TAC std_ss [stack_list_rev_APPEND,word_mul_n2w,LENGTH_REVERSE]
  \\ FULL_SIMP_TAC std_ss [WORD_ADD_SUB]
  \\ FULL_SIMP_TAC std_ss [AC ADD_COMM ADD_ASSOC,word_mul_n2w]
  \\ ONCE_REWRITE_TAC [GSYM LENGTH_REVERSE]
  \\ ASM_SIMP_TAC std_ss [stack_list_rev_REVERSE]
  \\ FULL_SIMP_TAC std_ss [REVERSE_REVERSE,AC STAR_COMM STAR_ASSOC,LENGTH_REVERSE]);

val imm32_lemma = prove(
  ``(k:num) < 2 ** 28 ==>
    (SIGN_EXTEND 32 64 (w2n ((n2w:num->word32) (8 * k))) = 8 * k)``,
  FULL_SIMP_TAC (srw_ss()) [w2n_n2w,bitTheory.SIGN_EXTEND_def,LET_DEF]
  \\ REPEAT STRIP_TAC \\ `(8 * k) < 4294967296` by DECIDE_TAC
  \\ FULL_SIMP_TAC std_ss [bitTheory.BIT_def,bitTheory.BITS_THM]
  \\ `8 * k < 2147483648` by DECIDE_TAC
  \\ FULL_SIMP_TAC std_ss [LESS_DIV_EQ_ZERO]);

val x64_pops = save_thm("x64_pops",let
  val ((pops,_,_),_) = x64_spec "4881C4"
  val pops = RW [GSYM IMM32_def] pops
  val th = Q.INST [`imm32`|->`n2w (8*k)`,`rip`|->`p`]  pops
  val th = DISCH ``(k:num) < 2 ** 28`` th
  val lemma2 = prove(
    ``k < 2 ** 28 ==> (8 * k) < 18446744073709551616n``,
    FULL_SIMP_TAC std_ss [] \\ DECIDE_TAC);
  val th = SIMP_RULE bool_ss [lemma2,RW1 [MULT_COMM] MULT_DIV,
                                     RW1 [MULT_COMM] MOD_EQ_0,imm32_lemma] th
  val th = Q.INST [`x1`|->`ss`] (RW [GSYM SPEC_MOVE_COND] th)
  val th = SIMP_RULE bool_ss [imm32_lemma] th
  val (_,_,sts,_) = x64_tools
  val th = th |> HIDE_STATUS_RULE true sts
  val th = th |> Q.INST [`r4`|->`rsp`,`df`|->`dm`,`f`|->`m`,`rip`|->`p`]
  val th = SPEC_FRAME_RULE th ``
             zMEMORY64 dm m *
             zR1 zGhost_stack_top top * zR1 zGhost_stack_bottom base *
             cond (stack_ok rsp top base stack dm m /\ k <= LENGTH stack)``
  val (th,goal) = SPEC_WEAKEN_RULE th
    ``zPC (p + 7w) * zSTACK (base,DROP k stack) * ~zS``
  val lemma = prove(goal,
    SIMP_TAC std_ss [SEP_IMP_def,zSTACK_def,SEP_CLAUSES,SEP_EXISTS_THM]
    \\ REPEAT STRIP_TAC \\ Q.LIST_EXISTS_TAC [`rsp+n2w (8*k)`,`top`,`dm`,`m`]
    \\ FULL_SIMP_TAC (std_ss++sep_cond_ss) [cond_STAR]
    \\ IMP_RES_TAC stack_ok_POPS
    \\ FULL_SIMP_TAC (std_ss++star_ss) [zR_def])
  val th = MP th lemma
  val th = th |> Q.GENL [`rsp`,`top`,`dm`,`m`]
              |> SIMP_RULE std_ss [SPEC_PRE_EXISTS]
  val (th,goal) = SPEC_STRENGTHEN_RULE th
    ``zPC p * zSTACK (base,stack) * ~zS * cond (k <= LENGTH stack /\ k < 2 ** 28)``
  val lemma = prove(goal,
    SIMP_TAC std_ss [SEP_IMP_def,zSTACK_def,SEP_CLAUSES,SEP_EXISTS_THM]
    \\ REPEAT STRIP_TAC \\ Q.LIST_EXISTS_TAC [`rsp`,`top`,`dm`,`m`]
    \\ FULL_SIMP_TAC (std_ss++sep_cond_ss) [cond_STAR]
    \\ IMP_RES_TAC stack_ok_POPS
    \\ FULL_SIMP_TAC (std_ss++star_ss) [zR_def])
  val th = MP th lemma
  in th |> stack_ss end);

(* ret *)

val x64_ret_raw_spec_1 = let
  val th = x64_Lib.x64_step (x64_encode "ret")
  val c = calc_code th
  val th = pre_process_thm th
  val th = RW [w2n_MOD] th
  val th = x64_prove_one_spec_1 th c
  val th = introduce_zMEMORY64 th
  in th end

val x64_ret_spec_1 = save_thm("x64_ret_spec_1",let
  val th = x64_ret_raw_spec_1
  val th = th |> Q.INST [`r4`|->`rsp`,`df`|->`dm`,`f`|->`m`,`rip`|->`p`]
  val th = SPEC_1_FRAME_RULE th ``
             zR1 zGhost_stack_top top * zR1 zGhost_stack_bottom base *
             cond (stack_ok rsp top base stack dm m /\ stack <> [])``
  val (th,goal) = SPEC_WEAKEN_RULE th
    ``zPC (HD stack) * zSTACK (base,TL stack)``
  val lemma = prove(goal,
    SIMP_TAC std_ss [SEP_IMP_def,zSTACK_def,SEP_CLAUSES,SEP_EXISTS_THM]
    \\ REPEAT STRIP_TAC \\ Q.LIST_EXISTS_TAC [`rsp+8w`,`top`,`dm`,`m`]
    \\ FULL_SIMP_TAC (std_ss++sep_cond_ss) [cond_STAR]
    \\ IMP_RES_TAC stack_ok_POP
    \\ FULL_SIMP_TAC (std_ss++star_ss) [zR_def])
  val th = MP th lemma
  val th = th |> Q.GENL [`rsp`,`top`,`dm`,`m`]
              |> SIMP_RULE std_ss [SPEC_1_PRE_EXISTS]
  val (th,goal) = SPEC_STRENGTHEN_RULE th
    ``zPC p * zSTACK (base,stack) * cond (stack <> [])``
  val lemma = prove(goal,
    SIMP_TAC std_ss [SEP_IMP_def,zSTACK_def,SEP_CLAUSES,SEP_EXISTS_THM]
    \\ REPEAT STRIP_TAC \\ Q.LIST_EXISTS_TAC [`rsp`,`top`,`dm`,`m`]
    \\ FULL_SIMP_TAC (std_ss++sep_cond_ss) [cond_STAR]
    \\ IMP_RES_TAC stack_ok_POP
    \\ FULL_SIMP_TAC (std_ss++star_ss) [zR_def])
  val th = MP th lemma
  in th |> stack_ss end);

val x64_ret = save_thm("x64_ret",let
  val ((th,_,_),_) = x64_spec_memory64 (x64_encode "ret")
  val th = th |> Q.INST [`r4`|->`rsp`,`df`|->`dm`,`f`|->`m`,`rip`|->`p`]
  val th = SPEC_FRAME_RULE th ``
             zR1 zGhost_stack_top top * zR1 zGhost_stack_bottom base *
             cond (stack_ok rsp top base stack dm m /\ stack <> [])``
  val (th,goal) = SPEC_WEAKEN_RULE th
    ``zPC (HD stack) * zSTACK (base,TL stack)``
  val lemma = prove(goal,
    SIMP_TAC std_ss [SEP_IMP_def,zSTACK_def,SEP_CLAUSES,SEP_EXISTS_THM]
    \\ REPEAT STRIP_TAC \\ Q.LIST_EXISTS_TAC [`rsp+8w`,`top`,`dm`,`m`]
    \\ FULL_SIMP_TAC (std_ss++sep_cond_ss) [cond_STAR]
    \\ IMP_RES_TAC stack_ok_POP
    \\ FULL_SIMP_TAC (std_ss++star_ss) [zR_def])
  val th = MP th lemma
  val th = th |> Q.GENL [`rsp`,`top`,`dm`,`m`]
              |> SIMP_RULE std_ss [SPEC_PRE_EXISTS]
  val (th,goal) = SPEC_STRENGTHEN_RULE th
    ``zPC p * zSTACK (base,stack) * cond (stack <> [])``
  val lemma = prove(goal,
    SIMP_TAC std_ss [SEP_IMP_def,zSTACK_def,SEP_CLAUSES,SEP_EXISTS_THM]
    \\ REPEAT STRIP_TAC \\ Q.LIST_EXISTS_TAC [`rsp`,`top`,`dm`,`m`]
    \\ FULL_SIMP_TAC (std_ss++sep_cond_ss) [cond_STAR]
    \\ IMP_RES_TAC stack_ok_POP
    \\ FULL_SIMP_TAC (std_ss++star_ss) [zR_def])
  val th = MP th lemma
  in th |> stack_ss end);

(* SPEC_1 jmp imm *)

val x64_ret_raw_spec_1 = save_thm("x64_ret_raw_spec_1",let
  val th = x64_Lib.x64_step "48E9"
  val c = calc_code th
  val th = pre_process_thm th
  val th = RW [w2n_MOD] th
  val th = x64_prove_one_spec_1 th c
  in th end);

(* read/write stack *)

val LENGTH_LESS = prove(
  ``!xs m. m < LENGTH xs ==> ?ys z zs. (xs = ys ++ z::zs) /\ (LENGTH ys = m)``,
  Induct \\ SIMP_TAC (srw_ss()) [] \\ REPEAT STRIP_TAC
  \\ Cases_on `m` \\ FULL_SIMP_TAC std_ss [LENGTH_NIL,APPEND,CONS_11]
  \\ RES_TAC \\ Q.LIST_EXISTS_TAC [`h::ys`,`z`,`zs`]
  \\ FULL_SIMP_TAC std_ss [APPEND,LENGTH,GSYM APPEND_ASSOC]);

val EL_LENGTH = prove(
  ``!xs y ys. EL (LENGTH xs) (xs ++ y::ys) = y``,
  Induct \\ FULL_SIMP_TAC std_ss [LENGTH,EL,APPEND,HD,TL]);

val stack_ok_EL = store_thm("stack_ok_EL",
  ``stack_ok rsp top base stack dm m /\
    w2n r8 DIV 8 < LENGTH stack /\ (w2n r8 MOD 8 = 0) ==>
    (r8 + rsp IN dm /\ (r8 + rsp && 0x7w = 0x0w)) /\
    stack_ok rsp top base (LUPDATE r0 (w2n r8 DIV 8) stack) dm
      ((r8 + rsp =+ r0) m) /\
    (m (r8 + rsp) = EL (w2n r8 DIV 8) stack)``,
  SIMP_TAC std_ss [stack_ok_thm] \\ STRIP_TAC
  \\ Cases_on `r8` \\ FULL_SIMP_TAC (srw_ss()) []
  \\ MP_TAC (DIVISION |> SIMP_RULE std_ss [PULL_FORALL]
                      |> Q.SPECL [`8`,`n`] |> RW1 [MULT_COMM])
  \\ ASM_SIMP_TAC std_ss [] \\ Q.ABBREV_TAC `k = n DIV 8`
  \\ POP_ASSUM (K ALL_TAC) \\ STRIP_TAC \\ FULL_SIMP_TAC std_ss []
  \\ POP_ASSUM (K ALL_TAC)
  \\ IMP_RES_TAC LENGTH_LESS
  \\ POP_ASSUM (ASSUME_TAC o GSYM)
  \\ FULL_SIMP_TAC std_ss [LUPDATE_LENGTH,EL_LENGTH]
  \\ FULL_SIMP_TAC std_ss [PULL_EXISTS]
  \\ Q.EXISTS_TAC `rest`
  \\ FULL_SIMP_TAC std_ss [LENGTH,LENGTH_APPEND]
  \\ FULL_SIMP_TAC std_ss [stack_list_APPEND,stack_list_def]
  \\ SEP_R_TAC \\ STRIP_TAC
  THEN1 (SIMP_TAC std_ss [GSYM word_mul_n2w]
         \\ Q.PAT_X_ASSUM `0x7w && rsp = 0x0w` MP_TAC \\ blastLib.BBLAST_TAC)
  \\ SEP_W_TAC \\ FULL_SIMP_TAC (std_ss++star_ss) []);

val LENGTH_LESS_REV = prove(
  ``!xs m. m < LENGTH xs ==> ?ys z zs. (xs = ys ++ z::zs) /\ (LENGTH zs = m)``,
  recInduct SNOC_INDUCT \\ SIMP_TAC std_ss [LENGTH,LENGTH_SNOC]
  \\ SIMP_TAC (srw_ss()) [] \\ REPEAT STRIP_TAC
  \\ Cases_on `m` \\ FULL_SIMP_TAC std_ss [LENGTH_NIL,APPEND,CONS_11,APPEND_NIL]
  THEN1 (METIS_TAC []) \\ RES_TAC \\ Q.LIST_EXISTS_TAC [`ys`,`z`,`zs ++ [x]`]
  \\ FULL_SIMP_TAC std_ss [APPEND,LENGTH,GSYM APPEND_ASSOC,LENGTH_APPEND,ADD1]);

val stack_ok_REV_EL = store_thm("stack_ok_REV_EL",
  ``stack_ok rsp top base stack dm m /\
    w2n r8 DIV 8 < LENGTH stack /\ (w2n r8 MOD 8 = 0) ==>
    (base - 8w - r8 IN dm /\ (base - 8w - r8 && 0x7w = 0x0w)) /\
    (m (base - 8w - r8) = EL (w2n r8 DIV 8) (REVERSE stack))``,
  SIMP_TAC std_ss [stack_ok_thm] \\ STRIP_TAC
  \\ Cases_on `r8` \\ FULL_SIMP_TAC std_ss [w2n_n2w]
  \\ MP_TAC (DIVISION |> SIMP_RULE std_ss [PULL_FORALL]
                      |> Q.SPECL [`8`,`n`] |> RW1 [MULT_COMM])
  \\ ASM_SIMP_TAC std_ss [] \\ Q.ABBREV_TAC `k = n DIV 8`
  \\ POP_ASSUM (K ALL_TAC) \\ STRIP_TAC \\ FULL_SIMP_TAC std_ss []
  \\ POP_ASSUM (K ALL_TAC)
  \\ IMP_RES_TAC LENGTH_LESS_REV
  \\ FULL_SIMP_TAC std_ss [REVERSE_APPEND,REVERSE_DEF]
  \\ SIMP_TAC std_ss [GSYM APPEND_ASSOC,APPEND]
  \\ POP_ASSUM (ASSUME_TAC o GSYM)
  \\ FULL_SIMP_TAC std_ss [] \\ POP_ASSUM (K ALL_TAC)
  \\ ONCE_REWRITE_TAC [GSYM LENGTH_REVERSE]
  \\ SIMP_TAC std_ss [rich_listTheory.EL_LENGTH_APPEND
       |> Q.SPEC `x::xs` |> SIMP_RULE (srw_ss()) []]
  \\ SIMP_TAC std_ss [LENGTH_REVERSE]
  \\ FULL_SIMP_TAC std_ss [stack_list_APPEND,stack_list_def]
  \\ Q.PAT_X_ASSUM `xx = base` (ASSUME_TAC o GSYM) \\ POP_ASSUM (K ALL_TAC)
  \\ Q.PAT_X_ASSUM `xx = base` (ASSUME_TAC o GSYM)
  \\ FULL_SIMP_TAC std_ss [LENGTH_APPEND,LENGTH,LEFT_ADD_DISTRIB]
  \\ SIMP_TAC std_ss [MULT_CLAUSES,GSYM word_arith_lemma1]
  \\ SIMP_TAC std_ss [WORD_ADD_SUB,WORD_ADD_ASSOC]
  \\ ONCE_REWRITE_TAC [word_arith_lemma1]
  \\ ONCE_REWRITE_TAC [word_arith_lemma1]
  \\ SIMP_TAC std_ss [WORD_ADD_SUB,WORD_ADD_ASSOC]
  \\ SEP_R_TAC \\ FULL_SIMP_TAC std_ss []
  \\ SIMP_TAC std_ss [GSYM word_mul_n2w]
  \\ Q.PAT_X_ASSUM `rsp && 0x7w = 0x0w` MP_TAC
  \\ blastLib.BBLAST_TAC);

val x64_el_r0_r8 = save_thm("x64_el_r0_r8",let
  val ((th,_,_),_) = x64_spec_memory64 (x64_encode "mov [rsp+r8], r0")
  val th = th |> RW [WORD_ADD_SUB]
  val th = Q.INST [`rip`|->`p`] th
  val pre = ``w2n r8 DIV 8 < LENGTH (stack:word64 list) /\
              (w2n (r8:word64) MOD 8 = 0)``
  val th = th |> Q.INST [`r4`|->`rsp`,`df`|->`dm`,`f`|->`m`,`rip`|->`p`]
  val th = SPEC_FRAME_RULE th ``
             zR1 zGhost_stack_top top * zR1 zGhost_stack_bottom base *
             cond (stack_ok rsp top base stack dm m /\ ^pre)``
  val (th,goal) = SPEC_WEAKEN_RULE th ``(zPC (p + 0x4w) * zR 0x8w r8 *
      zR 0x0w r0 * zSTACK (base,LUPDATE r0 (w2n r8 DIV 8) stack))``
  val lemma = prove(goal,
    SIMP_TAC std_ss [SEP_IMP_def,zSTACK_def,SEP_CLAUSES,SEP_EXISTS_THM]
    \\ REPEAT STRIP_TAC \\ Q.LIST_EXISTS_TAC [`rsp`,`top`,`dm`,
        `(r8 + rsp =+ r0) m`]
    \\ FULL_SIMP_TAC (std_ss++sep_cond_ss) [cond_STAR]
    \\ IMP_RES_TAC stack_ok_EL
    \\ FULL_SIMP_TAC (std_ss++star_ss) [zR_def])
  val th = MP th lemma
  val th = th |> Q.GENL [`rsp`,`top`,`dm`,`m`]
              |> SIMP_RULE std_ss [SPEC_PRE_EXISTS]
  val (th,goal) = SPEC_STRENGTHEN_RULE th
    ``zPC p * zR 0x8w r8 * zR 0x0w r0 * zSTACK (base,stack) * cond (^pre)``
  val lemma = prove(goal,
    SIMP_TAC std_ss [SEP_IMP_def,zSTACK_def,SEP_CLAUSES,SEP_EXISTS_THM]
    \\ REPEAT STRIP_TAC \\ Q.LIST_EXISTS_TAC [`rsp`,`top`,`dm`,`m`]
    \\ FULL_SIMP_TAC (std_ss++sep_cond_ss) [cond_STAR]
    \\ IMP_RES_TAC stack_ok_EL
    \\ FULL_SIMP_TAC (std_ss++star_ss) [zR_def])
  val th = MP th lemma
  in th |> stack_ss end);

val x64_lupdate_r0_r8 = save_thm("x64_lupdate_r0_r8",let
  val ((th,_,_),_) = x64_spec_memory64 (x64_encode "mov r0, [rsp+r8]")
  val th = th |> RW [WORD_ADD_SUB]
  val th = Q.INST [`rip`|->`p`] th
  val pre = ``w2n r8 DIV 8 < LENGTH (stack:word64 list) /\
              (w2n (r8:word64) MOD 8 = 0)``
  val th = th |> Q.INST [`r4`|->`rsp`,`df`|->`dm`,`f`|->`m`,`rip`|->`p`]
  val th = SPEC_FRAME_RULE th ``
             zR1 zGhost_stack_top top * zR1 zGhost_stack_bottom base *
             cond (stack_ok rsp top base stack dm m /\ ^pre)``
  val (th,goal) = SPEC_WEAKEN_RULE th ``(zPC (p + 0x4w) * zR 0x8w r8 *
      zR 0x0w (EL (w2n r8 DIV 8) stack) * zSTACK (base,stack))``
  val lemma = prove(goal,
    SIMP_TAC std_ss [SEP_IMP_def,zSTACK_def,SEP_CLAUSES,SEP_EXISTS_THM]
    \\ REPEAT STRIP_TAC \\ Q.LIST_EXISTS_TAC [`rsp`,`top`,`dm`,`m`]
    \\ FULL_SIMP_TAC (std_ss++sep_cond_ss) [cond_STAR]
    \\ IMP_RES_TAC stack_ok_EL
    \\ FULL_SIMP_TAC (std_ss++star_ss) [zR_def])
  val th = MP th lemma
  val th = th |> Q.GENL [`rsp`,`top`,`dm`,`m`]
              |> SIMP_RULE std_ss [SPEC_PRE_EXISTS]
  val (th,goal) = SPEC_STRENGTHEN_RULE th
    ``zPC p * zR 0x8w r8 * zR 0x0w r0 * zSTACK (base,stack) * cond (^pre)``
  val lemma = prove(goal,
    SIMP_TAC std_ss [SEP_IMP_def,zSTACK_def,SEP_CLAUSES,SEP_EXISTS_THM]
    \\ REPEAT STRIP_TAC \\ Q.LIST_EXISTS_TAC [`rsp`,`top`,`dm`,`m`]
    \\ FULL_SIMP_TAC (std_ss++sep_cond_ss) [cond_STAR]
    \\ IMP_RES_TAC stack_ok_EL
    \\ FULL_SIMP_TAC (std_ss++star_ss) [zR_def])
  val th = MP th lemma
  in th |> stack_ss end);

val imm32_lemma = prove(
  ``(k:num) < 2 ** 28 ==>
    (SIGN_EXTEND 32 64 (w2n ((n2w:num->word32) (8 * k))) = 8 * k)``,
  FULL_SIMP_TAC (srw_ss()) [w2n_n2w,bitTheory.SIGN_EXTEND_def,LET_DEF]
  \\ REPEAT STRIP_TAC \\ `(8 * k) < 4294967296` by DECIDE_TAC
  \\ FULL_SIMP_TAC std_ss [bitTheory.BIT_def,bitTheory.BITS_THM]
  \\ `8 * k < 2147483648` by DECIDE_TAC
  \\ FULL_SIMP_TAC std_ss [LESS_DIV_EQ_ZERO]);

val stack_ok_EL_VAR = prove(
  ``stack_ok rsp top base stack dm m /\ k < LENGTH stack ==>
    (rsp + n2w (8 * k) IN dm /\ (rsp + n2w (8 * k) && 0x7w = 0x0w)) /\
    stack_ok rsp top base (LUPDATE r0 k stack) dm ((rsp + n2w (8 * k) =+ r0) m) /\
    (m (rsp + n2w (8 * k)) = EL k stack)``,
  SIMP_TAC std_ss [stack_ok_thm] \\ STRIP_TAC
  \\ FULL_SIMP_TAC std_ss []
  \\ IMP_RES_TAC LENGTH_LESS
  \\ POP_ASSUM (ASSUME_TAC o GSYM)
  \\ FULL_SIMP_TAC std_ss [LUPDATE_LENGTH,EL_LENGTH]
  \\ FULL_SIMP_TAC std_ss [PULL_EXISTS]
  \\ Q.EXISTS_TAC `rest`
  \\ FULL_SIMP_TAC std_ss [LENGTH,LENGTH_APPEND]
  \\ FULL_SIMP_TAC std_ss [stack_list_APPEND,stack_list_def]
  \\ SEP_R_TAC \\ STRIP_TAC
  THEN1 (SIMP_TAC std_ss [GSYM word_mul_n2w]
         \\ Q.PAT_X_ASSUM `rsp && 0x7w = 0x0w` MP_TAC \\ blastLib.BBLAST_TAC)
  \\ SEP_W_TAC \\ FULL_SIMP_TAC (std_ss++star_ss) []);

val x64_el_r0_imm = save_thm("x64_el_r0_imm",let
  val ((th,_,_),_) = x64_spec_memory64 "488B8424"
  val th = RW [GSYM IMM32_def] th
  val th = Q.INST [`imm32`|->`n2w (8*k)`,`rip`|->`p`] th
  val th = DISCH ``(k:num) < 2 ** 28`` th
  val th = SIMP_RULE bool_ss [imm32_lemma] th
  val lemma2 = prove(
    ``k < 2 ** 28 ==> (8 * k) < 18446744073709551616n``,
    FULL_SIMP_TAC std_ss [] \\ DECIDE_TAC);
  val th = RW1 [WORD_ADD_COMM] th |> RW [WORD_ADD_SUB]
  val th = SIMP_RULE std_ss [lemma2,RW1 [MULT_COMM] MULT_DIV,w2n_n2w,
                             RW1 [MULT_COMM] MOD_EQ_0,EVAL ``dimword (:64)``] th
  val th = SIMP_RULE std_ss [GSYM SPEC_MOVE_COND] th
  val pre = ``k < LENGTH (stack:word64 list) /\ k < 268435456``
  val th = th |> Q.INST [`r4`|->`rsp`,`df`|->`dm`,`f`|->`m`,`rip`|->`p`]
  val th = SPEC_FRAME_RULE th ``
             zR1 zGhost_stack_top top * zR1 zGhost_stack_bottom base *
             cond (stack_ok rsp top base stack dm m /\ ^pre)``
  val th = RW1 [WORD_ADD_COMM] th
  val (th,goal) = SPEC_WEAKEN_RULE th ``(zPC (p + 0x8w) *
      zR 0x0w (EL k stack) * zSTACK (base,stack))``
  val lemma = prove(goal,
    SIMP_TAC std_ss [SEP_IMP_def,zSTACK_def,SEP_CLAUSES,SEP_EXISTS_THM]
    \\ REPEAT STRIP_TAC \\ Q.LIST_EXISTS_TAC [`rsp`,`top`,`dm`,`m`]
    \\ FULL_SIMP_TAC (std_ss++sep_cond_ss) [cond_STAR]
    \\ IMP_RES_TAC stack_ok_EL_VAR
    \\ FULL_SIMP_TAC (std_ss++star_ss) [zR_def])
  val th = MP th lemma
  val th = th |> Q.GENL [`rsp`,`top`,`dm`,`m`]
              |> SIMP_RULE std_ss [SPEC_PRE_EXISTS]
  val (th,goal) = SPEC_STRENGTHEN_RULE th
    ``zPC p * zR 0x0w r0 * zSTACK (base,stack) * cond (^pre)``
  val lemma = prove(goal,
    SIMP_TAC std_ss [SEP_IMP_def,zSTACK_def,SEP_CLAUSES,SEP_EXISTS_THM]
    \\ REPEAT STRIP_TAC \\ Q.LIST_EXISTS_TAC [`rsp`,`top`,`dm`,`m`]
    \\ FULL_SIMP_TAC (std_ss++sep_cond_ss) [cond_STAR]
    \\ IMP_RES_TAC stack_ok_EL_VAR
    \\ FULL_SIMP_TAC (std_ss++star_ss) [zR_def])
  val th = MP th lemma
  in th |> stack_ss end);

val x64_lupdate_r0_imm = save_thm("x64_lupdate_r0_imm",let
  val ((th,_,_),_) = x64_spec_memory64 "48898424"
  val th = RW [GSYM IMM32_def] th
  val th = Q.INST [`imm32`|->`n2w (8*k)`,`rip`|->`p`] th
  val th = DISCH ``(k:num) < 2 ** 28`` th
  val th = SIMP_RULE bool_ss [imm32_lemma] th
  val lemma2 = prove(
    ``k < 2 ** 28 ==> (8 * k) < 18446744073709551616n``,
    FULL_SIMP_TAC std_ss [] \\ DECIDE_TAC);
  val th = RW1 [WORD_ADD_COMM] th |> RW [WORD_ADD_SUB]
  val th = SIMP_RULE std_ss [lemma2,RW1 [MULT_COMM] MULT_DIV,w2n_n2w,
                             RW1 [MULT_COMM] MOD_EQ_0,EVAL ``dimword (:64)``] th
  val th = SIMP_RULE std_ss [GSYM SPEC_MOVE_COND] th
  val pre = ``k < LENGTH (stack:word64 list) /\ k < 268435456``
  val th = th |> Q.INST [`r4`|->`rsp`,`df`|->`dm`,`f`|->`m`,`rip`|->`p`]
  val th = SPEC_FRAME_RULE th ``
             zR1 zGhost_stack_top top * zR1 zGhost_stack_bottom base *
             cond (stack_ok rsp top base stack dm m /\ ^pre)``
  val th = RW1 [WORD_ADD_COMM] th
  val (th,goal) = SPEC_WEAKEN_RULE th ``(zPC (p + 0x8w) *
      zR 0x0w r0 * zSTACK (base,LUPDATE r0 k stack))``
  val lemma = prove(goal,
    SIMP_TAC std_ss [SEP_IMP_def,zSTACK_def,SEP_CLAUSES,SEP_EXISTS_THM]
    \\ REPEAT STRIP_TAC
    \\ Q.LIST_EXISTS_TAC [`rsp`,`top`,`dm`,`(rsp + n2w (8 * k) =+ r0) m`]
    \\ FULL_SIMP_TAC (std_ss++sep_cond_ss) [cond_STAR]
    \\ IMP_RES_TAC stack_ok_EL_VAR
    \\ FULL_SIMP_TAC (std_ss++star_ss) [zR_def])
  val th = MP th lemma
  val th = th |> Q.GENL [`rsp`,`top`,`dm`,`m`]
              |> SIMP_RULE std_ss [SPEC_PRE_EXISTS]
  val (th,goal) = SPEC_STRENGTHEN_RULE th
    ``zPC p * zR 0x0w r0 * zSTACK (base,stack) * cond (^pre)``
  val lemma = prove(goal,
    SIMP_TAC std_ss [SEP_IMP_def,zSTACK_def,SEP_CLAUSES,SEP_EXISTS_THM]
    \\ REPEAT STRIP_TAC \\ Q.LIST_EXISTS_TAC [`rsp`,`top`,`dm`,`m`]
    \\ FULL_SIMP_TAC (std_ss++sep_cond_ss) [cond_STAR]
    \\ IMP_RES_TAC stack_ok_EL_VAR
    \\ FULL_SIMP_TAC (std_ss++star_ss) [zR_def])
  val th = MP th lemma
  in th |> stack_ss end);


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
        ^IO (pi,input,po,output) * ~zS * zSTACK (base,x::stack)) {}
       (zPC x * zR1 RAX (HD (SNOC (~0w) (MAP w2w input))) * ~zR1 RDI *
        ^caller_saver_tm * ^callee_saved_tm *
        ^IO (pi,DROP 1 input,po,output) * ~zS * zSTACK (base,stack))``;

val io_putchar_tm =
  ``SPEC X64_MODEL
       (zPC po * ~zR1 RAX * zR1 RDI (w2w c) * ^caller_saver_tm * ^callee_saved_tm *
        ^IO (pi,input,po,output) * ~zS * zSTACK (base,x::stack)) {}
       (zPC x * ~zR1 RAX * ~zR1 RDI * ^caller_saver_tm * ^callee_saved_tm *
        ^IO (pi,input,po,output ++ [c]) * ~zS * zSTACK (base,stack))``;

fun genall tm v =
  foldr mk_forall tm (filter (fn x => x !~ v) (free_vars tm));

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
