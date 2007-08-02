(* ========================================================================= *)
(* FILE          : correctScript.sml                                         *)
(* DESCRIPTION   : Formal verification of the ARM6                           *)
(*                                                                           *)
(* AUTHOR        : (c) Anthony Fox, University of Cambridge                  *)
(* DATE          : 2001 - 2005                                               *)
(* ========================================================================= *)

(* interactive use:
  should run with "hol -I .."

  app load ["my_listTheory", "io_onestepTheory", "armTheory", "coreTheory",
            "lemmasTheory", "coprocessorTheory", "multTheory", "blockTheory",
            "wordsLib", "iclass_compLib", "armLib", "pred_setSimps"];
*)

open HolKernel boolLib bossLib;
open Q arithmeticTheory rich_listTheory my_listTheory wordsLib wordsTheory;
open onestepTheory io_onestepTheory iclass_compLib armLib;
open armTheory coreTheory lemmasTheory coprocessorTheory;
open multTheory blockTheory interruptsTheory;

val _ = new_theory "correct";

(* ------------------------------------------------------------------------- *)

infix \\ << >>

val op \\ = op THEN;
val op << = op THENL;
val op >> = op THEN1;

val Abbr = BasicProvers.Abbr;
val PRED_SET_ss = pred_setSimps.PRED_SET_ss;

val FST_COND_RAND = ISPEC `FST` COND_RAND;
val SND_COND_RAND = ISPEC `SND` COND_RAND;

val booli_ss = bool_ss ++ ICLASS_ss ++ rewrites [iseq_distinct];
val std_ss = std_ss ++ boolSimps.LET_ss;
val arith_ss = arith_ss ++ boolSimps.LET_ss;
val stdi_ss = armLib.stdi_ss++rewrites[FST_COND_RAND,SND_COND_RAND];

val SUC2NUM = CONV_RULE numLib.SUC_TO_NUMERAL_DEFN_CONV;

val GENLISTn = SUC2NUM GENLIST;
val numeral_funpow = numeralTheory.numeral_funpow;

val POP_LAST_TAC = POP_ASSUM (K ALL_TAC);
fun POP_LASTN_TAC n = NTAC n POP_LAST_TAC;

val tt = set_trace "types";
val fvs = set_trace "goalstack fvs";

(* ------------------------------------------------------------------------- *)

val IS_MEMOP2_def = Define `IS_MEMOP2 (nmrq2,nopc1,nrw,nbw,areg) = nopc1`;

val arm6out_nchotomy =
  armLib.tupleCases
  ``(dout:word32, mrq2:bool, nopc1:bool, nrw:bool, nbw:bool, areg:word32)``;

val IS_MEMOP2 = prove(
  `IS_MEMOP = IS_MEMOP2 o SND`,
  REWRITE_TAC [FUN_EQ_THM]
    \\ STRIP_TAC \\ SPEC_THEN `x` STRUCT_CASES_TAC arm6out_nchotomy
    \\ SIMP_TAC std_ss [IS_MEMOP2_def,IS_MEMOP_def]);

val LET_FILTER = prove(
  `(!P. FILTER P [] = []) /\
    !P h t. FILTER P (h::t) = let l = FILTER P t in (if P h then h::l else l)`,
  SIMP_TAC (list_ss++boolSimps.LET_ss) []);

(* ------------------------------------------------------------------------- *)

local
  val SIMP_SPEC_0 = SIMP_RULE list_ss [] o SPEC `0`
in
  val HD_SNOC   = SIMP_SPEC_0 EL_SNOC
  val HD_MAP    = SIMP_SPEC_0 EL_MAP
  val HD_APPEND = SIMP_SPEC_0 EL_APPEND1
end;

val HD_GENLIST =
  (GEN_ALL o SIMP_RULE list_ss [] o INST [`x` |-> `0`] o SPEC_ALL) EL_GENLIST;

val HD_APPEND2 = prove(
  `!n f l. HD (GENLIST f n ++ l) = if n = 0 then HD l else f 0`,
  Cases \\ SIMP_TAC list_ss [GENLIST,SNOC,HD_APPEND]
    \\ Cases_on `n'`
    \\ SIMP_TAC list_ss [LENGTH_SNOC,LENGTH_GENLIST,HD_SNOC,
         HD_APPEND,HD_GENLIST] \\ SIMP_TAC list_ss [GENLIST,SNOC]);

val FILTER_SND = prove(
   `!P a h b. ~NULL a ==>
      (FILTER (P o SND) (ZIP (a,h::b)) =
        let t = FILTER (P o SND) (ZIP (TL a,b)) in
          if P h then (HD a,h)::t else t)`,
  Cases_on `a` \\ RW_TAC (list_ss++boolSimps.LET_ss) []);

val CONS_SNOC = prove(
  `!l a b. a::(SNOC b l) = SNOC b (a::l)`,
  Cases \\ SIMP_TAC list_ss [SNOC]);

val GENLIST_CONS = prove(
  `!n f. GENLIST (\t. f t) (SUC n) = f 0::(GENLIST (\t. f (SUC t)) n)`,
  Induct \\ SIMP_TAC list_ss [GENLIST,SNOC]
    \\ REWRITE_TAC [CONS_SNOC]
    \\ POP_ASSUM (fn th => SIMP_TAC bool_ss [GSYM th,GENLIST]));

val MOVE_DOUT_INV =
  (GEN_ALL o SIMP_RULE std_ss [] o DISCH `~NULL l` o GSYM o SPEC_ALL)
  MOVE_DOUT_def;

val NULL_GENLIST = prove(`!n f. NULL (GENLIST f n) = (n = 0)`,
  Cases \\ SIMP_TAC list_ss [GENLIST,NULL_SNOC]);

val NULL_MAP = prove(`!l f. NULL (MAP f l) = NULL l`,
  Cases \\ SIMP_TAC list_ss []);

val NULL_APPEND_RIGHT = prove(`!a b. ~NULL b ==> ~NULL (a ++ b)`,
  RW_TAC list_ss [NULL_EQ_NIL]);

val NULL_APPEND_LEFT = prove(`!a b. ~NULL a ==> ~NULL (a ++ b)`,
  RW_TAC list_ss [NULL_EQ_NIL]);

val LENGTH_NULL = (GSYM o REWRITE_RULE [GSYM NULL_EQ_NIL]) LENGTH_NIL;

val LENGTH_NOT_NULL = prove(`0 < LENGTH l = ~NULL l`,
  SIMP_TAC arith_ss [LENGTH_NULL]);

val FILTER_MEMOP_ONE = (GEN_ALL o
   SIMP_RULE list_ss [GSYM IS_MEMOP2,MOVE_DOUT_INV,TL_SNOC,NULL_MAP,
     HD_SNOC,LENGTH_NOT_NULL,HD_MAP] o
   DISCH `~NULL t` o
   SIMP_CONV list_ss [MOVE_DOUT_def,IS_MEMOP2,FILTER_SND,NULL_SNOC])
   ``FILTER IS_MEMOP (MOVE_DOUT x (h::t))``;

val FILTER_MEMOP_SINGLETON =
   (SIMP_CONV list_ss [MOVE_DOUT_def,IS_MEMOP2,FILTER_SND,NULL_SNOC,SNOC])
   ``FILTER IS_MEMOP (MOVE_DOUT x [h])``;

val LENGTH_MAPS = prove(
  `!l x f g. ~(l = []) ==> (LENGTH (SNOC x (TL (MAP g l))) = LENGTH (MAP f l))`,
  Induct \\ ASM_SIMP_TAC list_ss [SNOC,rich_listTheory.LENGTH_SNOC]);

val LENGTH_MOVE_DOUT = prove(
  `!l x. LENGTH (MOVE_DOUT x l) = LENGTH l`,
  RW_TAC list_ss [MOVE_DOUT_def,LENGTH_ZIP,LENGTH_MAPS,NULL_EQ_NIL,LENGTH_SNOC,
                  REWRITE_RULE [LENGTH_NOT_NULL,NULL_EQ_NIL] LENGTH_TL]
    \\ FULL_SIMP_TAC arith_ss [GSYM NULL_EQ_NIL,GSYM LENGTH_NOT_NULL]);

val FILTER_MOVE_DOUT = prove(
  `!l x. (FILTER IS_MEMOP (MOVE_DOUT x l) = []) = (FILTER IS_MEMOP l = [])`,
  Induct >> SIMP_TAC list_ss [MOVE_DOUT_def]
    \\ RW_TAC (list_ss++boolSimps.LET_ss)
         [TL_SNOC,NULL_EQ_NIL,MOVE_DOUT_def,NULL_SNOC,FILTER_SND,IS_MEMOP2]
    \\ FULL_SIMP_TAC std_ss [MOVE_DOUT_def,NULL_EQ_NIL,IS_MEMOP2]);

val IS_MEM_MOVE_DOUT = prove(
  `!l n x. n < LENGTH l ==>
       (IS_MEMOP (EL n (MOVE_DOUT x l)) = IS_MEMOP (EL n l))`,
  RW_TAC list_ss [IS_MEMOP2,MOVE_DOUT_def,NULL_EQ_NIL]
    \\ METIS_TAC [listTheory.EL_ZIP,LENGTH_MAPS,LENGTH_MAP,
         EL_MAP,pairTheory.SND]);

val FILTER_MEMOP_ALL = prove(
  `!f d x. (!t. t < d ==> ~IS_MEMOP (f t)) ==>
         (FILTER IS_MEMOP (MOVE_DOUT x (GENLIST (\t. f t) d)) = [])`,
  METIS_TAC [FILTER_ALL,IS_MEM_MOVE_DOUT,LENGTH_GENLIST,
    LENGTH_MOVE_DOUT,EL_GENLIST]);

val FILTER_MEMOP_NONE = prove(
  `!f d x. (!t. t < d ==> IS_MEMOP (f t)) ==>
     (FILTER IS_MEMOP (MOVE_DOUT x (GENLIST (\t. f t) d)) =
      MOVE_DOUT x (GENLIST (\t. f t) d))`,
  METIS_TAC [FILTER_NONE,IS_MEM_MOVE_DOUT,LENGTH_GENLIST,
    LENGTH_MOVE_DOUT,EL_GENLIST]);

val TL_EQ_BUTFIRSTN_1 = prove(
  `!l. ~(l = []) ==> (BUTFIRSTN 1 l = TL l)`,
  Cases \\ SIMP_TAC list_ss [SUC2NUM BUTFIRSTN]);

val NOT_NIL_GTEQ_1 =
  (REWRITE_RULE [DECIDE ``!n. ~(n = 0) = (1 <= n)``] o
   ONCE_REWRITE_RULE [DECIDE ``!a:bool b. (a = b) = (~a = ~b)``]) LENGTH_NIL;

val TL_APPEND =
  (SIMP_RULE std_ss [REWRITE_RULE [NULL_EQ_NIL] NULL_APPEND_LEFT,
     NOT_NIL_GTEQ_1,TL_EQ_BUTFIRSTN_1] o
  SPEC `1`) BUTFIRSTN_APPEND1;

val LENGTH_MAPS2 = prove(
  `!l x y f g. LENGTH (SNOC x (MAP f l)) = LENGTH (y::MAP g l)`,
  SIMP_TAC bool_ss [LENGTH_SNOC,LENGTH_MAP,LENGTH]);

val MOVE_DOUT_APPEND = prove(
  `!b a x. ~NULL b ==>
     (MOVE_DOUT x (a ++ b) = MOVE_DOUT (FST (HD b)) a ++ MOVE_DOUT x b)`,
  Induct \\ RW_TAC list_ss [MOVE_DOUT_def,NULL_EQ_NIL,ZIP_APPEND,
         LENGTH_MAPS,LENGTH_MAPS2]
    \\ SIMP_TAC list_ss [SNOC_APPEND]
    \\ ONCE_REWRITE_TAC [CONS_APPEND]
    \\ SIMP_TAC list_ss []
    \\ METIS_TAC [APPEND_ASSOC,TL_APPEND,REWRITE_RULE [NULL_EQ_NIL] NULL_MAP]);

val MAP_CONG2 = prove(
  `!a b f g. (LENGTH a = LENGTH b) /\
             (!n. n < LENGTH a ==> (f (EL n a) = g (EL n b))) ==>
             (MAP f a = MAP g b)`,
  METIS_TAC [LIST_EQ,EL_MAP,LENGTH_MAP]);

val LENGTH_MAPS3 = prove(
  `!l x f g. ~NULL l ==> (LENGTH (SNOC x (TL l)) = LENGTH l)`,
  RW_TAC list_ss [rich_listTheory.LENGTH_SNOC,LENGTH_TL,LENGTH_NULL]);

val MAP_LDM_MEMOP = prove(
  `!y n. MAP MEMOP (MOVE_DOUT y (GENLIST (\t. (f t,b1,b2,F,b3,g t)) n)) =
         GENLIST (\t. MemRead (g t)) n`,
  Induct_on `n` >> SIMP_TAC list_ss [GENLIST,MOVE_DOUT_def]
    \\ RW_TAC list_ss [GENLIST,MOVE_DOUT_def,NULL_SNOC,MAP_SNOC,MAP_GENLIST,
         TL_SNOC,NULL_GENLIST,MEMOP_def,ZIP_SNOC,LENGTH_GENLIST,LENGTH_MAPS3]
    \\ FULL_SIMP_TAC std_ss [MOVE_DOUT_def,MAP_GENLIST,NULL_GENLIST]);

val MAP_LDM_MEMOP = GEN_ALL MAP_LDM_MEMOP;

val lem = prove(
  `!f g n x. x < n ==>
      ((\t. MemWrite b (g t) (if t + 1 = n then f n else f (t + 1))) x =
       (\t. MemWrite b (g t) (if t + 1 = SUC n then y else f (t + 1))) x)`,
  RW_TAC arith_ss [ADD1]);

val MAP_STM_MEMOP = prove(
  `!y n.
    MAP MEMOP (MOVE_DOUT y (GENLIST (\t. (f t,b1,b2,T,b3,g t)) n)) =
    GENLIST (\t. MemWrite (~b3) (g t) (if t + 1 = n then y else f (t + 1))) n`,
  Induct_on `n` >> SIMP_TAC list_ss [GENLIST,MOVE_DOUT_def]
    \\ RW_TAC list_ss [GENLIST,MOVE_DOUT_def,NULL_SNOC,MAP_SNOC,MAP_GENLIST,
         TL_SNOC,NULL_GENLIST,MEMOP_def,ZIP_SNOC,LENGTH_GENLIST,LENGTH_MAPS3]
    \\ FULL_SIMP_TAC std_ss [MOVE_DOUT_def,MAP_GENLIST,NULL_GENLIST]
    \\ METIS_TAC [GEN_ALL (MATCH_MP (SPEC_ALL GENLIST_FUN_EQ)
                    (SPECL [`f`,`g`,`n`] lem))]);

val MAP_STM_MEMOP = GEN_ALL MAP_STM_MEMOP;

(* ------------------------------------------------------------------------- *)

val DUR_IC =
 (SIMP_RULE bossLib.bool_ss [GSYM RIGHT_AND_OVER_OR,GSYM LEFT_AND_OVER_OR] o
  SIMP_RULE (stdi_ss++PBETA_ss++boolSimps.CONJ_ss++boolSimps.DNF_ss)
   [RWA_def,PCCHANGE_def,FST_COND_RAND,SND_COND_RAND]) DUR_IC_def;

val DUR_X2 = CONJ (GSYM IMP_DISJ_THM) ((SIMP_RULE (srw_ss()++boolSimps.LET_ss)
   [ABORTINST_def,IC_def,IFLAGS_def,DECODE_PSR_def] o
   INST [`iregval` |-> `T`,`onewinst` |-> `T`,`ointstart` |-> `F`]) DUR_X);

val arm6state_inp = ``<|state := ARM6 (DP reg psr areg din alua alub dout)
  (CTRL pipea pipeaval pipeb pipebval ireg iregval ointstart onewinst endinst
     obaselatch opipebll nxtic nxtis nopc1 oorst resetlatch onfq ooonfq
     oniq oooniq pipeaabt pipebabt iregabt2 dataabt2 aregn2 mrq2 nbw nrw
     sctrlreg psrfb oareg mask orp oorp mul mul2 borrow2 mshift);
  inp := (inp : num -> bool # bool # bool # bool # word32 # bool # bool) |>``;

val arm6state = (snd o hd o snd o TypeBase.dest_record) arm6state_inp;

val INIT_ARM6 = SIMP_RULE std_ss [ABORTINST_def,NXTIC_def] INIT_ARM6_def;

val INIT_INIT = prove(
  `!x. Abbrev (x = ^arm6state_inp) /\ Abbrev (x0 = SINIT INIT_ARM6 x) ==>
         (SINIT INIT_ARM6 x0 = x0) /\ (PROJ_IREG x0.state = ireg) /\
         (ABS_ARM6 x0.state = ABS_ARM6 x.state)`,
  REPEAT STRIP_TAC
    \\ SIMP_TAC (srw_ss()) [Abbr`x`,Abbr`x0`,SINIT_def,PROJ_IREG_def,NXTIC_def,
         ABS_ARM6_def,INIT_ARM6,MASK_MASK,num2exception_exception2num]);

val IS_ABORT_LEM = prove(
  `!i t. IS_ABORT i t = FST (SND (i t))`,
  NTAC 2 STRIP_TAC
    \\ REWRITE_TAC [IS_ABORT_def]
    \\ Cases_on_arm6inp `i (t:num)`
    \\ SIMP_TAC std_ss [PROJ_ABORT_def]);

val IS_ABORT = CONJ
  ((GEN_ALL o fst o EQ_IMP_RULE o SPEC_ALL) IS_ABORT_LEM)
  ((GEN_ALL o fst o EQ_IMP_RULE o SPEC_ALL o
    ONCE_REWRITE_RULE [DECIDE ``!a b. (a = b) = (~a = ~b)``]) IS_ABORT_LEM);

val SWI_LEM = SIMP_CONV (stdi_ss++SWI_EX_ss) [] ``MASK swi_ex t3 x y``;

val LEM = prove(
  `!a x y z. a \/ ~((if ~a then x else y) = z) = a \/ ~(x = z)`,
  Cases \\ REWRITE_TAC []);

val LEM = CONJ (CONJ (CONJ LEM
          ((GEN_ALL o SIMP_RULE std_ss [] o SPEC `a \/ b`) LEM))
          ((GEN_ALL o SIMP_RULE std_ss [] o SPEC `a /\ ~b`) LEM))
          ((GEN_ALL o SIMP_RULE std_ss [] o SPEC `~a`) LEM);

val LEM2 = prove(
  `!a x y z. (a /\ ((if a then x else y) = z)) /\ c =
      a /\ ((x = z) /\ c)`, Cases \\ REWRITE_TAC []);

val finish_rws =
  [INIT_ARM6_def,DECODE_PSR_def,NXTIC_def,MASK_MASK,
   SWI_LEM,AREGN1_THM,AREGN1_BIJ,TO_WRITE_READ6,
   REG_READ_WRITE,REG_READ_WRITE_PC,REG_WRITE_WRITE];

val REG_WRITE_COMMUTE_PC = (GEN_ALL o
  SIMP_RULE std_ss [] o DISCH `~(n = 15w)` o SPEC_ALL) REG_WRITE_WRITE_PC;

val WORD_NEQS =
   LIST_CONJ [(EQF_ELIM o EVAL) ``14w = 15w:word4``,
              (EQF_ELIM o EVAL) ``2w = 0w:word3``,
              (EQF_ELIM o EVAL) ``2w = 7w:word3``];

val finish_rws2 =
  [TO_WRITE_READ6,READ_TO_READ6,REG_WRITE_WRITE,REG_READ_WRITE_NEQ,
   (GEN_ALL o REWRITE_RULE [] o INST [`n2` |-> `n1`] o
    SPEC_ALL o CONJUNCT1) REG_READ_WRITE,CONJUNCT2 REG_READ_WRITE,
   REG_WRITE_COMMUTE_PC,CONJUNCT1 exception_BIJ,CPSR_WRITE_READ,CPSR_READ_WRITE,
   GSYM WORD_ADD_SUB_SYM,WORD_ADD_SUB,WORD_ADD_0,ADD4_ADD4,WORD_NEQS];

val REMOVE_STUFF = REPEAT (WEAKEN_TAC (fn th =>
  not (can (match_term ``~(x = 15w:word4)``) th) andalso
  not (can (match_term ``~(x:word3 IN X)``) th) andalso
  not (can (match_term ``a \/ ~(x = 15w:word4)``) th)));

val FINISH_OFF =
  REMOVE_STUFF \\ RW_TAC std_ss finish_rws
    \\ FULL_SIMP_TAC std_ss [MASK_MASK,REG_READ_WRITE,REG_READ_WRITE_PC,
         EVAL ``14w = 15w:word4``];

val REGVAL_lem = prove(
  `!P a:bool ** 'a.
     ((a = b) ==> P) ==> (P \/ ~((if P then x else a) = b))`,
  RW_TAC std_ss []);

val REGVAL_lem2 = prove(
  `!P a:bool ** 'a.
     (~P \/ ~((if P then 14w:word4 else b) = 15w))`,
  RW_TAC std_ss [WORD_NEQS]);

val LT_RESET_TAC = POP_ASSUM MP_TAC
  \\ ASM_SIMP_TAC (std_ss++STATE_INP_ss++boolSimps.LIFT_COND_ss)
       [Abbr`w`,Abbr`x`,Abbr`x0`,SINIT_def,INIT_ARM6,DUR_X2]
  \\ ASM_SIMP_TAC stdi_ss [AC ADD_ASSOC ADD_COMM,ADD1,DUR_IC]
  \\ PROVE_TAC [];

val NOT_RESET2b = (GEN_ALL o REWRITE_RULE [] o SPECL [`x`,`T`]) NOT_RESET2;

val PROJ_IF_COND = GEN_ALL(prove(
  `PROJ_IF_FLAGS (if a then ARM reg1 psr else ARM reg2 psr) =
     let (nzcv,i,f,m) = DECODE_PSR (CPSR_READ psr) in (i,f)`,
  RW_TAC std_ss [PROJ_IF_FLAGS_def]));

val PROJ_IF_COND2 = GEN_ALL(prove(
  `PROJ_IF_FLAGS (if a then ARM reg (CPSR_WRITE psr
     (SET_NZCV (NZCV d) (CPSR_READ psr))) else ARM reg2 psr) =
   let (nzcv,i,f,m) = DECODE_PSR (CPSR_READ psr) in (i,f)`,
  RW_TAC std_ss [PROJ_IF_FLAGS_def,NZCV_def,DECODE_IFMODE_SET_NZCV,
    DECODE_PSR_def,CPSR_WRITE_READ]));

val PROJ_IF_COND3 = GEN_ALL(prove(
  `PROJ_IF_FLAGS (
     if a then
       ARM reg psr
     else
       ARM reg2 (if b then CPSR_WRITE psr (SET_NZCV d (CPSR_READ psr))
                      else psr)) =
     let (nzcv,i,f,m) = DECODE_PSR (CPSR_READ psr) in (i,f)`,
  RW_TAC std_ss [PROJ_IF_FLAGS_def,DECODE_IFMODE_SET_NZCV,
    DECODE_PSR_def,CPSR_WRITE_READ]));

val PROJ_IF_COND4 = GEN_ALL(prove(
  `PROJ_IF_FLAGS (
     ARM reg (if a then
       CPSR_WRITE psr
           (if b then SPSR_READ psr m
            else if c then SET_NZCV d (CPSR_READ psr)
                      else SET_NZCV e (CPSR_READ psr))
       else psr)) =
     (if a /\ b then
        let (nzcv,i,f,m) = DECODE_PSR (SPSR_READ psr m) in (i,f)
      else
        let (nzcv,i,f,m) = DECODE_PSR (CPSR_READ psr) in (i,f))`,
  RW_TAC std_ss [PROJ_IF_FLAGS_def,DECODE_IFMODE_SET_NZCV,
    DECODE_PSR_def,CPSR_WRITE_READ] \\ FULL_SIMP_TAC std_ss []));

val CP_NOT = prove(
  `!ic. ic IN {cdp_und; mrc; mcr; stc; ldc} ==>
     ~(ic = swp) /\ ~(ic = mrs_msr) /\ ~(ic = data_proc) /\ ~(ic = reg_shift) /\
     ~(ic = mla_mul) /\ ~(ic = ldr) /\ ~(ic = str) /\ ~(ic = ldm) /\
     ~(ic = stm) /\ ~(ic = br) /\ ~(ic = swi_ex) /\ ~(ic = unexec)`,
  RW_TAC (std_ss++PRED_SET_ss) []);

val CP_NOT2 = prove(
  `!ic w x. ic IN {cdp_und; mrc} ==>
        (ic IN {cdp_und; mrc; mcr; stc; ldc} /\
       ~(ic = mcr) /\ ~(ic = ldc) /\ ~(ic = stc)) /\
        ((if (ic = cdp_und) \/ ic IN {mcr; mrc; ldc; stc} /\ a /\ b then
           w
         else if ic = mrc then w + 2 else x) =
         (if (ic = cdp_und) \/ a /\ b then 0 else 2) + w)`,
  RW_TAC (arith_ss++PRED_SET_ss) []);

val CP_NOT3 = prove(
  `!ic w x. ic IN {cdp_und; mrc} ==> (~(ic = cdp_und) ==> (ic = mrc))`,
  RW_TAC (arith_ss++PRED_SET_ss) []);

val STC_LDC_NOT = prove(
  `(!ic. ic IN {stc; ldc} ==> ~(ic = cdp_und) /\ ~(ic = mrc) /\ ~(ic = mcr) /\
          ((ic = ldc) \/ (ic = stc))) /\
   (!ic. ~(ic IN {stc; ldc}) ==> ~(ic = stc) /\ ~(ic = ldc))`,
  RW_TAC (std_ss++PRED_SET_ss) []);

val EXTRACT_UNDEFINED = prove(
  `~(ic IN {0w; 1w; 2w; 5w}) ==> ~(ic IN {0w; 2w; 5w})`,
  RW_TAC (std_ss++PRED_SET_ss) []);

val SIMP_interrupt2exception5_mrs_msr =
  (GEN_ALL o SIMP_RULE std_ss [] o
   INST [`i'` |-> `FST (x:bool # bool)`,`f'` |-> `SND (x:bool#bool)`] o
   DISCH `DECODE_INST ireg = mrs_msr` o SPEC_ALL) SIMP_interrupt2exception5;

val DATA_PROCESSING =
 (SIMP_RULE std_ss [COND_RATOR,SET_NZC_def] o PairRules.PBETA_RULE o
  SIMP_RULE std_ss [ARITHMETIC_THM,TEST_OR_COMP_THM,DECODE_DATAP_def])
  DATA_PROCESSING_def;

val word2_software = prove(`num2exception (w2n (2w:word3)) = software`,
  EVAL_TAC \\ PROVE_TAC [software]);

val finish_rws3 =
  [ABS_ARM6_def,NEXT_ARM_def,state_arm_ex_case_def,EXEC_INST_def,DECODE_PSR_def,
   STC_LDC_NOT,CP_NOT,LDC_STC_def,DECODE_LDC_STC_def,ADDR_MODE5_def,MRC_def,
   MLA_MUL_def,DECODE_MLA_MUL_def,LDM_STM_def,DECODE_LDM_STM_def,ADDR_MODE4_def,
   EXCEPTION_def,MRS_def,DECODE_MRS_def,MSR_def,DECODE_MSR_def,
   DATA_PROCESSING,ADDR_MODE1_def,BRANCH_def,DECODE_BRANCH_def,
   SWP_def,DECODE_SWP_def,LDR_STR_def,DECODE_LDR_STR_def,ADDR_MODE2_def,
   SIMP_interrupt2exception,SIMP_interrupt2exception2,SIMP_interrupt2exception3,
   SIMP_interrupt2exception4,SIMP_interrupt2exception5,
   SIMP_interrupt2exception5_mrs_msr,SIMP_IS_Dabort,word2_software,
   PROJ_IF_FLAGS_def,PROJ_IF_COND,PROJ_IF_COND2,PROJ_IF_COND3,PROJ_IF_COND4,
   PROJ_DATA_def,CPSR_WRITE_READ,
   NOT_RESET,NOT_RESET2,NOT_RESET2b,LSL_ZERO,EXTRACT_UNDEFINED];

fun mk_pat t1 t2 n =
  [QUOTE (t1 ^ " = " ^ t2 ^ " " ^
    String.concat (List.tabulate(n - 1, (fn i => "v"^(Int.toString i)^" "))) ^
    "v" ^ (Int.toString (n - 1)))];

val PAT_TAC =
  MAP_EVERY (fn n => PAT_ABBREV_TAC (mk_pat "z" n 17) \\ POP_LAST_TAC)
   ["ointstart'","obaselatch'","onfq'","ooonfq'","oniq'","oooniq'",
    "pipeaabt'","pipebabt'","iregabt'","dataabt'"];

(* ------------------------------------------------------------------------- *)

val _ = print "*\nVerifying output: mul\n*\n"; (*============================*)

val MEM_MLA_MUL = Count.apply prove(
  `!t x. Abbrev (x = ^arm6state_inp) /\
         Abbrev (x0 = SINIT INIT_ARM6 x) /\
         (DECODE_INST ireg = mla_mul) /\ (aregn2 = 2w) /\
         CONDITION_PASSED (NZCV (CPSR_READ psr)) ireg ==>
         ~FST (DUR_X x0) ==> (!t. t < DUR_ARM6 x0 ==>
         ~IS_MEMOP (OUT_ARM6 ((FUNPOW (SNEXT NEXT_ARM6) t x0).state)))`,
  REWRITE_TAC [markerTheory.Abbrev_def] \\ NTAC 2 STRIP_TAC
    \\ ABBREV_TAC `pc = REG_READ6 reg usr 15w`
    \\ ABBREV_TAC `cpsr = CPSR_READ psr`
    \\ ABBREV_TAC `nbs = DECODE_MODE ((4 >< 0) cpsr)`
    \\ ABBREV_TAC `w = MLA_MUL_DUR (REG_READ6 reg nbs ((11 >< 8) ireg))`
    \\ ASM_SIMP_TAC (stdi_ss++STATE_INP_ss) [DUR_X2,DUR_ARM6_def,DUR_IC_def,
         INIT_ARM6,SINIT_def]
    \\ STRIP_TAC
    \\ RULE_ASSUM_TAC (ONCE_REWRITE_RULE [ADD_COMM])
    \\ `~IS_RESET inp 0` by ASM_SIMP_TAC arith_ss []
    \\ IMP_RES_TAC NOT_RESET_EXISTS
    \\ STRIP_TAC
    \\ Cases_on `t`
    >> SIMP_TAC (std_ss++STATE_INP_ss) [FUNPOW,OUT_ARM6_def,IS_MEMOP_def]
    \\ STRIP_TAC
    \\ POP_ASSUM (fn th => ASSUME_TAC
         (MATCH_MP (DECIDE ``!a b. SUC a < 1 + b ==> a <= b``) th))
    \\ ASM_SIMP_TAC bool_ss [SNEXT,FUNPOW]
    \\ MLA_MUL_TAC
    \\ ASM_SIMP_TAC (stdi_ss++ARITH_ss++PBETA_ss) [MULT_ALU6_ZERO,LSL_ZERO,
         w2w_0,WORD_MULT_CLAUSES,WORD_ADD_0,REGVAL_lem]
    \\ REWRITE_TAC [IF_NEG,DECIDE ``~a /\ ~b = ~(a \/ b)``]
    \\ SIMP_TAC std_ss []
    \\ RES_MP_TAC [`i` |-> `inp`] MLA_MUL_INVARIANT
    \\ POP_ASSUM (STRIP_ASSUME_TAC o
         (CONV_RULE (TOP_DEPTH_CONV (CHANGED_CONV (SKOLEM_CONV)))))
    \\ ASM_SIMP_TAC (std_ss++STATE_INP_ss) [OUT_ARM6_def,IS_MEMOP_def]);

val _ = print "*\nVerifying time-consistency and correctess: mul\n*\n"; (* * *)

val MLA_MUL = Count.apply prove(
  `!x. Abbrev (x = ^arm6state_inp) /\ inp IN STRM_ARM6 /\
       Abbrev (x0 = SINIT INIT_ARM6 x) /\
       (DECODE_INST ireg = mla_mul) /\ (aregn2 = 2w) /\
       CONDITION_PASSED (NZCV (CPSR_READ psr)) ireg ==>
       ~FST (DUR_X x0) ==>
       (let s = (FUNPOW (SNEXT NEXT_ARM6) (DUR_ARM6 x0) x0).state in
          (INIT_ARM6 s = s) /\
          (STATE_ARM 1 <|state := ABS_ARM6 x.state; inp := SMPL_ARM6 x|> =
           ABS_ARM6 s))`,
  NTAC 2 STRIP_TAC \\ FULL_SIMP_TAC stdi_ss [DUR_ARM6_def]
    \\ ABBREV_TAC `pc = REG_READ6 reg usr 15w`
    \\ ABBREV_TAC `cpsr = CPSR_READ psr`
    \\ ABBREV_TAC `nbs = DECODE_MODE ((4 >< 0) cpsr)`
    \\ ABBREV_TAC `w = MLA_MUL_DUR (REG_READ6 reg nbs ((11 >< 8) ireg))`
    \\ `(x.inp = inp) /\ (x.state = ^arm6state) /\
        (<|state := x0.state; inp := inp|> = x0)`
    by SIMP_TAC (std_ss++STATE_INP_ss) [Abbr`x`,Abbr`x0`,SINIT_def]
    \\ ASM_SIMP_TAC (srw_ss()++boolSimps.LET_ss++SIZES_ss) [num2exception_thm,
         SUC2NUM STATE_ARM_def,ABS_ARM6_def,SMPL_ARM6_def,PACK_def,IMM_LEN_def,
         SUC2NUM IMM_ARM6_def,MAP_STRM_def,COMBINE_def,SMPL_EXC_ARM6_def,
         SMPL_DATA_ARM6_def,IFLAGS_def,STATE_ARM6_COR,FUNPOW,ADVANCE_ZERO,
         DECODE_PSR_def]
    \\ POP_LASTN_TAC 3
    \\ STRIP_TAC
    \\ `(!t. t < w + 1 ==> ~IS_RESET inp t) /\ (SND (DUR_X x0) = SUC w)`
    by LT_RESET_TAC
    \\ ASM_SIMP_TAC std_ss [DUR_ARM6_def,FUNPOW]
    \\ ABBREV_TAC `s = SNEXT NEXT_ARM6 x0` \\ POP_ASSUM MP_TAC
    \\ `~IS_RESET inp 0` by ASM_SIMP_TAC arith_ss []
    \\ IMP_RES_TAC NOT_RESET_EXISTS
    \\ ASM_SIMP_TAC (stdi_ss++STATE_INP_ss)
         [Abbr`x0`,Abbr`x`,SNEXT,SINIT_def,INIT_ARM6_def]
    \\ MLA_MUL_TAC
    \\ ASM_SIMP_TAC (arith_ss++ICLASS_ss++PBETA_ss)
         [FST_COND_RAND,SND_COND_RAND,IF_NEG,LSL_ZERO,MULT_ALU6_ZERO,REGVAL_lem,
          TO_WRITE_READ6,w2w_0, WORD_MULT_CLAUSES,WORD_ADD_0]
    \\ REWRITE_TAC [GSYM DE_MORGAN_THM,IF_NEG]
    \\ STRIP_TAC \\ UNABBREV_TAC `s`
    \\ PAT_ABBREV_TAC `s = FUNPOW (SNEXT NEXT_ARM6) w q`
    \\ POP_ASSUM MP_TAC
    \\ RES_MP_TAC [`i` |-> `inp`] MLA_MUL_TN
    \\ POP_ASSUM (STRIP_ASSUME_TAC o
         (CONV_RULE (TOP_DEPTH_CONV (CHANGED_CONV (SKOLEM_CONV)))))
    \\ ASM_SIMP_TAC (arith_ss++STATE_INP_ss) []
    \\ POP_ASSUM (ASSUME_TAC o GEN_ALL o
         (MATCH_MP (DECIDE ``a /\ b /\ c /\ d ==> a /\ b /\ c``)) o SPEC_ALL)
    \\ STRIP_TAC \\ UNABBREV_TAC `s` \\ CONJ_TAC
    << [
      RULE_ASSUM_TAC (SIMP_RULE (std_ss++PRED_SET_ss) [])
        \\ RW_TAC std_ss finish_rws
        \\ METIS_TAC [],
      ASM_SIMP_TAC (std_ss++STATE_INP_ss) [ABS_ARM6_def]
        \\ PAT_ABBREV_TAC (mk_pat "aregn" "aregn'" 17)
        \\ `~(aregn IN {0w; 1w; 2w; 5w}) /\
              ((aregn = 7w) ==> ~(cpsr %% 6)) /\
              ((aregn = 6w) ==> ~(cpsr %% 7))`
        by METIS_TAC []
        \\ ASM_SIMP_TAC (stdi_ss++STATE_INP_ss) ([Abbr`cpsr`,ALU_multiply_def,
             MLA_MUL_CARRY_def,MSHIFT_def,SET_NZC_def] @ finish_rws3)
        \\ RW_TAC std_ss ([Abbr`pc`,WORD_ADD_0,CARRY_LEM] @ finish_rws2)
        \\ FULL_SIMP_TAC std_ss []]);

(* ------------------------------------------------------------------------- *)

val ALU_ABBREV_TAC = with_flag (priming,SOME "")
  (PAT_ABBREV_TAC `alu = ALU6 ic is xireg xborrow2 xmul xdataabt xalua xalub xc`);

val PSR_ABBREV_TAC = with_flag (priming,SOME "")
  (PAT_ABBREV_TAC `psr = xpsr:psr`);

val lem = prove(
  `!ic. ic IN {cdp_und; mrc; mcr; stc; ldc} ==>
      ((ic = cdp_und) \/ ic IN {mcr; mrc; ldc; stc} /\ b /\ c =
       (ic = cdp_und) \/  b /\ c)`,
  RW_TAC (std_ss++PRED_SET_ss) []);

val lem2 = prove(
  `!ic w a x y z. ic IN {cdp_und; mrc; mcr; stc; ldc} /\
      ~(ic IN {stc; ldc}) ==>
      ((if (ic = cdp_und) \/ a then (w:num)
        else if ic = mcr then w + x
        else if ic = mrc then w + y
        else z) =
      (if (ic = cdp_und) \/ a then 0
       else if ic = mcr then x else y) + w)`,
  RW_TAC (arith_ss++PRED_SET_ss) []);

val LT_RESET_TAC = POP_ASSUM MP_TAC
  \\ ASM_SIMP_TAC (std_ss++STATE_INP_ss++boolSimps.LIFT_COND_ss)
         [Abbr`w`,Abbr`x`,Abbr`x0`,SINIT_def,INIT_ARM6,DUR_X2]
  \\ ASM_SIMP_TAC std_ss [CP_NOT,CP_NOT2,STC_LDC_NOT,DUR_IC];

val lem3 = prove(
  `(!inp w. inp IN STRM_ARM6 /\ (!t. t < 1 + w ==> ~IS_RESET inp t) ==>
      ?ABORT NFQ NIQ DATA CPA CPB.
         (inp w = (T,ABORT,NFQ,NIQ,DATA,CPA,CPB)) /\ (CPA ==> CPB)) /\
   (!inp w. inp IN STRM_ARM6 /\ (!t. t < 2 + w ==> ~IS_RESET inp t) ==>
      (?ABORT NFQ NIQ DATA CPA CPB.
         (inp w = (T,ABORT,NFQ,NIQ,DATA,CPA,CPB)) /\ (CPA ==> CPB)) /\
      (?ABORT NFQ NIQ DATA CPA CPB.
         (inp (w + 1) = (T,ABORT,NFQ,NIQ,DATA,CPA,CPB)) /\ (CPA ==> CPB)))`,
  RW_TAC std_ss [IN_DEF,STRM_ARM6_def,IS_RESET_def,IS_ABSENT_def,IS_BUSY_def]
    \\ PAT_ASSUM `!t. PROJ_CPA (inp t) ==> PROJ_CPB (inp t)`
           (fn th => ASSUME_TAC (SPEC `w` th) \\ ASSUME_TAC (SPEC `w + 1` th))
    \\ `w < 1 + w /\ w < 2 + w /\ w + 1 < 2 + w` by DECIDE_TAC \\ RES_TAC
    \\ Cases_on_arm6inp `inp (w:num)`
    \\ Cases_on_arm6inp `inp (w + 1)`
    \\ FULL_SIMP_TAC std_ss [PROJ_NRESET_def,PROJ_CPA_def,PROJ_CPB_def]);

val _ = print "*\nVerifying output: cdp_und, mrc\n*\n"; (*===================*)

val CP_MEMOPS = Count.apply prove(
  `!x y. Abbrev (x = ^arm6state_inp) /\ inp IN STRM_ARM6 /\
         Abbrev (x0 = SINIT INIT_ARM6 x) /\
         (DECODE_INST ireg IN {cdp_und; mrc}) /\ (aregn2 = 2w) /\
         CONDITION_PASSED (NZCV (CPSR_READ psr)) ireg ==>
         ~FST (DUR_X x0) ==> (!t. t < DUR_ARM6 x0 ==>
         ~IS_MEMOP (OUT_ARM6 ((FUNPOW (SNEXT NEXT_ARM6) t x0).state)))`,
  NTAC 3 STRIP_TAC \\ FULL_SIMP_TAC stdi_ss [DUR_ARM6_def,FILTER_MOVE_DOUT]
    \\ ABBREV_TAC `i = CPSR_READ psr %% 7`
    \\ ABBREV_TAC `f = CPSR_READ psr %% 6`
    \\ ABBREV_TAC `nbs = DECODE_MODE ((4 >< 0) (CPSR_READ psr))`
    \\ ABBREV_TAC `b = BUSY_WAIT (onfq,ooonfq,oniq,oooniq,f,i,pipebabt) inp`
    \\ ABBREV_TAC `w = 1 + b`
    \\ STRIP_TAC
    \\ `!t. t < w ==> ~IS_RESET inp t` by (LT_RESET_TAC \\ RW_TAC arith_ss [])
    \\ RES_MP1_TAC [] COPROC_BUSY_WAIT >> METIS_TAC [CP_NOT2]
    \\ RES_MP1_TAC [] COPROC_BUSY_WAIT2 >> (POP_LAST_TAC \\ METIS_TAC [CP_NOT2])
    \\ PAT_ASSUM `~FST (DUR_X x0)` MP_TAC
    \\ FULL_SIMP_TAC (std_ss++STATE_INP_ss) [Abbr`x`,SINIT_def,INIT_ARM6]
    \\ UNABBREV_TAC `x0` \\ ASM_SIMP_TAC stdi_ss [DUR_X2]
    \\ PAT_ABBREV_TAC `d = DUR_IC ic ireg rs iflags inp` \\ POP_ASSUM MP_TAC
    \\ ASM_SIMP_TAC stdi_ss [CP_NOT,CP_NOT2,DUR_IC]
    \\ STRIP_TAC \\ UNABBREV_TAC `d`
    \\ COND_CASES_TAC \\ ASM_SIMP_TAC std_ss [ADD,GSYM IMP_DISJ_THM]
    \\ NTAC 2 STRIP_TAC
    << [
      PAT_ASSUM `!t. t < w ==> P` IMP_RES_TAC
        \\ POP_ASSUM SUBST1_TAC
        \\ ASM_SIMP_TAC (std_ss++STATE_INP_ss++PRED_SET_ss)
               [OUT_ARM6_def,IS_MEMOP_def,CP_NOT2],
      STRIP_TAC
        \\ `t < w \/ ((t = w) \/ (t = 1 + w))` by DECIDE_TAC
        << [
          PAT_ASSUM `!t. t < w ==> P` IMP_RES_TAC
            \\ POP_ASSUM SUBST1_TAC
            \\ ASM_SIMP_TAC (std_ss++STATE_INP_ss++PRED_SET_ss)
                 [OUT_ARM6_def,IS_MEMOP_def,CP_NOT2],
          ASM_SIMP_TAC (std_ss++STATE_INP_ss++PRED_SET_ss)
            [OUT_ARM6_def,IS_MEMOP_def,CP_NOT2],
          IMP_RES_TAC lem3 \\ POP_LASTN_TAC 6
            \\ ASM_SIMP_TAC (std_ss++PRED_SET_ss) [FUNPOW_COMP,CP_NOT2]
            \\ FULL_SIMP_TAC std_ss [IS_BUSY_def,CP_NOT3]
            \\ ASM_SIMP_TAC (bossLib.std_ss++STATE_INP_ss)
                 [SNEXT_def,ADVANCE_def,numeral_funpow,ADD_0]
            \\ ASM_SIMP_TAC (stdi_ss++MRC_ss++PBETA_ss)
                 [SND_COND_RAND,FST_COND_RAND,OUT_ARM6_def,IS_MEMOP_def]]]);

val ELL_1_TL_GENLIST = prove(
  `!inp w. 0 < w ==>
     (ELL 1 (TL (GENLIST (\s. PROJ_DATA (inp s)) (2 + w))) =
      PROJ_DATA (inp w))`,
  RW_TAC list_ss [DECIDE ``2 + w = SUC (SUC w)``,GENLIST,TL_SNOC,
         NULL_SNOC,SUC2NUM ELL,LAST,BUTLAST]
    \\ METIS_TAC [LENGTH_NOT_NULL,LENGTH_GENLIST]);

val ALU2_ss = rewrites
  [GSYM ONE_COMP_THREE_ADD,LSL_ZERO,LSL_TWO,
   ALUOUT_ALU_logic,ALUOUT_ADD,ALUOUT_SUB];

val _ = print "*\nVerifying time-consistency \
              \and correctness: cdp_und, mrc, mcr, stc, ldc\n*\n"; (*========*)

val CP_TC = Count.apply prove(
  `!x. Abbrev (x = ^arm6state_inp) /\ inp IN STRM_ARM6 /\
       Abbrev (x0 = SINIT INIT_ARM6 x) /\
       (DECODE_INST ireg IN {cdp_und; mrc; mcr; stc; ldc}) /\ (aregn2 = 2w) /\
       CONDITION_PASSED (NZCV (CPSR_READ psr)) ireg ==>
       ~FST (DUR_X x0) ==>
       (let s = (FUNPOW (SNEXT NEXT_ARM6) (DUR_ARM6 x0) x0).state in
          (INIT_ARM6 s = s) /\
          (STATE_ARM 1 <|state := ABS_ARM6 x.state; inp := SMPL_ARM6 x|> =
           ABS_ARM6 s))`,
  NTAC 2 STRIP_TAC \\ FULL_SIMP_TAC stdi_ss [DUR_ARM6_def]
    \\ ABBREV_TAC `i = CPSR_READ psr %% 7`
    \\ ABBREV_TAC `f = CPSR_READ psr %% 6`
    \\ ABBREV_TAC `nbs = DECODE_MODE ((4 >< 0) (CPSR_READ psr))`
    \\ ABBREV_TAC `b = BUSY_WAIT (onfq,ooonfq,oniq,oooniq,f,i,pipebabt) inp`
    \\ `(x.inp = inp) /\ (x.state = ^arm6state) /\
        (<|state := x0.state; inp := inp|> = x0) /\
        (IFLAGS x0.state = (onfq,ooonfq,oniq,oooniq,f,i,pipebabt))`
    by ASM_SIMP_TAC (srw_ss()++boolSimps.LET_ss++STATE_INP_ss)
         [Abbr`x`,Abbr`x0`,SINIT_def,IFLAGS_def,INIT_ARM6_def,DECODE_PSR_def]
    \\ ASM_SIMP_TAC (srw_ss()++boolSimps.LET_ss++SIZES_ss) [num2exception_thm,
         SUC2NUM STATE_ARM_def,ABS_ARM6_def,SMPL_ARM6_def,PACK_def,IMM_LEN_def,
         SUC2NUM IMM_ARM6_def,MAP_STRM_def,COMBINE_def,SMPL_EXC_ARM6_def,
         SMPL_DATA_ARM6_def,STATE_ARM6_COR,FUNPOW,ADVANCE_ZERO,DECODE_PSR_def]
    \\ POP_LASTN_TAC 3
    \\ Cases_on `DECODE_INST ireg IN {stc; ldc} /\ ~IS_BUSY inp b`
    << [
      ABBREV_TAC `w = 1 + b + LEAST n. IS_BUSY (ADVANCE b inp) n`
        \\ STRIP_TAC
        \\ `(!t. t < w ==> ~IS_RESET inp t) /\ (SND (DUR_X x0) = w)`
        by (LT_RESET_TAC \\ PROVE_TAC [])
        \\ RES_MP_TAC [] LDC_STC_THM2
        \\ ASM_SIMP_TAC (std_ss++STATE_INP_ss) [DUR_ARM6_def]
        \\ CONJ_TAC
        << [
          FINISH_OFF \\ FULL_SIMP_TAC (std_ss++PRED_SET_ss++SIZES_ss) [n2w_11],
          POP_LAST_TAC \\ ASM_SIMP_TAC stdi_ss finish_rws3
            \\ RW_TAC (std_ss++SIZES_ss)
                 ([UP_DOWN_def,w2w_extract] @ finish_rws2)
        ],
      ABBREV_TAC `w = 1 + b` \\ STRIP_TAC
        \\ `!t. t < w ==> ~IS_RESET inp t`
        by (LT_RESET_TAC \\ RW_TAC arith_ss [] \\
              FULL_SIMP_TAC (std_ss++PRED_SET_ss) [])
        \\ PAT_ASSUM `~FST (DUR_X x0)` MP_TAC
        \\ RES_MP_TAC [] COPROC_BUSY_WAIT2
        \\ FULL_SIMP_TAC (std_ss++STATE_INP_ss)
             [Abbr`x`,SINIT_def,INIT_ARM6,DUR_ARM6_def]
        \\ UNABBREV_TAC `x0` \\ ASM_SIMP_TAC stdi_ss [DUR_X2]
        \\ PAT_ABBREV_TAC `d = DUR_IC ic ireg rs iflags inp`
        \\ POP_ASSUM MP_TAC
        \\ ASM_SIMP_TAC stdi_ss [CP_NOT,DUR_IC,STC_LDC_NOT,lem]
        << [
          ASM_SIMP_TAC std_ss [lem2]
            \\ STRIP_TAC \\ UNABBREV_TAC `d`
            \\ ASM_SIMP_TAC std_ss [FUNPOW_COMP,IS_BUSY_def]
            \\ PAT_ASSUM `FUNPOW z w q = r` (K ALL_TAC)
            \\ Cases_on `(DECODE_INST ireg = cdp_und) \/ PROJ_CPB (inp b) /\
                  CP_INTERRUPT (onfq,ooonfq,oniq,oooniq,f,i,pipebabt) inp b`
            \\ ASM_SIMP_TAC (std_ss++STATE_INP_ss) [FUNPOW]
            << [
              POP_ASSUM (fn th => ASSUME_TAC th \\ ASSUME_TAC
                (MATCH_MP (DECIDE ``!a b c. a \/ b /\ c ==>
                                        (~a /\ (~b \/ ~c) = F)``) th))
                \\ POP_ASSUM SUBST1_TAC
                \\ STRIP_TAC
                << [
                  POP_LASTN_TAC 2 \\ FINISH_OFF \\ POP_ASSUM MP_TAC
                    \\ FULL_SIMP_TAC (std_ss++PRED_SET_ss++SIZES_ss) [n2w_11],
                  FULL_SIMP_TAC std_ss [] \\ ASM_SIMP_TAC stdi_ss finish_rws3
                    \\ RW_TAC std_ss finish_rws2
                ],
              STRIP_TAC
                \\ PAT_ABBREV_TAC `s = FUNPOW fx nx
                       (xx: (state_arm6, bool # bool # bool # bool #
                               word32 # bool # bool) state_inp)`
                \\ NTAC 2 (POP_ASSUM MP_TAC)
                \\ POP_ASSUM (ASSUME_TAC o SIMP_RULE std_ss [])
                \\ ASM_SIMP_TAC std_ss []
                \\ Cases_on `DECODE_INST ireg = mcr`
                \\ ASM_SIMP_TAC std_ss []
                \\ STRIP_TAC \\ IMP_RES_TAC lem3
                \\ POP_LASTN_TAC 4
                << (let
                  val tac = ASM_SIMP_TAC (bossLib.std_ss++STATE_INP_ss)
                         [SNEXT_def,ADVANCE_def,numeral_funpow,ADD_0]
                    \\ ASM_SIMP_TAC (stdi_ss++MCR_ss++MRC_ss++PBETA_ss)
                         [SND_COND_RAND,FST_COND_RAND,IF_NEG,REGVAL_lem]
                    \\ STRIP_TAC \\ UNABBREV_TAC `s`
                    \\ CONJ_TAC
                  val tac2 = ASM_SIMP_TAC (std_ss++STATE_INP_ss)
                               ([state_arm6_11,dp_11,ctrl_11] @ finish_rws)
                    \\ ASM_SIMP_TAC (std_ss++boolSimps.CONJ_ss)
                         [AC DISJ_ASSOC DISJ_COMM,MASK_MASK]
                in [ (* MCR *) tac >> tac2
                    \\ SIMP_TAC (std_ss++STATE_INP_ss) []
                    \\ ASM_SIMP_TAC stdi_ss finish_rws3
                    \\ RW_TAC std_ss finish_rws2,
                   (* MRC *)
                  `(DECODE_INST ireg = mrc) /\ 0 < w`
                    by FULL_SIMP_TAC (arith_ss++PRED_SET_ss) [Abbr`w`]
                    \\ tac >> (tac2 \\  FINISH_OFF)
                    \\ `~PROJ_CPB (inp b)`
                    by (IMP_RES_TAC EXISTS_BUSY_WAIT_IMP_BUSY_WAIT_DONE \\
                         FULL_SIMP_TAC stdi_ss [BUSY_WAIT_DONE_def,IS_BUSY_def]
                           \\ METIS_TAC [])
                    \\ IMP_RES_TAC ELL_1_TL_GENLIST
                    \\ ASM_SIMP_TAC (stdi_ss++STATE_INP_ss++ALU_ss++ALU2_ss)
                         finish_rws3
                    \\ RW_TAC std_ss finish_rws2
                ] end)
            ], (* BUSY ==> INTERRUPT *)
          `CP_INTERRUPT (onfq,ooonfq,oniq,oooniq,f,i,pipebabt) inp b`
            by (POP_LAST_TAC \\ IMP_RES_TAC EXISTS_BUSY_WAIT_IMP_BUSY_WAIT_DONE
                  \\ METIS_TAC [BUSY_WAIT_DONE_def])
            \\ ASM_SIMP_TAC std_ss []
            \\ STRIP_TAC \\ UNABBREV_TAC `d`
            \\ ASM_SIMP_TAC (std_ss++STATE_INP_ss) []
            \\ PAT_ASSUM `FUNPOW z w q = r` (K ALL_TAC)
            \\ CONJ_TAC
            << [
              FULL_SIMP_TAC std_ss [IS_BUSY_def] \\ FINISH_OFF
                \\ FULL_SIMP_TAC (std_ss++PRED_SET_ss++SIZES_ss) [n2w_11],
              ASM_SIMP_TAC stdi_ss finish_rws3
                \\ FULL_SIMP_TAC std_ss [IS_BUSY_def]]]]);

(* ------------------------------------------------------------------------- *)

val RESET_THM = prove(
  `!x i. (!t. t < SUC x ==> ~IS_RESET i t) =
         (if x = 0 then ~IS_RESET i x
          else (!t. t < x ==> ~IS_RESET i t) /\ ~IS_RESET i x)`,
  REPEAT STRIP_TAC \\ EQ_TAC \\ RW_TAC arith_ss []
    \\ FULL_SIMP_TAC arith_ss [DECIDE ``t < 1 ==> (t = 0)``]
    \\ Cases_on `t = x` \\ FULL_SIMP_TAC arith_ss []);

(*
val CONCAT_MSR =
  (SIMP_RULE std_ss [WORD_SLICE_ZERO_THM,WORD_BITS_HB_0] o
   SIMP_RULE arith_ss [WORD_SLICE_COMP_RWT,GSYM WORD_SLICE_ZERO_THM] o
   SPECL [`a`,`a`] o CONJUNCT1) CONCAT_MSR_THM;
*)

val CPSR_WRITE_READ_COND = GEN_ALL(prove(
  `CPSR_READ
     (if a then
        CPSR_WRITE psr
          (if USER nbs then CPSR_READ psr else SPSR_READ psr nbs)
      else
        psr) =
   CPSR_READ (if a then CPSR_WRITE psr (SPSR_READ psr nbs) else psr)`,
  RW_TAC std_ss [SPSR_READ_THM2]
));

val CPSR_WRITE_READ_COND2 = GEN_ALL(prove(
  `(n = 7) \/ (n = 6) ==>
   (CPSR_READ
     (if a then
        CPSR_WRITE psr
          (if b then SET_NZCV c (CPSR_READ psr) else SET_NZCV d (CPSR_READ psr))
      else
        psr) %% n =
    CPSR_READ psr %% n)`,
  RW_TAC std_ss [CPSR_WRITE_READ] \\ SIMP_TAC std_ss [DECODE_IFMODE_SET_NZCV]));

val _ = print "*\nVerifying: mrs_msr, data_proc, \
               \reg_shift, br, swi_ex, unexec\n*\n"; (*======================*)

val NON_MEMOPS = Count.apply prove(
  `!x y.
   Abbrev (x = ^arm6state_inp) /\
   Abbrev (x0 = SINIT INIT_ARM6 x) /\
   (DECODE_INST ireg IN {mrs_msr; data_proc; reg_shift; br; swi_ex; unexec}) /\
   (aregn2 = 2w) /\ CONDITION_PASSED (NZCV (CPSR_READ psr)) ireg ==>
   ~FST (DUR_X x0) ==>
   (let s = (FUNPOW (SNEXT NEXT_ARM6) (DUR_ARM6 x0) x0).state in
      (INIT_ARM6 s = s) /\
      (STATE_ARM 1 <|state := ABS_ARM6 x.state; inp := SMPL_ARM6 x|> =
       ABS_ARM6 s)) /\
      (FILTER IS_MEMOP (MOVE_DOUT y
         (GENLIST (\t. OUT_ARM6 ((FUNPOW (SNEXT NEXT_ARM6) t x0).state))
            (DUR_ARM6 x0))) = [])`,
  NTAC 3 STRIP_TAC
    \\ ABBREV_TAC `nbs = DECODE_MODE ((4 >< 0) (CPSR_READ psr))`
    \\ ASM_SIMP_TAC (srw_ss()++boolSimps.LET_ss++SIZES_ss) [num2exception_thm,
         Abbr`x`,DUR_ARM6_def,FILTER_MOVE_DOUT,SUC2NUM STATE_ARM_def,
         ABS_ARM6_def,SMPL_ARM6_def,SMPL_DATA_ARM6_def,IFLAGS_def,ADVANCE_ZERO,
         DECODE_PSR_def,PACK_def,IMM_LEN_def,SUC2NUM IMM_ARM6_def,MAP_STRM_def,
         COMBINE_def,SMPL_EXC_ARM6_def,STATE_ARM6_COR,FUNPOW]
    \\ FULL_SIMP_TAC (std_ss++STATE_INP_ss++PRED_SET_ss)
         [SINIT_def,DECODE_INST_NOT_UNEXEC,INIT_ARM6]
    \\ ASM_SIMP_TAC (stdi_ss++STATE_INP_ss) [Abbr`x0`,DUR_X2]
    \\ PAT_ABBREV_TAC `d = DUR_IC ic ireg rs iflags inp` \\ POP_ASSUM MP_TAC
    \\ ASM_SIMP_TAC stdi_ss [DUR_IC] \\ STRIP_TAC \\ UNABBREV_TAC `d`
    \\ TRY COND_CASES_TAC \\ SIMP_TAC std_ss [SUC2NUM RESET_THM]
    \\ STRIP_TAC \\ IMP_RES_TAC NOT_RESET_EXISTS
    \\ ASM_SIMP_TAC (bossLib.std_ss++STATE_INP_ss)
         [OUT_ARM6_def,IS_MEMOP2,IS_MEMOP2_def,LET_FILTER,SNOC,GENLISTn,
          SNEXT_def,ADVANCE_def,PROJ_DATA_def,TL,numeral_funpow]
    \\ REPEAT (PAT_ABBREV_TAC `s = NEXT_ARM6 a b`)
    \\ RULE_ASSUM_TAC (REWRITE_RULE [DECIDE ``~(a /\ b) = ~a \/ ~b``])
    \\ REPEAT (PAT_ASSUM `Abbrev (q = NEXT_ARM6 (ARM6 dp ctrl) inp)` MP_TAC
           \\ ASM_SIMP_TAC (booli_ss++pairSimps.PAIR_ss++MRS_MSR_ss++BR_ss++
                  DATA_PROC_ss++REG_SHIFT_ss++SWI_EX_ss++UNEXEC_ss++PBETA_ss)
                [SND_COND_RAND,FST_COND_RAND,REGVAL_lem2,WORD_NEQS]
           \\ TRY ALU_ABBREV_TAC \\ TRY PSR_ABBREV_TAC
           \\ ASM_SIMP_TAC bossLib.old_arith_ss [markerTheory.Abbrev_def,LEM]
           \\ DISCH_THEN SUBST_ALL_TAC
           \\ SIMP_TAC (bossLib.std_ss++STATE_INP_ss)
                [OUT_ARM6_def,IS_MEMOP2_def])
    \\ ASM_SIMP_TAC (stdi_ss++UNEXEC_ss++SWI_EX_ss) []
    \\ (CONJ_TAC >> FINISH_OFF
    \\ RULE_ASSUM_TAC (SIMP_RULE (stdi_ss++PBETA_ss++ALU_ss++ALU2_ss)
         [GSYM IMMEDIATE_THM,IMMEDIATE_THM2])
    \\ TRY (UNABBREV_TAC `psr1`) \\ TRY (UNABBREV_TAC `psr2`)
    \\ FULL_SIMP_TAC (stdi_ss++STATE_INP_ss)
         ([CPSR_WRITE_READ_COND,CPSR_WRITE_READ_COND2,PSR_WRITE_COMM,
           DECODE_MODE_mode_num,DECODE_IFMODE_SET_IFMODE,
           exception_distinct,state_arm_ex_11] @ finish_rws3)
    \\ TRY (UNABBREV_TAC `alu`) \\ TRY (UNABBREV_TAC `alu1`)
    \\ TRY (UNABBREV_TAC `alu2`)
    \\ RW_TAC (stdi_ss++ALU2_ss) ([SET_NZC_def,SPSR_READ_WRITE,CONCAT_MSR,
         SHIFT_IMMEDIATE_THM2,IMMEDIATE_THM2,SHIFT_REGISTER_THM2,
         SOFTWARE_ADDRESS] @ finish_rws2)
    \\ NTAC 2 (FULL_SIMP_TAC std_ss [])
    \\ TRY (METIS_TAC [DATA_PROC_IMP_NOT_BIT4,REG_SHIFT_IMP_BITS])));

(* ------------------------------------------------------------------------- *)

val _ = print "*\nVerifying: exception entry, unexecuted\n*\n"; (*===========*)

val NON_MEMOPS_UNEXEC = Count.apply prove(
  `!x y. Abbrev (x = ^arm6state_inp) /\
         Abbrev (x0 = SINIT INIT_ARM6 x) /\
         ((aregn2 = 2w) ==>
            ~CONDITION_PASSED (NZCV (CPSR_READ psr)) ireg) ==>
         ~FST (DUR_X x0) ==>
         (let s = (FUNPOW (SNEXT NEXT_ARM6) (DUR_ARM6 x0) x0).state in
            (INIT_ARM6 s = s) /\
            (STATE_ARM 1 <|state := ABS_ARM6 x.state; inp := SMPL_ARM6 x|> =
             ABS_ARM6 s)) /\
         (FILTER IS_MEMOP (MOVE_DOUT y
            (GENLIST (\t. OUT_ARM6 ((FUNPOW (SNEXT NEXT_ARM6) t x0).state))
               (DUR_ARM6 x0))) = [])`,
  NTAC 3 STRIP_TAC
    \\ FULL_SIMP_TAC (srw_ss()++boolSimps.LET_ss++PRED_SET_ss++SIZES_ss)
         [num2exception_thm,Abbr`x`,Abbr`x0`,SUC2NUM STATE_ARM_def,ABS_ARM6_def,
          SMPL_ARM6_def,SMPL_DATA_ARM6_def,IFLAGS_def,ADVANCE_ZERO,
          DECODE_PSR_def,PACK_def,IMM_LEN_def,SUC2NUM IMM_ARM6_def,MAP_STRM_def,
          SMPL_EXC_ARM6_def,IC_def,ABORTINST_def,NXTIC_def,DUR_X,DUR_ARM6_def,
          DUR_IC,FILTER_MOVE_DOUT,IFLAGS_def,SINIT_def,SUC2NUM RESET_THM,
          DECIDE ``!x y b. (x = y) ==> b = ~(x = y) \/ (x = y) /\ b``,
          INIT_ARM6_def,num2exception_exception2num,COMBINE_def,
          FST_COND_RAND,SND_COND_RAND,STATE_ARM6_COR,FUNPOW]
    \\ STRIP_TAC
    \\ ASM_SIMP_TAC (bossLib.std_ss++STATE_INP_ss)
         [OUT_ARM6_def,IS_MEMOP2,IS_MEMOP2_def,LET_FILTER,SNOC,GENLISTn,
          SNEXT_def,ADVANCE_def,numeral_funpow]
    \\ REPEAT (PAT_ABBREV_TAC `s = NEXT_ARM6 a b`)
    \\ IMP_RES_TAC NOT_RESET_EXISTS
    \\ REPEAT (PAT_ASSUM `Abbrev (q = NEXT_ARM6 (ARM6 dp ctrl) inp)` MP_TAC
         \\ ASM_SIMP_TAC (booli_ss++SWI_EX_ss++UNEXEC_ss++pairSimps.PAIR_ss++
              PBETA_ss) [SND_COND_RAND,FST_COND_RAND,WORD_NEQS]
         \\ TRY ALU_ABBREV_TAC \\ TRY PSR_ABBREV_TAC \\ STRIP_TAC
         \\ POP_ASSUM (fn th => FULL_SIMP_TAC (bossLib.std_ss++STATE_INP_ss)
              [OUT_ARM6_def,IS_MEMOP2_def,
               REWRITE_RULE [markerTheory.Abbrev_def] th]))
    \\ SIMP_TAC (stdi_ss++SWI_EX_ss) []
    \\ (CONJ_TAC >> FINISH_OFF
    \\ RULE_ASSUM_TAC (SIMP_RULE (stdi_ss++ALU_ss) [])
    \\ TRY (UNABBREV_TAC `psr1` \\ UNABBREV_TAC `psr2`)
    \\ FULL_SIMP_TAC (stdi_ss++STATE_INP_ss)
           ([PSR_WRITE_COMM,DECODE_MODE_mode_num,num2exception_word3,
             DECODE_IFMODE_SET_IFMODE] @ finish_rws3)
    \\ TRY (UNABBREV_TAC `alu1` \\ UNABBREV_TAC `alu2`)
    \\ RW_TAC (stdi_ss++ALU2_ss) ([INTERRUPT_ADDRESS] @ finish_rws2)));

(* ------------------------------------------------------------------------- *)

val SINIT_ARM6 = (GSYM o SIMP_CONV std_ss [SINIT_def]) ``SINIT INIT_ARM6 x``;

val IS_SOME_COND = GEN_ALL(prove(
  `IS_SOME (if b then SOME a else NONE) = b`,
  RW_TAC (std_ss++optionSimps.OPTION_ss) []));

val _ = print "*\nVerifying: swp, ldr, str\n*\n"; (*=========================*)

val BASIC_MEMOPS = Count.apply prove(
  `!x. Abbrev (x = ^arm6state_inp) /\
       Abbrev (x0 = SINIT INIT_ARM6 x) /\
       (DECODE_INST ireg IN {swp; ldr; str}) /\ (aregn2 = 2w) /\
       CONDITION_PASSED (NZCV (CPSR_READ psr)) ireg ==>
       ~FST (DUR_X x0) ==>
       (let s = (FUNPOW (SNEXT NEXT_ARM6) (DUR_ARM6 x0) x0).state in
            (INIT_ARM6 s = s) /\
            (STATE_ARM 1 <|state := ABS_ARM6 x.state; inp := SMPL_ARM6 x|> =
             ABS_ARM6 s)) /\
       (OUT_ARM (ABS_ARM6 x.state) =
        OSMPL_ARM6 x0 (GENLIST
        (\t. OUT_ARM6 ((FUNPOW (SNEXT NEXT_ARM6) t x0).state)) (DUR_ARM6 x0)))`,
  NTAC 2 STRIP_TAC \\ IMP_RES_TAC INIT_INIT
    \\ ASM_SIMP_TAC (srw_ss()++boolSimps.LET_ss++SIZES_ss) [num2exception_thm,
         Abbr`x`,DUR_ARM6_def,SUC2NUM STATE_ARM_def,ABS_ARM6_def,SMPL_ARM6_def,
         SMPL_DATA_ARM6_def,IFLAGS_def,OSMPL_ARM6_def,ADVANCE_ZERO,
         DECODE_PSR_def,PACK_def,IMM_LEN_def,SUC2NUM IMM_ARM6_def,MAP_STRM_def,
         COMBINE_def,SMPL_EXC_ARM6_def,STATE_ARM6_COR,FUNPOW]
    \\ POP_LASTN_TAC 3
    \\ ABBREV_TAC `nbs = DECODE_MODE ((4 >< 0) (CPSR_READ psr))`
    \\ FULL_SIMP_TAC (stdi_ss++STATE_INP_ss++PRED_SET_ss)
         [SINIT_def,DECODE_INST_NOT_UNEXEC,INIT_ARM6]
    \\ ASM_SIMP_TAC (stdi_ss++STATE_INP_ss) [Abbr`x0`,DUR_X2]
    \\ PAT_ABBREV_TAC `d = DUR_IC ic ireg rs iflags inp` \\ POP_ASSUM MP_TAC
    \\ ASM_SIMP_TAC stdi_ss [DUR_IC] \\ STRIP_TAC \\ UNABBREV_TAC `d`
    \\ TRY COND_CASES_TAC \\ SIMP_TAC std_ss [SUC2NUM RESET_THM]
    \\ STRIP_TAC \\ IMP_RES_TAC NOT_RESET_EXISTS
    \\ ASM_SIMP_TAC (list_ss++STATE_INP_ss)
         [OUT_ARM6_def,IS_MEMOP2,IS_MEMOP2_def,LET_FILTER,SNOC,GENLISTn,
          PROJ_DATA_def,MOVE_DOUT_def,SNEXT_def,ADVANCE_def,numeral_funpow]
    \\ REPEAT (PAT_ABBREV_TAC `s = NEXT_ARM6 a b`)
    \\ FULL_SIMP_TAC bossLib.std_ss []
    \\ REPEAT (PAT_ASSUM `Abbrev (q = NEXT_ARM6 (ARM6 dp ctrl) inp)` MP_TAC
         \\ ASM_SIMP_TAC (booli_ss++pairSimps.PAIR_ss++SWP_ss++LDR_ss++
                STR_ss++ARITH_ss++UNEXEC_ss++PBETA_ss)
               [SND_COND_RAND,FST_COND_RAND]
         \\ TRY ALU_ABBREV_TAC
         \\ ASM_SIMP_TAC bossLib.old_arith_ss [markerTheory.Abbrev_def,LEM,LEM2]
         \\ DISCH_THEN SUBST_ALL_TAC
         \\ SIMP_TAC (bossLib.std_ss++STATE_INP_ss)
              [OUT_ARM6_def,IS_MEMOP2_def])
    \\ (CONJ_TAC
    << [
      CONJ_TAC >> (ASM_SIMP_TAC bossLib.std_ss [LEM] \\ FINISH_OFF)
        \\ RULE_ASSUM_TAC (SIMP_RULE (stdi_ss++ALU_ss++ALU2_ss) [])
        \\ FULL_SIMP_TAC (stdi_ss++STATE_INP_ss)
             ([IS_SOME_COND,HD,LDR_IMP_BITS,STR_IMP_BITS] @ finish_rws3)
        \\ TRY (UNABBREV_TAC `alu`) \\ TRY (UNABBREV_TAC `alu1`)
        \\ TRY (UNABBREV_TAC `alu2`) \\ TRY (UNABBREV_TAC `alu3`)
        \\ RW_TAC (stdi_ss++ALU2_ss++SIZES_ss) ([UP_DOWN_def,BW_READ_def,
             SLICE_ROR_THM,SHIFT_IMMEDIATE_THM2,IMMEDIATE_THM2,SND_ROR,
             SHIFT_ALIGN,w2w_extract] @ finish_rws2)
        \\ NTAC 2 (FULL_SIMP_TAC std_ss finish_rws2)
        \\ Cases_on `(19 >< 16) ireg = 15w:word4`
        \\ FULL_SIMP_TAC std_ss finish_rws2,
      TRY (UNABBREV_TAC `alu1`)
        \\ ASM_SIMP_TAC (stdi_ss++listSimps.LIST_ss++ALU_ss++ALU2_ss++SIZES_ss)
         ([Abbr`alu`,SWP_def,LDR_STR_def,DECODE_SWP_def,DECODE_LDR_STR_def,
           ADDR_MODE2_def,DECODE_PSR_def,OUT_ARM_def,MEMOP_def,SNOC,
           LDR_IMP_BITS,STR_IMP_BITS,IF_NEG,UP_DOWN_THM,SHIFT_IMMEDIATE_THM2,
           num2exception_word3,w2w_extract] @ finish_rws2)])
);

(* ------------------------------------------------------------------------- *)

val NOT_ABORT = METIS_PROVE []
   ``(!s. ~(s < SUC n) \/ ~IS_ABORT i (s + 1)) ==>
    ~(?s. s < SUC n /\ IS_ABORT i (s + 1))``;

val IN_LDM_STM =
  SIMP_CONV (std_ss++pred_setSimps.PRED_SET_ss) [] ``ic IN {ldm; stm}``;

val MASKN_1 = (REWRITE_RULE [MASKN_ZERO] o SPEC `0`) MASKN_SUC;
val MASKN_2 = (SIMP_RULE arith_ss [] o SPEC `1`) MASKN_SUC;

val LDM_PENCZ_ZERO =
  (GEN_ALL o REWRITE_RULE [MASKN_ZERO] o INST [`x` |-> `0`] o SPEC_ALL o
   CONJUNCT1 o SIMP_RULE (std_ss++PRED_SET_ss) [] o SPEC `ldm`) PENCZ_THM;

val PENCZ_ONE = prove(
  `!list. 0 < LENGTH (REGISTER_LIST list) ==>
       (PENCZ ldm list (MASKN 1 list) = (LENGTH (REGISTER_LIST list) = 1))`,
  REPEAT STRIP_TAC \\ `ldm IN {ldm; stm}` by SIMP_TAC (std_ss++PRED_SET_ss) []
    \\ Cases_on `LENGTH (REGISTER_LIST list) = 1`
    \\ ASM_SIMP_TAC arith_ss [PENCZ_THM]
    \\ PROVE_TAC [PENCZ_THM]);

val NOT_T3 = prove(
  `!b. ~((if b then tm else tn) = t3)`, RW_TAC stdi_ss []);

val next_7tuple = (GEN_ALL o ONCE_REWRITE_CONV [form_7tuple]) ``NEXT_ARM6 x i``;

val LDM_INIT =
  (SIMP_RULE (std_ss++boolSimps.CONJ_ss++ICLASS_ss)
     [NOT_T3,IN_LDM_STM,PENCZ_THM3,MASKN_SUC,MASKN_1,LSL_ZERO] o
   SIMP_RULE (bossLib.bool_ss++LDM_ss++PBETA_ss)
     [IS_ABORT,SND_COND_RAND,FST_COND_RAND] o
   SIMP_RULE (bossLib.bool_ss++LDM_ss) [IS_ABORT,SND_COND_RAND,FST_COND_RAND] o
   CONV_RULE (RAND_CONV (RHS_CONV (LAND_CONV
     (ONCE_REWRITE_CONV [next_7tuple])))) o
   CONV_RULE (RAND_CONV (RHS_CONV (ONCE_REWRITE_CONV [next_7tuple]))) o
   SIMP_RULE stdi_ss [IC_def,ABORTINST_def,NXTIC_def,DECODE_PSR_def] o
   DISCH `(DECODE_INST ireg = ldm) /\ (aregn2 = 2w) /\
          CONDITION_PASSED (NZCV (CPSR_READ psr)) ireg` o
   SIMP_CONV bossLib.bool_ss [INIT_ARM6_def])
   ``NEXT_ARM6 (NEXT_ARM6 (INIT_ARM6 (ARM6 (DP reg psr areg din alua alub dout)
       (CTRL pipea pipeaval pipeb pipebval ireg iregval ointstart onewinst
          endinst obaselatch opipebll nxtic nxtis nopc1 oorst resetlatch
          onfq ooonfq oniq oooniq pipeaabt pipebabt iregabt2 dataabt2 aregn2
          mrq2 nbw nrw sctrlreg psrfb oareg mask orp oorp mul mul2 borrow2
          mshift))) i0) i1``;

val LDM_INIT2 = prove(
  `!x. Abbrev (x = ^arm6state_inp) /\
       Abbrev (x0 = SINIT INIT_ARM6 x) /\
       (DECODE_INST ireg = ldm) /\ (aregn2 = 2w) /\
       CONDITION_PASSED (NZCV (CPSR_READ psr)) ireg /\
       Abbrev (w = LENGTH (REGISTER_LIST ((15 >< 0) ireg))) ==>
       ~FST (DUR_X x0) ==>
       (!t. t < SUC (SUC w) ==> ~IS_RESET inp t) /\
       (DUR_ARM6 x0 = (if ireg %% 15 /\ ~?s. s < w /\ IS_ABORT inp (s + 1)
                       then 2 else 0) + 1 + (w - 1) + 2)`,
  NTAC 2 STRIP_TAC
    \\ FULL_SIMP_TAC (stdi_ss++STATE_INP_ss)
         [Abbr`x`,SINIT_def,IC_def,ABORTINST_def,NXTIC_def,INIT_ARM6,
            DECODE_PSR_def]
    \\ UNABBREV_TAC `x0`
    \\ ASM_SIMP_TAC stdi_ss [IC_def,ABORTINST_def,NXTIC_def,DUR_X,DUR_ARM6_def,
         DUR_IC,SINIT_def,DECODE_PSR_def,GSYM IMP_DISJ_THM]
    \\ STRIP_TAC \\ IMP_RES_TAC IS_RESET_THM2
    \\ POP_ASSUM (SPEC_THEN `SUC (SUC w)` (ASSUME_TAC o REWRITE_RULE
         [DECIDE ``!x y. SUC (SUC x) <= 2 + (x - 1) + 1 + y``]))
    \\ ASM_SIMP_TAC (std_ss++numSimps.ARITH_AC_ss) []);

val LDM_f =
  `\t. ((f t reg psr (inp:num->bool#bool#bool#bool#word32#bool#bool)):word32,
         F,T,F,T,
         FIRST_ADDRESS (ireg %% 24) (ireg:word32 %% 23)
           (REG_READ6 reg (DECODE_MODE ((4 >< 0) (CPSR_READ psr)))
             ((19 >< 16) ireg))
             (WB_ADDRESS (ireg %% 23)
                (REG_READ6 reg (DECODE_MODE ((4 >< 0) (CPSR_READ psr)))
                ((19 >< 16) ireg))
                (LENGTH (REGISTER_LIST ((15 >< 0) ireg)))) + n2w (SUC t) * 4w)`;

val SNEXT2 = (BETA_RULE o REWRITE_RULE [FUN_EQ_THM]) SNEXT_def;

val LDM_GENLIST_MEMOP_EQ = prove(
  `!x. Abbrev (x = ^arm6state_inp) /\
       Abbrev (x0 = SINIT INIT_ARM6 x) /\
       (DECODE_INST ireg = ldm) /\ (aregn2 = 2w) /\
       CONDITION_PASSED (NZCV (CPSR_READ psr)) ireg /\
       Abbrev (SUC n = LENGTH (REGISTER_LIST ((15 >< 0) ireg))) ==>
       ~FST (DUR_X x0) ==>
        (?f. GENLIST (\t. OUT_ARM6 ((FUNPOW (SNEXT NEXT_ARM6) t
               (FUNPOW (SNEXT NEXT_ARM6) 2 x0)).state)) n =
             GENLIST (^(Parse.Term LDM_f)) n)`,
  REPEAT STRIP_TAC
    \\ EXISTS_TAC `\t reg psr inp. if t = 0 then
         REG_READ6 (REG_WRITE reg usr 15w (REG_READ6 reg usr 15w + 4w))
         (DECODE_MODE ((4 >< 0) (CPSR_READ psr))) ARB else PROJ_DATA (inp t)`
    \\ MATCH_MP_TAC GENLIST_FUN_EQ
    \\ REPEAT STRIP_TAC
    \\ MAP_EVERY IMP_RES_TAC [LDM_INIT2,LDM_INIT]
    \\ `~IS_RESET inp 0 /\ ~IS_RESET inp 1` by ASM_SIMP_TAC arith_ss []
    \\ IMP_RES_TAC NOT_RESET_EXISTS
    \\ ASM_SIMP_TAC (arith_ss++STATE_INP_ss) [Abbr`x`,Abbr`x0`,SINIT_def,
         PENCZ_ONE,numeral_funpow,SNEXT2,ADVANCE_def,GSYM ADVANCE_COMP,
         LDM_PENCZ_ZERO]
    \\ PAT_ASSUM `!sctrlreg resetlatch. P` (K ALL_TAC)
    \\ REPEAT ALU_ABBREV_TAC
    \\ `SUC n = LENGTH (REGISTER_LIST ((15 >< 0) ireg))` by METIS_TAC []
    \\ `0 < SUC n /\ x' <= SUC n - 1 /\ ~(SUC n = 1)` by DECIDE_TAC
    \\ IMP_RES_TAC NEXT_CORE_LDM_TN_X
    \\ PAT_ASSUM `~(SUC n = 1)` (fn th =>
         FULL_SIMP_TAC std_ss [th,WORD_MULT_CLAUSES,IS_ABORT_def])
    \\ PAT_ASSUM `inp 1 = q` SUBST_ALL_TAC
    \\ FULL_SIMP_TAC std_ss [PROJ_DATA_def,PROJ_ABORT_def]
    \\ POP_ASSUM (STRIP_ASSUME_TAC o
         (CONV_RULE (TOP_DEPTH_CONV (CHANGED_CONV (SKOLEM_CONV)))))
    \\ UNABBREV_TAC `alu1`
    \\ ASM_SIMP_TAC (arith_ss++ICLASS_ss++STATE_INP_ss) [PROJ_DATA_def,
         OUT_ARM6_def,IN_LDM_STM,GSYM FIRST_ADDRESS,TO_WRITE_READ6]);

val FILTER_LDM_MEMOPS_X = prove(
  `!y x. Abbrev (x = ^arm6state_inp) /\
         Abbrev (x0 = SINIT INIT_ARM6 x) /\
         (DECODE_INST ireg = ldm) /\ (aregn2 = 2w) /\
         CONDITION_PASSED (NZCV (CPSR_READ psr)) ireg /\
         Abbrev (SUC n = LENGTH (REGISTER_LIST ((15 >< 0) ireg))) /\
         ~FST (DUR_X x0) ==>
         (let l = MOVE_DOUT y (GENLIST
            (\t. OUT_ARM6 ((FUNPOW (SNEXT NEXT_ARM6) t
                  (FUNPOW (SNEXT NEXT_ARM6) 2 x0)).state)) n) in
          FILTER IS_MEMOP l = l)`,
  SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC
    \\ IMP_RES_TAC LDM_GENLIST_MEMOP_EQ \\ NTAC 15 (POP_LAST_TAC)
    \\ POP_ASSUM SUBST1_TAC
    \\ MATCH_MP_TAC ((GEN_ALL o BETA_RULE o ISPEC LDM_f) FILTER_MEMOP_NONE)
    \\ RW_TAC bossLib.std_ss [IS_MEMOP_def]);

fun PAT_TAC (asl, w) =
  let val g = (snd o strip_comb o snd o dest_comb o snd o hd o snd o
               TypeBase.dest_record o rhs o snd o dest_comb o fst o dest_imp) w
  in
    (MAP_EVERY (fn x => ABBREV_TAC `x = ^(List.nth(g,x))` \\ POP_LAST_TAC)
               [6,16,17,18,19,20,21,34,35,36,37]) (asl, w)
  end;

val PROJ_IREG_COR = GEN_ALL (prove(
  `Abbrev (x = ^arm6state_inp) /\ Abbrev (x0 = SINIT INIT_ARM6 x) ==>
     (PROJ_IREG x0.state = ireg)`,
  STRIP_TAC \\ ASM_SIMP_TAC (std_ss++STATE_INP_ss)
    [Abbr`x`,Abbr`x0`,SINIT_def,INIT_ARM6_def,PROJ_IREG_def]));

val state_inp_simp =
   simpLib.SIMP_PROVE (srw_ss()) [state_inp_component_equality]
   ``<| state := x.state; inp := x.inp |> = x``;

local
  fun tac ss = PAT_ASSUM `Abbrev (q = NEXT_ARM6 (ARM6 dp ctrl) inp)` MP_TAC
   \\ ASM_SIMP_TAC (booli_ss++pairSimps.PAIR_ss++ss++PBETA_ss)
        [NOT_ABORT,SND_COND_RAND,FST_COND_RAND]
   \\ TRY ALU_ABBREV_TAC \\ STRIP_TAC
   \\ POP_ASSUM (fn th => FULL_SIMP_TAC (bossLib.std_ss++boolSimps.CONJ_ss)
       [OUT_ARM6_def,IS_MEMOP2_def,REWRITE_RULE [markerTheory.Abbrev_def] th])
in
  val LDM_TAC = tac LDM_ss
  val UNEXEC_TAC = tac UNEXEC_ss
end;

val _ = print "*\nVerifying output: ldm\n*\n"; (*============================*)

val LDM_MEMOPS = Count.apply prove(
  `!x. Abbrev (x = ^arm6state_inp) /\
       Abbrev (x0 = SINIT INIT_ARM6 x) /\
       (DECODE_INST ireg = ldm) /\ (aregn2 = 2w) /\
       CONDITION_PASSED (NZCV (CPSR_READ psr)) ireg ==>
       ~FST (DUR_X x0) ==>
       (OUT_ARM (ABS_ARM6 x.state) =
        OSMPL_ARM6 x0 (GENLIST
          (\t. OUT_ARM6 ((FUNPOW (SNEXT NEXT_ARM6) t x0).state))
            (DUR_ARM6 x0)))`,
  REPEAT STRIP_TAC
    \\ ABBREV_TAC `nbs = DECODE_MODE ((4 >< 0) (CPSR_READ psr))`
    \\ ABBREV_TAC `w = LENGTH (REGISTER_LIST ((15 >< 0) ireg))`
    \\ Cases_on `w`
    \\ MAP_EVERY IMP_RES_TAC [LDM_INIT2,INIT_INIT,PROJ_IREG_COR]
    \\ ASM_SIMP_TAC (std_ss++ICLASS_ss)
        [FUNPOW,ADVANCE_ZERO,STATE_ARM6_COR,
         OSMPL_ARM6_def,SINIT_def,SUC2NUM IMM_ARM6_def,state_inp_simp]
    \\ POP_LASTN_TAC 4
    << [
      `~(ireg %% 15)` by METIS_TAC [PENCZ_THM2,WORD_BITS_150_ZERO]
        \\ `!mask. PENCZ ldm ((15 >< 0) ireg) mask`
        by METIS_TAC [PENCZ_THM2,PENCZ_THM3,IN_LDM_STM]
        \\ ASM_SIMP_TAC (list_ss++boolSimps.LET_ss++STATE_INP_ss)
             [Abbr`x`,Abbr`x0`,SINIT_def,numeral_funpow,SNOC,HD_GENLIST,
              IS_MEMOP2_def,NULL_GENLIST,NULL_APPEND_RIGHT,ADVANCE_def,
              INIT_ARM6_def,ABS_ARM6_def,SNEXT2,GENLISTn,FILTER_MEMOP_ONE,
              FILTER_MEMOP_SINGLETON,OUT_ARM6_def]
        \\ REPEAT (PAT_ABBREV_TAC `q = NEXT_ARM6 a b`)
        \\ `~IS_RESET inp 0 /\ ~IS_RESET inp 1` by ASM_SIMP_TAC arith_ss []
        \\ IMP_RES_TAC NOT_RESET_EXISTS
        \\ NTAC 2 LDM_TAC
        \\ ASM_SIMP_TAC stdi_ss [OUT_ARM_def,DECODE_PSR_def,LDM_STM_def,
             DECODE_LDM_STM_def,ADDR_MODE4_def,DECODE_INST_LDM,ADDRESS_LIST_def,
             GENLIST,MAP],
      IMP_RES_TAC FILTER_LDM_MEMOPS_X
        \\ FULL_SIMP_TAC stdi_ss [STATE_ARM6_COR,OSMPL_ARM6_def]
        \\ MAP_EVERY (fn th => ONCE_REWRITE_TAC [th])
             [FUNPOW_COMP,GENLIST_APPEND,GENLIST_APPEND]
        \\ BETA_TAC \\ REWRITE_TAC
             [(GEN_ALL o INST [`b` |-> `2`] o SPEC_ALL) FUNPOW_COMP]
        \\ COND_CASES_TAC
        << [
          `~((15 >< 0) ireg = 0w:word16)` by METIS_TAC [WORD_BITS_150_ZERO]
            \\ `RP ldm ((15 >< 0) ireg) (MASKN n ((15 >< 0) ireg)) = 15w`
            by METIS_TAC [RP_LAST_15,WORD_BITS_150_ZERO,
                 DECIDE ``0 < SUC n /\ (!m n. (m = SUC n) ==> (n = (m - 1)))``],
          PAT_ASSUM `~(a /\ b)` (K ALL_TAC)
        ]
        \\ ASM_SIMP_TAC list_ss [FILTER_MEMOP_ONE,FILTER_MEMOP_SINGLETON,
             NULL_GENLIST,NULL_APPEND_RIGHT,GENLISTn,SNOC,HD_GENLIST,
             HD_APPEND2,IS_MEMOP2_def,CONJUNCT1 FUNPOW]
        \\ ASM_SIMP_TAC list_ss [FILTER_APPEND,FILTER_MEMOP_ONE,
             FILTER_MEMOP_SINGLETON,MOVE_DOUT_APPEND]
        \\ PAT_ASSUM `!y. FILTER f l = l` (K ALL_TAC)
        \\ RES_MP_TAC [] LDM_GENLIST_MEMOP_EQ \\ POP_ASSUM IMP_RES_TAC
        \\ PAT_ASSUM `Abbrev (x0 = SINIT INIT_ARM6 x)` MP_TAC
        \\ ASM_SIMP_TAC (bossLib.std_ss++STATE_INP_ss) [Abbr`x`,SINIT_def,
             IC_def,ABORTINST_def,NXTIC_def,DECODE_PSR_def,SNEXT2,ADVANCE_def,
             INIT_ARM6,numeral_funpow]
        \\ POP_LAST_TAC \\ STRIP_TAC
        \\ SIMP_TAC (bossLib.std_ss++STATE_INP_ss) [Abbr`x0`,OUT_ARM6_def,
             IS_MEMOP2_def,GSYM ADVANCE_COMP]
        \\ SIMP_TAC bossLib.std_ss [ONCE_REWRITE_RULE [ADD_COMM] FUNPOW_COMP]
        \\ REPEAT (PAT_ABBREV_TAC `q = NEXT_ARM6 a b`)
        \\ ABBREV_TAC `sn = FUNPOW (SNEXT NEXT_ARM6) n
              <| state := q'; inp := ADVANCE 2 inp|>`
        \\ `~IS_RESET inp 0 /\ ~IS_RESET inp 1` by ASM_SIMP_TAC arith_ss []
        \\ IMP_RES_TAC NOT_RESET_EXISTS2
        \\ NTAC 2 LDM_TAC
        \\ PAT_ASSUM `Abbrev (sn = FUNPOW f n state)` MP_TAC
        \\ `0 < SUC n` by DECIDE_TAC \\ IMP_RES_TAC NEXT_CORE_LDM_TN_W1
        \\ POP_ASSUM MP_TAC
        \\ ASM_SIMP_TAC (bossLib.old_arith_ss++STATE_INP_ss) [GSYM ADVANCE_COMP,
             LDM_PENCZ_ZERO,NOT_T3,PROJ_DATA_def,PROJ_ABORT_def,PENCZ_ONE,
             MASKN_1,MASKN_SUC,SPECL [`i`,`1`] IS_ABORT_def,PENCZ_THM3,LSL_ZERO]
        \\ DISCH_THEN (STRIP_ASSUME_TAC o
             (CONV_RULE (TOP_DEPTH_CONV (CHANGED_CONV (SKOLEM_CONV)))))
        \\ ASM_SIMP_TAC (bossLib.old_arith_ss++STATE_INP_ss)
             [numeral_funpow,SNEXT2,ADVANCE_def]
        \\ POP_LAST_TAC \\ PAT_TAC
        \\ REPEAT (PAT_ABBREV_TAC `q = NEXT_ARM6 a b`)
        \\ STRIP_TAC \\ UNABBREV_TAC `sn`
        \\ RULE_ASSUM_TAC (SIMP_RULE (bossLib.old_arith_ss++STATE_INP_ss)
             [ADVANCE_def,PROJ_DATA_def])
        \\ ASM_SIMP_TAC (bossLib.std_ss++STATE_INP_ss)
             [OUT_ARM6_def,IS_MEMOP2_def]
        << [
          `~IS_RESET inp (SUC n + 1)` by ASM_SIMP_TAC arith_ss []
            \\ IMP_RES_TAC NOT_RESET_EXISTS \\ POP_LASTN_TAC 2
            \\ LDM_TAC \\ Cases_on_arm6inp `inp (SUC n + 2)`
            \\ UNEXEC_TAC \\ POP_LASTN_TAC 4, ALL_TAC ]
        \\ ASM_SIMP_TAC (stdi_ss++listSimps.LIST_ss++ARITH_ss)
             ([Abbr`alu`,combinTheory.o_ABS_R,GSYM FIRST_ADDRESS,LSL_ZERO,
               num2exception_word3,ABS_ARM6_def,MEMOP_def,MAP_LDM_MEMOP,
               OUT_ARM_def,DECODE_PSR_def,LDM_STM_def,DECODE_LDM_STM_def,
               ADDR_MODE4_def,DECODE_INST_LDM,ADDRESS_LIST_def,word_mul_n2w,
               MAP_GENLIST,GENLIST_CONS,WORD_ADD_0,IN_LDM_STM] @ finish_rws2)]);

val REV_ADD4 = DECIDE ``a + b + c + d = d + c + b + a:num``;

val LDM_LEM = prove(
  `!ireg:word32 base abort.
     Abbrev (w = LENGTH (REGISTER_LIST ((15 >< 0) ireg))) /\ 0 < w ==>
     ((abort /\ (base = 15w) \/
       ~((if abort then
            base
          else
            RP ldm ((15 >< 0) ireg) (MASKN (w - 1) ((15 >< 0) ireg))) = 15w)) =
     (abort \/ ~(ireg %% 15)))`,
  REPEAT STRIP_TAC
    \\ Cases_on `base = 15w` \\ ASM_SIMP_TAC std_ss [Abbr`w`,LEM,RP_LAST_15]
    \\ Cases_on `abort` \\ ASM_SIMP_TAC std_ss [RP_LAST_15,WORD_BITS_150_ZERO]);

val REG_WRITE_READ_NEQ_15 =
  (GEN_ALL o CONV_RULE (LAND_CONV (ONCE_DEPTH_CONV SYM_CONV)) o
   SIMP_RULE arith_ss [TO_WRITE_READ6] o
   INST [`n1` |-> `15w`] o SPEC_ALL) REG_READ_WRITE_NEQ;

val ABBREV_RP_LAST_15 =
  (GEN_ALL o REWRITE_RULE [DECIDE ``a ==> b ==> c = a /\ b ==> c``] o
   SIMP_RULE std_ss [] o
   DISCH `Abbrev (w = LENGTH (REGISTER_LIST list))` o
   SPEC_ALL) RP_LAST_15;

val IF_COND = prove(
  `~(~USER nbs /\ ireg %% 22) ==>
      (CPSR_READ (if ireg %% 22 then
          CPSR_WRITE (psr:psrs -> word32) (SPSR_READ psr nbs)
        else
          psr) = CPSR_READ psr)`,
  RW_TAC std_ss [USER_usr,CPSR_READ_WRITE]);

val REG_WRITEN_SUC = (GEN_ALL o SIMP_RULE arith_ss [] o
  DISCH `0 < n` o INST [`n` |-> `n - 1`] o SPEC_ALL) REG_WRITEN_SUC;

local val spec_list_rule =
  (GEN_ALL o SIMP_RULE arith_ss [GSYM WORD_BITS_150_ZERO,ADVANCE_def] o
   DISCH `0 < LENGTH (REGISTER_LIST ((15 >< 0) ireg))` o
   INST [`list` |-> `(15 >< 0) (ireg:word32)`,`i` |-> `ADVANCE 1 i`] o SPEC_ALL)
in
  val REG_WRITEN_WRITE_PC3 = spec_list_rule REG_WRITEN_WRITE_PC
  val REG_WRITEN_WRITE_PC4 = spec_list_rule REG_WRITEN_WRITE_PC2
end;

fun PAT_TAC n =
  MAP_EVERY (fn s => PAT_ABBREV_TAC (mk_pat "z" s n) \\ POP_LAST_TAC)
        ["ointstart'","onfq'","ooonfq'","oniq'","oooniq'",
         "pipeaabt'","pipebabt'","borrow2'"]
   \\ MAP_EVERY (fn s => PAT_ABBREV_TAC (mk_pat "q" s n) \\ POP_LAST_TAC)
        ["oareg'","mul'"]
   \\ PAT_ABBREV_TAC (mk_pat "q:word32" "mul2'" n) \\ POP_LAST_TAC
   \\ PAT_ABBREV_TAC (mk_pat "q:word5" "mshift'" n) \\ POP_LAST_TAC
   \\ PAT_ABBREV_TAC (mk_pat "aregn" "aregn'" n);

val _ = print "*\nVerifying time-consistency and correctness: ldm\n*\n"; (*==*)

val LDM = Count.apply prove(
  `!x. Abbrev (x = ^arm6state_inp) /\ inp IN STRM_ARM6 /\
       Abbrev (x0 = SINIT INIT_ARM6 x) /\
       (DECODE_INST ireg = ldm) /\ (aregn2 = 2w) /\
       CONDITION_PASSED (NZCV (CPSR_READ psr)) ireg ==>
       ~FST (DUR_X x0) ==>
       (let s = (FUNPOW (SNEXT NEXT_ARM6) (DUR_ARM6 x0) x0).state in
          (INIT_ARM6 s = s) /\
          (STATE_ARM 1 <|state := ABS_ARM6 x.state; inp := SMPL_ARM6 x|> =
           ABS_ARM6 s))`,
  REPEAT STRIP_TAC
    \\ ABBREV_TAC `nbs = DECODE_MODE ((4 >< 0) (CPSR_READ psr))`
    \\ ABBREV_TAC `w = LENGTH (REGISTER_LIST ((15 >< 0) ireg))`
    \\ MAP_EVERY IMP_RES_TAC [LDM_INIT2,INIT_INIT,PROJ_IREG_COR]
    \\ `(x.inp = inp) /\ (x.state = ^arm6state) /\
        (<|state := x0.state; inp := inp|> = x0)`
    by SIMP_TAC (std_ss++STATE_INP_ss) [Abbr`x`,Abbr`x0`,SINIT_def]
    \\ ASM_SIMP_TAC (srw_ss()++boolSimps.LET_ss++SIZES_ss) [num2exception_thm,
         SUC2NUM STATE_ARM_def,ABS_ARM6_def,SMPL_ARM6_def,SMPL_DATA_ARM6_def,
         IFLAGS_def,ADVANCE_ZERO,DECODE_PSR_def,PACK_def,IMM_LEN_def,
         SUC2NUM IMM_ARM6_def,MAP_STRM_def,COMBINE_def,SMPL_EXC_ARM6_def,
         STATE_ARM6_COR,FUNPOW,ADVANCE_ZERO,OSMPL_ARM6_def,SINIT_def,
         SUC2NUM IMM_ARM6_def,state_inp_simp]
    \\ POP_LASTN_TAC 7
    \\ PAT_ABBREV_TAC `s = (FUNPOW (SNEXT NEXT_ARM6) d x0).state`
    \\ POP_ASSUM MP_TAC
    \\ REWRITE_TAC [FUNPOW_COMP]
    \\ PAT_ASSUM `~FST (DUR_X x0)` MP_TAC
    \\ ASM_SIMP_TAC (bossLib.std_ss++STATE_INP_ss)
         [Abbr`x`,Abbr`x0`,ADVANCE_def,SINIT_def,SNEXT,numeral_funpow]
    \\ `~IS_RESET inp 0 /\ ~IS_RESET inp 1` by ASM_SIMP_TAC arith_ss []
    \\ MAP_EVERY IMP_RES_TAC [NOT_RESET_EXISTS2,LDM_INIT]
    \\ ASM_SIMP_TAC stdi_ss [DUR_X2,DUR_IC_def,INIT_ARM6] \\ POP_LAST_TAC
    \\ STRIP_TAC \\ REPEAT ALU_ABBREV_TAC
    \\ Cases_on `(15 >< 0) ireg = 0w:word16`
    \\ ASM_SIMP_TAC stdi_ss [PENCZ_THM3,IN_LDM_STM]
    << [
      MAP_EVERY IMP_RES_TAC [PENCZ_THM2,CONJUNCT1 WORD_BITS_150_ZERO]
        \\ ASM_SIMP_TAC std_ss [Abbr`w`,SUB_0,FUNPOW]
        \\ `~IS_RESET inp 2` by ASM_SIMP_TAC arith_ss []
        \\ IMP_RES_TAC NOT_RESET_EXISTS2 \\ POP_LASTN_TAC 2
        \\ ASM_SIMP_TAC (std_ss++STATE_INP_ss) [SNEXT_def,ADVANCE_def]
        \\ iclass_compLib.LDM_TAC
        \\ FULL_SIMP_TAC (stdi_ss++STATE_INP_ss) []
        \\ STRIP_TAC \\ UNABBREV_TAC `s` \\ CONJ_TAC
        << [
          RW_TAC std_ss finish_rws \\ FULL_SIMP_TAC std_ss [],
          IMP_RES_TAC DECODE_INST_LDM
            \\ ASM_SIMP_TAC (stdi_ss++STATE_INP_ss++SIZES_ss)
                 (word_0::finish_rws3)
            \\ RW_TAC stdi_ss ([Abbr`alu`,FIRSTN,WB_ADDRESS_ZERO,IN_LDM_STM,
                 (REWRITE_RULE [] o SPEC `0w`) PENCZ_THM2,LDM_LIST_EMPTY,
                 USER_usr] @ finish_rws2)
        ],
      `0 < w` by FULL_SIMP_TAC arith_ss [Abbr`w`,PENCZ_THM2]
        \\ ABBREV_TAC `abort = ?s. s < w /\ IS_ABORT inp (s + 1)`
        \\ `Abbrev (~abort = !s. s < w ==> ~IS_ABORT inp (s + 1))`
        by SIMP_TAC std_ss [Abbr`abort`,IS_ABORT_def,IMP_DISJ_THM,
             markerTheory.Abbrev_def]
        \\ FULL_SIMP_TAC std_ss []
        \\ IMP_RES_TAC NEXT_CORE_LDM_TN_W1
        \\ POP_ASSUM (STRIP_ASSUME_TAC o
             (CONV_RULE (TOP_DEPTH_CONV (CHANGED_CONV (SKOLEM_CONV)))))
        \\ PAT_ASSUM `inp 1 = (T,ABORT1,NFQ1,NIQ1,DATA1,CPA1,CPB1)`
             (fn th => RULE_ASSUM_TAC (SIMP_RULE std_ss
               [SPECL [`x`,`1`] IS_ABORT_def,PROJ_ABORT_def,PROJ_DATA_def,th]))
        \\ ASM_SIMP_TAC (stdi_ss++ARITH_ss) [PENCZ_ONE,
             GSYM ADVANCE_COMP,LDM_PENCZ_ZERO]
        \\ PAT_ASSUM `!sctrlreg reg psrfb. P` (ASSUME_TAC o GEN_ALL o
            (MATCH_MP (DECIDE ``a /\ b /\ c /\ d ==> a /\ b /\ c``)) o SPEC_ALL)
        \\ PAT_TAC 23
        \\ `~(aregn IN {0w; 1w; 2w; 5w}) /\
              ((aregn = 7w) ==> ~(CPSR_READ psr %% 6)) /\
              ((aregn = 6w) ==> ~(CPSR_READ psr %% 7))`
        by METIS_TAC [Abbr`aregn`]
        \\ RM_ABBREV_TAC `aregn`
        \\ PAT_ASSUM `!sctrlreg reg psrfb. P` (K ALL_TAC)
        \\ `~IS_RESET inp (w + 1)`
        by METIS_TAC [DECIDE ``!w. 0 < w ==> w + 1 < 2 + (w - 1) + 1 + x``]
        \\ IMP_RES_TAC NOT_RESET_EXISTS2
        \\ ASM_SIMP_TAC arith_ss [SNEXT,numeral_funpow,ADVANCE_def]
        \\ iclass_compLib.LDM_TAC
        \\ RES_MP_TAC [`base` |-> `(19 >< 16) ireg`] LDM_LEM
        \\ ASM_SIMP_TAC (stdi_ss++ARITH_ss++boolSimps.CONJ_ss++PBETA_ss)
             [ALUOUT_ALU_logic,LSL_ZERO,DECIDE ``a /\ b \/ ~a = a ==> b``]
        \\ POP_LAST_TAC
        \\ Cases_on `~abort /\ ireg %% 15`
        \\ ASM_SIMP_TAC std_ss [FUNPOW]
        << [
          REPEAT (PAT_ASSUM `~IS_RESET inp x` (K ALL_TAC))
            \\ `~IS_RESET inp (w + 2) /\ ~IS_RESET inp (w + 3)`
            by FULL_SIMP_TAC arith_ss []
            \\ IMP_RES_TAC NOT_RESET_EXISTS2
            \\ RES_MP_TAC [`list` |-> `(15 >< 0) (ireg:word32)`]
                 ABBREV_RP_LAST_15
            \\ ASM_SIMP_TAC arith_ss [REG_WRITEN_def,SNEXT,
                 numeral_funpow,ADVANCE_def]
            \\ POP_LAST_TAC
            \\ iclass_compLib.UNEXEC_TAC
            \\ SIMP_TAC (stdi_ss++STATE_INP_ss) []
            \\ STRIP_TAC \\ UNABBREV_TAC `s` \\ CONJ_TAC
            << [
              POP_ASSUM_LIST (K ALL_TAC) \\ RW_TAC std_ss finish_rws
                \\ FULL_SIMP_TAC std_ss [],
              IMP_RES_TAC DECODE_INST_LDM
                \\ `w <= LENGTH (REGISTER_LIST ((15 >< 0) ireg)) /\
                         LENGTH (REGISTER_LIST ((15 >< 0) ireg)) <= w + 3`
                by SIMP_TAC arith_ss [Abbr`w`]
                \\ Cases_on `~USER nbs /\ ireg %% 22`
                \\ IMP_RES_TAC IF_COND
                \\ ASM_SIMP_TAC (stdi_ss++STATE_INP_ss)
                     ([REG_WRITEN_SUC,GSYM WORD_BITS_150_ZERO] @ finish_rws3)
                \\ RW_TAC stdi_ss ([Abbr`w`,Abbr`alu`,
                     (SIMP_RULE arith_ss [FST_ADDR_MODE4] o INST [`n` |->
                      `LENGTH (REGISTER_LIST ((15 >< 0) ireg)) + 3`] o
                       SPEC_ALL) REGISTER_LIST_LDM_THM,GSYM WORD_BITS_150_ZERO,
                      SND_ADDR_MODE4,REG_WRITEN_WRITE_PC4,GSYM FIRST_ADDRESS,
                      ALUOUT_ALU_logic,LENGTH_ADDR_MODE4,GSYM WB_ADDRESS,
                      REG_READ_WRITEN_PC,ADVANCE_def,LSL_ZERO,IN_LDM_STM,
                      REG_WRITE_WRITEN_PC,REG_WRITEN_WRITE_PC3] @ finish_rws2)
                \\ FULL_SIMP_TAC std_ss [CPSR_READ_WRITE]
            ],
          STRIP_TAC \\ UNABBREV_TAC `s`
            \\ FULL_SIMP_TAC (std_ss++STATE_INP_ss) [FUNPOW]
            << [ALL_TAC,
             `~(RP ldm ((15 >< 0) ireg) (MASKN (w - 1) ((15 >< 0) ireg)) = 15w)`
                by METIS_TAC [RP_LAST_15,CONJUNCT2 WORD_BITS_150_ZERO]
                \\ `w - 1 < w` by DECIDE_TAC]
            \\ (CONJ_TAC
            << [
              RW_TAC std_ss finish_rws \\ FULL_SIMP_TAC std_ss [],
              IMP_RES_TAC DECODE_INST_LDM
                \\ `abort ==> ((LEAST s. IS_ABORT inp (s + 1)) < w) /\
                       ((LEAST s. s < w /\ IS_ABORT inp (s + 1)) =
                        (LEAST s. IS_ABORT inp (s + 1))) /\
                    ((w = 1) ==>
                       ((LEAST s. s < 1 /\ IS_ABORT inp (s + 1)) =
                        (LEAST s. IS_ABORT inp (s + 1))))`
                by (SIMP_TAC std_ss [Abbr`abort`,GSYM IS_ABORT_def,
                      LEAST_ABORT_LT2,LEAST_ABORT_ISA] \\
                    METIS_TAC [LEAST_ABORT_ISA])
                \\ Cases_on `abort` \\ FULL_SIMP_TAC std_ss []
                \\ ASM_SIMP_TAC (stdi_ss++STATE_INP_ss)
                     ([SIMP_PROJ_Dabort,REG_WRITEN_SUC,
                       GSYM WORD_BITS_150_ZERO] @ finish_rws3)
                \\ RW_TAC arith_ss ([Abbr`w`,Abbr`alu`,
                      (SIMP_RULE arith_ss [FST_ADDR_MODE4] o
                       INST [`n` |-> `LENGTH (REGISTER_LIST ireg) + 1`] o
                       SPEC_ALL) REGISTER_LIST_LDM_THM,GSYM WORD_BITS_150_ZERO,
                      SND_ADDR_MODE4,REG_WRITEN_WRITE_PC4,GSYM FIRST_ADDRESS,
                      REG_WRITEN_COMMUTE_PC,ALUOUT_ALU_logic,LENGTH_ADDR_MODE4,
                      GSYM WB_ADDRESS,REG_READ_WRITEN_PC,REG_WRITEN_COMMUTES,
                      REG_READ_WRITEN_PC2,ADVANCE_def,LSL_ZERO,IN_LDM_STM,
                      REG_WRITE_WRITEN_PC,REG_WRITEN_WRITE_PC3] @ finish_rws2)
                \\ `(LEAST s. IS_ABORT inp (s + 1)) = 0` by DECIDE_TAC
                \\ ASM_SIMP_TAC std_ss ((CONJUNCT1 REG_WRITEN_def)::finish_rws2)
            ])]]);

(* ------------------------------------------------------------------------- *)

val LENGTH_ONE = prove(
  `!l. (LENGTH l = 1) ==> (l = [HD l])`,
  Cases \\ SIMP_TAC list_ss [LENGTH_NIL]);

val HD_TL = prove(
  `!l. (0 < LENGTH l) ==> (l = ((HD l)::TL l))`,
  Cases \\ SIMP_TAC list_ss [LENGTH_NIL]);

val STM_PENCZ_ZERO =
  (GEN_ALL o REWRITE_RULE [MASKN_ZERO] o INST [`x` |-> `0`] o SPEC_ALL o
   CONJUNCT1 o SIMP_RULE std_ss [IN_LDM_STM] o SPEC `stm`) PENCZ_THM;

val STM_PENCZ_ONE =
  (GEN_ALL o REWRITE_RULE [] o INST [`x` |-> `1`] o SPEC_ALL o
   CONJUNCT1 o SIMP_RULE std_ss [IN_LDM_STM] o SPEC `stm`) PENCZ_THM;

val STM_INIT =
  (SIMP_RULE (stdi_ss++boolSimps.CONJ_ss++ARITH_ss)
     [MASK_def,STM_PENCZ_ZERO,STM_PENCZ_ONE,IN_LDM_STM,MASKN_2,LSL_ZERO] o
   SIMP_RULE (booli_ss++STM_ss++PBETA_ss)
     [IS_ABORT,SND_COND_RAND,FST_COND_RAND,IN_LDM_STM,MASKN_1] o
   CONV_RULE (RAND_CONV (RHS_CONV
     (LAND_CONV (ONCE_REWRITE_CONV [next_7tuple])))) o
   CONV_RULE (RAND_CONV (RHS_CONV (ONCE_REWRITE_CONV [next_7tuple]))) o
   SIMP_RULE stdi_ss [IC_def,ABORTINST_def,NXTIC_def,DECODE_PSR_def] o
   DISCH `1 < LENGTH (REGISTER_LIST ((15 >< 0) ireg)) /\
          (DECODE_INST ireg = stm) /\ (aregn2 = 2w) /\
          CONDITION_PASSED (NZCV (CPSR_READ psr)) ireg` o
   SIMP_CONV bossLib.bool_ss [INIT_ARM6_def])
   ``NEXT_ARM6 (NEXT_ARM6 (INIT_ARM6 (ARM6 (DP reg psr areg din alua alub dout)
       (CTRL pipea pipeaval pipeb pipebval ireg iregval ointstart onewinst
          endinst obaselatch opipebll nxtic nxtis nopc1 oorst resetlatch
          onfq ooonfq oniq oooniq pipeaabt pipebabt iregabt2 dataabt2 aregn2
          mrq2 nbw nrw sctrlreg psrfb oareg mask orp oorp mul mul2 borrow2
          mshift))) i0) i1``;

val STM_INIT2 = prove(
  `!x. Abbrev (x = ^arm6state_inp) /\
       Abbrev (x0 = SINIT INIT_ARM6 x) /\
       (DECODE_INST ireg = stm) /\ (aregn2 = 2w) /\
       CONDITION_PASSED (NZCV (CPSR_READ psr)) ireg /\
       Abbrev (l = LENGTH (REGISTER_LIST ((15 >< 0) ireg))) ==>
       ~FST (DUR_X x0) ==>
       (!t. t < SUC l ==> ~IS_RESET inp t) /\ (DUR_ARM6 x0 = (2 + (l - 1)))`,
  NTAC 2 STRIP_TAC
    \\ FULL_SIMP_TAC (stdi_ss++STATE_INP_ss) [Abbr`x`,Abbr`x0`,SINIT_def,
         IC_def,ABORTINST_def,NXTIC_def,INIT_ARM6_def,DECODE_PSR_def,IC_def,
         ABORTINST_def,NXTIC_def,DUR_X,DUR_ARM6_def,DUR_IC,SINIT_def,
         GSYM IMP_DISJ_THM]
    \\ STRIP_TAC \\ IMP_RES_TAC IS_RESET_THM2
    \\ POP_ASSUM (SPEC_THEN `SUC l` (STRIP_ASSUME_TAC o
         REWRITE_RULE [DECIDE ``!x y. SUC x <= 2 + (x - 1)``])));

val STM_f =
  `\t. (if t = 0 then
          REG_READ6 (REG_WRITE reg usr 15w
            (REG_READ6 reg usr 15w + 4w)) nbs (RP stm ((15 >< 0) ireg) Tw)
         else
           REG_READ6
             (if ireg %% 21 /\ ~((19 >< 16) ireg = 15w:word4) then
                REG_WRITE (REG_WRITE reg usr 15w
                  (REG_READ6 reg usr 15w + 4w)) nbs ((19 >< 16) ireg)
                  (WB_ADDRESS (ireg %% 23)
                     (REG_READ6 reg (DECODE_MODE ((4 >< 0) (CPSR_READ psr)))
                     ((19 >< 16) (ireg:word32)))
                     (LENGTH (REGISTER_LIST ((15 >< 0) ireg))))
              else
                REG_WRITE reg usr 15w (REG_READ6 reg usr 15w + 4w)) nbs
             (RP stm ((15 >< 0) ireg) (MASKN t ((15 >< 0) ireg))),F,T,T,T,
          FIRST_ADDRESS (ireg %% 24) (ireg %% 23)
            (REG_READ6 reg (DECODE_MODE ((4 >< 0) (CPSR_READ psr)))
            ((19 >< 16) ireg))
            (WB_ADDRESS (ireg %% 23)
               (REG_READ6 reg (DECODE_MODE ((4 >< 0) (CPSR_READ psr)))
               ((19 >< 16) ireg))
               (LENGTH (REGISTER_LIST ((15 >< 0) ireg)))) + n2w (SUC t) * 4w)`;

val STM_GENLIST_MEMOP_EQ = prove(
  `!x. Abbrev (x = ^arm6state_inp) /\
       Abbrev (x0 = SINIT INIT_ARM6 x) /\
       Abbrev (nbs = if ireg %% 22 then usr
                     else DECODE_MODE ((4 >< 0) (CPSR_READ psr))) /\
       (DECODE_INST ireg = stm) /\ (aregn2 = 2w) /\
       CONDITION_PASSED (NZCV (CPSR_READ psr)) ireg /\
       Abbrev (SUC n = LENGTH (REGISTER_LIST ((15 >< 0) ireg))) ==>
       ~FST (DUR_X x0) ==>
        (GENLIST (\t. OUT_ARM6 ((FUNPOW (SNEXT NEXT_ARM6) t
           (FUNPOW (SNEXT NEXT_ARM6) 2 x0)).state)) n =
         GENLIST (^(Parse.Term STM_f)) n)`,
  REPEAT STRIP_TAC
    \\ MATCH_MP_TAC GENLIST_FUN_EQ
    \\ MAP_EVERY IMP_RES_TAC [STM_INIT2,STM_INIT]
    \\ ASM_SIMP_TAC (arith_ss++STATE_INP_ss) [Abbr`x`,Abbr`x0`,SINIT_def,
         numeral_funpow,SNEXT,ADVANCE_def,GSYM ADVANCE_COMP,
         STM_PENCZ_ZERO,PENCZ_ONE]
    \\ POP_LAST_TAC
    \\ REPEAT ALU_ABBREV_TAC
    \\ REPEAT STRIP_TAC
    \\ `~IS_RESET inp 0 /\ ~IS_RESET inp 1`
      by METIS_TAC [DECIDE ``0 < SUC (SUC n) /\ 1 < SUC (SUC n)``]
    \\ IMP_RES_TAC NOT_RESET_EXISTS2
    \\ `1 < SUC n /\ x <= SUC n - 2 /\ ~(SUC n = 1)` by DECIDE_TAC
    \\ `SUC n = LENGTH (REGISTER_LIST ((15 >< 0) ireg))` by METIS_TAC []
    \\ IMP_RES_TAC NEXT_CORE_STM_TN_X
    \\ PAT_ASSUM `~(SUC n = 1)`
         (fn th => FULL_SIMP_TAC std_ss [th,WORD_MULT_CLAUSES])
    \\ POP_ASSUM (STRIP_ASSUME_TAC o
         (CONV_RULE (TOP_DEPTH_CONV (CHANGED_CONV (SKOLEM_CONV)))))
    \\ ASM_SIMP_TAC (arith_ss++STATE_INP_ss) [Abbr`alu`,Abbr`alu1`,
         IS_ABORT_def,PROJ_ABORT_def,ADVANCE_def,OUT_ARM6_def,GSYM WB_ADDRESS,
         GSYM FIRST_ADDRESS,TO_WRITE_READ6,IN_LDM_STM]);

val FILTER_STM_MEMOPS_X = prove(
  `!x. Abbrev (x = ^arm6state_inp) /\
       Abbrev (x0 = SINIT INIT_ARM6 x) /\
       (DECODE_INST ireg = stm) /\ (aregn2 = 2w) /\
       CONDITION_PASSED (NZCV (CPSR_READ psr)) ireg /\
       Abbrev (SUC n = LENGTH (REGISTER_LIST ((15 >< 0) ireg))) /\
       ~FST (DUR_X x0) ==>
       (let l = MOVE_DOUT y (GENLIST (\t. OUT_ARM6 ((FUNPOW (SNEXT NEXT_ARM6) t
                  (FUNPOW (SNEXT NEXT_ARM6) 2 x0)).state)) n) in
        FILTER IS_MEMOP l = l)`,
  SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC
    \\ ABBREV_TAC `nbs = if ireg %% 22 then usr
                         else DECODE_MODE ((4 >< 0) (CPSR_READ psr))`
    \\ IMP_RES_TAC STM_GENLIST_MEMOP_EQ
    \\ POP_ASSUM SUBST1_TAC
    \\ MATCH_MP_TAC ((GEN_ALL o BETA_RULE o ISPEC STM_f) FILTER_MEMOP_NONE)
    \\ RW_TAC bossLib.std_ss [IS_MEMOP_def]);

val FILTER_STM_MEMOPS_X =
  SIMP_RULE (bool_ss++boolSimps.LET_ss) [] FILTER_STM_MEMOPS_X;

val STM_TAC =
  PAT_ASSUM `Abbrev (q = NEXT_ARM6 (ARM6 dp ctrl) inp)` MP_TAC
   \\ ASM_SIMP_TAC (booli_ss++pairSimps.PAIR_ss++STM_ss++PBETA_ss)
        [SND_COND_RAND,FST_COND_RAND]
   \\ TRY ALU_ABBREV_TAC \\ STRIP_TAC
   \\ POP_ASSUM (fn th => FULL_SIMP_TAC (bossLib.std_ss++boolSimps.CONJ_ss)
        [OUT_ARM6_def,IS_MEMOP2_def,REWRITE_RULE [markerTheory.Abbrev_def] th]);

val _ = print "*\nVerifying output: stm\n*\n"; (*============================*)

val STM_MEMOPS = Count.apply prove(
  `!x. Abbrev (x = ^arm6state_inp) /\ Abbrev (x0 = SINIT INIT_ARM6 x) /\
    (DECODE_INST ireg = stm) /\ (aregn2 = 2w) /\
    CONDITION_PASSED (NZCV (CPSR_READ psr)) ireg ==>
    ~FST (DUR_X x0) ==>
    (OUT_ARM (ABS_ARM6 x.state) =
     OSMPL_ARM6 x0 (GENLIST
       (\t. OUT_ARM6 ((FUNPOW (SNEXT NEXT_ARM6) t x0).state)) (DUR_ARM6 x0)))`,
  REPEAT STRIP_TAC
    \\ ABBREV_TAC `nbs = DECODE_MODE ((4 >< 0) (CPSR_READ psr))`
    \\ ABBREV_TAC `w = LENGTH (REGISTER_LIST ((15 >< 0) ireg))`
    \\ MAP_EVERY IMP_RES_TAC [STM_INIT2,INIT_INIT,PROJ_IREG_COR]
    \\ ASM_SIMP_TAC (arith_ss++ICLASS_ss)
         [FUNPOW,ADVANCE_ZERO,STATE_ARM6_COR,OSMPL_ARM6_def,SINIT_def,
          SUC2NUM IMM_ARM6_def,state_inp_simp]
    \\ POP_LASTN_TAC 4
    \\ `~IS_RESET inp 0` by ASM_SIMP_TAC arith_ss []
    \\ IMP_RES_TAC NOT_RESET_EXISTS2
    \\ Cases_on `w`
    << [
      FULL_SIMP_TAC (std_ss++STATE_INP_ss) [Abbr`x`,SINIT_def,INIT_ARM6_def,
             IC_def,ABORTINST_def,NXTIC_def, DECODE_PSR_def]
        \\ SIMP_TAC (list_ss++STATE_INP_ss) [Abbr`x0`,GENLISTn,OUT_ARM6_def,
             IS_MEMOP2_def,FILTER_MEMOP_ONE,FILTER_MEMOP_SINGLETON,ADVANCE_def,
             SNEXT,numeral_funpow,SNOC,ABS_ARM6_def]
        \\ REPEAT (PAT_ABBREV_TAC `q = NEXT_ARM6 a b`)
        \\ `!mask. PENCZ stm ((15 >< 0) ireg) mask`
        by METIS_TAC [PENCZ_THM2,PENCZ_THM3,IN_LDM_STM]
        \\ STM_TAC
        \\ `REGISTER_LIST ((15 >< 0) ireg) = []` by METIS_TAC [LENGTH_NIL]
        \\ ASM_SIMP_TAC (stdi_ss++listSimps.LIST_ss) [OUT_ARM_def,
             DECODE_PSR_def,LDM_STM_def,STM_LIST_def,DECODE_LDM_STM_def,
             ADDR_MODE4_def,DECODE_INST_STM,ADDRESS_LIST_def,
             GENLIST,ZIP,MAP],
      Cases_on `n`
        << [
          FULL_SIMP_TAC (std_ss++STATE_INP_ss) [Abbr`x`,SINIT_def,
                  INIT_ARM6_def,IC_def,ABORTINST_def,NXTIC_def,DECODE_PSR_def]
            \\ `~IS_RESET inp 1` by ASM_SIMP_TAC arith_ss []
            \\ IMP_RES_TAC NOT_RESET_EXISTS2
            \\ SIMP_TAC (list_ss++STATE_INP_ss) [Abbr`x0`,GENLISTn,
                 OUT_ARM6_def,IS_MEMOP2_def,FILTER_MEMOP_ONE,
                 FILTER_MEMOP_SINGLETON,ADVANCE_def,SNEXT,numeral_funpow,
                 SNOC,ABS_ARM6_def]
            \\ REPEAT (PAT_ABBREV_TAC `q = NEXT_ARM6 a b`)
            \\ NTAC 2 STM_TAC
            \\ `LENGTH (FST (ADDR_MODE4 (ireg %% 24) (ireg %% 23)
                  (REG_READ6 reg nbs ((19 >< 16) ireg)) ((15 >< 0) ireg))) = 1`
            by METIS_TAC [LENGTH_ADDR_MODE4]
            \\ POP_ASSUM (ASSUME_TAC o (MATCH_MP LENGTH_ONE))
            \\ ASM_SIMP_TAC (stdi_ss++ARITH_ss++PBETA_ss)
                 ([Abbr`alu`,STM_PENCZ_ZERO,FILTER_MEMOP_SINGLETON,
                   IS_MEMOP2_def,OUT_ARM_def,DECODE_PSR_def,LDM_STM_def,
                   STM_LIST_def,LSL_ZERO,DECODE_LDM_STM_def,DECODE_INST_STM,
                   ADDRESS_LIST_def,MAP,MEMOP_def,GENLISTn,SNOC,IN_LDM_STM,
                   SND_ADDR_MODE4,MASKN_ZERO,GSYM WB_ADDRESS,GSYM FIRST_ADDRESS,
                   ALUOUT_ALU_logic,WORD_MULT_CLAUSES,num2exception_word3,
                   FST_HD_FST_ADDR_MODE4,LENGTH_ONE] @ finish_rws2)
            \\ POP_ASSUM SUBST1_TAC
            \\ ASM_SIMP_TAC arith_ss [ZIP,MAP,FST_HD_FST_ADDR_MODE4]
            \\ RW_TAC arith_ss finish_rws2
            \\ Cases_on `RP stm ((15 >< 0) ireg) Tw = 15w`
            \\ RW_TAC arith_ss ([REG_READ_WRITE_NEQ,REG_WRITE_READ_NEQ_15] @
                 finish_rws2),
          IMP_RES_TAC FILTER_STM_MEMOPS_X
            \\ ASM_SIMP_TAC list_ss [NULL_GENLIST,GENLISTn,FILTER_MEMOP_ONE,
                 ONCE_REWRITE_RULE [ADD_COMM] GENLIST_APPEND,
                 (GEN_ALL o INST [`b` |-> `2`] o SPEC_ALL) FUNPOW_COMP,
                 FILTER_MEMOP_SINGLETON,SNOC,HD_GENLIST,CONJUNCT1 FUNPOW]
            \\ POP_LAST_TAC \\ UNABBREV_TAC `nbs`
            \\ ABBREV_TAC `nbs = if ireg %% 22 then usr
                                 else DECODE_MODE ((4 >< 0) (CPSR_READ psr))`
            \\ IMP_RES_TAC STM_GENLIST_MEMOP_EQ
            \\ POP_ASSUM SUBST1_TAC
            \\ SIMP_TAC (bossLib.old_arith_ss++STATE_INP_ss)
                 [Abbr`x0`,Abbr`x`,SINIT_def,SNEXT,numeral_funpow]
            \\ REPEAT (PAT_ABBREV_TAC `q = NEXT_ARM6 a b`)
            \\ FULL_SIMP_TAC (bossLib.std_ss++STATE_INP_ss) [INIT_ARM6,IC_def,
                 ABORTINST_def,NXTIC_def,DECODE_PSR_def]
            \\ FULL_SIMP_TAC (bossLib.std_ss++STATE_INP_ss)
                 [ADVANCE_def,OUT_ARM6_def,IS_MEMOP2_def,ABS_ARM6_def]
            \\ `~IS_RESET inp 1` by ASM_SIMP_TAC arith_ss []
            \\ IMP_RES_TAC NOT_RESET_EXISTS2 \\ POP_LAST_TAC
            \\ NTAC 2 STM_TAC
            \\ ASM_SIMP_TAC (bossLib.old_arith_ss++STATE_INP_ss) [MASK_def,
                 STM_PENCZ_ZERO,STM_PENCZ_ONE,LSL_ZERO,MASKN_1,MASKN_2,
                 GSYM ADVANCE_COMP,iseq_distinct]
            \\ UNABBREV_TAC `nbs`
            \\ ABBREV_TAC `cpsr = CPSR_READ psr`
            \\ ABBREV_TAC `nbs = DECODE_MODE ((4 >< 0) cpsr)`
            \\ `1 < SUC (SUC n')` by DECIDE_TAC
            \\ `!t. t < SUC (SUC n') ==> ~IS_RESET inp t`
            by ASM_SIMP_TAC arith_ss []
            \\ IMP_RES_TAC NEXT_CORE_STM_TN_W1
            \\ POP_ASSUM (STRIP_ASSUME_TAC o
                 (CONV_RULE (TOP_DEPTH_CONV (CHANGED_CONV (SKOLEM_CONV)))))
            \\ `SUC n' = SUC (SUC n') - 1` by DECIDE_TAC
            \\ POP_ASSUM SUBST1_TAC
            \\ ASM_SIMP_TAC (bossLib.std_ss++STATE_INP_ss) [OUT_ARM6_def]
            \\ POP_LAST_TAC
            \\ `LENGTH (FST (ADDR_MODE4 (ireg %% 24) (ireg %% 23)
                  (REG_READ6 reg nbs ((19 >< 16) ireg)) ((15 >< 0) ireg))) =
                SUC (SUC n')`
            by PROVE_TAC [LENGTH_ADDR_MODE4]
            \\ ASM_SIMP_TAC (stdi_ss++PBETA_ss++listSimps.LIST_ss++ARITH_ss)
                 ([Abbr`alu`,Abbr`alu1`,combinTheory.o_ABS_R,word_mul_n2w,
                   LSL_ZERO,ABS_ARM6_def,MEMOP_def,MAP_STM_MEMOP,OUT_ARM_def,
                   DECODE_PSR_def,LDM_STM_def,DECODE_LDM_STM_def,IN_LDM_STM,
                   SND_ADDR_MODE4,DECODE_INST_STM,ADDRESS_LIST_def,MAP_GENLIST,
                   WORD_ADD_0,STM_LIST_def,SND_ADDR_MODE4,GSYM WB_ADDRESS,
                   GSYM FIRST_ADDRESS,FST_HD_FST_ADDR_MODE4,ZIP_GENLIST,
                   LENGTH_GENLIST,num2exception_word3] @ finish_rws2)
            \\ ASM_SIMP_TAC list_ss [(GEN_ALL o SPEC `SUC n`) GENLIST_CONS,
                 FST_HD_FST_ADDR_MODE4,WORD_ADD_0]
            \\ CONJ_TAC
            << [
              RW_TAC arith_ss finish_rws2
                \\ Cases_on `RP stm ((15 >< 0) ireg) Tw = 15w`
                \\ RW_TAC arith_ss
                     ([REG_READ_WRITE_NEQ,REG_WRITE_READ_NEQ_15] @ finish_rws2),
              MATCH_MP_TAC GENLIST_FUN_EQ
                \\ SIMP_TAC arith_ss [GSYM ADD1]
                \\ `SUC n' < LENGTH (REGISTER_LIST ((15 >< 0) ireg))`
                by ASM_SIMP_TAC arith_ss [LENGTH_ADDR_MODE4]
                \\ RW_TAC arith_ss ([REG_READ_WRITE_NEQ,REG_WRITE_READ_NEQ_15,
                     (GSYM o CONJUNCT2) EL,GSYM REGISTER_LIST_STM_THM] @
                     finish_rws2)
                \\ PAT_ASSUM `q = (19 >< 16) ireg` (SUBST1_TAC o SYM)
                << (let fun tac x = Cases_on `RP stm ((15 >< 0) ireg)
                              (MASKN (SUC (^x)) ((15 >< 0) ireg)) = 15w` \\
                        RW_TAC arith_ss ([REG_READ_WRITE_NEQ,RP_NOT_EQUAL_ZERO,
                          REG_WRITE_READ_NEQ_15] @ finish_rws2) in
                  [tac ``n':num``, tac ``x:num``, tac ``n':num``, tac ``x:num``]
                   end)]]]);

val _ = print "*\nVerifying time-consistency and correctness: stm\n*\n"; (*==*)

val STM = Count.apply prove(
  `!x. Abbrev (x = ^arm6state_inp) /\ inp IN STRM_ARM6 /\
       Abbrev (x0 = SINIT INIT_ARM6 x) /\
       (DECODE_INST ireg = stm) /\ (aregn2 = 2w) /\
       CONDITION_PASSED (NZCV (CPSR_READ psr)) ireg ==>
       ~FST (DUR_X x0) ==>
       (let s = (FUNPOW (SNEXT NEXT_ARM6) (DUR_ARM6 x0) x0).state in
          (INIT_ARM6 s = s) /\
          (STATE_ARM 1 <|state := ABS_ARM6 x.state; inp := SMPL_ARM6 x|> =
           ABS_ARM6 s))`,
  REPEAT STRIP_TAC
    \\ ABBREV_TAC `nbs = DECODE_MODE ((4 >< 0) (CPSR_READ psr))`
    \\ ABBREV_TAC `w = LENGTH (REGISTER_LIST ((15 >< 0) ireg))`
    \\ MAP_EVERY IMP_RES_TAC [STM_INIT2,INIT_INIT,PROJ_IREG_COR]
    \\ `(x.inp = inp) /\ (x.state = ^arm6state) /\
        (<|state := x0.state; inp := inp|> = x0)`
    by SIMP_TAC (std_ss++STATE_INP_ss) [Abbr`x`,Abbr`x0`,SINIT_def]
    \\ ASM_SIMP_TAC (srw_ss()++boolSimps.LET_ss++SIZES_ss) [num2exception_thm,
         SUC2NUM STATE_ARM_def,ABS_ARM6_def,SMPL_ARM6_def,SMPL_DATA_ARM6_def,
         IFLAGS_def,ADVANCE_ZERO,DECODE_PSR_def,PACK_def,IMM_LEN_def,
         SUC2NUM IMM_ARM6_def,MAP_STRM_def,COMBINE_def,SMPL_EXC_ARM6_def,
         STATE_ARM6_COR,FUNPOW,ADVANCE_ZERO,OSMPL_ARM6_def,SINIT_def,
         SUC2NUM IMM_ARM6_def,state_inp_simp]
    \\ POP_LASTN_TAC 7
    \\ PAT_ABBREV_TAC `s = (FUNPOW (SNEXT NEXT_ARM6) d x0).state`
    \\ POP_ASSUM MP_TAC
    \\ ONCE_REWRITE_TAC [ADD_COMM] \\ REWRITE_TAC [FUNPOW_COMP]
    \\ PAT_ASSUM `~FST (DUR_X x0)` MP_TAC
    \\ ASM_SIMP_TAC (bossLib.std_ss++STATE_INP_ss)
         [Abbr`x`,Abbr`x0`,ADVANCE_def,SINIT_def,SNEXT,numeral_funpow]
    \\ ASM_SIMP_TAC stdi_ss [DUR_X2,DUR_IC_def,INIT_ARM6] \\ POP_LAST_TAC
    \\ STRIP_TAC
    \\ `~IS_RESET inp 0 /\ ~IS_RESET inp 1` by ASM_SIMP_TAC arith_ss []
    \\ IMP_RES_TAC NOT_RESET_EXISTS2
    \\ iclass_compLib.STM_TAC \\ ALU_ABBREV_TAC
    \\ SIMP_TAC (stdi_ss++boolSimps.CONJ_ss++PBETA_ss)
         [FST_COND_RAND,SND_COND_RAND,LSL_ZERO,MASKN_1]
    \\ Cases_on `(15 >< 0) ireg = 0w:word16`
    \\ ASM_SIMP_TAC stdi_ss [PENCZ_THM3,IN_LDM_STM]
    << [
      IMP_RES_TAC PENCZ_THM2
        \\ ASM_SIMP_TAC (arith_ss++STATE_INP_ss) [Abbr`w`,FUNPOW]
        \\ STRIP_TAC \\ UNABBREV_TAC `s` \\ CONJ_TAC >> FINISH_OFF
        \\ IMP_RES_TAC DECODE_INST_STM
        \\ ASM_SIMP_TAC (stdi_ss++STATE_INP_ss)
             ([Abbr`alu`,LSL_ZERO,ALUOUT_ALU_logic,WB_ADDRESS_ZERO,IN_LDM_STM,
               (REWRITE_RULE [] o SPEC `0w`) PENCZ_THM2] @ finish_rws3)
        \\ RW_TAC std_ss finish_rws2,
      `~PENCZ stm ((15 >< 0) ireg) Tw`
          by (FULL_SIMP_TAC std_ss [PENCZ_THM2] \\
              METIS_TAC [STM_PENCZ_ZERO,NOT_ZERO_LT_ZERO])
        \\ Cases_on `w = 1`
        << [
          `PENCZ stm ((15 >< 0) ireg) (MASKN 1 ((15 >< 0) ireg))`
            by PROVE_TAC [PENCZ_THM,IN_LDM_STM]
            \\ ASM_SIMP_TAC (arith_ss++STATE_INP_ss) [Abbr`w`,FUNPOW]
            \\ STRIP_TAC \\ UNABBREV_TAC `s` \\ CONJ_TAC >> FINISH_OFF
            \\ IMP_RES_TAC DECODE_INST_STM
            \\ ASM_SIMP_TAC (stdi_ss++ARITH_ss++STATE_INP_ss)
                 ([Abbr`alu`,LSL_ZERO,ALUOUT_ALU_logic,GSYM WB_ADDRESS,
                   IN_LDM_STM] @ finish_rws3)
            \\ RW_TAC std_ss finish_rws2,
          `1 < w` by FULL_SIMP_TAC arith_ss [Abbr`w`,PENCZ_THM2]
            \\ `~(PENCZ stm ((15 >< 0) ireg) (MASKN 1 ((15 >< 0) ireg)))`
            by PROVE_TAC [PENCZ_THM,IN_LDM_STM]
            \\ ASM_SIMP_TAC stdi_ss [LSL_ZERO,MASK_def,GSYM ADVANCE_COMP]
            \\ IMP_RES_TAC (simpLib.SIMP_PROVE arith_ss []
                 ``!w. 1 < w ==> (!t. t < 2 + (w - 1) ==> ~IS_RESET i t) ==>
                  (!t. t < SUC w ==> ~IS_RESET i t)``)
            \\ ABBREV_TAC `cpsr = CPSR_READ psr`
            \\ IMP_RES_TAC NEXT_CORE_STM_TN_W1
            \\ POP_ASSUM (STRIP_ASSUME_TAC o
                 (CONV_RULE (TOP_DEPTH_CONV (CHANGED_CONV (SKOLEM_CONV)))))
            \\ ASM_SIMP_TAC (stdi_ss++STATE_INP_ss) [MASKN_2]
            \\ POP_ASSUM (ASSUME_TAC o GEN_ALL o (MATCH_MP
                 (DECIDE ``a /\ b /\ c /\ d ==> a /\ b /\ c``)) o SPEC_ALL)
            \\ PAT_TAC 25
            \\ `~(aregn IN {0w; 1w; 2w; 5w}) /\
                ((aregn = 7w) ==> ~(CPSR_READ psr %% 6)) /\
                ((aregn = 6w) ==> ~(CPSR_READ psr %% 7))`
            by METIS_TAC []
            \\ RM_ABBREV_TAC `aregn`
            \\ PAT_ASSUM `!sctrlreg reg psrfb. P` (K ALL_TAC)
            \\ STRIP_TAC \\ UNABBREV_TAC `s` \\ CONJ_TAC
            << [
              FINISH_OFF
                \\ FULL_SIMP_TAC (std_ss++PRED_SET_ss++SIZES_ss) [n2w_11],
              IMP_RES_TAC DECODE_INST_STM
                \\ ASM_SIMP_TAC (stdi_ss++ARITH_ss++STATE_INP_ss)
                     ([Abbr`alu`,Abbr`cpsr`,LSL_ZERO,ALUOUT_ALU_logic,
                       GSYM WB_ADDRESS,IN_LDM_STM] @ finish_rws3)
                \\ RW_TAC std_ss finish_rws2]]]);

(* ------------------------------------------------------------------------- *)

val lem = (GEN_ALL o BETA_RULE o
  ISPEC `\t. OUT_ARM6 ((FUNPOW (SNEXT NEXT_ARM6) t x).state)`) FILTER_MEMOP_ALL;

val _ = print "*\nVerifying output\n*\n"; (*=================================*)

val ARM6_OUT_THM = prove(
  `!x. (x = ^arm6state_inp) ==> inp IN STRM_ARM6 ==>
   (OUTPUT ARM_SPEC <|state := ABS_ARM6 x.state; inp := SMPL_ARM6 x|> 0 =
      OSMPL OSMPL_ARM6 ARM6_SPEC IMM_ARM6 (x,OUTPUT ARM6_SPEC x) 0)`,
  RW_TAC std_ss []
    \\ SIMP_TAC (srw_ss()++boolSimps.LET_ss) [OUTPUT_def,ARM_SPEC_def,
         ARM6_SPEC_def,STATE_ARM6_COR,STATE_ARM_def,FUNPOW,ADVANCE_ZERO,
         IMM_LEN_def,OSMPL_def,SINIT_def,SUC2NUM IMM_ARM6_def,MAP_STRM_def,
         PACK_def]
    \\ ABBREV_TAC `x = ^arm6state_inp` \\ ABBREV_TAC `x0 = SINIT INIT_ARM6 x`
    \\ `(<|state := INIT_ARM6 (^arm6state); inp := inp|> = x0)`
    by RW_TAC std_ss [Abbr`x`,Abbr`x0`,SINIT_def]
    \\ POP_ASSUM SUBST1_TAC
    \\ `^arm6state = x.state` by RW_TAC std_ss [Abbr`x`]
    \\ POP_ASSUM SUBST1_TAC
    \\ IMP_RES_TAC INIT_INIT
    \\ Cases_on `FST (DUR_X x0) \/ (DECODE_INST ireg = mcr) \/
       (DECODE_INST ireg = ldc) \/ (DECODE_INST ireg = stc)`
    << [ (* reset *)
      ASM_SIMP_TAC (std_ss++STATE_INP_ss) [Abbr`x`,ABS_ARM6_def,OSMPL_ARM6_def],
      FULL_SIMP_TAC std_ss []
        \\ Cases_on `(aregn2 = 2w:word3) ==>
             ~CONDITION_PASSED (NZCV (CPSR_READ psr)) ireg`
        << [ (* exception or not executed *)
          IMP_RES_TAC NON_MEMOPS_UNEXEC
            \\ FULL_SIMP_TAC stdi_ss [IMP_DISJ_THM,OSMPL_ARM6_def,MAP]
            \\ ASM_SIMP_TAC (std_ss++STATE_INP_ss) [Abbr`x`,ABS_ARM6_def,
                 OUT_ARM_def,DECODE_PSR_def,num2exception_word3],
          FULL_SIMP_TAC bool_ss []
            \\ `2w:word3 = 2w` by SIMP_TAC (std_ss++SIZES_ss) [n2w_11]
            \\ Cases_on `DECODE_INST ireg = ldm` >> IMP_RES_TAC LDM_MEMOPS
            \\ Cases_on `DECODE_INST ireg = stm` >> IMP_RES_TAC STM_MEMOPS
            \\ Cases_on `DECODE_INST ireg IN {swp; ldr; str}`
            >> IMP_RES_TAC BASIC_MEMOPS
            \\ Cases_on `DECODE_INST ireg IN {mrs_msr; data_proc;
                 reg_shift; br; swi_ex; unexec}`
            << [
              IMP_RES_TAC NON_MEMOPS \\ POP_LASTN_TAC 2
                \\ FULL_SIMP_TAC (stdi_ss++PRED_SET_ss++STATE_INP_ss)
                     [Abbr`x`,OSMPL_ARM6_def,ABS_ARM6_def,OUT_ARM_def,
                      DECODE_PSR_def,MAP],
              Cases_on `DECODE_INST ireg IN {cdp_und; mrc}`
                << [
                  IMP_RES_TAC CP_MEMOPS \\ POP_LAST_TAC \\ IMP_RES_TAC lem
                    \\ ASM_SIMP_TAC (stdi_ss++STATE_INP_ss) [Abbr`x`,
                         OSMPL_ARM6_def,ABS_ARM6_def,OUT_ARM_def,
                         DECODE_PSR_def,MAP,CP_NOT,CP_NOT2],
                  `DECODE_INST ireg = mla_mul`
                    by (Cases_on `DECODE_INST ireg` \\
                        FULL_SIMP_TAC (bossLib.bool_ss++PRED_SET_ss) [])
                    \\ IMP_RES_TAC MEM_MLA_MUL \\ POP_LAST_TAC
                    \\ IMP_RES_TAC lem
                    \\ ASM_SIMP_TAC (stdi_ss++STATE_INP_ss)
                         [Abbr`x`,OSMPL_ARM6_def,ABS_ARM6_def,OUT_ARM_def,
                          DECODE_PSR_def,MAP]]]]]);

val ARM6_OUT_THM = GEN_ALL (SIMP_RULE (srw_ss()) [] ARM6_OUT_THM);

(* ------------------------------------------------------------------------- *)

val FST_DUR_X = prove(
   `!x. FST (DUR_X x) ==>
       (?t. IS_RESET x.inp t) /\
       (DUR_ARM6 x =
        (LEAST t.  IS_RESET x.inp t /\ ~IS_RESET x.inp (t + 1) /\
                  ~IS_RESET x.inp (t + 2)) + 3)`,
  Cases \\ Cases_on_arm6 `a`
    \\ RW_TAC std_ss [DUR_X_def,DECODE_PSR_def,DUR_ARM6_def]
    \\ METIS_TAC []);

val _ = print "*\nVerifying time-consistency\n*\n"; (*=======================*)

val ARM6_TCON_LEM1 = prove(
  `!x. (x = ^arm6state_inp) ==> inp IN STRM_ARM6 ==>
       (INIT_ARM6 (STATE_ARM6 (IMM_ARM6 x 1) x) = STATE_ARM6 (IMM_ARM6 x 1) x)`,
  RW_TAC bool_ss []
    \\ SIMP_TAC (srw_ss()++boolSimps.LET_ss) [ARM6_SPEC_def,STATE_ARM6_COR,
         FUNPOW,ADVANCE_ZERO,SINIT_def,SUC2NUM IMM_ARM6_def]
    \\ ABBREV_TAC `x = ^arm6state_inp` \\ ABBREV_TAC `x0 = SINIT INIT_ARM6 x`
    \\ `(<|state := INIT_ARM6 (^arm6state); inp := inp|> = x0)`
    by RW_TAC std_ss [Abbr`x`,Abbr`x0`,SINIT_def]
    \\ POP_ASSUM SUBST1_TAC
    \\ Cases_on `FST (DUR_X x0)`
    << [ (* reset *)
      PAT_ASSUM `inp IN STRM_ARM6` (fn th => `x0.inp IN STRM_ARM6`
        by ASM_SIMP_TAC (std_ss++STATE_INP_ss) [Abbr`x0`,Abbr`x`,SINIT_def,th])
        \\ MAP_EVERY IMP_RES_TAC [FST_DUR_X,LEAST_NOT_RESET]
        \\ PAT_ASSUM `IS_RESET x0.inp t` (K ALL_TAC)
        \\ MAP_EVERY IMP_RES_TAC [LEAST_RESET_GT_TWO,PREVIOUS_THREE_RESET]
        \\ REPEAT (PAT_ASSUM `~a ==> b` (K ALL_TAC))
        \\ IMP_RES_TAC (DECIDE ``!n. (2 < n) ==> (n = n - 3 + 3)``)
        \\ POP_ASSUM (fn th => ONCE_REWRITE_TAC [th] \\
             RULE_ASSUM_TAC (ONCE_REWRITE_RULE [th]))
        \\ ASM_REWRITE_TAC [DECIDE ``!a. a + 3 + 3 = 6 + a``]
        \\ REWRITE_TAC [FUNPOW_COMP]
        \\ PAT_ABBREV_TAC `y = FUNPOW (SNEXT NEXT_ARM6) xt x0`
        \\ RULE_ASSUM_TAC (ONCE_REWRITE_RULE [GSYM STATE_FUNPOW_INIT2])
        \\ UNABBREV_TAC `y`
        \\ PAT_ABBREV_TAC `y = (FUNPOW (SNEXT NEXT_ARM6) xt x0).state`
        \\ IMP_RES_TAC SPEC_AFTER_NRESET2
        \\ POP_ASSUM (SPEC_THEN `y` ASSUME_TAC)
        \\ FULL_SIMP_TAC (arith_ss++STATE_INP_ss) [AFTER_NRESET2_THM3],
      Cases_on `(aregn2 = 2w) ==> ~CONDITION_PASSED (NZCV (CPSR_READ psr)) ireg`
        >> IMP_RES_TAC (SIMP_RULE std_ss [] NON_MEMOPS_UNEXEC)
        \\ FULL_SIMP_TAC bool_ss []
        \\ `2w:word3 = 2w` by SIMP_TAC (std_ss++SIZES_ss) [n2w_11]
        \\ `DECODE_INST ireg IN {cdp_und; mrc; mcr; stc; ldc} \/
            DECODE_INST ireg IN {mrs_msr; data_proc; reg_shift;
              br; swi_ex; unexec} \/
            DECODE_INST ireg IN {swp; ldr; str} \/
            (DECODE_INST ireg = mla_mul) \/
            (DECODE_INST ireg = ldm) \/
            (DECODE_INST ireg = stm)`
        by (SIMP_TAC (std_ss++PRED_SET_ss) [] \\
            Cases_on `DECODE_INST ireg` \\ ASM_REWRITE_TAC [])
        << (map (IMP_RES_TAC o (SIMP_RULE std_ss []))
              [CP_TC,NON_MEMOPS,BASIC_MEMOPS,MLA_MUL,LDM,STM])
    ] (* reset *)
);

val ARM6_TCON_ONE = GEN_ALL (SIMP_RULE bool_ss [] ARM6_TCON_LEM1);

val _ = print "*\nVerifying correctness\n*\n"; (*============================*)

val ARM6_COR_LEM1 = prove(
  `!x. (x = ^arm6state_inp) ==> inp IN STRM_ARM6 ==>
       (STATE_ARM 1 <|state := ABS_ARM6 x.state; inp := SMPL_ARM6 x|> =
        ABS_ARM6 (STATE_ARM6 (IMM_ARM6 x 1) x))`,
  RW_TAC bool_ss []
    \\ SIMP_TAC (srw_ss()++boolSimps.LET_ss) [ARM6_SPEC_def,STATE_ARM6_COR,
         FUNPOW,ADVANCE_ZERO,SINIT_def,SUC2NUM IMM_ARM6_def]
    \\ ABBREV_TAC `x = ^arm6state_inp` \\ ABBREV_TAC `x0 = SINIT INIT_ARM6 x`
    \\ `^arm6state = x.state` by RW_TAC std_ss [Abbr`x`]
    \\ `(<|state := INIT_ARM6 (^arm6state); inp := inp|> = x0)`
    by RW_TAC std_ss [Abbr`x`,Abbr`x0`,SINIT_def]
    \\ NTAC 2 (POP_ASSUM SUBST1_TAC)
    \\ Cases_on `FST (DUR_X x0)`
    << [
      PAT_ASSUM `inp IN STRM_ARM6` (fn th => `x0.inp IN STRM_ARM6`
        by ASM_SIMP_TAC (std_ss++STATE_INP_ss) [Abbr`x0`,Abbr`x`,SINIT_def,th])
        \\ MAP_EVERY IMP_RES_TAC [FST_DUR_X,LEAST_NOT_RESET]
        \\ `<|state := x0.state; inp := x.inp|> = x0`
        by SIMP_TAC (std_ss++STATE_INP_ss) [Abbr`x`,Abbr`x0`,SINIT_def]
        \\ ASM_SIMP_TAC (arith_ss++STATE_INP_ss)
             [SUC2NUM STATE_ARM_def,SMPL_ARM6_def,COMBINE_def,SMPL_EXC_ARM6_def,
              SMPL_DATA_ARM6_def,SUC2NUM IMM_ARM6_def,SUC2NUM STATE_ARM6_COR,
              MAP_STRM_def,FUNPOW,ADVANCE_ZERO,NEXT_ARM_def]
        \\ POP_LAST_TAC
        \\ PAT_ASSUM `IS_RESET x0.inp t` (K ALL_TAC)
        \\ MAP_EVERY IMP_RES_TAC [LEAST_RESET_GT_TWO,PREVIOUS_THREE_RESET]
        \\ REPEAT (PAT_ASSUM `~a ==> b` (K ALL_TAC))
        \\ IMP_RES_TAC (DECIDE ``!n. (2 < n) ==> (n = n - 3 + 3)``)
        \\ POP_ASSUM (fn th => ONCE_REWRITE_TAC [th] \\
              RULE_ASSUM_TAC (ONCE_REWRITE_RULE [th]))
        \\ ASM_REWRITE_TAC [DECIDE ``!a. a + 3 + 3 = 6 + a``]
        \\ REWRITE_TAC [FUNPOW_COMP]
        \\ PAT_ABBREV_TAC `y = FUNPOW (SNEXT NEXT_ARM6) xt x0`
        \\ RULE_ASSUM_TAC (ONCE_REWRITE_RULE [GSYM STATE_FUNPOW_INIT2])
        \\ UNABBREV_TAC `y`
        \\ PAT_ABBREV_TAC `y = (FUNPOW (SNEXT NEXT_ARM6) xt x0).state`
        \\ IMP_RES_TAC SPEC_AFTER_NRESET2
        \\ POP_ASSUM (SPEC_THEN `y` ASSUME_TAC)
        \\ POP_ASSUM_LIST (fn thl => ASSUME_TAC (hd thl))
        \\ FULL_SIMP_TAC arith_ss [AFTER_NRESET2_THM4],
      Cases_on `(aregn2 = 2w) ==> ~CONDITION_PASSED (NZCV (CPSR_READ psr)) ireg`
        >> IMP_RES_TAC (SIMP_RULE std_ss [] NON_MEMOPS_UNEXEC)
        \\ FULL_SIMP_TAC bool_ss []
        \\ `2w:word3 = 2w` by SIMP_TAC (std_ss++SIZES_ss) [n2w_11]
        \\ `DECODE_INST ireg IN {cdp_und; mrc; mcr; stc; ldc} \/
            DECODE_INST ireg IN {mrs_msr; data_proc; reg_shift;
              br; swi_ex; unexec} \/
            DECODE_INST ireg IN {swp; ldr; str} \/
            (DECODE_INST ireg = mla_mul) \/
            (DECODE_INST ireg = ldm) \/
            (DECODE_INST ireg = stm)`
        by (SIMP_TAC (std_ss++PRED_SET_ss) [] \\
            Cases_on `DECODE_INST ireg` \\ ASM_REWRITE_TAC [])
        << (map (IMP_RES_TAC o (SIMP_RULE std_ss []))
              [CP_TC,NON_MEMOPS,BASIC_MEMOPS,MLA_MUL,LDM,STM])
    ] (* reset *)
);

val ARM6_COR_ONE = GEN_ALL (SIMP_RULE (std_ss++STATE_INP_ss) [] ARM6_COR_LEM1);

(* ------------------------------------------------------------------------- *)

val DUR_IC_WELL = prove(
  `!ic ireg rs iflags inp. 0 < DUR_IC ic ireg rs iflags inp`,
  RW_TAC arith_ss [DUR_IC_def]);

val DUR_ARM6_WELL = store_thm("DUR_ARM6_WELL",
  `!x. 0 < DUR_ARM6 x`,
  Cases \\ Cases_on_arm6 `a`
    \\ RW_TAC arith_ss [DECODE_PSR_def,DUR_ARM6_def,DUR_X_def,DUR_IC_WELL]);

val IMM_ARM6_THM = store_thm("IMM_ARM6_THM",
  `UIMMERSION IMM_ARM6 ARM6_SPEC DUR_ARM6`,
  RW_TAC stdi_ss [UIMMERSION_def,DUR_ARM6_WELL,IMM_ARM6_def,ARM6_SPEC_def]);

val IMM_ARM6_UNIFORM = store_thm("IMM_ARM6_UNIFORM",
  `UNIFORM IMM_ARM6 ARM6_SPEC`,
  REWRITE_TAC [UNIFORM_def]
    \\ EXISTS_TAC `DUR_ARM6`
    \\ REWRITE_TAC [IMM_ARM6_THM]);

val IMM_ARM6_ONE =
  MATCH_MP UIMMERSION_ONE (CONJ STATE_ARM6_IMAP_INIT IMM_ARM6_THM);

(* ------------------------------------------------------------------------- *)

val ARM6_DATA_ABSTRACTION = store_thm("ARM6_DATA_ABSTRACTION",
  `DATA_ABSTRACTION ABS_ARM6
    (state_out_state o ARM6_SPEC 0) (state_out_state o ARM_SPEC 0)`,
  RW_TAC bool_ss [MATCH_MP DATA_ABSTRACTION_I
           (CONJ STATE_ARM_THM3 STATE_ARM6_IMAP_INIT)]
    \\ Cases_on `a`
    \\ Q.MATCH_ABBREV_TAC `?b. ABS_ARM6 (INIT_ARM6 b) = ARM_EX s c e`
    \\ Q.RM_ALL_ABBREVS_TAC \\ Cases_on `s`
    \\ EXISTS_TAC `ARM6 (DP (ADD8_PC f) f0 areg din alua alub dout)
     (CTRL pipea pipeaval pipeb pipebval c iregval ointstart onewinst endinst
       obaselatch opipebll nxtic nxtis nopc1 oorst resetlatch onfq ooonfq
       oniq oooniq pipeaabt pipebabt iregabt2 dataabt2 (n2w (exception2num e))
       mrq2 nbw nrw sctrlreg psrfb oareg mask orp oorp mul mul2 borrow2 mshift)`
    \\ SIMP_TAC std_ss [ABS_ARM6_def,SUB8_INV,INIT_ARM6_def]
    \\ Cases_on `e` \\ SIMP_TAC (std_ss++SIZES_ss)
         [exception2num_thm,num2exception_thm,w2n_n2w]);

(* ------------------------------------------------------------------------- *)

val STRM_ARM6_LEM = prove(
  `!x. (x = ^arm6state_inp) ==>
       inp IN STRM_ARM6 ==> PROJ_NRESET (inp (IMM_ARM6 x 1 - 1))`,
  REPEAT STRIP_TAC
    \\ ASM_SIMP_TAC (srw_ss()++boolSimps.LET_ss++STATE_INP_ss) [IFLAGS_def,
         IMM_ARM6_ONE,INIT_ARM6_def,DUR_ARM6_def,DUR_X,DECODE_PSR_def]
    \\ COND_CASES_TAC
    << [
      POP_ASSUM MP_TAC \\ PAT_ABBREV_TAC `d = DUR_IC xic xireg xrs xiflags xi`
        \\ STRIP_TAC \\ FULL_SIMP_TAC std_ss []
        \\ POP_ASSUM (SPEC_THEN `d - 1` ASSUME_TAC)
        \\ UNABBREV_TAC `d`
        \\ FULL_SIMP_TAC arith_ss [IS_RESET_def,DUR_IC_WELL],
      FULL_SIMP_TAC std_ss [(REWRITE_RULE [PROVE [] ``(~a = b) = (a = ~b)``] o
              GSYM) IS_RESET_def]
        \\ IMP_RES_TAC LEAST_NOT_RESET
        \\ ASM_SIMP_TAC arith_ss []]);

val lem = simpLib.SIMP_PROVE (srw_ss())
  [io_onestepTheory.state_inp_component_equality]
  ``state_inp a b = <|state:= a; inp := b|>``;

val STRM_ARM6_LEMb = prove(
  `!x. x.inp IN STRM_ARM6 ==> ~IS_RESET x.inp (IMM_ARM6 x 1 - 1)`,
  Cases \\ Cases_on_arm6 `a` \\ SIMP_TAC (std_ss++STATE_INP_ss)
    [lem,IS_RESET_def,GEN_ALL (SIMP_RULE bool_ss [] STRM_ARM6_LEM)]);

val STRM_ARM6_THM = store_thm("STRM_ARM6_THM",
  `!x t. x.inp IN STRM_ARM6 ==> (ADVANCE (IMM_ARM6 x 1) x.inp) IN STRM_ARM6`,
  REPEAT STRIP_TAC \\ IMP_RES_TAC STRM_ARM6_LEMb
    \\ FULL_SIMP_TAC bool_ss [IN_DEF,STRM_ARM6_def,ADVANCE_def,IS_RESET_def,
         IS_BUSY_def,IS_ABSENT_def]
    \\ REPEAT STRIP_TAC
    << [
      PAT_ASSUM `!t. ~PROJ_NRESET (x.inp t) ==> b`
        (SPEC_THEN `IMM_ARM6 x 1 + t` IMP_RES_TAC)
        \\ Cases_on `t`
        \\ FULL_SIMP_TAC arith_ss [ADD1],
      PAT_ASSUM `!t. ?t2.  t < t2 /\ PROJ_NRESET (x.inp t2) /\ b`
        (SPEC_THEN `IMM_ARM6 x 1 + t` STRIP_ASSUME_TAC),
      PAT_ASSUM `!t. ?t2. P`
        (SPEC_THEN `IMM_ARM6 x 1 + t` STRIP_ASSUME_TAC),
      PAT_ASSUM `!t. ~PROJ_CPB (x.inp t) ==> p`
        (SPEC_THEN `IMM_ARM6 x 1 + t` IMP_RES_TAC)]
    \\ EXISTS_TAC `t2 - IMM_ARM6 x 1`
        \\ ASM_SIMP_TAC arith_ss []);

val ARM6_STREAM_ABSTRACTION = store_thm("ARM6_STREAM_ABSTRACTION",
  `STREAM_ABSTRACTION SMPL_ARM6 UNIV STRM_ARM6`,
  RW_TAC std_ss [STREAM_ABSTRACTION_def,pred_setTheory.IN_UNIV]
    \\ EXISTS_TAC `\t. (T,T,F,F,word_0,T,T)`
    \\ SIMP_TAC std_ss [IN_DEF,STRM_ARM6_def,IS_RESET_def,IS_ABSENT_def,
           IS_BUSY_def,PROJ_NRESET_def,PROJ_CPA_def,PROJ_CPB_def]
    \\ STRIP_TAC \\ EXISTS_TAC `t + 1` \\ DECIDE_TAC);

(* ------------------------------------------------------------------------- *)

val ARM6_TCON_LEM0 = store_thm("ARM6_TCON_LEM0",
  `!x. (x = ^arm6state_inp) ==>
   (INIT_ARM6 (STATE_ARM6 (IMM_ARM6 x 0) x) = STATE_ARM6 (IMM_ARM6 x 0) x)`,
   RW_TAC bool_ss []
     \\ SIMP_TAC (std_ss++STATE_INP_ss)
          [STATE_ARM6_def,IMM_ARM6_def,INIT_ARM6_def,NXTIC_def,MASK_def]);

val ARM6_TCON_ZERO = GEN_ALL (SIMP_RULE bool_ss [] ARM6_TCON_LEM0);

val INIT = REWRITE_RULE [GSYM FUN_EQ_THM] (CONJUNCT1 STATE_ARM6_def);

val ARM6_TIME_CON_IMM = store_thm("ARM6_TIME_CON_IMM",
  `TCON_IMMERSION ARM6_SPEC IMM_ARM6 STRM_ARM6`,
  SIMP_TAC bool_ss [STRM_ARM6_THM,MATCH_MP TCON_IMMERSION_ONE_STEP_THM
    (CONJ STATE_ARM6_IMAP_INIT IMM_ARM6_UNIFORM)]
    \\ REPEAT STRIP_TAC
    \\ Cases_on `x` \\ Cases_on_arm6 `a`
    \\ FULL_SIMP_TAC (std_ss++STATE_INP_ss) [lem,ARM6_SPEC_STATE,INIT,
         ARM6_TCON_ZERO,ARM6_TCON_ONE]);

(* ------------------------------------------------------------------------- *)

val lem2 = prove(
  `(!t1 t2 i. IS_ABORT (ADVANCE t1 i) t2 = IS_ABORT i (t1 + t2)) /\
    !t1 t2 i. IS_BUSY (ADVANCE t1 i) t2 = IS_BUSY i (t1 + t2)`,
  REPEAT STRIP_TAC
    \\ REWRITE_TAC [FUN_EQ_THM]
    \\ SIMP_TAC arith_ss [IS_ABORT_def,IS_BUSY_def,ADVANCE_def]);

val TCON_SMPL_ARM6 = prove(
  `TCON_SMPL SMPL_ARM6 IMM_ARM6 ARM6_SPEC STRM_ARM6`,
  RW_TAC std_ss [TCON_SMPL_def]
    \\ REWRITE_TAC [FUN_EQ_THM]
    \\ MAP_EVERY ASSUME_TAC [STATE_ARM6_IMAP,IMM_ARM6_UNIFORM,ARM6_TIME_CON_IMM]
    \\ IMP_RES_TAC (GSYM TCON_IMMERSION_COR)
    \\ X_GEN_TAC `t2` \\ Cases_on `x`
    \\ ABBREV_TAC `inp = f` \\ RM_ABBREV_TAC `inp`
    \\ `state_inp a inp = <| state:= a; inp := inp |>`
      by (SIMP_TAC (srw_ss()) [state_inp_component_equality])
    \\ FULL_SIMP_TAC (arith_ss++STATE_INP_ss) [GSYM ARM6_SPEC_STATE,
         COMBINE_def,SMPL_ARM6_def,ADVANCE_def,GSYM ADVANCE_COMP,lem2,
         SMPL_EXC_ARM6_def,SMPL_DATA_ARM6_def,MAP_STRM_def,PACK_def,
         IMM_LEN_def,ADVANCE_def,
         (GSYM o SIMP_RULE (srw_ss()) [] o GEN_ALL o
          INST [`x` |-> `<| state:= a; inp := inp |>`] o SPEC_ALL o
          SIMP_RULE std_ss [TCON_IMMERSION_def]) ARM6_TIME_CON_IMM]
    \\ POP_ASSUM (K ALL_TAC)
    \\ POP_ASSUM (fn th => REWRITE_TAC [(GSYM o SPECL [`t2 + 1`,`t`]) th,
         (GSYM o SPECL [`t2`,`t`]) th] \\ ASSUME_TAC th)
    \\ SIMP_TAC arith_ss []);

(* ------------------------------------------------------------------------- *)

val ARM6_COR_LEM0 = store_thm("ARM6_COR_LEM0",
  `!x. (x = ^arm6state_inp) ==>
   (STATE_ARM 0 <|state := ABS_ARM6 x.state; inp := SMPL_ARM6 x|> =
    ABS_ARM6 (STATE_ARM6 (IMM_ARM6 x 0) x))`,
  RW_TAC bool_ss []
    \\ SIMP_TAC (std_ss++STATE_INP_ss) [STATE_ARM_def,STATE_ARM6_def,
         IMM_ARM6_def,INIT_ARM6_def,ABS_ARM6_def]);

val ARM6_COR_ZERO = GEN_ALL (SIMP_RULE (srw_ss()) [] ARM6_COR_LEM0);

(* ------------------------------------------------------------------------- *)

val CORRECT_ARM6 = store_thm("CORRECT_ARM6",
  `CORRECT ARM_SPEC ARM6_SPEC IMM_ARM6 ABS_ARM6
     (OSMPL OSMPL_ARM6 ARM6_SPEC IMM_ARM6) SMPL_ARM6 UNIV STRM_ARM6`,
  MATCH_MP_TAC ONE_STEP_THM
    \\ EXISTS_TAC `OSMPL_ARM6`
    \\ SIMP_TAC std_ss [STATE_ARM_THM2,STATE_ARM6_IMAP,IMM_ARM6_UNIFORM,
         ARM6_DATA_ABSTRACTION,ARM6_STREAM_ABSTRACTION,
         REWRITE_RULE [TCONa_def] (MATCH_MP TCON_I_THMa STATE_ARM_THM3),
         ARM6_TIME_CON_IMM,TCON_SMPL_ARM6]
    \\ REPEAT STRIP_TAC
    \\ Cases_on `x` \\ Cases_on_arm6 `a`
    \\ FULL_SIMP_TAC (std_ss++STATE_INP_ss)
         [lem,ARM6_SPEC_STATE,ARM_SPEC_STATE,ARM6_COR_ZERO,ARM6_COR_ONE,
          ARM6_OUT_THM]);

(* ------------------------------------------------------------------------- *)

val _ = export_theory();
