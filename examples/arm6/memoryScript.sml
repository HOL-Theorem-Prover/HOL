(* app load ["metisLib","my_listTheory","armTheory","coreTheory","lemmasTheory","multTheory",
             "lemmasLib","io_onestepTheory","compLib","pred_setSimps"]; *)
open HolKernel boolLib bossLib Q arithmeticTheory rich_listTheory my_listTheory io_onestepTheory
     word32Theory armTheory coreTheory lemmasTheory lemmasLib multTheory blockTheory interruptsTheory;

(* -------------------------------------------------------- *)

val _ = new_theory "memory";

val _ = numLib.prefer_num();

val FST_COND_RAND = ISPEC `FST` COND_RAND;
val SND_COND_RAND = ISPEC `SND` COND_RAND;

val booli_ss = bool_ss ++ rewrites [iclass_distinct,iseq_distinct];
val std_ss = std_ss ++ boolSimps.LET_ss;
val arith_ss = arith_ss ++ boolSimps.LET_ss;
val stdi_ss = compLib.stdi_ss++rewrites[FST_COND_RAND,SND_COND_RAND];
val PBETA_CONV = PairRules.PBETA_CONV;

(* -------------------------------------------------------- *)

val PBETA_CONV_ss = simpLib.SIMPSET
  {convs = [{name="PBETA_CONV",trace = 3,conv=K (K PBETA_CONV),key= SOME([],``(\(x,y). s1) s2``)}],
   rewrs = [], congs = [], filter = NONE, ac = [], dprocs = []};

val SUC2NUM = CONV_RULE numLib.SUC_TO_NUMERAL_DEFN_CONV;

(* -------------------------------------------------------- *)

val IS_MEMOP2_def = Define`
  IS_MEMOP2 (nmrq2,nopc1,nrw,nbw,areg) = nopc1`;

val IS_MEMOP2 = prove(
  `IS_MEMOP = IS_MEMOP2 o SND`,
  REWRITE_TAC [FUN_EQ_THM]
    THEN Cases
    THEN Cases_on `r` THEN Cases_on `r'`
    THEN Cases_on `r` THEN Cases_on `r'`
    THEN SIMP_TAC std_ss [IS_MEMOP2_def,IS_MEMOP_def]
);

val LET_FILTER = prove(
  `(!P. FILTER P [] = []) /\
    !P h t. FILTER P (h::t) = let l = FILTER P t in (if P h then h::l else l)`,
  SIMP_TAC (list_ss++boolSimps.LET_ss) []
);

(* -------------------------------------------------------- *)

val HD_SNOC = (SIMP_RULE list_ss [] o SPEC `0`) EL_SNOC;
val HD_MAP = (SIMP_RULE list_ss [] o SPEC `0`) EL_MAP;
val HD_GENLIST = (GEN_ALL o SIMP_RULE list_ss [] o INST [`x` |-> `0`] o SPEC_ALL) EL_GENLIST;
val HD_APPEND = (SIMP_RULE list_ss [] o SPEC `0`) EL_APPEND1;

val HD_APPEND2 = prove(
  `!n f l. HD (GENLIST f n ++ l) = if n = 0 then HD l else f 0`,
  Cases THEN SIMP_TAC list_ss [GENLIST,SNOC,HD_APPEND]
    THEN Cases_on `n'` THEN SIMP_TAC list_ss [LENGTH_SNOC,LENGTH_GENLIST,HD_SNOC,HD_APPEND,HD_GENLIST]
    THEN SIMP_TAC list_ss [GENLIST,SNOC]
);

val FILTER_SND = prove(
   `!P a h b. ~NULL a ==>
      (FILTER (P o SND) (ZIP (a,h::b)) =
        let t = FILTER (P o SND) (ZIP (TL a,b)) in
          if P h then (HD a,h)::t else t)`,
  Cases_on `a` THEN RW_TAC (list_ss++boolSimps.LET_ss) []
);

val CONS_SNOC = store_thm("CONS_SNOC",
  `!l a b. a::(SNOC b l) = SNOC b (a::l)`,
  Cases THEN SIMP_TAC list_ss [SNOC]
);

val GENLIST_CONS = prove(
  `!n f. GENLIST (\t. f t) (SUC n) = f 0::(GENLIST (\t. f (SUC t)) n)`,
  Induct THEN SIMP_TAC list_ss [GENLIST,SNOC]
    THEN REWRITE_TAC [CONS_SNOC]
    THEN POP_ASSUM (fn th => SIMP_TAC bool_ss [GSYM th,GENLIST])
);

val MOVE_DOUT_INV = (GEN_ALL o SIMP_RULE std_ss [] o DISCH `~NULL l` o GSYM o SPEC_ALL) MOVE_DOUT_def;

val NULL_GENLIST = prove(`!n f. NULL (GENLIST f n) = (n = 0)`, Cases THEN SIMP_TAC list_ss [GENLIST,NULL_SNOC]);
val NULL_MAP = prove(`!l f. NULL (MAP f l) = NULL l`, Cases THEN SIMP_TAC list_ss []);
val NULL_APPEND_RIGHT = prove(`!a b. ~NULL b ==> ~NULL (a ++ b)`, RW_TAC list_ss [NULL_EQ_NIL]);
val NULL_APPEND_LEFT = prove(`!a b. ~NULL a ==> ~NULL (a ++ b)`, RW_TAC list_ss [NULL_EQ_NIL]);

val LENGTH_NULL = (GSYM o REWRITE_RULE [GSYM NULL_EQ_NIL]) LENGTH_NIL;
val LENGTH_NOT_NULL = prove(`0 < LENGTH l = ~NULL l`, SIMP_TAC arith_ss [LENGTH_NULL]);

val FILTER_MEMOP_ONE =
  (GEN_ALL o SIMP_RULE list_ss [GSYM IS_MEMOP2,MOVE_DOUT_INV,TL_SNOC,NULL_MAP,HD_SNOC,LENGTH_NOT_NULL,HD_MAP] o
   DISCH `~NULL t` o SIMP_CONV list_ss [MOVE_DOUT_def,IS_MEMOP2,FILTER_SND,NULL_SNOC])
   ``FILTER IS_MEMOP (MOVE_DOUT x (h::t))``;

val FILTER_MEMOP_SINGLETON =
   (SIMP_CONV list_ss [MOVE_DOUT_def,IS_MEMOP2,FILTER_SND,NULL_SNOC,SNOC])
   ``FILTER IS_MEMOP (MOVE_DOUT x [h])``;

val LENGTH_MAPS = prove(
  `!l x f g. ~(l = []) ==> (LENGTH (SNOC x (TL (MAP g l))) = LENGTH (MAP f l))`,
  Induct THEN ASM_SIMP_TAC list_ss [SNOC,rich_listTheory.LENGTH_SNOC]
);

val LENGTH_MOVE_DOUT = prove(
  `!l x. LENGTH (MOVE_DOUT x l) = LENGTH l`,
  RW_TAC list_ss [MOVE_DOUT_def,LENGTH_ZIP,LENGTH_MAPS,NULL_EQ_NIL,LENGTH_SNOC,
                  REWRITE_RULE [LENGTH_NOT_NULL,NULL_EQ_NIL] LENGTH_TL]
    THEN FULL_SIMP_TAC arith_ss [GSYM NULL_EQ_NIL,GSYM LENGTH_NOT_NULL]
);

val FILTER_MOVE_DOUT = prove(
  `!l x. (FILTER IS_MEMOP (MOVE_DOUT x l) = []) = (FILTER IS_MEMOP l = [])`,
  Induct THEN1 SIMP_TAC list_ss [MOVE_DOUT_def]
    THEN RW_TAC (list_ss++boolSimps.LET_ss) [TL_SNOC,NULL_EQ_NIL,MOVE_DOUT_def,NULL_SNOC,FILTER_SND,IS_MEMOP2]
    THEN FULL_SIMP_TAC std_ss [MOVE_DOUT_def,NULL_EQ_NIL,IS_MEMOP2]
);

val IS_MEM_MOVE_DOUT = prove(
  `!l n x. n < LENGTH l ==> (IS_MEMOP (EL n (MOVE_DOUT x l)) = IS_MEMOP (EL n l))`,
  RW_TAC list_ss [IS_MEMOP2,MOVE_DOUT_def,NULL_EQ_NIL]
    THEN metisLib.METIS_TAC [listTheory.EL_ZIP,LENGTH_MAPS,LENGTH_MAP,EL_MAP,pairTheory.SND]
);

val FILTER_MEMOP_ALL = prove(
  `!f d x. (!t. t < d ==> ~IS_MEMOP (f t)) ==>
         (FILTER IS_MEMOP (MOVE_DOUT x (GENLIST (\t. f t) d)) = [])`,
  metisLib.METIS_TAC [FILTER_ALL,IS_MEM_MOVE_DOUT,LENGTH_GENLIST,LENGTH_MOVE_DOUT,EL_GENLIST]
);

val FILTER_MEMOP_NONE = prove(
  `!f d x. (!t. t < d ==> IS_MEMOP (f t)) ==>
         (FILTER IS_MEMOP (MOVE_DOUT x (GENLIST (\t. f t) d)) = MOVE_DOUT x (GENLIST (\t. f t) d))`,
  metisLib.METIS_TAC [FILTER_NONE,IS_MEM_MOVE_DOUT,LENGTH_GENLIST,LENGTH_MOVE_DOUT,EL_GENLIST]
);

val TL_EQ_BUTFIRSTN_1 = store_thm("TL_EQ_BUTFIRSTN_1",
  `!l. ~(l = []) ==> (BUTFIRSTN 1 l = TL l)`,
  Cases THEN SIMP_TAC list_ss [SUC2NUM BUTFIRSTN]
);

val NOT_NIL_GTEQ_1 =
  (REWRITE_RULE [DECIDE ``!n. ~(n = 0) = (1 <= n)``] o
   ONCE_REWRITE_RULE [DECIDE ``!a b. (a = b) = (~a = ~b)``]) LENGTH_NIL;

val TL_APPEND =
  (SIMP_RULE std_ss [REWRITE_RULE [NULL_EQ_NIL] NULL_APPEND_LEFT,NOT_NIL_GTEQ_1,TL_EQ_BUTFIRSTN_1] o
    SPEC `1`) BUTFIRSTN_APPEND1;

val LENGTH_MAPS2 = prove(
  `!l x y f g. LENGTH (SNOC x (MAP f l)) = LENGTH (y::MAP g l)`,
  SIMP_TAC bool_ss [LENGTH_SNOC,LENGTH_MAP,LENGTH]
);

val MOVE_DOUT_APPEND = prove(
  `!b a x. ~NULL b ==>
         (MOVE_DOUT x (a ++ b) = MOVE_DOUT (FST (HD b)) a ++ MOVE_DOUT x b)`,
  Induct
    THEN RW_TAC list_ss [MOVE_DOUT_def,NULL_EQ_NIL,ZIP_APPEND,LENGTH_MAPS,LENGTH_MAPS2]
    THEN SIMP_TAC list_ss [SNOC_APPEND]
    THEN ONCE_REWRITE_TAC [CONS_APPEND]
    THEN SIMP_TAC list_ss []
    THEN metisLib.METIS_TAC [APPEND_ASSOC,TL_APPEND,REWRITE_RULE [NULL_EQ_NIL] NULL_MAP]
);

val MAP_CONG2 = prove(
  `!a b f g. (LENGTH a = LENGTH b) /\
             (!n. n < LENGTH a ==> (f (EL n a) = g (EL n b))) ==>
             (MAP f a = MAP g b)`,
  metisLib.METIS_TAC [LIST_EQ,EL_MAP,LENGTH_MAP]
);

(* -------------------------------------------------------- *)

val LENGTH_MAPS3 = prove(
  `!l x f g. ~NULL l ==> (LENGTH (SNOC x (TL l)) = LENGTH l)`,
  RW_TAC list_ss [rich_listTheory.LENGTH_SNOC,LENGTH_TL,LENGTH_NULL]
);

val MAP_LDM_MEMOP = prove(
  `!y n. MAP MEMOP (MOVE_DOUT y (GENLIST (\t. (f t,b1,b2,F,b3,g t)) n)) =
             GENLIST (\t. MemRead (g t)) n`,
  Induct_on `n` THEN1 SIMP_TAC list_ss [GENLIST,MOVE_DOUT_def]
    THEN RW_TAC list_ss [GENLIST,MOVE_DOUT_def,NULL_SNOC,MAP_SNOC,MAP_GENLIST,TL_SNOC,NULL_GENLIST,
           MEMOP_def,ZIP_SNOC,LENGTH_GENLIST,LENGTH_MAPS3]
    THEN FULL_SIMP_TAC std_ss [MOVE_DOUT_def,MAP_GENLIST,NULL_GENLIST]
);

val MAP_LDM_MEMOP = GEN_ALL MAP_LDM_MEMOP;

val lem = prove(
  `!f g n x. x < n ==> ((\t. MemWrite b (g t) (if t + 1 = n then f n else f (t + 1))) x =
                        (\t. MemWrite b (g t) (if t + 1 = SUC n then y else f (t + 1))) x)`,
  RW_TAC arith_ss [ADD1]
);

val MAP_STM_MEMOP = prove(
  `!y n. MAP MEMOP (MOVE_DOUT y (GENLIST (\t. (f t,b1,b2,T,b3,g t)) n)) =
             GENLIST (\t. MemWrite (~b3) (g t) (if t + 1 = n then y else f (t + 1))) n`,
  Induct_on `n` THEN1 SIMP_TAC list_ss [GENLIST,MOVE_DOUT_def]
    THEN RW_TAC list_ss [GENLIST,MOVE_DOUT_def,NULL_SNOC,MAP_SNOC,MAP_GENLIST,TL_SNOC,NULL_GENLIST,
           MEMOP_def,ZIP_SNOC,LENGTH_GENLIST,LENGTH_MAPS3]
    THEN FULL_SIMP_TAC std_ss [MOVE_DOUT_def,MAP_GENLIST,NULL_GENLIST]
    THEN metisLib.METIS_TAC [GEN_ALL (MATCH_MP (SPEC_ALL GENLIST_FUN_EQ) (SPECL [`f`,`g`,`n`] lem))]
);

val MAP_STM_MEMOP = GEN_ALL MAP_STM_MEMOP;

(* -------------------------------------------------------- *)

val DUR_IC = (SIMP_RULE bossLib.bool_ss [GSYM RIGHT_AND_OVER_OR,GSYM LEFT_AND_OVER_OR] o
  SIMP_RULE (stdi_ss++PBETA_CONV_ss++boolSimps.CONJ_ss++boolSimps.DNF_ss)
   [RWA_def,PCCHANGE_def,FST_COND_RAND,SND_COND_RAND]) DUR_IC_def;

val DUR_X2 = (SIMP_RULE std_ss [ABORTINST_def,IC_def] o
             INST [`iregval` |-> `T`,`onewinst` |-> `T`,`ointstart` |-> `F`]) DUR_X;

val INIT_ARM6 = SIMP_RULE std_ss [num2exception_exception2num,ABORTINST_def,NXTIC_def] INIT_ARM6_def;

val IS_ABORT =
  CONJ ((GEN_ALL o fst o EQ_IMP_RULE o SPEC_ALL) blockTheory.IS_ABORT_LEM)
       ((GEN_ALL o fst o EQ_IMP_RULE o SPEC_ALL o
         ONCE_REWRITE_RULE [DECIDE ``!a b. (a = b) = (~a = ~b)``]) blockTheory.IS_ABORT_LEM);

val BIT_W32_NUM = GSYM word32Theory.WORD_BIT_def;
val BITS_W32_NUM = GSYM word32Theory.WORD_BITS_def;

val next_4tuple = (GEN_ALL o ONCE_REWRITE_CONV [form_4tuple]) ``NEXT_ARM6 x i``;

val SWI_LEM = SIMP_CONV (stdi_ss++compLib.SWI_EX_ss) [] ``MASK swi_ex t3 x y``;

val LEM = prove(
  `!a x y z. a \/ ~((if ~a then x else y) = z) = a \/ ~(x = z)`, Cases THEN REWRITE_TAC []);
val LEM = CONJ (CONJ (CONJ LEM
          ((GEN_ALL o SIMP_RULE std_ss [] o SPEC `a \/ b`) LEM))
          ((GEN_ALL o SIMP_RULE std_ss [] o SPEC `a /\ ~b`) LEM))
          ((GEN_ALL o SIMP_RULE std_ss [] o SPEC `~a`) LEM);

val INIT_INIT = prove(
  `!x. Abbrev (x = <| state := INIT_ARM6 (ARM6 (DP reg psr areg din alua alub dout)
                 (CTRL pipea pipeaval pipeb pipebval ireg iregval ointstart onewinst endinst
                       obaselatch opipebll nxtic nxtis nopc1 oorst resetlatch onfq ooonfq oniq oooniq
                       pipeaabt pipebabt iregabt2 dataabt2 aregn2 mrq2 nbw nrw sctrlreg psrfb oareg
                       mask orp oorp mul mu2 borrow2 mshift)); inp := i|>) ==>
  (<|state := INIT_ARM6 x.state; inp := x.inp|> = x)`,
  REPEAT STRIP_TAC THEN UNABBREV_TAC `x`
    THEN SIMP_TAC (srw_ss()) [INIT_ARM6,MASK_MASK,num2exception_exception2num,NXTIC_def]
);

val finish_rws = [INIT_ARM6_def,DECODE_PSR_def,NXTIC_def,MASK_MASK,SWI_LEM,
                  TO_WRITE_READ6,REG_READ_WRITE,REG_WRITE_COMMUTE_PC,REG_WRITE_READ_PC,
                  REGISTER_RANGES,RP_LT_16,RP_LT_16_0,AREGN1_THM,AREGN1_BIJ];

val REMOVE_STUFF = REPEAT (WEAKEN_TAC (fn th => not (can (match_term (Term `~(x = 15)`)) th) andalso
                                                not (can (match_term (Term `a \/ ~(x = 15)`)) th)));
val FINISH_OFF =
  REMOVE_STUFF THEN RW_TAC std_ss finish_rws
    THEN FULL_SIMP_TAC std_ss [MASK_MASK,REGISTER_RANGES,REG_READ_WRITE,REG_WRITE_READ_PC];

(* -------------------------------------------------------- *)

val MEM_MLA_MUL = prove(
  `!t x. Abbrev (x = <|state := INIT_ARM6 (ARM6 (DP reg psr areg din alua alub dout)
             (CTRL pipea pipeaval pipeb pipebval ireg iregval
                ointstart onewinst endinst obaselatch opipebll nxtic nxtis
                nopc1 oorst resetlatch onfq ooonfq oniq oooniq pipeaabt pipebabt iregabt2 dataabt2
                aregn2 mrq2 nbw nrw sctrlreg psrfb oareg
                mask orp oorp mul mu2 borrow2 mshift)); inp := i|>) /\
   (DECODE_INST (w2n ireg) = mla_mul) /\
   (num2exception aregn2 = software) /\
   CONDITION_PASSED (NZCV (w2n (CPSR_READ psr))) (w2n ireg) ==>
   ~FST (DUR_X x) ==> (!t. t < DUR_ARM6 x ==>
   ~IS_MEMOP (OUT_ARM6 ((FUNPOW (SNEXT NEXT_ARM6) t x).state)))`,
  REWRITE_TAC [markerTheory.Abbrev_def] THEN NTAC 2 STRIP_TAC
    THEN ASM_SIMP_TAC stdi_ss [DUR_X2,DUR_ARM6_def,DUR_IC_def, INIT_ARM6]
    THEN STRIP_TAC THEN POP_ASSUM (fn th => ASSUME_TAC (MATCH_MP IS_RESET_THM th)) THEN STRIP_TAC
    THEN Cases_on `t` THEN1 SIMP_TAC (std_ss++compLib.STATE_INP_ss) [FUNPOW,OUT_ARM6_def,IS_MEMOP_def]
    THEN STRIP_TAC THEN POP_ASSUM (fn th => ASSUME_TAC (MATCH_MP (DECIDE ``!a b. SUC a < 1 + b ==> a <= b``) th))
    THEN SIMP_TAC bool_ss [FUNPOW]
    THEN PURE_REWRITE_TAC [CONJUNCT1 arithmeticTheory.FUNPOW,SNEXT_NEXT_ARM6,pairTheory.FST,pairTheory.SND]
    THEN ABBREV_TAC `pc = REG_READ6 reg usr 15`
    THEN ABBREV_TAC `cpsr = CPSR_READ psr`
    THEN ABBREV_TAC `nbs = DECODE_MODE (WORD_BITS 4 0 cpsr)`
    THEN compLib.MLA_MUL_TAC
    THEN ASM_SIMP_TAC (stdi_ss++ARITH_ss++PBETA_CONV_ss)
           [MULT_ALU6_ZERO,GSYM WORD_BITS_def,LSL_ZERO,bitsTheory.BITS_ZERO2]
    THEN REWRITE_TAC [IF_NEG,DECIDE ``~a /\ ~b = ~(a \/ b)``] THEN SIMP_TAC std_ss []
    THEN IMP_RES_TAC MLA_MUL_INVARIANT
    THEN POP_ASSUM (STRIP_ASSUME_TAC o (CONV_RULE (TOP_DEPTH_CONV (CHANGED_CONV (SKOLEM_CONV)))))
    THEN ASM_SIMP_TAC (std_ss++compLib.STATE_INP_ss) [OUT_ARM6_def,IS_MEMOP_def]
);

(* -------------------------------------------------------- *)

val ALU_ABBREV_TAC = with_flag (priming,SOME "")
  (PAT_ABBREV_TAC `alu = ALU6 ic is xireg xborrow2 xmul xdataabt xalua xalub xc` THEN POP_ASSUM (K ALL_TAC));

val PSR_ABBREV_TAC = with_flag (priming,SOME "") (PAT_ABBREV_TAC `psr = xpsr:psr` THEN POP_ASSUM (K ALL_TAC));

val NON_MEMOPS = Count.apply prove(
  `!x y. Abbrev (x = <| state := INIT_ARM6 (ARM6 (DP reg psr areg din alua alub dout)
             (CTRL pipea pipeaval pipeb pipebval ireg iregval
                ointstart onewinst endinst obaselatch opipebll nxtic nxtis
                nopc1 oorst resetlatch onfq ooonfq oniq oooniq pipeaabt pipebabt iregabt2 dataabt2
                aregn2 mrq2 nbw nrw sctrlreg psrfb oareg
                mask orp oorp mul mu2 borrow2 mshift)); inp := i|>) /\
   (DECODE_INST (w2n ireg) IN {mrs_msr; data_proc; reg_shift; br; swi_ex; cdp_und; unexec}) /\
   (num2exception aregn2 = software) /\
   CONDITION_PASSED (NZCV (w2n (CPSR_READ psr))) (w2n ireg) ==>
   ~FST (DUR_X x) ==>
   (let s = (FUNPOW (SNEXT NEXT_ARM6) (DUR_ARM6 x) x).state in INIT_ARM6 s = s) /\
   (FILTER IS_MEMOP (MOVE_DOUT y (GENLIST (\t. OUT_ARM6 ((FUNPOW (SNEXT NEXT_ARM6) t x).state)) (DUR_ARM6 x))) = [])`,
  NTAC 3 STRIP_TAC THEN FULL_SIMP_TAC stdi_ss [DUR_ARM6_def,FILTER_MOVE_DOUT]
    THEN FULL_SIMP_TAC (stdi_ss++pred_setSimps.PRED_SET_ss) [DECODE_INST_NOT_UNEXEC,INIT_ARM6]
    THEN UNABBREV_TAC `x` THEN ASM_SIMP_TAC stdi_ss [DUR_X2]
    THEN ABBREV_TAC `d = DUR_IC ic ireg rs inp` THEN POP_ASSUM MP_TAC
    THEN ASM_SIMP_TAC stdi_ss [DUR_IC] THEN STRIP_TAC THEN UNABBREV_TAC `d`
    THEN TRY COND_CASES_TAC THEN STRIP_TAC THEN POP_ASSUM (fn th => ASSUME_TAC (MATCH_MP IS_RESET_THM th))
    THEN ASM_SIMP_TAC (bossLib.std_ss++compLib.STATE_INP_ss)
         [OUT_ARM6_def,IS_MEMOP2,IS_MEMOP2_def,LET_FILTER,SNOC,SUC2NUM GENLIST,
          SNEXT_def,ADVANCE_def,numeralTheory.numeral_funpow]
    THEN REPEAT (PAT_ABBREV_TAC `s = NEXT_ARM6 a b`)
    THEN RULE_ASSUM_TAC (REWRITE_RULE [DECIDE ``~(a /\ b) = ~a \/ ~b``])
    THEN REPEAT (PAT_ASSUM `Abbrev (q = NEXT_ARM6 (ARM6 dp ctrl) inp)` (MP_TAC o ONCE_REWRITE_RULE [next_4tuple])
           THEN ASM_SIMP_TAC (booli_ss++compLib.MRS_MSR_ss++compLib.DATA_PROC_ss++compLib.REG_SHIFT_ss++
                              compLib.BR_ss++compLib.SWI_EX_ss++compLib.UNDEF_ss++compLib.UNEXEC_ss++
                              PBETA_CONV_ss) [SND_COND_RAND,FST_COND_RAND]
           THEN TRY ALU_ABBREV_TAC THEN TRY PSR_ABBREV_TAC
           THEN ASM_SIMP_TAC bossLib.arith_ss [markerTheory.Abbrev_def,LEM]
           THEN DISCH_THEN SUBST_ALL_TAC
           THEN SIMP_TAC (bossLib.std_ss++compLib.STATE_INP_ss) [OUT_ARM6_def,IS_MEMOP2_def])
    THEN ASM_SIMP_TAC (stdi_ss++compLib.UNEXEC_ss++compLib.SWI_EX_ss) []
    THEN FINISH_OFF
);

val NON_MEMOPS_UNEXEC = prove(
  `!x y. Abbrev (x = <|state := INIT_ARM6 (ARM6 (DP reg psr areg din alua alub dout)
             (CTRL pipea pipeaval pipeb pipebval ireg iregval
                ointstart onewinst endinst obaselatch opipebll nxtic nxtis
                nopc1 oorst resetlatch onfq ooonfq oniq oooniq pipeaabt pipebabt iregabt2 dataabt2
                aregn2 mrq2 nbw nrw sctrlreg psrfb oareg
                mask orp oorp mul mu2 borrow2 mshift)); inp := i|>) /\
   ((num2exception aregn2 = software) ==> ~CONDITION_PASSED (NZCV (w2n (CPSR_READ psr))) (w2n ireg)) ==>
   ~FST (DUR_X x) ==>
   (let s = (FUNPOW (SNEXT NEXT_ARM6) (DUR_ARM6 x) x).state in INIT_ARM6 s = s) /\
   (FILTER IS_MEMOP (MOVE_DOUT y (GENLIST (\t. OUT_ARM6 ((FUNPOW (SNEXT NEXT_ARM6) t x).state)) (DUR_ARM6 x))) = [])`,
  NTAC 3 STRIP_TAC
    THEN FULL_SIMP_TAC stdi_ss
         [markerTheory.Abbrev_def,IC_def,ABORTINST_def,NXTIC_def,DUR_X,DUR_ARM6_def,DUR_IC,FILTER_MOVE_DOUT,
          DECIDE ``!x y b. (x = y) ==> b = ~(x = y) \/ (x = y) /\ b``,
          INIT_ARM6_def,DECODE_PSR,num2exception_exception2num]
    THEN STRIP_TAC THEN POP_ASSUM (fn th => ASSUME_TAC (MATCH_MP IS_RESET_THM th))
    THEN ASM_SIMP_TAC (bossLib.std_ss++compLib.STATE_INP_ss)
         [OUT_ARM6_def,IS_MEMOP2,IS_MEMOP2_def,LET_FILTER,SNOC,SUC2NUM GENLIST,
          SNEXT_def,ADVANCE_def,numeralTheory.numeral_funpow]
    THEN REPEAT (PAT_ABBREV_TAC `s = NEXT_ARM6 a b`)
    THEN REPEAT (PAT_ASSUM `Abbrev (q = NEXT_ARM6 (ARM6 dp ctrl) inp)` (MP_TAC o ONCE_REWRITE_RULE [next_4tuple])
           THEN ASM_SIMP_TAC (booli_ss++compLib.SWI_EX_ss++compLib.UNEXEC_ss++
                              PBETA_CONV_ss) [SND_COND_RAND,FST_COND_RAND]
           THEN TRY ALU_ABBREV_TAC THEN TRY PSR_ABBREV_TAC THEN STRIP_TAC
           THEN POP_ASSUM (fn th => FULL_SIMP_TAC (bossLib.std_ss++compLib.STATE_INP_ss)
                  [OUT_ARM6_def,IS_MEMOP2_def,REWRITE_RULE [markerTheory.Abbrev_def] th]))
    THEN SIMP_TAC (stdi_ss++compLib.SWI_EX_ss) []
    THEN FINISH_OFF
);

(* -------------------------------------------------------- *)

val ALU_ABBREV_TAC2 = with_flag (priming,SOME "")
  (PAT_ABBREV_TAC `alu = ALU6 ic is xireg xborrow2 xmul xdataabt xalua xalub xc`);

val PSR_ABBREV_TAC2 = with_flag (priming,SOME "") (PAT_ABBREV_TAC `psr = xpsr:psr`);

val BASIC_MEMOPS = Count.apply prove(
  `!x. Abbrev (x = <|state := INIT_ARM6 (ARM6 (DP reg psr areg din alua alub dout)
             (CTRL pipea pipeaval pipeb pipebval ireg iregval
                ointstart onewinst endinst obaselatch opipebll nxtic nxtis
                nopc1 oorst resetlatch onfq ooonfq oniq oooniq pipeaabt pipebabt iregabt2 dataabt2
                aregn2 mrq2 nbw nrw sctrlreg psrfb oareg
                mask orp oorp mul mu2 borrow2 mshift)); inp := i|>) /\
   (DECODE_INST (w2n ireg) IN {swp; ldr; str}) /\
   (num2exception aregn2 = software) /\
   CONDITION_PASSED (NZCV (w2n (CPSR_READ psr))) (w2n ireg) ==>
   ~FST (DUR_X x) ==>
   (let s = (FUNPOW (SNEXT NEXT_ARM6) (DUR_ARM6 x) x).state in INIT_ARM6 s = s) /\
   (OUT_ARM (ABS_ARM6 x.state) =
    OSMPL_ARM6 x (GENLIST (\t. OUT_ARM6 ((FUNPOW (SNEXT NEXT_ARM6) t x).state)) (DUR_ARM6 x)))`,
  NTAC 2 STRIP_TAC
    THEN FULL_SIMP_TAC (stdi_ss++pred_setSimps.PRED_SET_ss++compLib.STATE_INP_ss)
         [markerTheory.Abbrev_def,IC_def,ABORTINST_def,NXTIC_def,DUR_X,DUR_ARM6_def,DUR_IC,ABS_ARM6_def,
          STATE_ARM6_COR,OSMPL_ARM6_def,SINIT_def,INIT_ARM6,DECODE_PSR,MASK_MASK,num2exception_exception2num]
    THEN COND_CASES_TAC THEN STRIP_TAC THEN POP_ASSUM (fn th => ASSUME_TAC (MATCH_MP IS_RESET_THM th))
    THEN ASM_SIMP_TAC (list_ss++compLib.STATE_INP_ss)
         [OUT_ARM6_def,IS_MEMOP2,IS_MEMOP2_def,LET_FILTER,SNOC,SUC2NUM GENLIST,
          MOVE_DOUT_def,SNEXT_def,ADVANCE_def,numeralTheory.numeral_funpow]
    THEN REPEAT (PAT_ABBREV_TAC `s = NEXT_ARM6 a b`)
    THEN REPEAT (PAT_ASSUM `Abbrev (q = NEXT_ARM6 (ARM6 dp ctrl) inp)` (MP_TAC o ONCE_REWRITE_RULE [next_4tuple])
           THEN ASM_SIMP_TAC (booli_ss++compLib.SWP_ss++compLib.LDR_ss++compLib.STR_ss++compLib.UNEXEC_ss++
                              ARITH_ss++PBETA_CONV_ss) [IS_ABORT,SND_COND_RAND,FST_COND_RAND]
           THEN TRY ALU_ABBREV_TAC2 THEN STRIP_TAC
           THEN POP_ASSUM (fn th => FULL_SIMP_TAC (bossLib.std_ss++compLib.STATE_INP_ss)
                  [OUT_ARM6_def,IS_MEMOP2_def,REWRITE_RULE [markerTheory.Abbrev_def] th,LEM]))
    THEN (CONJ_TAC THEN1 (ASM_SIMP_TAC bossLib.std_ss [LEM] THEN FINISH_OFF)
    THEN UNABBREV_TAC `alu`
    THEN TRY (UNABBREV_TAC `alu1`)
    THEN ASM_SIMP_TAC (stdi_ss++listSimps.LIST_ss++compLib.ALU_ss)
         ([BIT_W32_NUM,BITS_W32_NUM,SWP_def,LDR_STR_def,DECODE_SWP_def,DECODE_LDR_STR_def,ADDR_MODE2_def,
           DECODE_PSR,OUT_ARM_def,MEMOP_def,SNOC,BIT_OPC,LDR_IMP_BITS,STR_IMP_BITS,
           IF_NEG,UP_DOWN_THM,SHIFT_IMMEDIATE_THM2] @ lemmasLib.finish_rws2))
);

(* -------------------------------------------------------- *)

val SNEXT = (BETA_RULE o REWRITE_RULE [FUN_EQ_THM]) SNEXT_def;

val NOT_ABORT = metisLib.METIS_PROVE []
   ``(!s. ~(s < SUC n) \/ ~IS_ABORT i (s + 1)) ==> ~(?s. s  < SUC n /\ IS_ABORT i (s + 1))``;

val UNEXEC_TAC =
   PAT_ASSUM `Abbrev (q = NEXT_ARM6 (ARM6 dp ctrl) inp)` (MP_TAC o ONCE_REWRITE_RULE [next_4tuple])
     THEN ASM_SIMP_TAC (booli_ss++compLib.UNEXEC_ss++PBETA_CONV_ss) [SND_COND_RAND,FST_COND_RAND]
     THEN TRY ALU_ABBREV_TAC2 THEN STRIP_TAC
     THEN POP_ASSUM (fn th => FULL_SIMP_TAC (bossLib.std_ss++boolSimps.CONJ_ss)
            [OUT_ARM6_def,IS_MEMOP2_def,REWRITE_RULE [markerTheory.Abbrev_def] th]);

val LDM_TAC =
   PAT_ASSUM `Abbrev (q = NEXT_ARM6 (ARM6 dp ctrl) inp)` (MP_TAC o ONCE_REWRITE_RULE [next_4tuple])
     THEN ASM_SIMP_TAC (booli_ss++compLib.LDM_ss++PBETA_CONV_ss) [IS_ABORT,NOT_ABORT,SND_COND_RAND,FST_COND_RAND]
     THEN TRY ALU_ABBREV_TAC2 THEN STRIP_TAC
     THEN POP_ASSUM (fn th => FULL_SIMP_TAC (bossLib.std_ss++boolSimps.CONJ_ss)
            [OUT_ARM6_def,IS_MEMOP2_def,REWRITE_RULE [markerTheory.Abbrev_def] th]);

val LDM_PENCZ_ZERO =
  (GEN_ALL o REWRITE_RULE [MASKN_ZERO] o INST [`x` |-> `0`] o SPEC_ALL o
   CONJUNCT1 o SIMP_RULE std_ss [] o SPEC `ldm`) PENCZ_THM;

val PENCZ_ONE = prove(
  `!n. 0 < LENGTH (REGISTER_LIST n) ==>
       (PENCZ ldm n (MASKN 16 1 n) = (LENGTH (REGISTER_LIST n) = 1))`,
  REPEAT STRIP_TAC THEN Cases_on `LENGTH (REGISTER_LIST n) = 1`
    THEN ASM_SIMP_TAC arith_ss [PENCZ_THM]
    THEN PROVE_TAC [PENCZ_THM]
);

val NOT_T3 = prove(
  `!b. ~((if b then tm else tn) = t3)`,
  RW_TAC stdi_ss []
);

val LDM_INIT =
  (SIMP_RULE (std_ss++boolSimps.CONJ_ss) [NOT_T3,MASKN_150,PENCZ_RP_150,MASKN16_2,MASKN16_1,PENCZ_THM3,LSL_ZERO] o
   SIMP_RULE (booli_ss++compLib.LDM_ss++PBETA_CONV_ss) [IS_ABORT,SND_COND_RAND,FST_COND_RAND] o
   CONV_RULE (RAND_CONV (RHS_CONV (LAND_CONV (ONCE_REWRITE_CONV [next_4tuple])))) o
   CONV_RULE (RAND_CONV (RHS_CONV (ONCE_REWRITE_CONV [next_4tuple]))) o
   SIMP_RULE stdi_ss [IC_def,ABORTINST_def,NXTIC_def,num2exception_exception2num,DECODE_PSR] o
   DISCH `(DECODE_INST (w2n ireg) = ldm) /\ (num2exception aregn2 = software) /\
          CONDITION_PASSED (NZCV (w2n (CPSR_READ psr))) (w2n ireg)` o
   SIMP_CONV bossLib.bool_ss [INIT_ARM6_def])
    ``NEXT_ARM6 (NEXT_ARM6 (INIT_ARM6 (ARM6 (DP reg psr areg din alua alub dout)
             (CTRL pipea pipeaval pipeb pipebval ireg iregval
                ointstart onewinst endinst obaselatch opipebll nxtic nxtis
                nopc1 oorst resetlatch onfq ooonfq oniq oooniq pipeaabt pipebabt iregabt2 dataabt2
                aregn2 mrq2 nbw nrw sctrlreg psrfb oareg
                mask orp oorp mul mu2 borrow2 mshift))) i0) i1``;

val LDM_INIT2 = prove(
  `!x. Abbrev (x = <|state := INIT_ARM6 (ARM6 (DP reg psr areg din alua alub dout)
             (CTRL pipea pipeaval pipeb pipebval ireg iregval
                ointstart onewinst endinst obaselatch opipebll nxtic nxtis
                nopc1 oorst resetlatch onfq ooonfq oniq oooniq pipeaabt pipebabt iregabt2 dataabt2
                aregn2 mrq2 nbw nrw sctrlreg psrfb oareg
                mask orp oorp mul mu2 borrow2 mshift)); inp := i|>) /\
   (DECODE_INST (w2n ireg) = ldm) /\
   (num2exception aregn2 = software) /\
   CONDITION_PASSED (NZCV (w2n (CPSR_READ psr))) (w2n ireg) /\
   (LENGTH (REGISTER_LIST (w2n ireg)) = l) ==>
   ~FST (DUR_X x) ==>
   (!t. t < SUC l ==> FST (i t)) /\
   (DUR_ARM6 x = (if WORD_BIT 15 ireg /\ ~?s. s < l /\ IS_ABORT i (s + 1) then 2 else 0) + 1 + (l - 1) + 2)`,
  NTAC 2 STRIP_TAC
    THEN FULL_SIMP_TAC stdi_ss
         [IC_def,ABORTINST_def,NXTIC_def,INIT_ARM6,DECODE_PSR,num2exception_exception2num]
    THEN UNABBREV_TAC `x`
    THEN ASM_SIMP_TAC stdi_ss [IC_def,ABORTINST_def,NXTIC_def,DUR_X,DUR_ARM6_def,DUR_IC,SINIT_def,DECODE_PSR]
    THEN STRIP_TAC THEN IMP_RES_TAC IS_RESET_THM2
    THEN POP_ASSUM (SPEC_THEN `SUC l`
           (ASSUME_TAC o REWRITE_RULE [DECIDE ``!x y. SUC x <= 2 + (x - 1) + 1 + y``]))
    THEN ASM_SIMP_TAC (std_ss++numSimps.ARITH_AC_ss) []
);

val LDM_f = `\t. ((f t reg psr (i:num -> bool # bool # bool # bool # word32)):word32,F,T,F,T,
                FIRST_ADDRESS (WORD_BIT 24 ireg) (WORD_BIT 23 ireg)
                  (REG_READ6 reg (DECODE_MODE (WORD_BITS 4 0 (CPSR_READ psr))) (WORD_BITS 19 16 ireg))
                  (WB_ADDRESS (WORD_BIT 23 ireg)
                     (REG_READ6 reg (DECODE_MODE (WORD_BITS 4 0 (CPSR_READ psr))) (WORD_BITS 19 16 ireg))
                     (LENGTH (REGISTER_LIST (w2n ireg)))) + w32 (SUC t) * 4w)`;

val LDM_GENLIST_MEMOP_EQ = prove(
  `!x. Abbrev (x = <| state := INIT_ARM6 (ARM6 (DP reg psr areg din alua alub dout)
             (CTRL pipea pipeaval pipeb pipebval ireg iregval
                ointstart onewinst endinst obaselatch opipebll nxtic nxtis
                nopc1 oorst resetlatch onfq ooonfq oniq oooniq pipeaabt pipebabt iregabt2 dataabt2
                aregn2 mrq2 nbw nrw sctrlreg psrfb oareg
                mask orp oorp mul mu2 borrow2 mshift)); inp := i|>) /\
   (DECODE_INST (w2n ireg) = ldm) /\
   (num2exception aregn2 = software) /\
   CONDITION_PASSED (NZCV (w2n (CPSR_READ psr))) (w2n ireg) /\
   (LENGTH (REGISTER_LIST (w2n ireg)) = SUC n) ==>
   ~FST (DUR_X x) ==>
    (?f. GENLIST (\t. OUT_ARM6 ((FUNPOW (SNEXT NEXT_ARM6) t (FUNPOW (SNEXT NEXT_ARM6) 2 x)).state)) n =
         GENLIST (^(Term LDM_f)) n)`,
  REPEAT STRIP_TAC
    THEN EXISTS_TAC `\t reg psr i. if t = 0 then
           REG_READ6 (REG_WRITE reg usr 15 (REG_READ6 reg usr 15 + 4w))
             (DECODE_MODE (WORD_BITS 4 0 (CPSR_READ psr))) ARB else PROJ_DATA (i t)`
    THEN MATCH_MP_TAC GENLIST_FUN_EQ
    THEN REPEAT STRIP_TAC
    THEN MAP_EVERY IMP_RES_TAC [LDM_INIT2,LDM_INIT]
    THEN UNABBREV_TAC `x`
    THEN ASM_SIMP_TAC (arith_ss++compLib.STATE_INP_ss) [numeralTheory.numeral_funpow,SNEXT,GSYM PROJ_DATA,
           GSYM IS_ABORT_LEM,ADVANCE_def,GSYM ADVANCE_COMP,LDM_PENCZ_ZERO,PENCZ_ONE]
    THEN POP_ASSUM (K ALL_TAC)
    THEN REPEAT ALU_ABBREV_TAC2
    THEN `0 < SUC n /\ x' <= SUC n - 1 /\ ~(SUC n = 1)` by DECIDE_TAC
    THEN PAT_ASSUM `LENGTH a = b` (ASSUME_TAC o SYM)
    THEN IMP_RES_TAC NEXT_CORE_LDM_TN_X
    THEN PAT_ASSUM `~(SUC n = 1)`
         (fn th => FULL_SIMP_TAC std_ss [th,WORD_MULT_CLAUSES])
    THEN POP_ASSUM (STRIP_ASSUME_TAC o (CONV_RULE (TOP_DEPTH_CONV (CHANGED_CONV (SKOLEM_CONV)))))
    THEN UNABBREV_TAC `alu1`
    THEN ASM_SIMP_TAC (arith_ss++compLib.STATE_INP_ss) [OUT_ARM6_def,GSYM FIRST_ADDRESS,TO_WRITE_READ6]
);

val FILTER_LDM_MEMOPS_X = prove(
  `!y x. Abbrev (x = <| state := INIT_ARM6 (ARM6 (DP reg psr areg din alua alub dout)
             (CTRL pipea pipeaval pipeb pipebval ireg iregval
                ointstart onewinst endinst obaselatch opipebll nxtic nxtis
                nopc1 oorst resetlatch onfq ooonfq oniq oooniq pipeaabt pipebabt iregabt2 dataabt2
                aregn2 mrq2 nbw nrw sctrlreg psrfb oareg
                mask orp oorp mul mu2 borrow2 mshift)); inp := i|>) /\
   (DECODE_INST (w2n ireg) = ldm) /\
   (num2exception aregn2 = software) /\
   CONDITION_PASSED (NZCV (w2n (CPSR_READ psr))) (w2n ireg) /\
   (LENGTH (REGISTER_LIST (w2n ireg)) = SUC n) /\
   ~FST (DUR_X x) ==>
   (let l = MOVE_DOUT y (GENLIST
                  (\t.  OUT_ARM6 ((FUNPOW (SNEXT NEXT_ARM6) t (FUNPOW (SNEXT NEXT_ARM6) 2 x)).state)) n) in
    FILTER IS_MEMOP l = l)`,
  SIMP_TAC std_ss [] THEN REPEAT STRIP_TAC
    THEN IMP_RES_TAC LDM_GENLIST_MEMOP_EQ THEN NTAC 15 (POP_ASSUM (K ALL_TAC)) THEN POP_ASSUM SUBST1_TAC
    THEN MATCH_MP_TAC ((GEN_ALL o BETA_RULE o ISPEC LDM_f) FILTER_MEMOP_NONE)
    THEN RW_TAC bossLib.std_ss [IS_MEMOP_def]
);

val pat = `z = (fx : word32 -> (register -> word32) -> word32 -> (psrs -> word32) -> bool ->
  word32 -> bool -> word32 -> bool -> bool -> bool -> bool -> bool -> num -> num -> num -> num ->
  word32 -> word32 -> bool -> word32 -> num -> word32 -> word32 -> num)
  z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 z15 z16 z17 z18 z19 z20 z21 z22 z23`;

val pat2 = `z = (fx : word32 -> (register -> word32) -> word32 -> (psrs -> word32) -> bool ->
  word32 -> bool -> word32 -> bool -> bool -> bool -> bool -> bool -> num -> num -> num -> num ->
  word32 -> word32 -> bool -> word32 -> num -> word32 -> word32 -> bool)
  z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 z15 z16 z17 z18 z19 z20 z21 z22 z23`;

val LDM_MEMOPS = Count.apply prove(
  `!x. Abbrev (x = <|state := INIT_ARM6 (ARM6 (DP reg psr areg din alua alub dout)
             (CTRL pipea pipeaval pipeb pipebval ireg iregval
                ointstart onewinst endinst obaselatch opipebll nxtic nxtis
                nopc1 oorst resetlatch onfq ooonfq oniq oooniq pipeaabt pipebabt iregabt2 dataabt2
                aregn2 mrq2 nbw nrw sctrlreg psrfb oareg
                mask orp oorp mul mu2 borrow2 mshift)); inp := i|>) /\
   (DECODE_INST (w2n ireg) = ldm) /\
   (num2exception aregn2 = software) /\
   CONDITION_PASSED (NZCV (w2n (CPSR_READ psr))) (w2n ireg) ==>
   ~FST (DUR_X x) ==>
   (OUT_ARM (ABS_ARM6 x.state) =
    OSMPL_ARM6 x (GENLIST (\t. OUT_ARM6 ((FUNPOW (SNEXT NEXT_ARM6) t x).state)) (DUR_ARM6 x)))`,
  REPEAT STRIP_TAC
    THEN Cases_on `LENGTH (REGISTER_LIST (w2n ireg))`
    THEN MAP_EVERY IMP_RES_TAC [LDM_INIT2,INIT_INIT]
    THEN ASM_SIMP_TAC arith_ss [STATE_ARM6_COR,OSMPL_ARM6_def,SINIT_def]
    THEN NTAC 2 (POP_ASSUM (K ALL_TAC))
    THENL [
      UNABBREV_TAC `x`
        THEN COND_CASES_TAC
        THEN `~WORD_BIT 15 ireg` by metisLib.METIS_TAC [PENCZ_THM2,WORD_BITS_150_ZERO]
        THEN `!mask. PENCZ ldm (w2n ireg) mask` by metisLib.METIS_TAC [PENCZ_THM2,PENCZ_THM3]
        THEN ASM_SIMP_TAC (list_ss++boolSimps.LET_ss++compLib.STATE_INP_ss) [numeralTheory.numeral_funpow,SNOC,
               HD_GENLIST,IS_MEMOP2_def,NULL_GENLIST,NULL_APPEND_RIGHT,ADVANCE_def,INIT_ARM6_def,ABS_ARM6_def,SNEXT,
               num2exception_exception2num,SUC2NUM GENLIST,FILTER_MEMOP_ONE,FILTER_MEMOP_SINGLETON,OUT_ARM6_def]
        THEN REPEAT (PAT_ABBREV_TAC `q = NEXT_ARM6 a b`) THEN NTAC 2 LDM_TAC
        THEN ASM_SIMP_TAC stdi_ss [BIT_W32_NUM,BITS_W32_NUM,OUT_ARM_def,DECODE_PSR,LDM_STM_def,
               DECODE_LDM_STM_def,ADDR_MODE4_def,DECODE_INST_LDM,ADDRESS_LIST_def,GENLIST,MAP,PENCZ_RP_150],
      IMP_RES_TAC FILTER_LDM_MEMOPS_X
        THEN FULL_SIMP_TAC stdi_ss [STATE_ARM6_COR,OSMPL_ARM6_def]
        THEN MAP_EVERY (fn th => ONCE_REWRITE_TAC [th]) [onestepTheory.FUNPOW_COMP,GENLIST_APPEND,GENLIST_APPEND]
        THEN BETA_TAC THEN REWRITE_TAC [(GEN_ALL o INST [`b` |-> `2`] o SPEC_ALL) onestepTheory.FUNPOW_COMP]
        THEN `0 < LENGTH (REGISTER_LIST (w2n ireg))` by DECIDE_TAC
        THEN `!t. t < SUC (LENGTH (REGISTER_LIST (w2n ireg))) ==> FST (i t)` by ASM_SIMP_TAC arith_ss []
        THEN COND_CASES_TAC
        THENL [
          `~(WORD_BITS 15 0 ireg = 0)` by metisLib.METIS_TAC [WORD_BITS_150_ZERO]
            THEN `RP ldm (w2n ireg) (MASKN 16 n (w2n ireg)) = 15`
              by metisLib.METIS_TAC [RP_LAST_15,DECIDE ``!m n. (m = SUC n) ==> (n = (m - 1))``],
          PAT_ASSUM `~(a /\ b)` (K ALL_TAC)
        ]
        THEN ASM_SIMP_TAC list_ss [FILTER_MEMOP_ONE,FILTER_MEMOP_SINGLETON,NULL_GENLIST,NULL_APPEND_RIGHT,
               SUC2NUM GENLIST,SNOC,HD_GENLIST,HD_APPEND2,IS_MEMOP2_def,CONJUNCT1 FUNPOW]
        THEN ASM_SIMP_TAC list_ss [FILTER_APPEND,FILTER_MEMOP_ONE,FILTER_MEMOP_SINGLETON,MOVE_DOUT_APPEND]
        THEN PAT_ASSUM `!y. FILTER f l = l` (K ALL_TAC)
        THEN IMP_RES_TAC LDM_GENLIST_MEMOP_EQ THEN NTAC 15 (POP_ASSUM (K ALL_TAC))
        THEN PAT_ASSUM `Abbrev x` MP_TAC
        THEN ASM_SIMP_TAC bossLib.std_ss [IC_def,ABORTINST_def,NXTIC_def,DECODE_PSR,SNEXT,ADVANCE_def,
               INIT_ARM6,numeralTheory.numeral_funpow]
        THEN POP_ASSUM (K ALL_TAC) THEN STRIP_TAC THEN UNABBREV_TAC `x`
        THEN SIMP_TAC (bossLib.std_ss++compLib.STATE_INP_ss) [OUT_ARM6_def,IS_MEMOP2_def,GSYM ADVANCE_COMP]
        THEN SIMP_TAC bossLib.std_ss [ONCE_REWRITE_RULE [ADD_COMM] onestepTheory.FUNPOW_COMP]
        THEN REPEAT (PAT_ABBREV_TAC `q = NEXT_ARM6 a b`)
        THEN ABBREV_TAC `sn = FUNPOW (SNEXT NEXT_ARM6) n <| state := q'; inp := ADVANCE 2 i|>`
        THEN NTAC 2 LDM_TAC
        THEN PAT_ASSUM `Abbrev (sn = FUNPOW f n state)` MP_TAC
        THEN IMP_RES_TAC NEXT_CORE_LDM_TN_W1
        THEN POP_ASSUM MP_TAC
        THEN ASM_SIMP_TAC (booli_ss++numSimps.ARITH_ss) [GSYM PROJ_DATA,GSYM IS_ABORT_LEM,
               GSYM ADVANCE_COMP,LDM_PENCZ_ZERO,NOT_T3,MASKN_150,PENCZ_RP_150,
               MASKN16_2,MASKN16_1,PENCZ_THM3,LSL_ZERO,PENCZ_ONE]
        THEN DISCH_THEN (STRIP_ASSUME_TAC o (CONV_RULE (TOP_DEPTH_CONV (CHANGED_CONV (SKOLEM_CONV)))))
        THEN ASM_SIMP_TAC bossLib.arith_ss [numeralTheory.numeral_funpow,SNEXT,ADVANCE_def]
        THEN POP_ASSUM (K ALL_TAC) THEN REPEAT (PAT_ABBREV_TAC pat THEN POP_ASSUM (K ALL_TAC))
        THEN REPEAT (PAT_ABBREV_TAC pat2 THEN POP_ASSUM (K ALL_TAC))
        THEN REPEAT (PAT_ABBREV_TAC `q = NEXT_ARM6 a b`)
        THEN STRIP_TAC THEN UNABBREV_TAC `sn`
        THEN RULE_ASSUM_TAC (SIMP_RULE (bossLib.arith_ss++compLib.STATE_INP_ss) [ADVANCE_def])
        THEN ASM_SIMP_TAC (bossLib.std_ss++compLib.STATE_INP_ss) [OUT_ARM6_def,IS_MEMOP2_def]
        THENL [ LDM_TAC THEN UNEXEC_TAC THEN NTAC 2 (POP_ASSUM (K ALL_TAC)), ALL_TAC ]
        THEN POP_ASSUM (K ALL_TAC)
        THEN UNABBREV_TAC `alu`
        THEN ASM_SIMP_TAC (stdi_ss++listSimps.LIST_ss++numSimps.ARITH_ss++numSimps.ARITH_AC_ss)
               ([BIT_W32_NUM,BITS_W32_NUM,combinTheory.o_ABS_R,MUL_EVAL,GSYM FIRST_ADDRESS,LSL_ZERO,
                 ABS_ARM6_def,MEMOP_def,MAP_LDM_MEMOP,OUT_ARM_def,DECODE_PSR,LDM_STM_def,DECODE_LDM_STM_def,
                 ADDR_MODE4_def,DECODE_INST_LDM,ADDRESS_LIST_def,num2exception_exception2num,MAP_GENLIST,
                 GENLIST_CONS,WORD_ADD_0] @ lemmasLib.finish_rws2)
    ]
);

(* -------------------------------------------------------- *)

val STM_TAC =
   PAT_ASSUM `Abbrev (q = NEXT_ARM6 (ARM6 dp ctrl) inp)` (MP_TAC o ONCE_REWRITE_RULE [next_4tuple])
     THEN ASM_SIMP_TAC (booli_ss++compLib.STM_ss++PBETA_CONV_ss) [SND_COND_RAND,FST_COND_RAND]
     THEN TRY ALU_ABBREV_TAC2 THEN STRIP_TAC
     THEN POP_ASSUM (fn th => FULL_SIMP_TAC (bossLib.std_ss++boolSimps.CONJ_ss)
            [OUT_ARM6_def,IS_MEMOP2_def,REWRITE_RULE [markerTheory.Abbrev_def] th]);

val STM_PENCZ_ZERO =
  (GEN_ALL o REWRITE_RULE [MASKN_ZERO] o INST [`x` |-> `0`] o SPEC_ALL o
   CONJUNCT1 o SIMP_RULE std_ss [] o SPEC `ldm`) PENCZ_THM;

val SPEC_PENCZ_THM = (GEN_ALL o REWRITE_RULE [MASKN_ZERO] o SPECL [`n`,`0`] o
                      CONJUNCT1 o SIMP_RULE stdi_ss [] o SPEC `stm`) PENCZ_THM;

val LENGTH_ONE = prove(
  `!l. (LENGTH l = 1) ==> (l = [HD l])`,
  Cases THEN SIMP_TAC list_ss [LENGTH_NIL]
);

val HD_TL = prove(
  `!l. (0 < LENGTH l) ==> (l = ((HD l)::TL l))`,
  Cases THEN SIMP_TAC list_ss [LENGTH_NIL]
);

val REG_WRITE_READ_PC2 = save_thm("REG_WRITE_READ_PC2",
  (GEN_ALL o CONV_RULE (LAND_CONV (ONCE_DEPTH_CONV SYM_CONV)) o SIMP_RULE arith_ss [TO_WRITE_READ6] o
   INST [`n1` |-> `15`] o SPEC_ALL) REG_WRITE_READ_NEQ
);

val STM_PENCZ_ZERO =
  (GEN_ALL o REWRITE_RULE [MASKN_ZERO] o INST [`x` |-> `0`] o SPEC_ALL o
   CONJUNCT1 o SIMP_RULE std_ss [] o SPEC `stm`) PENCZ_THM;

val STM_PENCZ_ONE =
  (GEN_ALL o REWRITE_RULE [] o INST [`x` |-> `1`] o SPEC_ALL o
   CONJUNCT1 o SIMP_RULE std_ss [] o SPEC `stm`) PENCZ_THM;

val STM_INIT =
  (SIMP_RULE (stdi_ss++boolSimps.CONJ_ss)
     [MASK_def,MASKN16_2b,MASKN_150,PENCZ_RP_150,MASKN16_1,STM_PENCZ_ONE,LSL_ZERO] o
   SIMP_RULE (booli_ss++compLib.STM_ss++PBETA_CONV_ss) [IS_ABORT,SND_COND_RAND,FST_COND_RAND] o
   CONV_RULE (RAND_CONV (RHS_CONV (LAND_CONV (ONCE_REWRITE_CONV [next_4tuple])))) o
   CONV_RULE (RAND_CONV (RHS_CONV (ONCE_REWRITE_CONV [next_4tuple]))) o
   SIMP_RULE stdi_ss [IC_def,ABORTINST_def,NXTIC_def,num2exception_exception2num,DECODE_PSR] o
   DISCH `1 < LENGTH (REGISTER_LIST (w2n ireg)) /\ (DECODE_INST (w2n ireg) = stm) /\
          (num2exception aregn2 = software) /\
          CONDITION_PASSED (NZCV (w2n (CPSR_READ psr))) (w2n ireg)` o
   SIMP_CONV bossLib.bool_ss [INIT_ARM6_def])
    ``NEXT_ARM6 (NEXT_ARM6 (INIT_ARM6 (ARM6 (DP reg psr areg din alua alub dout)
             (CTRL pipea pipeaval pipeb pipebval ireg iregval
                ointstart onewinst endinst obaselatch opipebll nxtic nxtis
                nopc1 oorst resetlatch onfq ooonfq oniq oooniq pipeaabt pipebabt iregabt2 dataabt2
                aregn2 mrq2 nbw nrw sctrlreg psrfb oareg
                mask orp oorp mul mu2 borrow2 mshift))) i0) i1``;

val STM_INIT2 = prove(
  `!x. Abbrev (x = <|state := INIT_ARM6 (ARM6 (DP reg psr areg din alua alub dout)
             (CTRL pipea pipeaval pipeb pipebval ireg iregval
                ointstart onewinst endinst obaselatch opipebll nxtic nxtis
                nopc1 oorst resetlatch onfq ooonfq oniq oooniq pipeaabt pipebabt iregabt2 dataabt2
                aregn2 mrq2 nbw nrw sctrlreg psrfb oareg
                mask orp oorp mul mu2 borrow2 mshift)); inp := i|>) /\
   (DECODE_INST (w2n ireg) = stm) /\
   (num2exception aregn2 = software) /\
   CONDITION_PASSED (NZCV (w2n (CPSR_READ psr))) (w2n ireg) /\
   (LENGTH (REGISTER_LIST (w2n ireg)) = l) ==>
   ~FST (DUR_X x) ==>
   (!t. t < SUC l ==> FST (i t)) /\ (DUR_ARM6 x = (2 + (l - 1)))`,
  NTAC 2 STRIP_TAC
    THEN FULL_SIMP_TAC stdi_ss
         [IC_def,ABORTINST_def,NXTIC_def,INIT_ARM6_def,DECODE_PSR,num2exception_exception2num]
    THEN UNABBREV_TAC `x`
    THEN ASM_SIMP_TAC stdi_ss [IC_def,ABORTINST_def,NXTIC_def,DUR_X,DUR_ARM6_def,DUR_IC,SINIT_def,DECODE_PSR]
    THEN STRIP_TAC THEN IMP_RES_TAC IS_RESET_THM2
    THEN POP_ASSUM (SPEC_THEN `SUC l`
           (STRIP_ASSUME_TAC o REWRITE_RULE [DECIDE ``!x y. SUC x <= 2 + (x - 1)``]))
);

val STM_f =
   `\t. (if t = 0 then
           REG_READ6 (REG_WRITE reg usr 15 (REG_READ6 reg usr 15 + 4w)) nbs (RP stm (w2n ireg) (ONECOMP 16 0))
         else
           REG_READ6
             (if WORD_BIT 21 ireg /\ ~(WORD_BITS 19 16 ireg = 15) then
                REG_WRITE (REG_WRITE reg usr 15 (REG_READ6 reg usr 15 + 4w)) nbs (WORD_BITS 19 16 ireg)
                  (WB_ADDRESS (WORD_BIT 23 ireg)
                     (REG_READ6 reg (DECODE_MODE (WORD_BITS 4 0 (CPSR_READ psr))) (WORD_BITS 19 16 ireg))
                     (LENGTH (REGISTER_LIST (w2n ireg))))
              else
                REG_WRITE reg usr 15 (REG_READ6 reg usr 15 + 4w)) nbs
             (RP stm (w2n ireg) (MASKN 16 t (w2n ireg))),F,T,T,T,
          FIRST_ADDRESS (WORD_BIT 24 ireg) (WORD_BIT 23 ireg)
            (REG_READ6 reg (DECODE_MODE (WORD_BITS 4 0 (CPSR_READ psr))) (WORD_BITS 19 16 ireg))
            (WB_ADDRESS (WORD_BIT 23 ireg) (REG_READ6 reg (DECODE_MODE (WORD_BITS 4 0 (CPSR_READ psr)))
                  (WORD_BITS 19 16 ireg)) (LENGTH (REGISTER_LIST (w2n ireg)))) + w32 (SUC t) * 4w)`;

val STM_GENLIST_MEMOP_EQ = prove(
  `!x. Abbrev (x = <|state := INIT_ARM6 (ARM6 (DP reg psr areg din alua alub dout)
             (CTRL pipea pipeaval pipeb pipebval ireg iregval
                ointstart onewinst endinst obaselatch opipebll nxtic nxtis
                nopc1 oorst resetlatch onfq ooonfq oniq oooniq pipeaabt pipebabt iregabt2 dataabt2
                aregn2 mrq2 nbw nrw sctrlreg psrfb oareg
                mask orp oorp mul mu2 borrow2 mshift)); inp := i|>) /\
   Abbrev (nbs = if WORD_BIT 22 ireg then usr else DECODE_MODE (WORD_BITS 4 0 (CPSR_READ psr))) /\
   (DECODE_INST (w2n ireg) = stm) /\
   (num2exception aregn2 = software) /\
   CONDITION_PASSED (NZCV (w2n (CPSR_READ psr))) (w2n ireg) /\
   (LENGTH (REGISTER_LIST (w2n ireg)) = SUC n) ==>
   ~FST (DUR_X x) ==>
    (GENLIST (\t. OUT_ARM6 ((FUNPOW (SNEXT NEXT_ARM6) t (FUNPOW (SNEXT NEXT_ARM6) 2 x)).state)) n =
     GENLIST (^(Term STM_f)) n)`,
  REPEAT STRIP_TAC
    THEN MATCH_MP_TAC GENLIST_FUN_EQ
    THEN MAP_EVERY IMP_RES_TAC [STM_INIT2,STM_INIT]
    THEN UNABBREV_TAC `x`
    THEN ASM_SIMP_TAC (arith_ss++compLib.STATE_INP_ss) [numeralTheory.numeral_funpow,SNEXT,GSYM PROJ_DATA,
           GSYM IS_ABORT_LEM,ADVANCE_def,GSYM ADVANCE_COMP,STM_PENCZ_ZERO,PENCZ_ONE]
    THEN POP_ASSUM (K ALL_TAC)
    THEN REPEAT ALU_ABBREV_TAC2
    THEN REPEAT STRIP_TAC
    THEN `1 < SUC n /\ x <= SUC n - 2 /\ ~(SUC n = 1)` by DECIDE_TAC
    THEN PAT_ASSUM `LENGTH a = b` (ASSUME_TAC o SYM)
    THEN IMP_RES_TAC NEXT_CORE_STM_TN_X
    THEN PAT_ASSUM `~(SUC n = 1)`
         (fn th => FULL_SIMP_TAC std_ss [th,WORD_MULT_CLAUSES])
    THEN POP_ASSUM (STRIP_ASSUME_TAC o (CONV_RULE (TOP_DEPTH_CONV (CHANGED_CONV (SKOLEM_CONV)))))
    THEN UNABBREV_TAC `alu`
    THEN UNABBREV_TAC `alu1`
    THEN ASM_SIMP_TAC (arith_ss++compLib.STATE_INP_ss)
           [OUT_ARM6_def,GSYM WB_ADDRESS,GSYM FIRST_ADDRESS,TO_WRITE_READ6]
);

val FILTER_STM_MEMOPS_X = prove(
  `!y x. Abbrev (x = <|state := INIT_ARM6 (ARM6 (DP reg psr areg din alua alub dout)
             (CTRL pipea pipeaval pipeb pipebval ireg iregval
                ointstart onewinst endinst obaselatch opipebll nxtic nxtis
                nopc1 oorst resetlatch onfq ooonfq oniq oooniq pipeaabt pipebabt iregabt2 dataabt2
                aregn2 mrq2 nbw nrw sctrlreg psrfb oareg
                mask orp oorp mul mu2 borrow2 mshift)); inp := i|>) /\
   (DECODE_INST (w2n ireg) = stm) /\
   (num2exception aregn2 = software) /\
   CONDITION_PASSED (NZCV (w2n (CPSR_READ psr))) (w2n ireg) /\
   (LENGTH (REGISTER_LIST (w2n ireg)) = SUC n) /\
   ~FST (DUR_X x) ==>
   (let l = MOVE_DOUT y (GENLIST
                  (\t.  OUT_ARM6 ((FUNPOW (SNEXT NEXT_ARM6) t (FUNPOW (SNEXT NEXT_ARM6) 2 x)).state)) n) in
    FILTER IS_MEMOP l = l)`,
  SIMP_TAC std_ss [] THEN REPEAT STRIP_TAC
    THEN ABBREV_TAC `nbs = if WORD_BIT 22 ireg then usr else DECODE_MODE (WORD_BITS 4 0 (CPSR_READ psr))`
    THEN IMP_RES_TAC STM_GENLIST_MEMOP_EQ
    THEN POP_ASSUM SUBST1_TAC
    THEN MATCH_MP_TAC ((GEN_ALL o BETA_RULE o ISPEC STM_f) FILTER_MEMOP_NONE)
    THEN RW_TAC bossLib.std_ss [IS_MEMOP_def]
);

val FILTER_STM_MEMOPS_X = SIMP_RULE (bool_ss++boolSimps.LET_ss) [] FILTER_STM_MEMOPS_X;

val STM_MEMOPS = Count.apply prove(
  `!x. Abbrev (x = <|state := INIT_ARM6 (ARM6 (DP reg psr areg din alua alub dout)
             (CTRL pipea pipeaval pipeb pipebval ireg iregval
                ointstart onewinst endinst obaselatch opipebll nxtic nxtis
                nopc1 oorst resetlatch onfq ooonfq oniq oooniq pipeaabt pipebabt iregabt2 dataabt2
                aregn2 mrq2 nbw nrw sctrlreg psrfb oareg
                mask orp oorp mul mu2 borrow2 mshift)); inp := i|>) /\
   (DECODE_INST (w2n ireg) = stm) /\
   (num2exception aregn2 = software) /\
   CONDITION_PASSED (NZCV (w2n (CPSR_READ psr))) (w2n ireg) ==>
   ~FST (DUR_X x) ==>
   (OUT_ARM (ABS_ARM6 x.state) =
    OSMPL_ARM6 x (GENLIST (\t. OUT_ARM6 ((FUNPOW (SNEXT NEXT_ARM6) t x).state)) (DUR_ARM6 x)))`,
  REPEAT STRIP_TAC
    THEN Cases_on `LENGTH (REGISTER_LIST (w2n ireg))`
    THEN MAP_EVERY IMP_RES_TAC [STM_INIT2,INIT_INIT]
    THEN ASM_SIMP_TAC arith_ss [STATE_ARM6_COR,OSMPL_ARM6_def,SINIT_def]
    THEN NTAC 2 (POP_ASSUM (K ALL_TAC))
    THENL [
      FULL_SIMP_TAC std_ss [INIT_ARM6_def,IC_def,ABORTINST_def,NXTIC_def,DECODE_PSR,num2exception_exception2num]
        THEN UNABBREV_TAC `x`
        THEN SIMP_TAC (list_ss++compLib.STATE_INP_ss) [SUC2NUM GENLIST,OUT_ARM6_def,IS_MEMOP2_def,FILTER_MEMOP_ONE,
               FILTER_MEMOP_SINGLETON,ADVANCE_def,SNEXT,numeralTheory.numeral_funpow,SNOC,ABS_ARM6_def]
        THEN REPEAT (PAT_ABBREV_TAC `q = NEXT_ARM6 a b`)
        THEN `!mask. PENCZ stm (w2n ireg) mask` by metisLib.METIS_TAC [PENCZ_THM2,PENCZ_THM3]
        THEN STM_TAC THEN IMP_RES_TAC LENGTH_NIL
        THEN ASM_SIMP_TAC (stdi_ss++listSimps.LIST_ss) [BIT_W32_NUM,BITS_W32_NUM,OUT_ARM_def,DECODE_PSR,
               LDM_STM_def,STM_LIST_def,DECODE_LDM_STM_def,ADDR_MODE4_def,DECODE_INST_STM,
               ADDRESS_LIST_def,PENCZ_RP_150,GENLIST,ZIP,MAP],
      Cases_on `n`
        THENL [
          FULL_SIMP_TAC std_ss [INIT_ARM6,IC_def,ABORTINST_def,NXTIC_def,DECODE_PSR,num2exception_exception2num]
            THEN UNABBREV_TAC `x`
            THEN SIMP_TAC (list_ss++compLib.STATE_INP_ss) [SUC2NUM GENLIST,OUT_ARM6_def,IS_MEMOP2_def,FILTER_MEMOP_ONE,
                   FILTER_MEMOP_SINGLETON,ADVANCE_def,SNEXT,numeralTheory.numeral_funpow,SNOC,ABS_ARM6_def]
            THEN REPEAT (PAT_ABBREV_TAC `q = NEXT_ARM6 a b`)
            THEN NTAC 2 STM_TAC
            THEN `LENGTH (FST (ADDR_MODE4 (WORD_BIT 24 ireg) (WORD_BIT 23 ireg)
                     (REG_READ6 reg (DECODE_MODE (WORD_BITS 4 0 (CPSR_READ psr)))
                     (WORD_BITS 19 16 ireg)) (w2n ireg))) = 1` by PROVE_TAC [LENGTH_ADDR_MODE4]
            THEN POP_ASSUM (ASSUME_TAC o (MATCH_MP LENGTH_ONE))
            THEN UNABBREV_TAC `alu`
            THEN ASM_SIMP_TAC (stdi_ss++numSimps.ARITH_ss++PBETA_CONV_ss) ([PENCZ_RP_150,SPEC_PENCZ_THM,
                   FILTER_MEMOP_SINGLETON,IS_MEMOP2_def,BIT_W32_NUM,BITS_W32_NUM,OUT_ARM_def,DECODE_PSR,
                   LDM_STM_def,STM_LIST_def,LSL_ZERO,DECODE_LDM_STM_def,DECODE_INST_STM,ADDRESS_LIST_def,
                   PENCZ_RP_150,MAP,MEMOP_def,SUC2NUM GENLIST,SNOC,SND_ADDR_MODE4,MASKN_ZERO,GSYM WB_ADDRESS,
                   GSYM FIRST_ADDRESS,RP_LT_16_0,ALUOUT_ALU_logic,WORD_MULT_CLAUSES,
                   FST_HD_FST_ADDR_MODE4,LENGTH_ONE] @ lemmasLib.finish_rws2)
            THEN POP_ASSUM SUBST1_TAC
            THEN ASM_SIMP_TAC arith_ss [ZIP,MAP,FST_HD_FST_ADDR_MODE4]
            THEN RW_TAC arith_ss ([RP_LT_16_0] @ lemmasLib.finish_rws2)
            THEN Cases_on `RP stm (w2n ireg) (ONECOMP 16 0) = 15`
            THEN RW_TAC arith_ss ([RP_LT_16_0,REG_WRITE_READ_NEQ,REG_WRITE_READ_PC2] @ lemmasLib.finish_rws2),
          IMP_RES_TAC FILTER_STM_MEMOPS_X
            THEN ASM_SIMP_TAC list_ss [(GEN_ALL o INST [`b` |-> `2`] o SPEC_ALL) onestepTheory.FUNPOW_COMP,
                   NULL_GENLIST,SUC2NUM GENLIST,FILTER_MEMOP_ONE,FILTER_MEMOP_SINGLETON,SNOC,GENLIST_APPEND,
                   HD_GENLIST,CONJUNCT1 FUNPOW]
            THEN POP_ASSUM (K ALL_TAC)
            THEN ABBREV_TAC `nbs = if WORD_BIT 22 ireg then usr else DECODE_MODE (WORD_BITS 4 0 (CPSR_READ psr))`
            THEN IMP_RES_TAC STM_GENLIST_MEMOP_EQ
            THEN POP_ASSUM SUBST1_TAC
            THEN SIMP_TAC bossLib.arith_ss [SNEXT,numeralTheory.numeral_funpow]
            THEN REPEAT (PAT_ABBREV_TAC `q = NEXT_ARM6 a b`)
            THEN FULL_SIMP_TAC bossLib.std_ss [INIT_ARM6,IC_def,ABORTINST_def,NXTIC_def,DECODE_PSR,
                   num2exception_exception2num]
            THEN UNABBREV_TAC `x`
            THEN FULL_SIMP_TAC (bossLib.std_ss++compLib.STATE_INP_ss)
                   [ADVANCE_def,OUT_ARM6_def,IS_MEMOP2_def,ABS_ARM6_def]
            THEN NTAC 2 STM_TAC
            THEN ASM_SIMP_TAC (booli_ss++numSimps.ARITH_ss) [MASK_def,MASKN16_2b,MASKN_150,PENCZ_RP_150,MASKN16_1,
                   STM_PENCZ_ZERO,STM_PENCZ_ONE,LSL_ZERO,GSYM ADVANCE_COMP]
            THEN UNABBREV_TAC `nbs`
            THEN ABBREV_TAC `cpsr = CPSR_READ psr`
            THEN ABBREV_TAC `nbs = DECODE_MODE (WORD_BITS 4 0 cpsr)`
            THEN `1 < LENGTH (REGISTER_LIST (w2n ireg))` by DECIDE_TAC
            THEN `!t. t < SUC (LENGTH (REGISTER_LIST (w2n ireg))) ==> FST (i t)` by ASM_SIMP_TAC arith_ss []
            THEN IMP_RES_TAC NEXT_CORE_STM_TN_W1
            THEN POP_ASSUM (STRIP_ASSUME_TAC o (CONV_RULE (TOP_DEPTH_CONV (CHANGED_CONV (SKOLEM_CONV)))))
            THEN `SUC n' = LENGTH (REGISTER_LIST (w2n ireg)) - 1` by DECIDE_TAC
            THEN POP_ASSUM SUBST1_TAC
            THEN ASM_SIMP_TAC (bossLib.std_ss++compLib.STATE_INP_ss) [OUT_ARM6_def]
            THEN POP_ASSUM (K ALL_TAC)
            THEN `LENGTH (FST (ADDR_MODE4 (WORD_BIT 24 ireg) (WORD_BIT 23 ireg)
                     (REG_READ6 reg nbs (WORD_BITS 19 16 ireg)) (w2n ireg))) = SUC (SUC n')`
              by PROVE_TAC [LENGTH_ADDR_MODE4]
            THEN UNABBREV_TAC `alu`
            THEN UNABBREV_TAC `alu1`
            THEN ASM_SIMP_TAC (stdi_ss++PBETA_CONV_ss++listSimps.LIST_ss++numSimps.ARITH_ss++numSimps.ARITH_AC_ss)
                   ([BIT_W32_NUM,BITS_W32_NUM,combinTheory.o_ABS_R,MUL_EVAL,GSYM FIRST_ADDRESS,LSL_ZERO,
                     ABS_ARM6_def,MEMOP_def,MAP_STM_MEMOP,OUT_ARM_def,DECODE_PSR,LDM_STM_def,DECODE_LDM_STM_def,
                     SND_ADDR_MODE4,DECODE_INST_STM,ADDRESS_LIST_def,num2exception_exception2num,MAP_GENLIST,
                     WORD_ADD_0,STM_LIST_def,SND_ADDR_MODE4,GSYM WB_ADDRESS,GSYM FIRST_ADDRESS,
                     FST_HD_FST_ADDR_MODE4,ZIP_GENLIST,LENGTH_GENLIST] @ lemmasLib.finish_rws2)
            THEN ASM_SIMP_TAC list_ss [(GEN_ALL o SPEC `SUC n`) GENLIST_CONS,FST_HD_FST_ADDR_MODE4,WORD_ADD_0]
            THEN CONJ_TAC
            THENL [
              RW_TAC arith_ss ([RP_LT_16_0] @ lemmasLib.finish_rws2)
                THEN Cases_on `RP stm (w2n ireg) (ONECOMP 16 0) = 15`
                THEN RW_TAC arith_ss ([RP_LT_16_0,REG_WRITE_READ_NEQ,REG_WRITE_READ_PC2] @ lemmasLib.finish_rws2),
              MATCH_MP_TAC GENLIST_FUN_EQ
                THEN SIMP_TAC arith_ss [GSYM ADD1]
                THEN `SUC n' < LENGTH (REGISTER_LIST (w2n ireg))` by ASM_SIMP_TAC arith_ss [LENGTH_ADDR_MODE4]
                THEN RW_TAC arith_ss ([RP_LT_16,REG_WRITE_READ_NEQ,REG_WRITE_READ_PC2,
                       (GSYM o CONJUNCT2) EL,REGISTER_LIST_STM_THM] @ lemmasLib.finish_rws2)
                THEN PAT_ASSUM `q = WORD_BITS 19 16 ireg` (SUBST1_TAC o SYM)
                THENL [
                  Cases_on `RP stm (w2n ireg) (MASKN 16 (SUC n') (w2n ireg)) = 15`,
                  Cases_on `RP stm (w2n ireg) (MASKN 16 (SUC x) (w2n ireg)) = 15`,
                  Cases_on `RP stm (w2n ireg) (MASKN 16 (SUC n') (w2n ireg)) = 15`,
                  Cases_on `RP stm (w2n ireg) (MASKN 16 (SUC x) (w2n ireg)) = 15`
                ]
                THEN RW_TAC arith_ss ([RP_LT_16,RP_LT_16_0,RP_NOT_EQUAL_ZERO,REG_WRITE_READ_NEQ,
                       REG_WRITE_READ_PC2] @ lemmasLib.finish_rws2)
            ]
        ]
    ]
);

(* -------------------------------------------------------- *)

val ABS_INIT = prove(
  `!x. ABS_ARM6 (INIT_ARM6 x) = ABS_ARM6 x`,
  Cases THEN Cases_on `d` THEN Cases_on `c`
    THEN SIMP_TAC std_ss [INIT_ARM6_def,ABS_ARM6_def,num2exception_exception2num]
);

val PROJ_STATE = simpLib.SIMP_PROVE (srw_ss()) [] ``!a b. <|state := a; inp := b|>.state = a``;
val PROJ_INP = simpLib.SIMP_PROVE (srw_ss()) [] ``!a b. <|state := a; inp := b|>.inp = b``;

val ARM6_OUT_THM = prove(
  `!x. (x = <|state := ARM6 (DP reg psr areg din alua alub dout)
               (CTRL pipea pipeaval pipeb pipebval ireg iregval
                ointstart onewinst endinst obaselatch opipebll nxtic nxtis
                nopc1 oorst resetlatch onfq ooonfq oniq oooniq pipeaabt pipebabt iregabt2 dataabt2
                aregn2 mrq2 nbw nrw sctrlreg psrfb oareg
                mask orp oorp mul mul2 borrow2 mshift); inp := i|>) ==>
    i IN STRM_ARM6 ==>
   (OUTPUT ARM_SPEC <|state := ABS_ARM6 x.state; inp := SMPL_ARM6 x|> 0 =
      OSMPL OSMPL_ARM6 ARM6_SPEC IMM_ARM6 (x,OUTPUT ARM6_SPEC x) 0)`,
  RW_TAC bool_ss []
    THEN SIMP_TAC (srw_ss()++boolSimps.LET_ss) [OUTPUT_def,ARM_SPEC_def,ARM6_SPEC_def,STATE_ARM6_COR,
                            STATE_ARM_def,FUNPOW,ADVANCE_ZERO,IMM_LEN_def,OSMPL_def,SINIT_def,
                            SUC2NUM IMM_ARM6_def,MAP_STRM_def,PACK_def]
    THEN ABBREV_TAC `x = <|state := INIT_ARM6 (ARM6 (DP reg psr areg din alua alub dout)
           (CTRL pipea pipeaval pipeb pipebval ireg iregval ointstart onewinst endinst obaselatch opipebll
                 nxtic nxtis nopc1 oorst resetlatch onfq ooonfq oniq oooniq pipeaabt pipebabt iregabt2 dataabt2
                 aregn2 mrq2 nbw nrw sctrlreg psrfb oareg mask orp oorp mul mul2 borrow2 mshift)); inp := i|>`
    THEN Cases_on `FST (DUR_X x)`
    THENL [ (* reset *)
      UNABBREV_TAC `x` THEN ASM_SIMP_TAC (std_ss++compLib.STATE_INP_ss) [OSMPL_ARM6_def,ABS_INIT],
      Cases_on `(num2exception aregn2 = software) ==> ~CONDITION_PASSED (NZCV (w2n (CPSR_READ psr))) (w2n ireg)`
        THENL [ (* exception or not executed *)
          IMP_RES_TAC NON_MEMOPS_UNEXEC
            THEN FULL_SIMP_TAC stdi_ss [IMP_DISJ_THM,OSMPL_ARM6_def,ABS_ARM6_def,OUT_ARM_def,DECODE_PSR,MAP],
          FULL_SIMP_TAC bool_ss [] THEN PAT_ABBREV_TAC `y = ARM6 d c`
            THEN `ABS_ARM6 y = ABS_ARM6 x.state`
              by metisLib.METIS_TAC [ABS_INIT,PROJ_STATE,markerTheory.Abbrev_def]
            THEN POP_ASSUM SUBST1_TAC THEN UNABBREV_TAC `y`
            THEN Cases_on `DECODE_INST (w2n ireg) = ldm` THEN1 IMP_RES_TAC LDM_MEMOPS
            THEN Cases_on `DECODE_INST (w2n ireg) = stm` THEN1 IMP_RES_TAC STM_MEMOPS
            THEN Cases_on `DECODE_INST (w2n ireg) IN {swp; ldr; str}` THEN1 IMP_RES_TAC BASIC_MEMOPS
            THEN Cases_on `DECODE_INST (w2n ireg) IN {mrs_msr; data_proc; reg_shift; br; swi_ex; cdp_und; unexec}`
            THENL [
              IMP_RES_TAC NON_MEMOPS
                THEN FULL_SIMP_TAC (stdi_ss++pred_setSimps.PRED_SET_ss++compLib.STATE_INP_ss)
                       [markerTheory.Abbrev_def,ABS_INIT,OSMPL_ARM6_def,ABS_ARM6_def,OUT_ARM_def,DECODE_PSR,MAP],
              FULL_SIMP_TAC (bool_ss++pred_setSimps.PRED_SET_ss) []
                THEN `DECODE_INST (w2n ireg) = mla_mul`
                  by (Cases_on `DECODE_INST (w2n ireg)` THEN FULL_SIMP_TAC bossLib.bool_ss [])
                THEN IMP_RES_TAC MEM_MLA_MUL
                THEN IMP_RES_TAC ((GEN_ALL o BETA_RULE o
                       ISPEC `\t. OUT_ARM6 ((FUNPOW (SNEXT NEXT_ARM6) t x).state)`) FILTER_MEMOP_ALL)
                THEN FULL_SIMP_TAC (stdi_ss++compLib.STATE_INP_ss)
                       [markerTheory.Abbrev_def,ABS_INIT,OSMPL_ARM6_def,ABS_ARM6_def,OUT_ARM_def,DECODE_PSR,MAP]
            ]
        ]
    ]
);

val ARM6_OUT_THM = save_thm("ARM6_OUT_THM",
  GEN_ALL (SIMP_RULE (srw_ss()) [] ARM6_OUT_THM)
);

(* -------------------------------------------------------- *)

val FST_DUR_X = prove(
   `!x. FST (DUR_X x) ==> 
         (?t. IS_RESET x.inp t) /\
         (DUR_ARM6 x =
          (LEAST t.  IS_RESET x.inp t /\ ~IS_RESET x.inp (t + 1) /\ ~IS_RESET x.inp (t + 2)) + 3)`,
  Cases THEN Cases_on `a` THEN Cases_on `d` THEN Cases_on `c`
    THEN RW_TAC std_ss [DUR_X_def,DECODE_PSR,DUR_ARM6_def]
    THEN metisLib.METIS_TAC []
);

val pat3 = `z = (fx : word32 -> word32 -> bool -> word32 -> bool -> word32 -> num -> bool -> bool ->
  bool -> bool -> bool -> bool -> word32 -> bool -> num -> word32 -> bool)
  z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 z15 z16`;

val pat4 = `z = (fx : word32 -> (register -> word32) -> word32 -> bool -> word32 -> bool -> word32 ->
  bool -> bool -> bool -> bool -> bool -> bool -> num -> num -> num -> num -> word32 -> word32 ->
  bool -> bool -> word32 -> num -> word32 -> word32 -> bool)
  z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 z15 z16 z17 z18 z19 z20 z21 z22 z23 z24`;

val pat5 = `z = (fx : word32 -> (register -> word32) -> word32 -> bool -> word32 -> bool -> word32 ->
  bool -> bool -> bool -> bool -> bool -> bool -> num -> num -> num -> num -> word32 -> word32 ->
  bool -> bool -> word32 -> num -> word32 -> word32 -> num)
  z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 z15 z16 z17 z18 z19 z20 z21 z22 z23 z24`;

val REV_ADD4 = DECIDE (Term `a + b + c + d = d + c + b + a`);

val LDM_LEM = prove(
  `!base abort. 0 < LENGTH (REGISTER_LIST (w2n ireg)) ==>
     (((base = 15) /\ abort \/
       ~((if abort /\ ~(base = 15) then
             base
          else
             (if ~abort then
                RP ldm (w2n ireg) (MASKN 16 (LENGTH (REGISTER_LIST (w2n ireg)) - 1) (w2n ireg))
             else
                ARB)) = 15)) = (abort \/ ~WORD_BIT 15 ireg))`,
  REPEAT STRIP_TAC
    THEN Cases_on `base = 15` THEN ASM_SIMP_TAC std_ss [LEM,RP_LAST_15]
    THEN Cases_on `abort` THEN ASM_SIMP_TAC std_ss [RP_LAST_15]
);

val ARM6_TCON_LEM1 = Count.apply prove(
  `!x. (x = <|state := ARM6 (DP reg psr areg din alua alub dout)
               (CTRL pipea pipeaval pipeb pipebval ireg iregval
                ointstart onewinst endinst obaselatch opipebll nxtic nxtis
                nopc1 oorst resetlatch onfq ooonfq oniq oooniq pipeaabt pipebabt iregabt2 dataabt2
                aregn2 mrq2 nbw nrw sctrlreg psrfb oareg
                mask orp oorp mul mul2 borrow2 mshift); inp := i|>) ==>
    i IN STRM_ARM6 ==>
   (INIT_ARM6 (STATE_ARM6 (IMM_ARM6 x 1) x) = STATE_ARM6 (IMM_ARM6 x 1) x)`,
  RW_TAC bool_ss []
    THEN SIMP_TAC (srw_ss()++boolSimps.LET_ss) [ARM6_SPEC_def,STATE_ARM6_COR,FUNPOW,ADVANCE_ZERO,
           SINIT_def,SUC2NUM IMM_ARM6_def]
    THEN ABBREV_TAC `x = <|state := INIT_ARM6 (ARM6 (DP reg psr areg din alua alub dout)
           (CTRL pipea pipeaval pipeb pipebval ireg iregval ointstart onewinst endinst obaselatch opipebll
                 nxtic nxtis nopc1 oorst resetlatch onfq ooonfq oniq oooniq pipeaabt pipebabt iregabt2 dataabt2
                 aregn2 mrq2 nbw nrw sctrlreg psrfb oareg mask orp oorp mul mul2 borrow2 mshift)); inp := i|>`
    THEN Cases_on `FST (DUR_X x)`
    THENL [ (* reset *)
      PAT_ASSUM `i IN STRM_ARM6` (fn th => `x.inp IN STRM_ARM6` by
           metisLib.METIS_TAC [th,PROJ_INP,markerTheory.Abbrev_def])
        THEN MAP_EVERY IMP_RES_TAC [FST_DUR_X,LEAST_NOT_RESET]
        THEN PAT_ASSUM `IS_RESET x.inp t` (K ALL_TAC)
        THEN MAP_EVERY IMP_RES_TAC [LEAST_RESET_GT_TWO,PREVIOUS_THREE_RESET]
        THEN REPEAT (PAT_ASSUM `~a ==> b` (K ALL_TAC))
        THEN IMP_RES_TAC (DECIDE ``!n. (2 < n) ==> (n = n - 3 + 3)``)
        THEN POP_ASSUM (fn th => ONCE_REWRITE_TAC [th] THEN RULE_ASSUM_TAC (ONCE_REWRITE_RULE [th]))
        THEN ASM_REWRITE_TAC [DECIDE ``!a. a + 3 + 3 = 6 + a``]
        THEN REWRITE_TAC [onestepTheory.FUNPOW_COMP]
        THEN PAT_ABBREV_TAC `y = FUNPOW (SNEXT NEXT_ARM6) xt x`
        THEN RULE_ASSUM_TAC (ONCE_REWRITE_RULE [GSYM STATE_FUNPOW_INIT2])
        THEN UNABBREV_TAC `y` THEN PAT_ABBREV_TAC `y = (FUNPOW (SNEXT next) xt x).state`
        THEN IMP_RES_TAC SPEC_AFTER_NRESET2 THEN POP_ASSUM (SPEC_THEN `y` ASSUME_TAC)
        THEN FULL_SIMP_TAC arith_ss [AFTER_NRESET2_THM3],
      Cases_on `(num2exception aregn2 = software) ==> ~CONDITION_PASSED (NZCV (w2n (CPSR_READ psr))) (w2n ireg)`
        THEN1 IMP_RES_TAC (SIMP_RULE std_ss [] NON_MEMOPS_UNEXEC)
        THEN FULL_SIMP_TAC bool_ss []
        THEN Cases_on `DECODE_INST (w2n ireg) IN {mrs_msr; data_proc; reg_shift; br; swi_ex; cdp_und; unexec}`
        THEN1 IMP_RES_TAC (SIMP_RULE std_ss [] NON_MEMOPS)
        THEN Cases_on `DECODE_INST (w2n ireg) IN {swp; ldr; str}`
        THEN1 IMP_RES_TAC (SIMP_RULE std_ss [] BASIC_MEMOPS)
        THEN ABBREV_TAC `s = (FUNPOW (SNEXT NEXT_ARM6) (DUR_ARM6 x) x).state`
        THEN POP_ASSUM (MP_TAC o SYM o REWRITE_RULE [markerTheory.Abbrev_def])
        THEN Cases_on `DECODE_INST (w2n ireg)`
        THEN FULL_SIMP_TAC (bool_ss++pred_setSimps.PRED_SET_ss) [] THEN REPEAT (PAT_ASSUM `~(r = t)` (K ALL_TAC))
        THEN FULL_SIMP_TAC stdi_ss [INIT_ARM6] THEN UNABBREV_TAC `x`
        THEN FULL_SIMP_TAC stdi_ss [DUR_X2,DUR_ARM6_def,DUR_IC_def]
        THENL [ (* mla_mul *)
          REWRITE_TAC [GSYM SUC_ONE_ADD,FUNPOW]
            THEN lemmasLib.UNFOLD_NEXT THEN compLib.MLA_MUL_TAC
            THEN ASM_SIMP_TAC (arith_ss++PBETA_CONV_ss) [iclass_distinct,FST_COND_RAND,SND_COND_RAND,IF_NEG,
                   GSYM WORD_BITS_def,LSL_ZERO,bitsTheory.BITS_ZERO2,MULT_ALU6_ZERO,TO_WRITE_READ6]
            THEN REWRITE_TAC [GSYM DE_MORGAN_THM,IF_NEG]
            THEN ABBREV_TAC `pc = REG_READ6 reg usr 15`
            THEN ABBREV_TAC `cpsr = CPSR_READ psr`
            THEN ABBREV_TAC `nbs = DECODE_MODE (WORD_BITS 4 0 cpsr)`
            THEN IMP_RES_TAC IS_RESET_THM
            THEN POP_ASSUM (ASSUME_TAC o REWRITE_RULE [DECIDE ``1 + n = n + 1``])
            THEN IMP_RES_TAC MLA_MUL_TN
            THEN POP_ASSUM (STRIP_ASSUME_TAC o (CONV_RULE (TOP_DEPTH_CONV (CHANGED_CONV (SKOLEM_CONV)))))
            THEN ASM_SIMP_TAC (arith_ss++compLib.STATE_INP_ss) []
            THEN REPEAT (PAT_ABBREV_TAC pat3 THEN POP_ASSUM (K ALL_TAC))
            THEN POP_ASSUM (ASSUME_TAC o GEN_ALL o SIMP_RULE (std_ss++pred_setSimps.PRED_SET_ss) [] o
                            (MATCH_MP (DECIDE ``a /\ b /\ c ==> a /\ b``)) o SPEC_ALL)
            THEN lemmasLib.FINISH_OFF 1
            THEN FULL_SIMP_TAC std_ss [GSYM exception2num_num2exception,exception_BIJ,num2exception_thm,
                   exception_distinct,num2exception_thm]
            THEN metisLib.METIS_TAC [], (* ldm *)
          ONCE_REWRITE_TAC [REV_ADD4] THEN ONCE_REWRITE_TAC [onestepTheory.FUNPOW_COMP]
            THEN IMP_RES_TAC IS_RESET_THM
            THEN IMP_RES_TAC (simpLib.SIMP_PROVE arith_ss []
                    ``(!t. t < (2 + x) + y + z ==> FST (i t)) ==> (!t. t < 2 ==> FST (i t))``)
            THEN NTAC 2 (lemmasLib.UNFOLD_NEXT THEN compLib.LDM_TAC THEN ALU_ABBREV_TAC)
            THEN SIMP_TAC (stdi_ss++boolSimps.CONJ_ss++PBETA_CONV_ss) [onestepTheory.FUNPOW_COMP,LSL_ZERO,NOT_T3]
            THEN Cases_on `WORD_BITS 15 0 ireg = 0`
            THEN ASM_SIMP_TAC stdi_ss [MASKN_150,PENCZ_RP_150,MASKN16_2,MASKN16_1,PENCZ_THM3]
            THENL [
              MAP_EVERY IMP_RES_TAC [PENCZ_THM2,WORD_BITS_150_ZERO]
                THEN ASM_REWRITE_TAC [SUB_0,FUNPOW]
                THEN lemmasLib.UNFOLD_NEXT THEN compLib.LDM_TAC
                THEN SIMP_TAC (stdi_ss++compLib.STATE_INP_ss) [] THEN lemmasLib.FINISH_OFF 0,
              `0 < LENGTH (REGISTER_LIST (w2n ireg))` by FULL_SIMP_TAC arith_ss [PENCZ_THM2]
                THEN IMP_RES_TAC (simpLib.SIMP_PROVE arith_ss []
                       ``0 < x /\ (!t. t < (2 + (x - 1)) + y + z ==> FST (i t)) ==> (!t. t < SUC x ==> FST (i t))``)
                THEN `FST (i (LENGTH (REGISTER_LIST (w2n ireg)) + 1))`
                  by metisLib.METIS_TAC [DECIDE ``!w. 0 < w ==> w + 1 < 2 + (w - 1) + 1 + x``]
                THEN ABBREV_TAC `abort = ?s. s < LENGTH (REGISTER_LIST (w2n ireg)) /\ FST (SND (i (s + 1)))`
                THEN `(!s. ~(s < LENGTH (REGISTER_LIST (w2n ireg))) \/ ~FST (SND (i (s + 1)))) = ~abort`
                  by metisLib.METIS_TAC [markerTheory.Abbrev_def]
                THEN IMP_RES_TAC NEXT_CORE_LDM_TN_W1
                THEN POP_ASSUM (STRIP_ASSUME_TAC o (CONV_RULE (TOP_DEPTH_CONV (CHANGED_CONV (SKOLEM_CONV)))))
                THEN ASM_SIMP_TAC (stdi_ss++numSimps.ARITH_ss) [PENCZ_ONE,GSYM ADVANCE_COMP,LDM_PENCZ_ZERO]
                THEN POP_ASSUM (ASSUME_TAC o GEN_ALL o SIMP_RULE (std_ss++pred_setSimps.PRED_SET_ss) [] o
                                (MATCH_MP (DECIDE ``a /\ b /\ c ==> a /\ b``)) o SPEC_ALL)
                THEN REPEAT (PAT_ABBREV_TAC pat2 THEN POP_ASSUM (K ALL_TAC))
                THEN PAT_ABBREV_TAC pat THEN REPEAT (PAT_ABBREV_TAC pat THEN POP_ASSUM (K ALL_TAC))
                THEN lemmasLib.UNFOLD_NEXT THEN compLib.LDM_TAC
                THEN ASM_SIMP_TAC (stdi_ss++numSimps.ARITH_ss++boolSimps.CONJ_ss++PBETA_CONV_ss)
                       [ALUOUT_ALU_logic,LSL_ZERO,LDM_LEM,IS_ABORT_LEM,DECIDE ``a /\ b \/ ~a = a ==> b``]
                THEN Cases_on `WORD_BIT 15 ireg /\ ~abort`
                THEN ASM_SIMP_TAC std_ss [FUNPOW,RP_LAST_15]
                THENL [
                  FULL_SIMP_TAC stdi_ss [IS_ABORT_LEM]
                    THEN `FST (i (LENGTH (REGISTER_LIST (w2n ireg)) + 1 + 1)) /\
                          FST (i (LENGTH (REGISTER_LIST (w2n ireg)) + 1 + 2))`
                      by ASM_SIMP_TAC arith_ss []
                    THEN NTAC 2 (lemmasLib.UNFOLD_NEXT THEN compLib.UNEXEC_TAC)
                    THEN SIMP_TAC (stdi_ss++compLib.STATE_INP_ss) [] THEN lemmasLib.FINISH_OFF 0,
                  FULL_SIMP_TAC (std_ss++compLib.STATE_INP_ss) [] THENL [
                      `~(RP ldm (w2n ireg) (MASKN 16 (LENGTH (REGISTER_LIST (w2n ireg)) - 1) (w2n ireg)) = 15)`
                         by metisLib.METIS_TAC [RP_LAST_15]
                        THEN `LENGTH (REGISTER_LIST (w2n ireg)) - 1 < LENGTH (REGISTER_LIST (w2n ireg))`
                         by DECIDE_TAC, ALL_TAC]
                    THEN lemmasLib.FINISH_OFF 2
                    THEN FULL_SIMP_TAC arith_ss [REG_WRITEN_COMMUTES,REG_READ_WRITE,REG_WRITE_READ_PC,
                           RP_LT_16,REG_WRITE_COMMUTE_PC,REGISTER_RANGES,ALUOUT_ALU_logic,LSL_ZERO,
                           DECIDE ``!a b. ~a \/ b = (a ==> b)``]
                ]
            ], (* stm *)
          ONCE_REWRITE_TAC [ADD_COMM] THEN REWRITE_TAC [onestepTheory.FUNPOW_COMP]
            THEN IMP_RES_TAC IS_RESET_THM
            THEN IMP_RES_TAC (simpLib.SIMP_PROVE arith_ss []
                    ``(!t. t < (2 + x) ==> FST (i t)) ==> (!t. t < 2 ==> FST (i t))``)
            THEN NTAC 2 (lemmasLib.UNFOLD_NEXT THEN compLib.STM_TAC THEN ALU_ABBREV_TAC)
            THEN ASM_SIMP_TAC (stdi_ss++boolSimps.CONJ_ss++PBETA_CONV_ss) [LSL_ZERO]
            THEN Cases_on `WORD_BITS 15 0 ireg = 0`
            THEN ASM_SIMP_TAC stdi_ss [MASKN_150,PENCZ_RP_150,MASKN16_1,PENCZ_THM3]
            THENL [
              IMP_RES_TAC PENCZ_THM2 THEN ASM_REWRITE_TAC [SUB_0,FUNPOW] THEN lemmasLib.FINISH_OFF 0,
              `~PENCZ stm (w2n ireg) (ONECOMP 16 0)` by FULL_SIMP_TAC arith_ss [SPEC_PENCZ_THM,PENCZ_THM2]
                THEN Cases_on `LENGTH (REGISTER_LIST (w2n ireg)) = 1`
                THENL [
                  `PENCZ stm (w2n ireg) (MASKN 16 1 (w2n ireg))` by PROVE_TAC [PENCZ_THM]
                    THEN ASM_REWRITE_TAC [SUB_EQUAL_0,FUNPOW] THEN lemmasLib.FINISH_OFF 0,
                  `1 < LENGTH (REGISTER_LIST (w2n ireg))` by FULL_SIMP_TAC arith_ss [PENCZ_THM2]
                    THEN `~(PENCZ stm (w2n ireg) (MASKN 16 1 (w2n ireg)))` by PROVE_TAC [PENCZ_THM]
                    THEN ASM_SIMP_TAC stdi_ss [LSL_ZERO,MASK_def,MASKN16_2b,GSYM ADVANCE_COMP]
                    THEN IMP_RES_TAC (simpLib.SIMP_PROVE arith_ss []
                           ``!w. 1 < w ==> (!t. t < 2 + (w - 1) ==> FST (i t)) ==> (!t. t < SUC w ==> FST (i t))``)
                    THEN ABBREV_TAC `cpsr = CPSR_READ psr`
                    THEN ABBREV_TAC `nbs = DECODE_MODE (WORD_BITS 4 0 cpsr)`
                    THEN IMP_RES_TAC NEXT_CORE_STM_TN_W1
                    THEN POP_ASSUM (STRIP_ASSUME_TAC o (CONV_RULE (TOP_DEPTH_CONV (CHANGED_CONV (SKOLEM_CONV)))))
                    THEN ASM_SIMP_TAC stdi_ss []
                    THEN POP_ASSUM (ASSUME_TAC o GEN_ALL o SIMP_RULE (std_ss++pred_setSimps.PRED_SET_ss) [] o
                                    (MATCH_MP (DECIDE ``a /\ b /\ c ==> a /\ b``)) o SPEC_ALL)
                    THEN REPEAT (PAT_ABBREV_TAC pat4 THEN POP_ASSUM (K ALL_TAC))
                    THEN PAT_ABBREV_TAC pat5 THEN REPEAT (PAT_ABBREV_TAC pat5 THEN POP_ASSUM (K ALL_TAC))
                    THEN lemmasLib.FINISH_OFF 2
                    THEN FULL_SIMP_TAC std_ss [GSYM exception2num_num2exception,exception_BIJ,num2exception_thm,
                           markerTheory.Abbrev_def,exception_distinct]
                    THEN metisLib.METIS_TAC []
                ]
            ]
        ] (* ic *)
    ] (* reset *)
);

val ARM6_TCON_ONE = save_thm("ARM6_TCON_ONE",GEN_ALL (SIMP_RULE bool_ss [] ARM6_TCON_LEM1));

(* -------------------------------------------------------- *)

val _ = export_theory();
