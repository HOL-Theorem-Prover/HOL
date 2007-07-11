(* ========================================================================= *)
(* FILE          : interruptsScript.sml                                      *)
(* DESCRIPTION   : A collection of lemmas about exception/interrupt handling *)
(*                                                                           *)
(* AUTHOR        : (c) Anthony Fox, University of Cambridge                  *)
(* DATE          : 2004-2005                                                 *)
(* ========================================================================= *)

(* interactive use:
  app load ["pred_setSimps", "io_onestepTheory", "armLib", "wordsLib",
            "armTheory", "coreTheory", "lemmasTheory"];
*)

open HolKernel boolLib bossLib;
open Q arithmeticTheory wordsLib;
open io_onestepTheory wordsTheory armTheory coreTheory lemmasTheory;

val _ = new_theory "interrupts";

(* ------------------------------------------------------------------------- *)

infix \\
val op \\ = op THEN;

val std_ss = std_ss ++ boolSimps.LET_ss;
val arith_ss = arith_ss ++ boolSimps.LET_ss;
val ICLASS_ss = armLib.ICLASS_ss;
val SIZES_ss = wordsLib.SIZES_ss;

fun Cases_on_arm6inp tm = FULL_STRUCT_CASES_TAC (SPEC tm arm6inp_nchotomy);
fun Cases_arm6 (g as (_,w)) =
  let val (Bvar,_) = with_exn dest_forall w (ERR "Cases_arm6" "not a forall")
  in (GEN_TAC \\ FULL_STRUCT_CASES_TAC (Thm.SPEC Bvar arm6_nchotomy)) g
  end
  handle e => raise wrap_exn "Lemmas" "Cases_arm6" e;

(* ------------------------------------------------------------------------- *)

val EXISTS_LEAST_NOT_RESET = prove(
  `!t i. i IN STRM_ARM6 /\ IS_RESET i t ==>
     ?t2. IS_RESET i t2 /\ ~IS_RESET i (t2 + 1) /\ ~IS_RESET i (t2 + 2)`,
  RW_TAC bool_ss [IN_DEF,STRM_ARM6_def]
    \\ PAT_ASSUM `!t. ?t2. t < t2 /\ (IS_BUSY i t2 ==> IS_ABSENT i t2)`
         (K ALL_TAC)
    \\ FIRST_X_ASSUM (SPEC_THEN `t`
         (STRIP_ASSUME_TAC o CONV_RULE numLib.EXISTS_LEAST_CONV))
    \\ POP_ASSUM (SPEC_THEN `t2 - 1` (ASSUME_TAC o SIMP_RULE arith_ss []))
    \\ EXISTS_TAC `t2 - 1` \\ Cases_on `t2`
    \\ FULL_SIMP_TAC arith_ss [ADD1] \\ FULL_SIMP_TAC bool_ss []
    \\ `n = t` by DECIDE_TAC \\ ASM_REWRITE_TAC []);

val LEAST_NOT_RESET = save_thm("LEAST_NOT_RESET",
  GEN_ALL (MATCH_MP (PROVE [] ``((a ==> b) /\ (b ==> c)) ==> (a ==> c)``)
    (CONJ (SPEC_ALL EXISTS_LEAST_NOT_RESET) ((SIMP_RULE std_ss [] o
       SPEC `\t. IS_RESET i t /\ ~IS_RESET i (t + 1) /\ ~IS_RESET i (t + 2)`)
         whileTheory.LEAST_EXISTS_IMP))));

val IS_RESET_LEM = prove(
  `!i t. ~IS_RESET i t ==> FST (i t)`,
  NTAC 2 STRIP_TAC \\ REWRITE_TAC [IS_RESET_def]
    \\ SPEC_THEN `i t` (fn th => ONCE_REWRITE_TAC [th]) form_7tuple
    \\ SIMP_TAC std_ss [PROJ_NRESET_def]);

val IS_RESET_THM = store_thm("IS_RESET_THM",
  `!i x. (!t. ~(t < x) \/ ~IS_RESET i t) ==> (!t. (t < x) ==> FST (i t))`,
  PROVE_TAC [IS_RESET_LEM]);

val IS_RESET_THM2 = store_thm("IS_RESET_THM2",
  `!y x i. (!t. (t < x) ==> ~IS_RESET i t) /\ y <= x ==>
            (!t. (t < y) ==> ~IS_RESET i t)`,
  METIS_TAC [LESS_LESS_EQ_TRANS]);

(* ------------------------------------------------------------------------- *)

val arm6ctrl = ``CTRL pipea pipeaval pipeb pipebval ireg iregval ointstart
  onewinst endinst obaselatch opipebll nxtic nxtis nopc1 oorst resetlatch
  onfq ooonfq oniq oooniq pipeaabt pipebabt iregabt2 dataabt2 aregn2 mrq2 nbw
  nrw sctrlreg psrfb oareg mask orp oorp mul mul2 borrow2 mshift``;

val AFTER_RESET1_def = Define`
  AFTER_RESET1 (ARM6 dp (^arm6ctrl)) = oorst /\ resetlatch`;

val AFTER_RESET2_def = Define`
  AFTER_RESET2 (ARM6 dp (^arm6ctrl)) = ~iregval /\ oorst /\ resetlatch`;

val AFTER_RESET3_def = Define`
  AFTER_RESET3 (ARM6 dp (^arm6ctrl)) =
   ~iregval /\ opipebll /\ oorst /\ resetlatch`;

val AFTER_RESET4_def = Define`
  AFTER_RESET4 (ARM6 dp (^arm6ctrl)) =
   pipeaval /\ pipebval /\ ~iregval /\ opipebll /\ oorst /\ resetlatch`;

val AFTER_NRESET1_def = Define`
  AFTER_NRESET1 (ARM6 dp (^arm6ctrl)) =
  pipeaval /\ pipebval /\ ~iregval /\ opipebll /\ ~oorst /\ resetlatch`;

val AFTER_NRESET2_def = Define`
  AFTER_NRESET2 (ARM6 dp (^arm6ctrl)) =
   pipeaval /\ pipebval /\ iregval /\ ointstart /\ endinst /\ onewinst /\
   opipebll /\ (nxtic = swi_ex) /\ (nxtis = t3) /\ ~nopc1 /\
   ~oorst /\ ~resetlatch /\ (aregn2 = 0w) /\ mrq2 /\ ~nrw /\ (mask = ARB)`;

(* ------------------------------------------------------------------------- *)

val IS_RESET_EXISTS = prove(
  `(!i t. IS_RESET i t ==>
    ?onfq oniq abort data cpa cpb. i t = (F,onfq,oniq,abort,data,cpa,cpb)) /\
    !i t. ~IS_RESET i t ==>
    ?onfq oniq abort data cpa cpb. i t = (T,onfq,oniq,abort,data,cpa,cpb)`,
  RW_TAC std_ss [IS_RESET_def] \\ Cases_on_arm6inp `i (t:num)`
    \\ FULL_SIMP_TAC std_ss [PROJ_NRESET_def]);

fun add_rws f rws =
  let val cmp_set = f()
      val _ = computeLib.add_thms rws cmp_set
    (*  val _ = computeLib.set_skip cmp_set ``COND`` NONE *)
  in
    cmp_set
  end;

fun reset_rws() =
  add_rws computeLib.bool_compset
    [pairTheory.FST,pairTheory.SND,LET_THM,pairTheory.UNCURRY_DEF,
     REWRITE_RULE [DECODE_PSR_def,COND_PAIR] NEXT_ARM6_def,
     RESETLATCH_def,AFTER_RESET1_def];

fun reset_rws2() = add_rws reset_rws
  [AFTER_RESET2_def,IREGVAL_def,PIPESTATIREGWRITE_def];

fun reset_rws3() = add_rws reset_rws2
  [AFTER_RESET3_def,PIPEBLL_def,ABORTINST_def,IC_def,NEWINST_def];

fun reset_rws4() = add_rws reset_rws3
  [AFTER_RESET4_def,PIPEALL_def,PIPEAVAL_def,PIPESTATAWRITE_def,
   PIPESTATBWRITE_def];

fun reset_rws5() = add_rws reset_rws4
  [AFTER_NRESET1_def,ENDINST_def,RWA_def,PCCHANGE_def,RESETSTART_def];

fun reset_rws6() = add_rws reset_rws5
  [AFTER_NRESET2_def,NOPC_def,AREGN1_def,NRW_def,NMREQ_def,MASK_def,NXTIC_def,
   NXTIS_def,INTSEQ_def,iclass_EQ_iclass,iclass2num_thm];

val AFTER_RESET1_THM = prove(
  `!a t i. IS_RESET i t ==> AFTER_RESET1 (NEXT_ARM6 a (i t))`,
  Cases_arm6 \\ REPEAT STRIP_TAC \\ IMP_RES_TAC IS_RESET_EXISTS
    \\ ASM_REWRITE_TAC [] \\ CONV_TAC (computeLib.CBV_CONV (reset_rws())));

val AFTER_RESET2_THM = prove(
  `!a t i. AFTER_RESET1 a /\ IS_RESET i t ==> AFTER_RESET2 (NEXT_ARM6 a (i t))`,
  Cases_arm6 \\ RW_TAC std_ss [AFTER_RESET1_def] \\ IMP_RES_TAC IS_RESET_EXISTS
    \\ ASM_REWRITE_TAC [] \\ CONV_TAC (computeLib.CBV_CONV (reset_rws2())));

val AFTER_RESET3_THM = prove(
  `!a t i. AFTER_RESET2 a /\ IS_RESET i t ==> AFTER_RESET3 (NEXT_ARM6 a (i t))`,
  Cases_arm6 \\ RW_TAC std_ss [AFTER_RESET2_def] \\ IMP_RES_TAC IS_RESET_EXISTS
    \\ ASM_REWRITE_TAC [] \\ CONV_TAC (computeLib.CBV_CONV (reset_rws3())));

val AFTER_RESET4_THM = prove(
  `!a t i. AFTER_RESET3 a /\ IS_RESET i t ==> AFTER_RESET4 (NEXT_ARM6 a (i t))`,
  Cases_arm6 \\ RW_TAC std_ss [AFTER_RESET3_def] \\ IMP_RES_TAC IS_RESET_EXISTS
    \\ ASM_REWRITE_TAC [] \\ CONV_TAC (computeLib.CBV_CONV (reset_rws4())));

val AFTER_NRESET1_THM = prove(
  `!a t i. AFTER_RESET4 a /\ ~IS_RESET i t ==>
           AFTER_NRESET1 (NEXT_ARM6 a (i t))`,
  Cases_arm6 \\ RW_TAC std_ss [AFTER_RESET4_def] \\ IMP_RES_TAC IS_RESET_EXISTS
    \\ ASM_REWRITE_TAC [] \\ CONV_TAC (computeLib.CBV_CONV (reset_rws5())));

val AFTER_NRESET2_THM = prove(
  `!a t i. AFTER_NRESET1 a /\ ~IS_RESET i t ==>
           AFTER_NRESET2 (NEXT_ARM6 a (i t))`,
  Cases_arm6 \\ RW_TAC std_ss [AFTER_NRESET1_def] \\ IMP_RES_TAC IS_RESET_EXISTS
    \\ ASM_REWRITE_TAC [] \\ CONV_TAC (computeLib.CBV_CONV (reset_rws6()))
    \\ SIMP_TAC std_ss []);

val AFTER_NRESET2_THM2 = prove(
  `!x. IS_RESET x.inp 0 /\ IS_RESET x.inp 1 /\
       IS_RESET x.inp 2 /\ IS_RESET x.inp 3 /\
      ~IS_RESET x.inp 4 /\ ~IS_RESET x.inp 5 ==>
         AFTER_NRESET2 ((FUNPOW (SNEXT NEXT_ARM6) 6 x).state)`,
  Cases \\ SIMP_TAC (srw_ss()) [] \\ REPEAT STRIP_TAC
    \\ IMP_RES_TAC (SPECL [`a`,`0`] AFTER_RESET1_THM)
    \\ POP_ASSUM (SPEC_THEN `a` ASSUME_TAC)
    \\ IMP_RES_TAC (SPECL [`a`,`1`] AFTER_RESET2_THM)
    \\ IMP_RES_TAC (SPECL [`a`,`2`] AFTER_RESET3_THM)
    \\ IMP_RES_TAC (SPECL [`a`,`3`] AFTER_RESET4_THM)
    \\ IMP_RES_TAC (SPECL [`a`,`4`] AFTER_NRESET1_THM)
    \\ IMP_RES_TAC (SPECL [`a`,`5`] AFTER_NRESET2_THM)
    \\ ASM_SIMP_TAC (srw_ss()++boolSimps.LET_ss)
         [numeralTheory.numeral_funpow,SNEXT_def,ADVANCE_def]);

val lem = prove(
  `!t1 t2 i. IS_RESET (ADVANCE t1 i) t2 = IS_RESET i (t1 + t2)`,
  SIMP_TAC bool_ss [IS_RESET_def,ADVANCE_def]);

val SPEC_AFTER_NRESET2 = save_thm("SPEC_AFTER_NRESET2",
  (GEN_ALL o SIMP_RULE arith_ss [] o DISCH `2 < t` o SPEC_ALL o
   INST [`t` |-> `t - 3`] o SIMP_RULE (srw_ss()) [lem] o
   SPEC `<| state := a; inp := ADVANCE t i|>`) AFTER_NRESET2_THM2);

val AFTER_NRESET2_THM3 = store_thm("AFTER_NRESET2_THM3",
  `!a.  AFTER_NRESET2 a ==> (INIT_ARM6 a = a)`,
  Cases_arm6 \\ RW_TAC (std_ss++SIZES_ss)
    [AFTER_NRESET2_def,INIT_ARM6_def,MASK_def,n2w_11]);

val AFTER_NRESET2_THM4 = store_thm("AFTER_NRESET2_THM4",
  `!a j k l m. AFTER_NRESET2 a ==>
     (NEXT_ARM (ABS_ARM6 j) ((\(a,b,c) d. (a,b,c,d))
         (case ABS_ARM6 a
            of ARM_EX v v1 v2 ->
               (exc2exception v2 v k,l,v1)) m) = ABS_ARM6 a)`,
  Cases_arm6 \\ RW_TAC std_ss [AFTER_NRESET2_def,ABS_ARM6_def,PROJ_Reset_def,
    NEXT_ARM_def,IS_Reset_def,exc2exception_def,num2exception_thm,word_0_n2w]);

(* ------------------------------------------------------------------------- *)

val lem = prove(
  `!i t. i IN STRM_ARM6 /\ IS_RESET i t /\ ~IS_RESET i (t + 1) ==>
       IS_RESET i (t - 1)`,
  RW_TAC bool_ss [IN_DEF,STRM_ARM6_def]
    \\ Cases_on `t` \\ FULL_SIMP_TAC arith_ss [ADD1]
    \\ PAT_ASSUM `!t. IS_RESET i t ==> b` (SPEC_THEN `n + 1` IMP_RES_TAC)
    \\ FULL_SIMP_TAC arith_ss []);

val lem2 = prove(
  `!i t. i IN STRM_ARM6 /\ IS_RESET i t /\ ~IS_RESET i (t + 1) ==>
           IS_RESET i (t - 1) /\ IS_RESET i (t - 2)`,
  REPEAT STRIP_TAC \\ IMP_RES_TAC lem
    \\ FULL_SIMP_TAC bool_ss [IN_DEF,STRM_ARM6_def]
    \\ Cases_on `t` \\ FULL_SIMP_TAC arith_ss [ADD1]
    \\ PAT_ASSUM `!t. IS_RESET i t ==> b` (SPEC_THEN `n` IMP_RES_TAC)
    \\ FULL_SIMP_TAC arith_ss []);

val PREVIOUS_THREE_RESET = store_thm("PREVIOUS_THREE_RESET",
  `!i t. i IN STRM_ARM6 /\ IS_RESET i t /\ ~IS_RESET i (t + 1) ==>
           IS_RESET i (t - 1) /\ IS_RESET i (t - 2) /\ IS_RESET i (t - 3)`,
  REPEAT STRIP_TAC \\ IMP_RES_TAC lem
    \\ FULL_SIMP_TAC bool_ss [IN_DEF,STRM_ARM6_def]
    \\ Cases_on `t` \\ FULL_SIMP_TAC arith_ss [ADD1]
    \\ PAT_ASSUM `!t. IS_RESET i t ==> b`
         (fn th => IMP_RES_TAC (SPEC `n` th) \\ ASSUME_TAC th)
    \\ FULL_SIMP_TAC arith_ss []
    \\ POP_ASSUM (SPEC_THEN `n - 1` IMP_RES_TAC)
    \\ FULL_SIMP_TAC arith_ss []
    \\ PROVE_TAC [DECIDE ``!n. ~(n = 0) ==> (n - 1 + 3 = n + 2)``]);

val LEAST_RESET_GT_TWO = store_thm("LEAST_RESET_GT_TWO",
  `!i t. i IN STRM_ARM6 /\ IS_RESET i t ==>
        2 < (LEAST t. IS_RESET i t /\ ~IS_RESET i (t + 1) /\
                     ~IS_RESET i (t + 2))`,
  REPEAT STRIP_TAC \\ IMP_RES_TAC LEAST_NOT_RESET
    \\ PAT_ASSUM `IS_RESET i t` (K ALL_TAC)
    \\ IMP_RES_TAC PREVIOUS_THREE_RESET
    \\ REPEAT (PAT_ASSUM `~a ==> b` (K ALL_TAC))
    \\ ABBREV_TAC `l = LEAST t. IS_RESET i t /\ ~IS_RESET i (t + 1) /\
                               ~IS_RESET i (t + 2)`
    \\ Cases_on `(l = 0) \/ (l = 1) \/ (l = 2)`
    \\ FULL_SIMP_TAC arith_ss [IN_DEF,STRM_ARM6_def]
    \\ POP_ASSUM (fn th => FULL_SIMP_TAC arith_ss [th])
    \\ PAT_ASSUM `!n. IS_RESET i t ==> b` IMP_RES_TAC
    \\ FULL_SIMP_TAC arith_ss []);

(* ------------------------------------------------------------------------- *)

val AREGN1_THM = store_thm("AREGN1_THM",
  `!resetstart dataabt1 fiqactl irqactl coproc1 iregabt2.
      (AREGN1 resetstart dataabt1 fiqactl irqactl coproc1 iregabt2 = 2w) =
     ~resetstart /\ ~dataabt1 /\ ~fiqactl /\ ~irqactl /\ ~coproc1 /\ ~iregabt2`,
  RW_TAC (std_ss++SIZES_ss) [AREGN1_def,n2w_11]);

val interrupt_exists = store_thm("interrupt_exists",
  `!i f. ?aregn:word3.
      ~(aregn IN {0w; 1w; 2w; 5w}) /\
      ((aregn = 7w) ==> f) /\ ((aregn = 6w) ==> i)`,
  NTAC 2 STRIP_TAC \\ EXISTS_TAC `3w`
    \\ RW_TAC (std_ss++SIZES_ss) [pred_setTheory.IN_INSERT,n2w_11,
         pred_setTheory.NOT_IN_EMPTY]);

val AREGN1_BIJ = store_thm("AREGN1_BIJ",
  `!resetstart dataabt1 fiqactl irqactl coproc1 iregabt2.
      exception2num (num2exception (
        w2n (AREGN1 resetstart dataabt1 fiqactl irqactl coproc1 iregabt2))) =
        w2n (AREGN1 resetstart dataabt1 fiqactl irqactl coproc1 iregabt2)`,
  SIMP_TAC std_ss [GSYM exception2num_num2exception,
    (SIMP_RULE (std_ss++SIZES_ss) [] o
     Thm.INST_TYPE [alpha |-> ``:3``]) w2n_lt]);

(* ------------------------------------------------------------------------- *)

val LESS_THM =
  CONV_RULE numLib.SUC_TO_NUMERAL_DEFN_CONV prim_recTheory.LESS_THM;

val num2exception_word3 = store_thm("num2exception_word3",
  `(!aregn:word3. (num2exception (w2n aregn) = reset)     = (aregn = 0w)) /\
   (!aregn:word3. (num2exception (w2n aregn) = undefined) = (aregn = 1w)) /\
   (!aregn:word3. (num2exception (w2n aregn) = software)  = (aregn = 2w)) /\
   (!aregn:word3. (num2exception (w2n aregn) = pabort)    = (aregn = 3w)) /\
   (!aregn:word3. (num2exception (w2n aregn) = dabort)    = (aregn = 4w)) /\
   (!aregn:word3. (num2exception (w2n aregn) = address)   = (aregn = 5w)) /\
   (!aregn:word3. (num2exception (w2n aregn) = interrupt) = (aregn = 6w)) /\
    !aregn:word3. (num2exception (w2n aregn) = fast)      = (aregn = 7w)`,
  REPEAT STRIP_TAC \\ `w2n aregn < 8`
    by PROVE_TAC [w2n_lt,EVAL ``dimword (:3)``]
    \\ FULL_SIMP_TAC (std_ss++SIZES_ss)
         [num2exception_thm,exception_EQ_exception,exception2num_thm,
          GSYM w2n_11,w2n_n2w,LESS_THM]);

val INTERRUPT_ADDRESS = store_thm("INTERRUPT_ADDRESS",
  `!aregn2:word3. n2w (4 * exception2num (num2exception (w2n aregn2))) =
       4w:word32 * w2w aregn2`,
  STRIP_TAC \\ `w2n aregn2 < 8` by PROVE_TAC [w2n_lt,EVAL ``dimword (:3)``]
    \\ FULL_SIMP_TAC (std_ss++SIZES_ss)
         [word_mul_def,w2n_w2w,w2n_n2w,exception2num_num2exception]);

val SOFTWARE_ADDRESS = save_thm("SOFTWARE_ADDRESS",
  (REWRITE_RULE [EVAL ``w2n (2w:word3)``,num2exception_thm] o
    SPEC `2w`) INTERRUPT_ADDRESS);

val NOT_RESET = store_thm("NOT_RESET",
  `!x n irqactl iregabt2 fiqactl dataabt1 coproc1.
     ~IS_Reset (exc2exception (num2exception (w2n
      (AREGN1 F dataabt1 fiqactl irqactl coproc1 iregabt2))) x n)`,
  RW_TAC (std_ss++SIZES_ss) [IS_Reset_def,exc2exception_def,num2exception_thm,
   AREGN1_def,w2n_n2w]);

val NOT_RESET2 = store_thm("NOT_RESET2",
  `!x ointstart n aregn.
    ~(aregn IN {0w; 2w; 5w}) ==>
     ~IS_Reset (exc2exception (num2exception (w2n
      (if ointstart then aregn else 2w:word3))) x n)`,
  RW_TAC (std_ss++SIZES_ss++pred_setSimps.PRED_SET_ss) [IS_Reset_def,
         exc2exception_def,num2exception_thm,w2n_n2w]
    \\ Cases_on `num2exception (w2n aregn)`
    \\ FULL_SIMP_TAC (srw_ss()) [num2exception_word3]);

val IS_Reset_IMP_EXISTS_SOME_Reset = store_thm("IS_Reset_IMP_EXISTS_SOME_Reset",
  `!i. IS_Reset i ==> (?s. i = SOME (Reset s))`,
  Cases \\ RW_TAC std_ss [IS_Reset_def] \\ Cases_on `x`
    \\ FULL_SIMP_TAC std_ss [interrupts_case_def] \\ PROVE_TAC []);

(* ------------------------------------------------------------------------- *)

val SIMP_IS_Dabort = store_thm("SIMP_IS_Dabort",
  `!x n irqactl iregabt2 fiqactl dataabt1 coproc1.
    IS_Dabort (exc2exception (num2exception (w2n 
    (AREGN1 F dataabt1 fiqactl irqactl coproc1 iregabt2))) x n) = dataabt1`,
  RW_TAC (std_ss++SIZES_ss) [IS_Dabort_def,AREGN1_def,exc2exception_def,
    num2exception_thm,w2n_n2w]);

val SIMP_PROJ_Dabort = store_thm("SIMP_PROJ_Dabort",
  `!x n irqactl iregabt2 fiqactl coproc1.
    PROJ_Dabort  (exc2exception (num2exception (w2n
    (AREGN1 F T fiqactl irqactl coproc1 iregabt2))) x n) = n`,
  RW_TAC (std_ss++SIZES_ss) [PROJ_Dabort_def,AREGN1_def,exc2exception_def,
    num2exception_thm,w2n_n2w]);

val CP_NOT = prove(
  `!ic. ic IN {cdp_und; mrc; mcr; stc; ldc} ==> ~(ic = mrs_msr)`,
  RW_TAC (std_ss++pred_setSimps.PRED_SET_ss) []);

(*
val EXTRACT_UNDEFINED =
  simpLib.SIMP_PROVE (std_ss++pred_setSimps.PRED_SET_ss)
   [AC DISJ_ASSOC DISJ_COMM]
   ``ic IN {reset; undefined; software; address} =
     ic IN {reset; software; address} \/ (ic = undefined)``;
*)

val SIMP_interrupt2exception = store_thm("SIMP_interrupt2exception",
  `!y reg psr ointstart n ireg i f aregn.
    CONDITION_PASSED (NZCV (CPSR_READ psr)) ireg /\
    ~(DECODE_INST ireg = mrs_msr) /\
   (((aregn = 1w) ==> DECODE_INST ireg IN {cdp_und; mrc; mcr; stc; ldc}) /\
   ~(aregn IN {0w; 2w; 5w}) \/
   ~(aregn IN {0w; 1w; 2w; 5w})) /\
   ((aregn = 7w) ==> ~f) /\ ((aregn = 6w) ==> ~i) ==>
     ((interrupt2exception (ARM_EX (ARM reg psr) ireg software) (i,f)
        (exc2exception (num2exception (
          w2n (if ointstart then aregn else 2w:word3))) y n)) =
       (num2exception (w2n (if ointstart then aregn else 2w))))`,
  NTAC 9 STRIP_TAC \\ Cases_on `num2exception (w2n aregn)`
    \\ Cases_on `ointstart` \\ ASM_SIMP_TAC (srw_ss()++SIZES_ss++
          boolSimps.LET_ss++ pred_setSimps.PRED_SET_ss)
         [DECODE_PSR_def,w2n_n2w,exc2exception_def,num2exception_thm,
          interrupt2exception_def]
    \\ FULL_SIMP_TAC std_ss [num2exception_word3]);

val SIMP_interrupt2exception2 = save_thm("SIMP_interrupt2exception2",
  (GEN_ALL o REWRITE_RULE [] o INST [`ointstart` |-> `T`] o
   SPEC_ALL) SIMP_interrupt2exception);

val SIMP_interrupt2exception3 = store_thm("SIMP_interrupt2exception3",
  `!y resetstart reg psr n irqactl iregabt2 ireg i fiqactl f dataabt1 coproc1.
     DECODE_INST ireg IN {cdp_und; mrc; mcr; stc; ldc} /\
     CONDITION_PASSED (NZCV (CPSR_READ psr)) ireg /\
     (fiqactl ==> ~f) /\ (irqactl ==> ~i) ==>
     ((interrupt2exception (ARM_EX (ARM reg psr) ireg software) (i,f)
       (exc2exception (num2exception (w2n
         (AREGN1 resetstart dataabt1 fiqactl irqactl coproc1 iregabt2))) y n)) =
       (num2exception (w2n
         (AREGN1 resetstart dataabt1 fiqactl irqactl coproc1 iregabt2))))`,
  RW_TAC (std_ss++SIZES_ss) [DECODE_PSR_def,AREGN1_def,CP_NOT,
    interrupt2exception_def,exc2exception_def,num2exception_thm,w2n_n2w]);

val SIMP_interrupt2exception4 = store_thm("SIMP_interrupt2exception4",
  `!y resetstart reg psr n irqactl iregabt2 ireg i fiqactl f exc dataabt1.
    ((exc = software) ==> ~CONDITION_PASSED (NZCV (CPSR_READ psr)) ireg) /\
    (fiqactl ==> ~f) /\ (irqactl ==> ~i) ==>
    ((interrupt2exception (ARM_EX (ARM reg psr) ireg exc) (i,f)
      (exc2exception (num2exception (w2n
        (AREGN1 resetstart dataabt1 fiqactl irqactl F iregabt2))) y n)) =
      (num2exception (w2n
        (AREGN1 resetstart dataabt1 fiqactl irqactl F iregabt2))))`,
  RW_TAC (std_ss++SIZES_ss) [DECODE_PSR_def,AREGN1_def,
    interrupt2exception_def,exc2exception_def,num2exception_thm,w2n_n2w]);

val SIMP_interrupt2exception5 = prove(
  `!y resetstart reg psr n irqactl iregabt2 ireg i' fiqactl f' dataabt1.
    CONDITION_PASSED (NZCV (CPSR_READ psr)) ireg ==>
    (let (flags,i,f,m) = DECODE_PSR (CPSR_READ psr)
     and old_flags = (DECODE_INST ireg = mrs_msr) in
       (fiqactl ==> if old_flags then ~f else ~f') /\
       (irqactl ==> if old_flags then ~i else ~i')) ==>
    ((interrupt2exception (ARM_EX (ARM reg psr) ireg software) (i',f')
      (exc2exception (num2exception (w2n
        (AREGN1 resetstart dataabt1 fiqactl irqactl F iregabt2))) y n)) =
      (num2exception (w2n
        (AREGN1 resetstart dataabt1 fiqactl irqactl F iregabt2))))`,
  RW_TAC (std_ss++SIZES_ss) [DECODE_PSR_def,AREGN1_def,
    interrupt2exception_def,exc2exception_def,num2exception_thm,w2n_n2w]);

val SIMP_interrupt2exception5 = save_thm("SIMP_interrupt2exception5",
  SIMP_RULE (std_ss++boolSimps.COND_elim_ss)
    [DECODE_PSR_def] SIMP_interrupt2exception5);

(* ------------------------------------------------------------------------- *)

val _ = export_theory();
