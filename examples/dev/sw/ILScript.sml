(*
app load ["pred_setSimps","pred_setTheory","whileTheory","finite_mapTheory","rich_listTheory"];
*)

open HolKernel Parse boolLib bossLib numLib pred_setSimps pred_setTheory
     arithmeticTheory word32Theory pairTheory listTheory whileTheory finite_mapTheory preARMTheory ARMCompositionTheory;

(*---------------------------------------------------------------------------------*)
(*---------------------------------------------------------------------------------*)

val _ = new_theory "IL";

val set_ss = std_ss ++ SET_SPEC_ss ++ PRED_SET_ss;

(*---------------------------------------------------------------------------------*)
(*      Registers and memory data in IL                                            *)
(*---------------------------------------------------------------------------------*)

val _ = Hol_datatype ` 
    MREG = R0 | R1 | R2 | R3 | R4 | R5 | R6 | R7 | R8 | R9 | R10 | R11 | R12 | R13 | R14`;

val _ = type_abbrev("MMEM", Type`:num # OFFSET`);      (* memory in ir *)

val _ = Hol_datatype `
    MEXP = MR of MREG          (* registers *)
         | MC of DATA          (* constants *)
         | MM of MMEM          (* memory    *)
    `;

val index_of_reg = Define `
    (index_of_reg R0 = 0) /\
    (index_of_reg R1 = 1) /\
    (index_of_reg R2 = 2) /\      
    (index_of_reg R3 = 3) /\
    (index_of_reg R4 = 4) /\
    (index_of_reg R5 = 5) /\
    (index_of_reg R6 = 6) /\
    (index_of_reg R7 = 7) /\
    (index_of_reg R8 = 8) /\
    (index_of_reg R9 = 9) /\
    (index_of_reg R10 = 10) /\
    (index_of_reg R11 = 11) /\
    (index_of_reg R12 = 12) /\
    (index_of_reg R13 = 13) /\
    (index_of_reg R14 = 14)
`;

val from_reg_index_def = Define `
    from_reg_index i = 
      if i = 0 then R0
      else if i = 1 then R1
      else if i = 2 then R2
      else if i = 3 then R3
      else if i = 4 then R4
      else if i = 5 then R5
      else if i = 6 then R6
      else if i = 7 then R7
      else if i = 8 then R8
      else if i = 9 then R9
      else if i = 10 then R10
      else if i = 11 then R11
      else if i = 12 then R12
      else if i = 13 then R13
      else R14`;

val from_reg_index_thm = Q.store_thm
  ("from_reg_index_thm",
   `(from_reg_index 0 = R0) /\
    (from_reg_index 1 = R1) /\
    (from_reg_index 2 = R2) /\
    (from_reg_index 3 = R3) /\
    (from_reg_index 4 = R4) /\
    (from_reg_index 5 = R5) /\
    (from_reg_index 6 = R6) /\
    (from_reg_index 7 = R7) /\
    (from_reg_index 8 = R8) /\
    (from_reg_index 9 = R9) /\
    (from_reg_index 10 = R10) /\
    (from_reg_index 11 = R11) /\
    (from_reg_index 12 = R12) /\
    (from_reg_index 13 = R13) /\
    (from_reg_index 14 = R14)`,
   RW_TAC std_ss [from_reg_index_def]
  );

val toREG_def = Define `
    toREG r =
       REG (index_of_reg r)`;

val toMEM_def = Define `
    toMEM ((base,offset):MMEM) =
       MEM (base,offset)`;        (* [base + offset] *)

val toEXP_def = Define `
    (toEXP (MR r) = toREG r) /\
    (toEXP (MC c) = WCONST c) /\ 
    (toEXP (MM m) = toMEM m)`;

(*---------------------------------------------------------------------------------*)
(*      Semantics of the intermediate language                                     *)
(*---------------------------------------------------------------------------------*)

val _ = Hol_datatype ` 
    DOPER = MLDR of MREG => MMEM |
           MSTR of MMEM => MREG |
           MMOV of MREG => MEXP |
           MADD of MREG => MEXP => MEXP |
           MSUB of MREG => MEXP => MEXP | 
           MRSB of MREG => MEXP => MEXP |
           MMUL of MREG => MEXP => MEXP |
           MAND of MREG => MEXP => MEXP |
           MORR of MREG => MEXP => MEXP |
	   MEOR of MREG => MEXP => MEXP |
	   MLSL of MREG => MEXP => MEXP |
	   MLSR of MREG => MEXP => MEXP |
	   MASR of MREG => MEXP => MEXP |
	   MROR of MREG => MEXP => MEXP |
           MPUSH of REGISTER => REGISTER list |
	   MPOP of REGISTER => REGISTER list`;

val _ = type_abbrev("CEXP", Type`:EXP # COND # EXP`);

val _ = Hol_datatype `CTL_STRUCTURE = 
    BLK of DOPER list |
    SC of CTL_STRUCTURE => CTL_STRUCTURE | 
    CJ of CEXP => CTL_STRUCTURE => CTL_STRUCTURE |
    TR of CEXP => CTL_STRUCTURE
  `;

(*---------------------------------------------------------------------------------*)
(*      Macro machine                                                              *)
(*      Stack Operations                                                           *)
(*      Since a negative integeter minus 0 results in 0, we assume the stack goes  *)
(*      up to avoid this problem                                                   *)
(*---------------------------------------------------------------------------------*)

(* Push into the stack from multiple registers with writing-back to the sp              *)

val pushL_def =
  Define `pushL st baseR regL = 
   write (FST (FOLDL (\(st1,i) reg. (write st1 (MEM(baseR,NEG i)) (read st reg), i+1)) (st,0) (REVERSE (MAP REG regL))))
         (REG baseR) (read st (REG baseR) - n2w (LENGTH regL))`;

(* Pop into multiple registers from the stack with writing-back to the sp   *)
 
val popL_def =
  Define `popL st baseR regL = 
   write (FST (FOLDL (\(st1,i) reg. (write st1 reg (read st (MEM(baseR, POS(i+1)))), i+1)) (st,0) (MAP REG regL)))
         (REG baseR) (read st (REG baseR) + n2w (LENGTH regL))`;

(*---------------------------------------------------------------------------------*)
(*      Decode assignment statement                                                *)
(*---------------------------------------------------------------------------------*)

val mdecode_def = Define `
  (!dst src.mdecode st (MLDR dst src) =
      write st (toREG dst) (read st (toMEM src))) /\
  (!dst src.mdecode st (MSTR dst src) =
      write st (toMEM dst) (read st (toREG src))) /\
  (mdecode st (MMOV dst src) =
      write st (toREG dst) (read st (toEXP src))) /\
  (mdecode st (MADD dst src1 src2) =
      write st (toREG dst) (read st (toEXP src1) + read st (toEXP src2))) /\
  (mdecode st (MSUB dst src1 src2) =
      write st (toREG dst) (read st (toEXP src1) - read st (toEXP src2))) /\
  (mdecode st (MRSB dst src1 src2) =
      write st (toREG dst) (read st (toEXP src2) - read st (toEXP src1))) /\
  (mdecode st (MMUL dst src1 src2) =
      write st (toREG dst) (read st (toEXP src1) * read st (toEXP src2))) /\
  (mdecode st (MAND dst src1 src2) =
      write st (toREG dst) (read st (toEXP src1) & read st (toEXP src2))) /\
  (mdecode st (MORR dst src1 src2) =
      write st (toREG dst) (read st (toEXP src1) | read st (toEXP src2))) /\
  (mdecode st (MEOR dst src1 src2) =
      write st (toREG dst) (read st (toEXP src1) # read st (toEXP src2))) /\
  (mdecode st (MLSL dst src1 src2) =
      write st (toREG dst) (read st (toEXP src1) << w2n (read st (toEXP src2)))) /\
  (mdecode st (MLSR dst src1 src2) =
      write st (toREG dst) (read st (toEXP src1) >>> w2n (read st (toEXP src2)))) /\  
  (mdecode st (MASR dst src1 src2) =
      write st (toREG dst) (read st (toEXP src1) >> w2n (read st (toEXP src2)))) /\
  (mdecode st (MROR dst src1 src2) =
      write st (toREG dst) (read st (toEXP src1) #>> w2n (read st (toEXP src2)))) /\
  (mdecode st (MPUSH dst' srcL) =
      pushL st dst' srcL) /\
  (mdecode st (MPOP dst' srcL) =
      popL st dst' srcL)
  `;

val translate_assignment_def = Define `
    (translate_assignment (MMOV dst src) = ((MOV,NONE,F),SOME (toREG dst), [toEXP src], NONE):INST) /\
    (translate_assignment (MADD dst src1 src2) = ((ADD,NONE,F),SOME (toREG dst), [toEXP src1; toEXP src2], NONE):INST) /\
    (translate_assignment (MSUB dst src1 src2) = ((SUB,NONE,F),SOME (toREG dst), [toEXP src1; toEXP src2], NONE):INST) /\
    (translate_assignment (MRSB dst src1 src2) = ((RSB,NONE,F),SOME (toREG dst), [toEXP src1; toEXP src2], NONE):INST) /\
    (translate_assignment (MMUL dst src1 src2) = ((MUL,NONE,F),SOME (toREG dst), [toEXP src1; toEXP src2], NONE):INST) /\
    (translate_assignment (MAND dst src1 src2) = ((AND,NONE,F),SOME (toREG dst), [toEXP src1; toEXP src2], NONE):INST) /\
    (translate_assignment (MORR dst src1 src2) = ((ORR,NONE,F),SOME (toREG dst), [toEXP src1; toEXP src2], NONE):INST) /\
    (translate_assignment (MEOR dst src1 src2) = ((EOR,NONE,F),SOME (toREG dst), [toEXP src1; toEXP src2], NONE):INST) /\
    (translate_assignment (MLSL dst src1 src2) = ((LSL,NONE,F),SOME (toREG dst), [toEXP src1; toEXP src2], NONE):INST) /\
    (translate_assignment (MLSR dst src1 src2) = ((LSR,NONE,F),SOME (toREG dst), [toEXP src1; toEXP src2], NONE):INST) /\
    (translate_assignment (MASR dst src1 src2) = ((ASR,NONE,F),SOME (toREG dst), [toEXP src1; toEXP src2], NONE):INST) /\
    (translate_assignment (MROR dst src1 src2) = ((ROR,NONE,F),SOME (toREG dst), [toEXP src1; toEXP src2], NONE):INST) /\
    (!dst src.translate_assignment (MLDR dst src) = ((LDR,NONE,F),SOME (toREG dst), [toMEM src], NONE):INST) /\
    (!dst src.translate_assignment (MSTR dst src) = ((STR,NONE,F),SOME (toREG src), [toMEM dst], NONE):INST) /\
    (!dst srcL.translate_assignment (MPUSH dst srcL) = ((STMFD,NONE,F),SOME (WREG dst), MAP REG srcL, NONE):INST) /\
    (!dst srcL.translate_assignment (MPOP dst srcL) = ((LDMFD,NONE,F),SOME (WREG dst), MAP REG srcL, NONE):INST)
    `;


val TRANSLATE_ASSIGMENT_CORRECT = Q.store_thm
  ("TRANSLATE_ASSIGMENT_CORRECT",
   `!(stm:DOPER) pc cpsr st.
       (SUC pc,cpsr,mdecode st stm) = decode_cond (pc,cpsr,st) (translate_assignment stm)`,
     SIMP_TAC std_ss [FORALL_DSTATE] THEN
     Cases_on `stm` THEN
     RW_TAC list_ss [translate_assignment_def, decode_cond_thm, decode_op_thm, write_thm,  mdecode_def] THEN
     RW_TAC list_ss [pushL_def, popL_def]
  );


val TRANSLATE_ASSIGMENT_CORRECT_2 = Q.store_thm
  ("TRANSLATE_ASSIGMENT_CORRECT_2",
   `!(stm:DOPER) s.
       decode_cond s (translate_assignment stm) = (SUC (FST s),FST (SND s),mdecode (SND (SND s)) stm)`,
     RW_TAC std_ss [] THEN
     METIS_TAC [ABS_PAIR_THM,FST,SND,TRANSLATE_ASSIGMENT_CORRECT]
  );

(*---------------------------------------------------------------------------------*)
(*      Decode from intermedia language to low level language                      *)
(*---------------------------------------------------------------------------------*)

val translate_def = Define `
    (translate (BLK (stm::stmL)) = translate_assignment stm :: translate (BLK stmL)) /\
    (translate (BLK []) = []) /\
    (translate (SC S1 S2) = 
         mk_SC (translate S1) (translate S2)) /\
    (translate (CJ cond Strue Sfalse) = 
	 mk_CJ cond (translate Strue) (translate Sfalse)) /\
    (translate (TR cond Sbody) = 
         mk_TR cond (translate Sbody))
  `;

(*---------------------------------------------------------------------------------*)
(*      Intermediate Representation                                                *)
(*      Definition of run_ir                                                       *) 
(*---------------------------------------------------------------------------------*)

val run_arm_def = Define `
      run_arm arm ((pc,cpsr,st),pcS) = runTo (upload arm (\i.ARB) pc) (pc+LENGTH arm) ((pc,cpsr,st),pcS)`;

val run_ir_def = Define `
      run_ir ir st = get_st (run_arm (translate ir) ((0,0w,st),{}))`;

val WELL_FORMED_def = Define `
      WELL_FORMED ir = well_formed (translate ir)`;

(*---------------------------------------------------------------------------------*)
(*      Hoare Rules for IR                                                         *) 
(*---------------------------------------------------------------------------------*)

val HOARE_SC_IR = Q.store_thm (
   "HOARE_SC_IR",
   `!ir1 ir2 P Q R T.
        WELL_FORMED ir1 /\ WELL_FORMED ir2 /\
           (!st. P st ==> Q (run_ir ir1 st)) /\
           (!st. R st ==> T (run_ir ir2 st)) /\ (!st. Q st ==> R st) ==>
             !st. P st ==>
                  T (run_ir (SC ir1 ir2) st)`,
   RW_TAC std_ss [WELL_FORMED_def, run_ir_def, translate_def, run_arm_def, eval_fl_def] THEN 
   IMP_RES_TAC (SIMP_RULE std_ss [eval_fl_def, uploadCode_def]  HOARE_SC_FLAT)
  );

val HOARE_CJ_IR = Q.store_thm (
   "HOARE_CJ_IR",
   `!cond ir_t ir_f P Q R.
       WELL_FORMED ir_t /\ WELL_FORMED ir_f /\
           (!st. P st ==> Q (run_ir ir_t st)) /\
           (!st. P st ==> R (run_ir ir_f st)) ==>
             !st. P st ==>
                if eval_cond cond st then Q (run_ir (CJ cond ir_t ir_f) st)
                    else R (run_ir (CJ cond ir_t ir_f) st)`,
   RW_TAC std_ss [WELL_FORMED_def, run_ir_def, translate_def, run_arm_def, eval_fl_def] THEN
   IMP_RES_TAC (SIMP_RULE std_ss [eval_fl_def, uploadCode_def] HOARE_CJ_FLAT) THEN
   METIS_TAC []
  );

val HOARE_TR_IR = Q.store_thm (
   "HOARE_TR_IR",
   `!cond ir P.
       WELL_FORMED ir /\  WF_TR (cond, translate ir) /\
         (!st. P st ==> P (run_ir ir st)) ==>
            !st. P st ==> P (run_ir (TR cond ir) st) /\ 
                 eval_cond cond (run_ir (TR cond ir) st)`,
   RW_TAC std_ss [WELL_FORMED_def, run_ir_def, translate_def, run_arm_def, eval_fl_def] THEN
   METIS_TAC [SIMP_RULE std_ss [eval_fl_def, uploadCode_def] HOARE_TR_FLAT]
  );

(*---------------------------------------------------------------------------------*)
(*      Well-formedness of IR                                                      *) 
(*---------------------------------------------------------------------------------*)

val UPLOAD_LEM_2 = Q.store_thm (
   "UPLOAD_LEM_2",
   `!s stm iB. (upload [stm] iB (FST s)) (FST s) = stm`,
   RW_TAC std_ss [] THEN
   `0 < LENGTH [stm]` by RW_TAC list_ss [] THEN
   METIS_TAC [UPLOAD_LEM, FST, DECIDE (Term`!x.x + 0 = x`), EL, HD]
   );

val STATEMENT_IS_WELL_FORMED = Q.store_thm (
   "STATEMENT_IS_WELL_FORMED",
   `!stm. well_formed [translate_assignment stm]`,
    RW_TAC list_ss [FORALL_DSTATE, well_formed_def, terminated_def, stopAt_def, status_independent_def] THENL [
        Cases_on `stm` THEN
            (fn g => 
               (SIMP_TAC list_ss [closed_def, Once RUNTO_ADVANCE, UPLOAD_LEM_2, TRANSLATE_ASSIGMENT_CORRECT_2, SUC_ONE_ADD] THEN
                RW_TAC set_ss [Once RUNTO_ADVANCE]) g
            ),
        Cases_on `stm` THEN
            Q.EXISTS_TAC `SUC 0` THEN
            `?s0 pcS0. s = (s0,pcS0)` by METIS_TAC [ABS_PAIR_THM] THEN
            RW_TAC arith_ss [FUNPOW, UPLOAD_LEM_2, step_def, TRANSLATE_ASSIGMENT_CORRECT_2, SUC_ONE_ADD],
        Cases_on `stm` THEN
            (fn g => 
               (SIMP_TAC list_ss [get_st_def, Once RUNTO_ADVANCE, SIMP_RULE std_ss [] (Q.SPEC `(pos0,cpsr0,regs,mem):STATE` 
			  (INST_TYPE [alpha |-> Type `:word32 # (num |-> word32) # (num |-> word32)`] UPLOAD_LEM_2)), 
                         TRANSLATE_ASSIGMENT_CORRECT_2, SUC_ONE_ADD] THEN
                RW_TAC std_ss [Once RUNTO_ADVANCE] THEN
                SIMP_TAC list_ss [get_st_def, Once RUNTO_ADVANCE, SIMP_RULE std_ss [] (Q.SPEC `(pos1,cpsr1,regs,mem):STATE` 
			  (INST_TYPE [alpha |-> Type `:word32 # (num |-> word32) # (num |-> word32)`] UPLOAD_LEM_2)), 
                         TRANSLATE_ASSIGMENT_CORRECT_2, SUC_ONE_ADD] THEN
                RW_TAC std_ss [Once RUNTO_ADVANCE]) g
            )
    ]
  );


val BLOCK_IS_WELL_FORMED = Q.store_thm (
   "BLOCK_IS_WELL_FORMED",
   `!stmL. WELL_FORMED (BLK stmL)`,
    Induct_on `stmL` THENL [
        RW_TAC list_ss [WELL_FORMED_def, well_formed_def, translate_def, closed_def, terminated_def, status_independent_def, stopAt_def] THENL [
            RW_TAC set_ss [Once RUNTO_ADVANCE],
            Q.EXISTS_TAC `0` THEN RW_TAC std_ss [FUNPOW],
            RW_TAC arith_ss [Once RUNTO_ADVANCE, get_st_def] THEN RW_TAC arith_ss [Once RUNTO_ADVANCE]
        ],
        GEN_TAC THEN `!h tl. h :: tl = [h:INST] ++ tl` by RW_TAC list_ss [] THEN
        METIS_TAC [WELL_FORMED_def, translate_def, mk_SC_def, SC_IS_WELL_FORMED, STATEMENT_IS_WELL_FORMED]
    ]
);

val IR_SC_IS_WELL_FORMED = Q.store_thm (
   "IR_SC_IS_WELL_FORMED",
   `!ir1 ir2. WELL_FORMED ir1 /\ WELL_FORMED ir2 ==>
        WELL_FORMED (SC ir1 ir2)`,
    RW_TAC std_ss [WELL_FORMED_def, translate_def] THEN
    IMP_RES_TAC (SC_IS_WELL_FORMED)
   );

val IR_CJ_IS_WELL_FORMED = Q.store_thm (
   "IR_CJ_IS_WELL_FORMED",
   `!cond ir_t ir_f. WELL_FORMED ir_t /\ WELL_FORMED ir_f ==>
        WELL_FORMED (CJ cond ir_t ir_f)`,
    RW_TAC std_ss [WELL_FORMED_def, translate_def] THEN
    IMP_RES_TAC (CJ_IS_WELL_FORMED) THEN
    METIS_TAC []
   );

val IR_TR_IS_WELL_FORMED = Q.store_thm (
   "IR_TR_IS_WELL_FORMED",
   `!ir cond. WELL_FORMED ir /\ WF_TR (cond, translate ir) ==>
        WELL_FORMED (TR cond ir)`,
    RW_TAC std_ss [WELL_FORMED_def, translate_def] THEN
    IMP_RES_TAC (TR_IS_WELL_FORMED)
   );

(*---------------------------------------------------------------------------------*)
(*      Semantics of IR                                                            *) 
(*---------------------------------------------------------------------------------*)

val IR_SEMANTICS_SC = Q.store_thm (
   "IR_SEMANTICS_SC",
   `WELL_FORMED ir1 /\ WELL_FORMED ir2 ==>
     (run_ir (SC ir1 ir2) st =
       run_ir ir2 (run_ir ir1 st))`,
    METIS_TAC [SIMP_RULE std_ss [] (Q.SPECL [`ir1`,`ir2`, `\st'. st' = st`, `\st'. st' = run_ir ir1 st`, `\st'. st' = run_ir ir1 st`,
                         `\st'. st' =  run_ir ir2 (run_ir ir1 st)`] HOARE_SC_IR)]
   );
   
 
val IR_SEMANTICS_BLK = Q.store_thm (
   "IR_SEMANTICS_BLK",
    `(run_ir (BLK (stm::stmL)) st =
          run_ir (BLK stmL) (mdecode st stm)) /\
     (run_ir (BLK []) st = st)`,

    REPEAT STRIP_TAC THENL [
       RW_TAC list_ss [run_ir_def, translate_def] THEN
           `translate_assignment stm::translate (BLK stmL) = translate (SC (BLK [stm]) (BLK stmL))` by RW_TAC list_ss [translate_def,mk_SC_def] THEN
           RW_TAC std_ss [GSYM run_ir_def] THEN
           `run_ir (BLK [stm]) st = mdecode st stm` by (
               RW_TAC list_ss [run_ir_def, run_arm_def, translate_def, Once RUNTO_ADVANCE] THEN
               RW_TAC list_ss [GSYM uploadCode_def, UPLOADCODE_LEM] THEN
               RW_TAC list_ss [GSYM TRANSLATE_ASSIGMENT_CORRECT, get_st_def, Once RUNTO_ADVANCE]
           ) THEN
           `well_formed [translate_assignment stm] /\ well_formed (translate (BLK stmL))` by 
               METIS_TAC [WELL_FORMED_def, BLOCK_IS_WELL_FORMED, STATEMENT_IS_WELL_FORMED] THEN
           FULL_SIMP_TAC list_ss [WELL_FORMED_def, IR_SEMANTICS_SC, translate_def],
       RW_TAC list_ss [run_ir_def, run_arm_def, translate_def, Once RUNTO_ADVANCE, get_st_def]
   ]
  );

val IR_SEMANTICS_CJ = Q.store_thm (
   "IR_SEMANTICS_CJ",
   ` WELL_FORMED ir_t /\ WELL_FORMED ir_f ==>
     (run_ir (CJ cond ir_t ir_f) st = 
          if eval_cond cond st then run_ir ir_t st
          else run_ir ir_f st)`,
   RW_TAC std_ss [] THEN
   METIS_TAC [SIMP_RULE std_ss [] (Q.SPECL [`cond`, `ir_t`, `ir_f`, `\st'. st' = st`, `\st'. st' = run_ir ir_t st`, 
                 `\st'. st' = run_ir ir_f st`] HOARE_CJ_IR)]
  );


val IR_SEMANTICS_TR = Q.store_thm (
   "IR_SEMANTICS_TR",
     `WELL_FORMED ir /\ WF_TR (cond,translate ir) ==>
      (run_ir (TR cond ir) st =
         WHILE (\st'.~eval_cond cond st') (run_ir ir) st)`,

    RW_TAC std_ss [WELL_FORMED_def, run_ir_def, run_arm_def, translate_def] THEN
    Q.ABBREV_TAC `arm = translate ir` THEN
    IMP_RES_TAC (SIMP_RULE set_ss [] (Q.SPECL [`cond`,`arm`,`(\i. ARB)`,`(0,0w,st):STATE`,`{}`] UNROLL_TR_LEM)) THEN
    POP_ASSUM (ASSUME_TAC o Q.SPEC `st`) THEN
    FULL_SIMP_TAC std_ss [FUNPOW,get_st_def] THEN
    NTAC 2 (POP_ASSUM (K ALL_TAC)) THEN
    Induct_on `loopNum cond arm (\i.ARB) ((0,0w,st),{})` THENL [
        REWRITE_TAC [Once EQ_SYM_EQ] THEN RW_TAC std_ss [FUNPOW,get_st_def] THEN
            IMP_RES_TAC LOOPNUM_BASIC THEN
            FULL_SIMP_TAC arith_ss [Once WHILE, get_st_def],

        REWRITE_TAC [Once EQ_SYM_EQ] THEN RW_TAC std_ss [FUNPOW] THEN
            IMP_RES_TAC LOOPNUM_INDUCTIVE THEN
            `v = loopNum cond arm (\i.ARB) ((0,0w,SND (SND (FST (runTo (upload arm (\i.ARB) 0) (LENGTH arm) ((0,0w,st),{}))))),{})` by
            METIS_TAC [ABS_PAIR_THM,DECIDE (Term`!x.0+x=x`),LOOPNUM_INDEPENDENT_OF_CPSR_PCS, get_st_def, FST, SND, DSTATE_IRRELEVANT_PCS, 
		well_formed_def] THEN
            RES_TAC THEN Q.PAT_ASSUM `v = x` (ASSUME_TAC o GSYM) THEN FULL_SIMP_TAC std_ss [] THEN POP_ASSUM (K ALL_TAC) THEN
            Q.PAT_ASSUM `v = x` (ASSUME_TAC o GSYM) THEN FULL_SIMP_TAC std_ss [] THEN POP_ASSUM (K ALL_TAC) THEN
            Q.PAT_ASSUM `~x` (ASSUME_TAC o SIMP_RULE std_ss [get_st_def]) THEN
            RW_TAC std_ss [Once WHILE] THEN
            Q.UNABBREV_TAC `arm` THEN
            `run_ir ir st = SND (SND (FST (runTo (upload (translate ir) (\i. ARB) 0) (LENGTH (translate ir)) ((0,0w,st),{}))))` by RW_TAC arith_ss [
                   get_st_def, run_ir_def, run_arm_def] THEN 
            METIS_TAC [SND,FST,get_st_def,FUNPOW_DSTATE, ABS_PAIR_THM]
      ]
  );


val SEMANTICS_OF_IR = Q.store_thm (
   "SEMANTICS_OF_IR",
   ` WELL_FORMED ir1 /\ WELL_FORMED ir2 ==>
     (run_ir (BLK (stm::stmL)) st =
          run_ir (BLK stmL) (mdecode st stm)) /\
     (run_ir (BLK []) st = st) /\
     (run_ir (SC ir1 ir2) st = run_ir ir2 (run_ir ir1 st)) /\
     (run_ir (CJ cond ir1 ir2) st =
           (if eval_cond cond st then run_ir ir1 st else run_ir ir2 st)) /\
     ( WF_TR (cond,translate ir1) ==> 
       (run_ir (TR cond ir1) st =
           WHILE (\st'. ~eval_cond cond st') (run_ir ir1) st))`,
   RW_TAC std_ss [IR_SEMANTICS_BLK, IR_SEMANTICS_CJ, IR_SEMANTICS_SC, IR_SEMANTICS_TR]
  );       

val _ = export_theory();
