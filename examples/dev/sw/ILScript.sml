(* interactive use:

quietdec := true;
loadPath := (concat Globals.HOLDIR "/examples/dev/sw") :: !loadPath;

app load ["pred_setSimps", "pred_setTheory",
     "arithmeticTheory", "wordsTheory", "wordsLib", "pairTheory", "listTheory", "whileTheory", "finite_mapTheory", "preARMTheory", "ARMCompositionTheory",
	  "relationTheory"];

quietdec := false;
*)


open HolKernel Parse boolLib bossLib numLib pred_setSimps pred_setTheory
     arithmeticTheory wordsTheory wordsLib pairTheory listTheory whileTheory finite_mapTheory preARMTheory ARMCompositionTheory relationTheory;

val _ = hide "B";
(*---------------------------------------------------------------------------------*)
(*---------------------------------------------------------------------------------*)

val _ = new_theory "IL";

val set_ss = std_ss ++ SET_SPEC_ss ++ PRED_SET_ss;

(*---------------------------------------------------------------------------------*)
(*      Registers and memory data in IL                                            *)
(*---------------------------------------------------------------------------------*)

val _ = Hol_datatype ` 
    MREG = R0 | R1 | R2 | R3 | R4 | R5 | R6 | R7 | R8 | R9 | R10 | R11 | R12 | R13 | R14`;

val _ = type_abbrev("MMEM", Type`:MREG # OFFSET`);      (* memory in ir *)

val _ = Hol_datatype `
    MEXP = MR of MREG          (* registers *)
         | MC of word4 => word8 (* constants *)
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
    (index_of_reg R14 = 14)`;

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
       preARM$MEM (index_of_reg base,offset)`;        (* [base + offset] *)

val toEXP_def = Define `
    (toEXP (MR r) = toREG r) /\
    (toEXP (MC shift c) = WCONST ((w2w c):word32 #>> (2*w2n shift)))`;

(*---------------------------------------------------------------------------------*)
(*      Semantics of the intermediate language                                     *)
(*---------------------------------------------------------------------------------*)

val _ = Hol_datatype ` 
    DOPER = MLDR of MREG => MMEM |
           MSTR of MMEM => MREG |
           MMOV of MREG => MEXP |
           MADD of MREG => MREG => MEXP |
           MSUB of MREG => MREG => MEXP | 
           MRSB of MREG => MREG => MEXP |
           MMUL of MREG => MREG => MREG |
           MAND of MREG => MREG => MEXP |
           MORR of MREG => MREG => MEXP |
     MEOR of MREG => MREG => MEXP |
     MLSL of MREG => MREG => word5 |
     MLSR of MREG => MREG => word5 |
     MASR of MREG => MREG => word5 |
     MROR of MREG => MREG => word5 |
     MPUSH of REGISTER => REGISTER list |
     MPOP of REGISTER => REGISTER list`;

val _ = type_abbrev("CEXP", Type`:MREG # COND # MEXP`);

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
      write st (toREG dst) (read st (toREG src1) + read st (toEXP src2))) /\
  (mdecode st (MSUB dst src1 src2) =
      write st (toREG dst) (read st (toREG src1) - read st (toEXP src2))) /\
  (mdecode st (MRSB dst src1 src2) =
      write st (toREG dst) (read st (toEXP src2) - read st (toREG src1))) /\
  (mdecode st (MMUL dst src1 src2_reg) =
      write st (toREG dst) (read st (toREG src1) * read st (toREG src2_reg))) /\
  (mdecode st (MAND dst src1 src2) =
      write st (toREG dst) (read st (toREG src1) && read st (toEXP src2))) /\
  (mdecode st (MORR dst src1 src2) =
      write st (toREG dst) (read st (toREG src1) !! read st (toEXP src2))) /\
  (mdecode st (MEOR dst src1 src2) =
      write st (toREG dst) (read st (toREG src1) ?? read st (toEXP src2))) /\
  (mdecode st (MLSL dst src2_reg src2_num) =
      write st (toREG dst) (read st (toREG src2_reg) << w2n src2_num)) /\
  (mdecode st (MLSR dst src2_reg src2_num) =
      write st (toREG dst) (read st (toREG src2_reg) >>> w2n src2_num)) /\  
  (mdecode st (MASR dst src2_reg src2_num) =
      write st (toREG dst) (read st (toREG src2_reg) >> w2n src2_num)) /\
  (mdecode st (MROR dst src2_reg src2_num) =
      write st (toREG dst) (read st (toREG src2_reg) #>> w2n src2_num)) /\
  (mdecode st (MPUSH dst' srcL) =
      pushL st dst' srcL) /\
  (mdecode st (MPOP dst' srcL) =
      popL st dst' srcL)
  `;

val translate_assignment_def = Define `
    (translate_assignment (MMOV dst src) = ((MOV,NONE,F),SOME (toREG dst), [toEXP src], NONE):INST) /\
    (translate_assignment (MADD dst src1 src2) = ((ADD,NONE,F),SOME (toREG dst), [toREG src1; toEXP src2], NONE):INST) /\
    (translate_assignment (MSUB dst src1 src2) = ((SUB,NONE,F),SOME (toREG dst), [toREG src1; toEXP src2], NONE):INST) /\
    (translate_assignment (MRSB dst src1 src2) = ((RSB,NONE,F),SOME (toREG dst), [toREG src1; toEXP src2], NONE):INST) /\
    (translate_assignment (MMUL dst src1 src2_reg) = ((MUL,NONE,F),SOME (toREG dst), [toREG src1; toREG src2_reg], NONE):INST) /\
    (translate_assignment (MAND dst src1 src2) = ((AND,NONE,F),SOME (toREG dst), [toREG src1; toEXP src2], NONE):INST) /\
    (translate_assignment (MORR dst src1 src2) = ((ORR,NONE,F),SOME (toREG dst), [toREG src1; toEXP src2], NONE):INST) /\
    (translate_assignment (MEOR dst src1 src2) = ((EOR,NONE,F),SOME (toREG dst), [toREG src1; toEXP src2], NONE):INST) /\
    (translate_assignment (MLSL dst src2_reg src2_num) = ((LSL,NONE,F),SOME (toREG dst), [toREG src2_reg; WCONST (w2w src2_num)], NONE):INST) /\
    (translate_assignment (MLSR dst src2_reg src2_num) = ((LSR,NONE,F),SOME (toREG dst), [toREG src2_reg; WCONST (w2w src2_num)], NONE):INST) /\
    (translate_assignment (MASR dst src2_reg src2_num) = ((ASR,NONE,F),SOME (toREG dst), [toREG src2_reg; WCONST (w2w src2_num)], NONE):INST) /\
    (translate_assignment (MROR dst src2_reg src2_num) = ((ROR,NONE,F),SOME (toREG dst), [toREG src2_reg; WCONST (w2w src2_num)], NONE):INST) /\
    (!dst src.translate_assignment (MLDR dst src) = ((LDR,NONE,F),SOME (toREG dst), [toMEM src], NONE):INST) /\
    (!dst src.translate_assignment (MSTR dst src) = ((STR,NONE,F),SOME (toREG src), [toMEM dst], NONE):INST) /\
    (!dst srcL.translate_assignment (MPUSH dst srcL) = ((STMFD,NONE,F),SOME (WREG dst), MAP REG srcL, NONE):INST) /\
    (!dst srcL.translate_assignment (MPOP dst srcL) = ((LDMFD,NONE,F),SOME (WREG dst), MAP REG srcL, NONE):INST)
    `;

val translate_condition_def = Define `
  translate_condition (r, c, e) =
    (toREG r, c, toEXP e)`

val eval_il_cond_def = Define `
  eval_il_cond cond = eval_cond (translate_condition cond)`;


val TRANSLATE_ASSIGMENT_CORRECT = Q.store_thm
  ("TRANSLATE_ASSIGMENT_CORRECT",
   `!(stm:DOPER) pc cpsr st.
       (SUC pc,cpsr,mdecode st stm) = decode_cond (pc,cpsr,st) (translate_assignment stm)`,
     SIMP_TAC std_ss [FORALL_DSTATE] THEN
     Cases_on `stm` THEN
     RW_TAC list_ss [translate_assignment_def, decode_cond_thm, decode_op_thm, write_thm,  mdecode_def] THEN
     RW_TAC list_ss [pushL_def, popL_def, read_thm, w2n_w2w, dimindex_5, dimindex_32]
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
	 mk_CJ (translate_condition cond) (translate Strue) (translate Sfalse)) /\
    (translate (TR cond Sbody) = 
         mk_TR (translate_condition cond) (translate Sbody))
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
      (WELL_FORMED (BLK stmL) = well_formed (translate (BLK stmL))) /\
      (WELL_FORMED (SC S1 S2) = well_formed (translate (SC S1 S2)) /\
                                WELL_FORMED S1 /\ WELL_FORMED S2) /\
      (WELL_FORMED (CJ cond S1 S2) = well_formed (translate (CJ cond S1 S2)) /\
                                WELL_FORMED S1 /\ WELL_FORMED S2) /\
      (WELL_FORMED (TR cond S1) = well_formed (translate (TR cond S1)) /\
                                WELL_FORMED S1 /\
                                WF_TR (translate_condition cond, translate S1))`;


val WELL_FORMED_SUB_def = Define `
      (WELL_FORMED_SUB (BLK stmL) = T) /\
      (WELL_FORMED_SUB (SC S1 S2) = WELL_FORMED S1 /\ WELL_FORMED S2) /\
      (WELL_FORMED_SUB (CJ cond S1 S2) = WELL_FORMED S1 /\ WELL_FORMED S2) /\
      (WELL_FORMED_SUB (TR cond S1) = WELL_FORMED S1 /\ WF_TR (translate_condition cond, translate S1))`;

val WELL_FORMED_SUB_thm = store_thm ("WELL_FORMED_SUB_thm",
    ``!ir. WELL_FORMED ir = (WELL_FORMED_SUB ir /\ well_formed (translate ir))``,

    Cases_on `ir` THEN
    REWRITE_TAC [WELL_FORMED_def, WELL_FORMED_SUB_def] THEN
    PROVE_TAC[]);

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
   RW_TAC std_ss [WELL_FORMED_SUB_thm, run_ir_def, translate_def, run_arm_def, eval_fl_def] THEN 
   IMP_RES_TAC (SIMP_RULE std_ss [eval_fl_def, uploadCode_def]  HOARE_SC_FLAT)
  );

val HOARE_CJ_IR = Q.store_thm (
   "HOARE_CJ_IR",
   `!cond ir_t ir_f P Q R.
       WELL_FORMED ir_t /\ WELL_FORMED ir_f /\
           (!st. P st ==> Q (run_ir ir_t st)) /\
           (!st. P st ==> R (run_ir ir_f st)) ==>
             !st. P st ==>
                if eval_il_cond cond st then Q (run_ir (CJ cond ir_t ir_f) st)
                    else R (run_ir (CJ cond ir_t ir_f) st)`,
   RW_TAC std_ss [WELL_FORMED_SUB_thm, run_ir_def, translate_def, run_arm_def, eval_fl_def, eval_il_cond_def] THEN
   IMP_RES_TAC (SIMP_RULE std_ss [eval_fl_def, uploadCode_def] HOARE_CJ_FLAT) THEN
   METIS_TAC []
  );

val HOARE_TR_IR = Q.store_thm (
   "HOARE_TR_IR",
   `!cond ir P.
       WELL_FORMED ir /\  WF_TR (translate_condition cond, translate ir) /\
         (!st. P st ==> P (run_ir ir st)) ==>
            !st. P st ==> P (run_ir (TR cond ir) st) /\ 
                 eval_il_cond cond (run_ir (TR cond ir) st)`,
   RW_TAC std_ss [WELL_FORMED_SUB_thm, run_ir_def, translate_def, run_arm_def, eval_fl_def, eval_il_cond_def] THEN
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
   `!ir1 ir2. WELL_FORMED ir1 /\ WELL_FORMED ir2 = WELL_FORMED (SC ir1 ir2)`,
    RW_TAC std_ss [WELL_FORMED_SUB_thm, WELL_FORMED_SUB_def, translate_def] THEN
    PROVE_TAC [SC_IS_WELL_FORMED]
   );

val IR_CJ_IS_WELL_FORMED = Q.store_thm (
   "IR_CJ_IS_WELL_FORMED",
   `!cond ir_t ir_f. WELL_FORMED ir_t /\ WELL_FORMED ir_f =
        WELL_FORMED (CJ cond ir_t ir_f)`,
    RW_TAC std_ss [WELL_FORMED_SUB_thm, WELL_FORMED_SUB_def, translate_def] THEN
    PROVE_TAC [CJ_IS_WELL_FORMED]
   );

val IR_TR_IS_WELL_FORMED = Q.store_thm (
   "IR_TR_IS_WELL_FORMED",
   `!ir cond. WELL_FORMED ir /\ WF_TR (translate_condition cond, translate ir) =
        WELL_FORMED (TR cond ir)`,
    RW_TAC std_ss [WELL_FORMED_SUB_thm, WELL_FORMED_SUB_def, translate_def] THEN
    PROVE_TAC [TR_IS_WELL_FORMED]
   );

val WELL_FORMED_thm = store_thm ("WELL_FORMED_thm",
    ``(WELL_FORMED (BLK stmL) = T) /\
      (WELL_FORMED (SC S1 S2) = WELL_FORMED S1 /\ WELL_FORMED S2) /\
      (WELL_FORMED (CJ cond S1 S2) = WELL_FORMED S1 /\ WELL_FORMED S2) /\
      (WELL_FORMED (TR cond S1) = WELL_FORMED S1 /\ WF_TR (translate_condition cond, translate S1))``,

      SIMP_TAC std_ss [BLOCK_IS_WELL_FORMED, IR_SC_IS_WELL_FORMED, IR_CJ_IS_WELL_FORMED, IR_TR_IS_WELL_FORMED]);


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
          if eval_il_cond cond st then run_ir ir_t st
          else run_ir ir_f st)`,
   RW_TAC std_ss [] THEN
   METIS_TAC [SIMP_RULE std_ss [] (Q.SPECL [`cond`, `ir_t`, `ir_f`, `\st'. st' = st`, `\st'. st' = run_ir ir_t st`, 
                 `\st'. st' = run_ir ir_f st`] HOARE_CJ_IR)]
  );


val IR_SEMANTICS_TR = Q.store_thm (
   "IR_SEMANTICS_TR",
     `WELL_FORMED ir /\ WF_TR (translate_condition cond,translate ir) ==>
      (run_ir (TR cond ir) st =
         WHILE (\st'.~eval_il_cond cond st') (run_ir ir) st)`,

    RW_TAC std_ss [WELL_FORMED_SUB_thm, run_ir_def, run_arm_def, translate_def, eval_il_cond_def] THEN
    Q.ABBREV_TAC `arm = translate ir` THEN
    IMP_RES_TAC (SIMP_RULE set_ss [] (Q.SPECL [`translate_condition cond`,`arm`,`(\i. ARB)`,`(0,0w,st):STATE`,`{}`] UNROLL_TR_LEM)) THEN
    POP_ASSUM (ASSUME_TAC o Q.SPEC `st`) THEN
    FULL_SIMP_TAC std_ss [FUNPOW,get_st_def] THEN
    NTAC 2 (POP_ASSUM (K ALL_TAC)) THEN
    Induct_on `loopNum (translate_condition cond) arm (\i.ARB) ((0,0w,st),{})` THENL [
        REWRITE_TAC [Once EQ_SYM_EQ] THEN RW_TAC std_ss [FUNPOW,get_st_def] THEN
            IMP_RES_TAC LOOPNUM_BASIC THEN
            FULL_SIMP_TAC arith_ss [Once WHILE, get_st_def],

        REWRITE_TAC [Once EQ_SYM_EQ] THEN RW_TAC std_ss [FUNPOW] THEN
            IMP_RES_TAC LOOPNUM_INDUCTIVE THEN
            `v = loopNum (translate_condition cond) arm (\i.ARB) ((0,0w,SND (SND (FST (runTo (upload arm (\i.ARB) 0) (LENGTH arm) ((0,0w,st),{}))))),{})` by
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


val IR_SEMANTICS_EMBEDDED_THM = Q.store_thm (
   "IR_SEMANTICS_EMBEDDED_THM",
		`!ir s. well_formed (translate ir) ==>
				(?pc cpsr pcS. 	  
				(run_arm (translate ir) s = ((pc, cpsr, run_ir ir (SND(SND(FST s)))), pcS)))`,

		SIMP_TAC std_ss [run_ir_def, well_formed_def] THEN
		REPEAT STRIP_TAC THEN
		`?pc cpsr st pcS. (s = ((pc,cpsr,st),pcS))` by METIS_TAC[PAIR, FST, SND] THEN
		ASM_REWRITE_TAC [run_arm_def] THEN
		Q.ABBREV_TAC `arm = (translate ir)` THEN
		`get_st (runTo (upload arm (\i. ARB) 0) (0 + LENGTH arm) ((0,0w,st),{})) =
		 get_st (runTo (upload arm (\i. ARB) pc) (pc + LENGTH arm) ((pc,cpsr,st),pcS))`
			 by METIS_TAC[status_independent_def, DSTATE_IRRELEVANT_PCS, FST] THEN
		ASM_SIMP_TAC std_ss [get_st_def] THEN 
		METIS_TAC[PAIR, FST, SND]);




val WF_ir_TR_def =  Define `
	WF_ir_TR (cond, ir) =
		WF_Loop ((eval_il_cond cond),
              (run_ir ir))`


val WF_ir_TR_thm = Q.store_thm (
   "WF_ir_TR_thm",
	  `!cond ir. WELL_FORMED ir ==>
		(WF_ir_TR (cond, ir) = WF_TR (translate_condition cond, translate ir))`,

SIMP_TAC std_ss [WF_ir_TR_def, WF_TR_def, WF_Loop_def, eval_il_cond_def, WELL_FORMED_SUB_thm] THEN
REPEAT STRIP_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THENL [
	Q_TAC EXISTS_TAC `inv_image R get_st` THEN
	ASM_SIMP_TAC std_ss [WF_inv_image] THEN
	GEN_TAC THEN
	`?pc' cpsr' pcS'. run_arm (translate ir) s =
		((pc',cpsr',run_ir ir (SND (SND (FST s)))),pcS')` by 
		METIS_TAC[IR_SEMANTICS_EMBEDDED_THM] THEN
	`?pc cpsr st pcS. (s = ((pc,cpsr,st),pcS))` by METIS_TAC[PAIR, FST, SND] THEN
	`runTo (upload (translate ir) iB pc) (pc + LENGTH (translate ir))
				((pc,cpsr,st),pcS) =
	run_arm (translate ir) ((pc,cpsr,st),pcS)` by ALL_TAC THEN1 (
		SIMP_TAC std_ss [run_arm_def] THEN
		METIS_TAC[WELL_FORMED_INSTB, FST]
	) THEN
	FULL_SIMP_TAC std_ss [relationTheory.inv_image_def, get_st_def],


	
	FULL_SIMP_TAC std_ss [FORALL_PROD] THEN
	`!iB pc cpsr st pcS. runTo (upload (translate ir) iB pc) (pc + LENGTH (translate ir))
				((pc,cpsr,st),pcS) =
	run_arm (translate ir) ((pc,cpsr,st),pcS)` by ALL_TAC THEN1 (
		SIMP_TAC std_ss [run_arm_def] THEN
		METIS_TAC[WELL_FORMED_INSTB, FST]
	) THEN
	FULL_SIMP_TAC std_ss [] THEN
	POP_ASSUM (fn thm => ALL_TAC) THEN

	`?Q. Q = \st st'. !s'. 
	   let s = (run_arm (translate ir) s') in
		(((get_st s' = st')) ==> ((get_st s = st) /\
	     R s s'))` by METIS_TAC[] THEN
	Q_TAC EXISTS_TAC `Q` THEN
	REPEAT STRIP_TAC THENL [
		FULL_SIMP_TAC std_ss [WF_DEF, LET_THM] THEN
		REPEAT STRIP_TAC THEN
		`?B'. B' = (\s. B (get_st s))` by METIS_TAC[] THEN
		Q.PAT_ASSUM `!B. (?w. B w) ==> X` (fn thm => Q_TAC 
			(fn t => (ASSUME_TAC (SPEC t thm))) `B'`) THEN
		Q.PAT_UNDISCH_TAC `X` THEN
		SIMP_TAC std_ss [GSYM LEFT_FORALL_IMP_THM,
			GSYM LEFT_EXISTS_IMP_THM] THEN

		`?w. B (get_st w)` by METIS_TAC[get_st_def, PAIR, FST, SND] THEN
		Q_TAC EXISTS_TAC `w'` THEN
		ASM_SIMP_TAC std_ss [] THEN
		REPEAT STRIP_TAC THEN
		Q_TAC EXISTS_TAC `get_st min` THEN
		ASM_SIMP_TAC std_ss [] THEN
		GEN_TAC THEN
		Q_TAC EXISTS_TAC `min` THEN
		SIMP_TAC std_ss [] THEN
	   METIS_TAC[],


		FULL_SIMP_TAC std_ss [LET_THM, get_st_def, run_ir_def] THEN
		GEN_TAC THEN
		`?pc cpsr st pcS. (s' = ((pc,cpsr,st),pcS))` by METIS_TAC[PAIR, FST, SND] THEN
		ASM_SIMP_TAC std_ss [] THEN
		FULL_SIMP_TAC std_ss [GSYM get_st_def, run_arm_def,  well_formed_def] THEN

		`(LENGTH (translate ir)) = 0 + (LENGTH (translate ir))` by DECIDE_TAC THEN
		METIS_TAC[status_independent_def, DSTATE_IRRELEVANT_PCS, FST]
	]
]);



val IR_SEMANTICS_TR___FUNPOW = Q.store_thm (
   "IR_SEMANTICS_TR___FUNPOW",
     `WELL_FORMED ir /\ WF_TR (translate_condition cond,translate ir) ==>
      (run_ir (TR cond ir) st =
        FUNPOW (run_ir ir) (shortest (eval_il_cond cond) (run_ir ir) st) st)`,


	SIMP_TAC std_ss [IR_SEMANTICS_TR] THEN
	REPEAT STRIP_TAC THEN
	`(\st'. ~eval_il_cond cond st') = $~ o (eval_il_cond cond)` by SIMP_TAC std_ss [combinTheory.o_DEF] THEN
	ASM_REWRITE_TAC[] THEN
	MATCH_MP_TAC ARMCompositionTheory.UNROLL_LOOP THEN
	METIS_TAC[WF_ir_TR_thm, WF_ir_TR_def]);




val SEMANTICS_OF_IR = Q.store_thm (
   "SEMANTICS_OF_IR",
   `(run_ir (BLK []) st = st) /\
    (run_ir (BLK (stm::stmL)) st =
          run_ir (BLK stmL) (mdecode st stm)) /\
    ((WELL_FORMED ir1 /\ WELL_FORMED ir2) ==>
    (run_ir (SC ir1 ir2) st = run_ir ir2 (run_ir ir1 st))) /\
    ((WELL_FORMED ir1 /\ WELL_FORMED ir2) ==>	 
     (run_ir (CJ cond ir1 ir2) st =
           (if eval_il_cond cond st then run_ir ir1 st else run_ir ir2 st))) /\
     (( WELL_FORMED ir1 /\ WF_TR (translate_condition cond,translate ir1)) ==> 
       (run_ir (TR cond ir1) st =
           WHILE (\st'. ~eval_il_cond cond st') (run_ir ir1) st))`,
   RW_TAC std_ss [IR_SEMANTICS_BLK, IR_SEMANTICS_CJ, IR_SEMANTICS_SC, IR_SEMANTICS_TR]
  );       

val _ = export_theory();
