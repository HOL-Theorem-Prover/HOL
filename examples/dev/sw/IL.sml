app load ["pred_setSimps","pred_setTheory","whileTheory","finite_mapTheory","rich_listTheory"];

open HolKernel Parse boolLib bossLib numLib pred_setSimps pred_setTheory
     arithmeticTheory word32Theory pairTheory listTheory whileTheory finite_mapTheory;

(*---------------------------------------------------------------------------------*)
(*      Registers and memory data in IL                                            *)
(*---------------------------------------------------------------------------------*)

val _ = Hol_datatype ` 
    MREG = R0 | R1 | R2 | R3 | R4 | R5 | R6 | R7 | R8 | R9 | R10 | R11 | R12 | R13 | R14`;

val _ = type_abbrev("MMEM", Type`:OFFSET`);

val _ = Hol_datatype ` 
    MEXP = Ril of MREG
         | Mil of MMEM`;

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
    (index_of_reg R6 = 10) /\
    (index_of_reg R7 = 11) /\
    (index_of_reg R8 = 12) /\
    (index_of_reg R9 = 13) /\
    (index_of_reg R9 = 14)
`;

val toREG = Define `
    toREG r =
       REG (index_of_reg r)`;

val toMEM = Define `
    toMEM (offset:MMEM) =
       MEM (11,offset)`;        (* [fp + offset] *)

(*---------------------------------------------------------------------------------*)
(*      Semantics of the intermediate language                                     *)
(*---------------------------------------------------------------------------------*)

val _ = Hol_datatype ` 
    DOPER = MLDR of MREG => MMEM |
           MSTR of MMEM => MREG |
           MMOV of MREG => MREG |
           MADD of MREG => MREG => MREG |
           MSUB of MREG => MREG => MREG | 
           MRSB of MREG => MREG => MREG |
           MMUL of MREG => MREG => MREG |
           MAND of MREG => MREG => MREG |
           MORR of MREG => MREG => MREG |
	   MEOR of MREG => MREG => MREG |
	   MLSL of MREG => MREG => MREG |
	   MLSR of MREG => MREG => MREG |
	   MASR of MREG => MREG => MREG |
	   MROR of MREG => MREG => MREG`;

val _ = Hol_datatype ` 
    SOPER =
           PUSHL of REGISTER list |
	   POPL of REGISTER list
   `;


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
(*---------------------------------------------------------------------------------*)

(* Push data in multiple registers into the stack without writing-back to the sp   *)
 
val popL =
  Define `popL st regL = 
    FST (FOLDL (\(st1,i) reg. (write st1 (REG reg) (read st (MEM(13,POS(i+1)))), i+1)) (st,0) regL)`;

(* Pop from the stack to multiple registers with writing-back to the sp            *)

val pushL =
  Define `pushL st regL = 
   write (FST (FOLDL (\(st1,i) reg. (write st1 (MEM(13,NEG i)) (read st (REG reg)), i+1)) (st,0) (REVERSE regL)))
                                        (REG 13) (read st (REG 13) - n2w (LENGTH regL))`;

(*---------------------------------------------------------------------------------*)
(*      Decode assignment statement                                                *)
(*---------------------------------------------------------------------------------*)

val mdecode = Define `
  (!dst src.mdecode st (MLDR dst src) =
      write st (toREG dst) (read st (toMEM src))) /\
  (!dst src.mdecode st (MSTR dst src) =
      write st (toMEM dst) (read st (toREG src))) /\
  (mdecode st (MMOV dst src) =
      write st (toREG dst) (read st (toREG src))) /\
  (mdecode st (MADD dst src1 src2) =
      write st (toREG dst) (read st (toREG src1) + read st (toREG src2))) /\
  (mdecode st (MSUB dst src1 src2) =
      write st (toREG dst) (read st (toREG src1) - read st (toREG src2))) /\
  (mdecode st (MRSB dst src1 src2) =
      write st (toREG dst) (read st (toREG src2) - read st (toREG src1))) /\
  (mdecode st (MMUL dst src1 src2) =
      write st (toREG dst) (read st (toREG src1) * read st (toREG src2))) /\
  (mdecode st (MAND dst src1 src2) =
      write st (toREG dst) (read st (toREG src1) & read st (toREG src2))) /\
  (mdecode st (MORR dst src1 src2) =
      write st (toREG dst) (read st (toREG src1) | read st (toREG src2))) /\
  (mdecode st (MEOR dst src1 src2) =
      write st (toREG dst) (read st (toREG src1) # read st (toREG src2))) /\
  (mdecode st (MLSL dst src1 src2) =
      write st (toREG dst) (read st (toREG src1) << w2n (read st (toREG src2)))) /\
  (mdecode st (MLSR dst src1 src2) =
      write st (toREG dst) (read st (toREG src1) >>> w2n (read st (toREG src2)))) /\  
  (mdecode st (MASR dst src1 src2) =
      write st (toREG dst) (read st (toREG src1) >> w2n (read st (toREG src2)))) /\
  (mdecode st (MROR dst src1 src2) =
      write st (toREG dst) (read st (toREG src1) #>> w2n (read st (toREG src2))))`;

val translate_assignment = Define `
    (translate_assignment (MMOV dst src) = ((MOV,NONE,F),SOME (toREG dst), [toREG src], NONE):INST) /\
    (translate_assignment (MADD dst src1 src2) = ((ADD,NONE,F),SOME (toREG dst), [toREG src1; toREG src2], NONE):INST) /\
    (translate_assignment (MSUB dst src1 src2) = ((SUB,NONE,F),SOME (toREG dst), [toREG src1; toREG src2], NONE):INST) /\
    (translate_assignment (MRSB dst src1 src2) = ((RSB,NONE,F),SOME (toREG dst), [toREG src1; toREG src2], NONE):INST) /\
    (translate_assignment (MMUL dst src1 src2) = ((MUL,NONE,F),SOME (toREG dst), [toREG src1; toREG src2], NONE):INST) /\
    (translate_assignment (MAND dst src1 src2) = ((AND,NONE,F),SOME (toREG dst), [toREG src1; toREG src2], NONE):INST) /\
    (translate_assignment (MORR dst src1 src2) = ((ORR,NONE,F),SOME (toREG dst), [toREG src1; toREG src2], NONE):INST) /\
    (translate_assignment (MEOR dst src1 src2) = ((EOR,NONE,F),SOME (toREG dst), [toREG src1; toREG src2], NONE):INST) /\
    (translate_assignment (MLSL dst src1 src2) = ((LSL,NONE,F),SOME (toREG dst), [toREG src1; toREG src2], NONE):INST) /\
    (translate_assignment (MLSR dst src1 src2) = ((LSR,NONE,F),SOME (toREG dst), [toREG src1; toREG src2], NONE):INST) /\
    (translate_assignment (MASR dst src1 src2) = ((ASR,NONE,F),SOME (toREG dst), [toREG src1; toREG src2], NONE):INST) /\
    (translate_assignment (MROR dst src1 src2) = ((ROR,NONE,F),SOME (toREG dst), [toREG src1; toREG src2], NONE):INST) /\
    (!dst src.translate_assignment (MLDR dst src) = ((LDR,NONE,F),SOME (toREG dst), [toMEM src], NONE):INST) /\
    (!dst src.translate_assignment (MSTR dst src) = ((STR,NONE,F),SOME (toREG src), [toMEM dst], NONE):INST)`;


val TRANSLATE_ASSIGMENT_CORRECT = Q.store_thm
  ("TRANSLATE_ASSIGMENT_CORRECT",
   `!(stm:DOPER) pc cpsr st.
       (SUC pc,cpsr,mdecode st stm) = decode_cond (pc,cpsr,st) (translate_assignment stm)`,
     SIMP_TAC std_ss [FORALL_DSTATE] THEN
     Cases_on `stm` THEN
     RW_TAC list_ss [translate_assignment, decode_cond_thm, decode_op_thm, write_thm,  mdecode]
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

val translate = Define `
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
(*      Operational Semantics of programs in intermedia language                   *)
(*---------------------------------------------------------------------------------*)

val run_ir = Define `
     (run_ir (BLK (stm::stmL)) st =
          run_ir (BLK stmL) (mdecode st stm)) /\
     (run_ir (BLK []) st =
          st) /\

     (run_ir (SC S1 S2) st = 
          run_ir S2 (run_ir S1 st)) /\

     (run_ir (CJ cond Strue Sfalse) st = 
          if eval_cond cond st then 
              run_ir Strue st
          else
              run_ir Sfalse st) /\

     (run_ir (TR cond Sbody) st =
         WHILE (\s.eval_cond cond s) (run_ir Sbody) st)
    `;

(*---------------------------------------------------------------------------------*)
(*      Stack Behaviors                                                            *)
(*---------------------------------------------------------------------------------*)


(*--------------------------------------------------------------------------------------------*)
(*      Sanity and Correctness of the translation from intermediate language to flat code     *)
(*--------------------------------------------------------------------------------------------*)

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
    RW_TAC list_ss [FORALL_DSTATE, well_formed, terminated, stopAt_def, status_independent] THENL [
        Cases_on `stm` THEN
            (fn g => 
               (SIMP_TAC list_ss [closed, Once RUNTO_ADVANCE, UPLOAD_LEM_2, TRANSLATE_ASSIGMENT_CORRECT_2, SUC_ONE_ADD] THEN
                RW_TAC set_ss [Once RUNTO_ADVANCE]) g
            ),
        Cases_on `stm` THEN
            Q.EXISTS_TAC `SUC 0` THEN
            `?s0 pcS0. s = (s0,pcS0)` by METIS_TAC [ABS_PAIR_THM] THEN
            RW_TAC arith_ss [FUNPOW, UPLOAD_LEM_2, step_def, TRANSLATE_ASSIGMENT_CORRECT_2, SUC_ONE_ADD],
        Cases_on `stm` THEN
            (fn g => 
               (SIMP_TAC list_ss [get_st, Once RUNTO_ADVANCE, SIMP_RULE std_ss [] (Q.SPEC `(pos0,cpsr0,regs,mem):STATE` 
			  (INST_TYPE [alpha |-> Type `:word32 # (num |-> word32) # (num |-> word32)`] UPLOAD_LEM_2)), 
                         TRANSLATE_ASSIGMENT_CORRECT_2, SUC_ONE_ADD] THEN
                RW_TAC std_ss [Once RUNTO_ADVANCE] THEN
                SIMP_TAC list_ss [get_st, Once RUNTO_ADVANCE, SIMP_RULE std_ss [] (Q.SPEC `(pos1,cpsr1,regs,mem):STATE` 
			  (INST_TYPE [alpha |-> Type `:word32 # (num |-> word32) # (num |-> word32)`] UPLOAD_LEM_2)), 
                         TRANSLATE_ASSIGMENT_CORRECT_2, SUC_ONE_ADD] THEN
                RW_TAC std_ss [Once RUNTO_ADVANCE]) g
            )
    ]
  );


val BLOCK_IS_WELL_FORMED = Q.store_thm (
   "BLOCK_IS_WELL_FORMED",
   `!stmL. well_formed (translate (BLK stmL))`,

    Induct_on `stmL` THENL [
        RW_TAC list_ss [well_formed, translate, closed, terminated, status_independent, stopAt_def] THENL [
            RW_TAC set_ss [Once RUNTO_ADVANCE],
            Q.EXISTS_TAC `0` THEN RW_TAC std_ss [FUNPOW],
            RW_TAC arith_ss [Once RUNTO_ADVANCE, get_st] THEN RW_TAC arith_ss [Once RUNTO_ADVANCE]
        ],
        GEN_TAC THEN `!h tl. h :: tl = [h:INST] ++ tl` by RW_TAC list_ss [] THEN
        METIS_TAC [translate, mk_SC, SC_IS_WELL_FORMED, STATEMENT_IS_WELL_FORMED]
    ]
);

