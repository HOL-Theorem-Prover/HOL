(* interactive use:

quietdec := true;
loadPath := (concat Globals.HOLDIR "/examples/dev/sw") :: !loadPath;

app load ["pred_setSimps", "pred_setTheory", "arithmeticTheory", "wordsTheory", "wordsLib", "pairTheory",
"listTheory", "whileTheory", "finite_mapTheory", "preARMTheory", "ARMCompositionTheory"];

quietdec := false;
*)


open HolKernel Parse boolLib bossLib numLib pred_setSimps pred_setTheory arithmeticTheory wordsTheory wordsLib
pairTheory listTheory whileTheory finite_mapTheory preARMTheory ARMCompositionTheory;

(*---------------------------------------------------------------------------------*)
(* Control Flow Level (CFL)                                                        *)
(* Prefixed by "M"                                                                 *)
(*---------------------------------------------------------------------------------*)

(*---------------------------------------------------------------------------------*)
(*  CFL explicitly lays outs the heap and stacks for function calls. It            *)
(*  specifies machine registers and memory locations for the variables in          *)
(*  HSL. A function call in HSL is implemented by dividing the processing          *)
(*  into three phases --- pre-call processing, function body execution and         *)
(*  post-call processing.  Pointer register hp (heap pointer, i.e. r10), fp        *)
(*  (frame pointer), ip (intra-procedure register pointer), sp (stack pointer)     *)
(*  and lr (link register) are used to control the layout of the heap and stack    *)
(*  frames for functions.  CFL works over machine registers and memory,            *)
(*  thus a (one-to-one) mapping from HSL variables to them is required.            *)
(*                                                                                 *)
(*  The translation from CFL to the object code simply performs the                *)
(*  linearization of control-flow structures.                                      *)
(*---------------------------------------------------------------------------------*)

val _ = new_theory "CFL";

val set_ss = std_ss ++ SET_SPEC_ss ++ PRED_SET_ss;

(*---------------------------------------------------------------------------------*)
(*      Registers and memory data in CFL                                           *)
(*      the pc is invisible in this level                                          *)
(*---------------------------------------------------------------------------------*)

val _ = Hol_datatype `
    MREG = R0 | R1 | R2 | R3 | R4 | R5 | R6 | R7 | R8 | R9 | R10 | R11 | R12 | R13 | R14`;

val _ = type_abbrev("MMEM", Type`:num # OFFSET`);      (* memory in ir *)

val _ = Hol_datatype `
    MEXP = MR of MREG          (* registers *)
         | MC of word32        (* constants *)
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
       preARM$MEM (base,offset)`;        (* [base + offset] *)

val toEXP_def = Define `
    (toEXP (MR r) = toREG r) /\
    (toEXP (MC c) = WCONST c)`;

(*---------------------------------------------------------------------------------*)
(*      Registers reserved for special purpose                                     *)
(*---------------------------------------------------------------------------------*)

val tp_def = Define `
    tp = 9`;

val gp_def = Define `
    gp = 10`;

val fp_def = Define `
    fp = 11`;

val ip_def = Define `
    ip = 12`;

val sp_def = Define `
    sp = 13`;

val lr_def = Define `
    lr = 14`;

(*---------------------------------------------------------------------------------*)
(*      Syntax of CFL                                                              *)
(*---------------------------------------------------------------------------------*)

val _ = Hol_datatype `
    DOPER =
     MLDR of MREG => MMEM |
     MSTR of MMEM => MREG |
     MMOV of MREG => MEXP |
     MADD of MREG => MREG => MEXP |
     MSUB of MREG => MREG => MEXP |
     MRSB of MREG => MREG => MEXP |
     MMUL of MREG => MREG => MEXP |
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
(*      Stack Operations (push and pop)                                            *)
(*      Complying with the ARM standard, the stack goes downwards                  *)
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
(*      Semantics of the CFL instructions (not structures)                         *)
(*      And their translation to ARM instructions                                  *)
(*      The semantics and translation of conditions in CJ and TR are also given    *)
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
  (mdecode st (MMUL dst src1 src2) =
      write st (toREG dst) (read st (toREG src1) * read st (toEXP src2))) /\
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
    (translate_assignment (MMUL dst src1 src2) = ((MUL,NONE,F),SOME (toREG dst), [toREG src1; toEXP src2], NONE):INST) /\
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
(*      An interpreter that specifies the translation of control flow structures   *)
(*      Other interpreters for the same synatx would be given                      *)
(*      No semantics is given here                                                 *)
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
(*      Derivation of the semantics of CFL by investigating the interpreter        *)
(*      The data state excluding pc and pcsr is observed                           *)
(*---------------------------------------------------------------------------------*)

val run_arm_def = Define `
      run_arm arm ((pc,cpsr,st),pcS) = runTo (upload arm (\i.ARB) pc) (pc+LENGTH arm) ((pc,cpsr,st),pcS)`;

val run_cfl_def = Define `
      run_cfl cfl st = get_st (run_arm (translate cfl) ((0,0w,st),{}))`;


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
    ``!S_cfl. WELL_FORMED S_cfl = (WELL_FORMED_SUB S_cfl /\ well_formed (translate S_cfl))``,

    Cases_on `S_cfl` THEN
    REWRITE_TAC [WELL_FORMED_def, WELL_FORMED_SUB_def] THEN
    PROVE_TAC[]);

(*---------------------------------------------------------------------------------*)
(*      Hoare Rules for CFL                                                        *)
(*---------------------------------------------------------------------------------*)

val HOARE_SC_CFL = Q.store_thm (
   "HOARE_SC_CFL",
   `!S1 S2 P Q R T.
        WELL_FORMED S1 /\ WELL_FORMED S2 /\
           (!st. P st ==> Q (run_cfl S1 st)) /\
           (!st. R st ==> T (run_cfl S2 st)) /\ (!st. Q st ==> R st) ==>
             !st. P st ==>
                  T (run_cfl (SC S1 S2) st)`,
   RW_TAC std_ss [WELL_FORMED_SUB_thm, run_cfl_def, translate_def, run_arm_def, eval_fl_def] THEN
   IMP_RES_TAC (SIMP_RULE std_ss [eval_fl_def, uploadCode_def]  HOARE_SC_FLAT)
  );

val HOARE_CJ_CFL = Q.store_thm (
   "HOARE_CJ_CFL",
   `!cond S_t S_f P Q R.
       WELL_FORMED S_t /\ WELL_FORMED S_f /\
           (!st. P st ==> Q (run_cfl S_t st)) /\
           (!st. P st ==> R (run_cfl S_f st)) ==>
             !st. P st ==>
                if eval_il_cond cond st then Q (run_cfl (CJ cond S_t S_f) st)
                    else R (run_cfl (CJ cond S_t S_f) st)`,
   RW_TAC std_ss [WELL_FORMED_SUB_thm, run_cfl_def, translate_def, run_arm_def, eval_fl_def, eval_il_cond_def] THEN
   IMP_RES_TAC (SIMP_RULE std_ss [eval_fl_def, uploadCode_def] HOARE_CJ_FLAT) THEN
   METIS_TAC []
  );

val HOARE_TR_CFL = Q.store_thm (
   "HOARE_TR_CFL",
   `!cond S_cfl P.
       WELL_FORMED S_cfl /\  WF_TR (translate_condition cond, translate S_cfl) /\
         (!st. P st ==> P (run_cfl S_cfl st)) ==>
            !st. P st ==> P (run_cfl (TR cond S_cfl) st) /\
                 eval_il_cond cond (run_cfl (TR cond S_cfl) st)`,
   RW_TAC std_ss [WELL_FORMED_SUB_thm, run_cfl_def, translate_def, run_arm_def, eval_fl_def, eval_il_cond_def] THEN
   METIS_TAC [SIMP_RULE std_ss [eval_fl_def, uploadCode_def] HOARE_TR_FLAT]
  );

(*---------------------------------------------------------------------------------*)
(*      Well-formedness of CFL programs                                            *)
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

val CFL_SC_IS_WELL_FORMED = Q.store_thm (
   "CFL_SC_IS_WELL_FORMED",
   `!S1 S2. WELL_FORMED S1 /\ WELL_FORMED S2 = WELL_FORMED (SC S1 S2)`,
    RW_TAC std_ss [WELL_FORMED_SUB_thm, WELL_FORMED_SUB_def, translate_def] THEN
    PROVE_TAC [SC_IS_WELL_FORMED]
   );

val CFL_CJ_IS_WELL_FORMED = Q.store_thm (
   "CFL_CJ_IS_WELL_FORMED",
   `!cond S_t S_f. WELL_FORMED S_t /\ WELL_FORMED S_f =
        WELL_FORMED (CJ cond S_t S_f)`,
    RW_TAC std_ss [WELL_FORMED_SUB_thm, WELL_FORMED_SUB_def, translate_def] THEN
    PROVE_TAC [CJ_IS_WELL_FORMED]
   );

val CFL_TR_IS_WELL_FORMED = Q.store_thm (
   "CFL_TR_IS_WELL_FORMED",
   `!S_cfl cond. WELL_FORMED S_cfl /\ WF_TR (translate_condition cond, translate S_cfl) =
        WELL_FORMED (TR cond S_cfl)`,
    RW_TAC std_ss [WELL_FORMED_SUB_thm, WELL_FORMED_SUB_def, translate_def] THEN
    PROVE_TAC [TR_IS_WELL_FORMED]
   );

val WELL_FORMED_thm = store_thm ("WELL_FORMED_thm",
    ``(WELL_FORMED (BLK stmL) = T) /\
      (WELL_FORMED (SC S1 S2) = WELL_FORMED S1 /\ WELL_FORMED S2) /\
      (WELL_FORMED (CJ cond S1 S2) = WELL_FORMED S1 /\ WELL_FORMED S2) /\
      (WELL_FORMED (TR cond S_body) = WELL_FORMED S_body /\ WF_TR (translate_condition cond, translate S_body))``,

      SIMP_TAC std_ss [BLOCK_IS_WELL_FORMED, CFL_SC_IS_WELL_FORMED, CFL_CJ_IS_WELL_FORMED, CFL_TR_IS_WELL_FORMED]);


(*---------------------------------------------------------------------------------*)
(*      Semantics of CFL derived from the interpreter                              *)
(*      Other interpreters will result in different semantics                      *)
(*---------------------------------------------------------------------------------*)

val CFL_SEMANTICS_SC = Q.store_thm (
   "CFL_SEMANTICS_SC",
   `WELL_FORMED S1 /\ WELL_FORMED S2 ==>
     (run_cfl (SC S1 S2) st =
       run_cfl S2 (run_cfl S1 st))`,
    METIS_TAC [SIMP_RULE std_ss [] (Q.SPECL [`S1`,`S2`, `\st'. st' = st`, `\st'. st' = run_cfl S1 st`,
               `\st'. st' = run_cfl S1 st`, `\st'. st' =  run_cfl S2 (run_cfl S1 st)`] HOARE_SC_CFL)]
   );


val CFL_SEMANTICS_BLK = Q.store_thm (
   "CFL_SEMANTICS_BLK",
    `(run_cfl (BLK (stm::stmL)) st =
          run_cfl (BLK stmL) (mdecode st stm)) /\
     (run_cfl (BLK []) st = st)`,

    REPEAT STRIP_TAC THENL [
       RW_TAC list_ss [run_cfl_def, translate_def] THEN
           `translate_assignment stm::translate (BLK stmL) = translate (SC (BLK [stm]) (BLK stmL))` by RW_TAC list_ss [translate_def,mk_SC_def] THEN
           RW_TAC std_ss [GSYM run_cfl_def] THEN
           `run_cfl (BLK [stm]) st = mdecode st stm` by (
               RW_TAC list_ss [run_cfl_def, run_arm_def, translate_def, Once RUNTO_ADVANCE] THEN
               RW_TAC list_ss [GSYM uploadCode_def, UPLOADCODE_LEM] THEN
               RW_TAC list_ss [GSYM TRANSLATE_ASSIGMENT_CORRECT, get_st_def, Once RUNTO_ADVANCE]
           ) THEN
           `well_formed [translate_assignment stm] /\ well_formed (translate (BLK stmL))` by
               METIS_TAC [WELL_FORMED_def, BLOCK_IS_WELL_FORMED, STATEMENT_IS_WELL_FORMED] THEN
           FULL_SIMP_TAC list_ss [WELL_FORMED_def, CFL_SEMANTICS_SC, translate_def],
       RW_TAC list_ss [run_cfl_def, run_arm_def, translate_def, Once RUNTO_ADVANCE, get_st_def]
   ]
  );

val CFL_SEMANTICS_CJ = Q.store_thm (
   "CFL_SEMANTICS_CJ",
   ` WELL_FORMED S_t /\ WELL_FORMED S_f ==>
     (run_cfl (CJ cond S_t S_f) st =
          if eval_il_cond cond st then run_cfl S_t st
          else run_cfl S_f st)`,
   RW_TAC std_ss [] THEN
   METIS_TAC [SIMP_RULE std_ss [] (Q.SPECL [`cond`, `S_t`, `S_f`, `\st'. st' = st`, `\st'. st' = run_cfl S_t st`,
                 `\st'. st' = run_cfl S_f st`] HOARE_CJ_CFL)]
  );


val CFL_SEMANTICS_TR = Q.store_thm (
   "CFL_SEMANTICS_TR",
     `WELL_FORMED S_body /\ WF_TR (translate_condition cond,translate S_body) ==>
      (run_cfl (TR cond S_body) st =
         WHILE (\st'.~eval_il_cond cond st') (run_cfl S_body) st)`,

    RW_TAC std_ss [WELL_FORMED_SUB_thm, run_cfl_def, run_arm_def, translate_def, eval_il_cond_def] THEN
    Q.ABBREV_TAC `arm = translate S_body` THEN
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
            `run_cfl S_body st = SND (SND (FST (runTo (upload (translate S_body) (\i. ARB) 0) (LENGTH (translate S_body)) ((0,0w,st),{}))))` by RW_TAC arith_ss [
                   get_st_def, run_cfl_def, run_arm_def] THEN
            METIS_TAC [SND,FST,get_st_def,FUNPOW_DSTATE, ABS_PAIR_THM]
      ]
  );


val SEMANTICS_OF_CFL = Q.store_thm (
   "SEMANTICS_OF_CFL",
   ` WELL_FORMED S1 /\ WELL_FORMED S2 ==>
     (run_cfl (BLK (stm::stmL)) st =
          run_cfl (BLK stmL) (mdecode st stm)) /\
     (run_cfl (BLK []) st = st) /\
     (run_cfl (SC S1 S2) st = run_cfl S2 (run_cfl S1 st)) /\
     (run_cfl (CJ cond S1 S2) st =
           (if eval_il_cond cond st then run_cfl S1 st else run_cfl S2 st)) /\
     ( WF_TR (translate_condition cond,translate S1) ==>
       (run_cfl (TR cond S1) st =
           WHILE (\st'. ~eval_il_cond cond st') (run_cfl S1) st))`,
   RW_TAC std_ss [CFL_SEMANTICS_BLK, CFL_SEMANTICS_CJ, CFL_SEMANTICS_SC, CFL_SEMANTICS_TR]
  );


val _ = export_theory();
