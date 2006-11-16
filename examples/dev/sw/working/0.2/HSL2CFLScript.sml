
(*
quietdec := true;

app load ["arithmeticTheory", "wordsTheory", "wordsLib", "pairTheory", "listTheory", "whileTheory", "finite_mapTheory",
          "pred_setSimps", "pred_setTheory", "preARMTheory", "bigInstTheory", "CFLTheory", "HSLTheory", "simplifier"];

open HolKernel Parse boolLib bossLib numLib arithmeticTheory wordsTheory wordsLib pairTheory listTheory whileTheory
       pred_setSimps pred_setTheory finite_mapTheory preARMTheory bigInstTheory CFLTheory HSLTheory simplifier;

quietdec := false;
*)

open HolKernel Parse boolLib bossLib numLib arithmeticTheory wordsTheory wordsLib simplifier
     pairTheory listTheory whileTheory pred_setSimps pred_setTheory finite_mapTheory preARMTheory 
     bigInstTheory CFLTheory HSLTheory;

(*---------------------------------------------------------------------------------*)

val _ = new_theory "HSL2CFL";

(*---------------------------------------------------------------------------------*)
(*      Translation from HSL to CFL                                                *)
(*---------------------------------------------------------------------------------*)

val conv_roc_def = Define `
  (conv_roc (Rg r) = MR (conv_reg r)) /\
  (conv_roc (Cn v) = MC v)
  `;

val toLocn_def = Define `
   toLocn i = (fp, NEG (12 + i))`;

val translate_assgn_def = Define `
    (translate_assgn (TLDR dst_reg src_mem) = MLDR (conv_reg dst_reg) (toLocn src_mem)) /\
    (translate_assgn (TSTR dst_mem src_reg) = MSTR (toLocn dst_mem) (conv_reg src_reg)) /\
    (translate_assgn (TMOV dst src) = MMOV (conv_reg dst) (conv_roc src)) /\

    (translate_assgn (TADD dst (Rg r) src) = MADD (conv_reg dst) (conv_reg r) (conv_roc src)) /\
    (translate_assgn (TADD dst (Cn v) (Rg r)) = MADD (conv_reg dst) (conv_reg r) (MC v)) /\
    (translate_assgn (TADD dst (Cn v1) (Cn v2)) = MMOV (conv_reg dst) (MC (v1+v2))) /\
    (translate_assgn (TSUB dst (Rg r) src) = MSUB (conv_reg dst) (conv_reg r) (conv_roc src)) /\
    (translate_assgn (TSUB dst (Cn v) (Rg r)) = MRSB (conv_reg dst) (conv_reg r) (MC v)) /\
    (translate_assgn (TSUB dst (Cn v1) (Cn v2)) = MMOV (conv_reg dst) (MC (v1-v2))) /\
    (translate_assgn (TRSB dst (Rg r) src) = MRSB (conv_reg dst) (conv_reg r) (conv_roc src)) /\
    (translate_assgn (TRSB dst (Cn v) (Rg r)) = MSUB (conv_reg dst) (conv_reg r) (MC v)) /\
    (translate_assgn (TRSB dst (Cn v1) (Cn v2)) = MMOV (conv_reg dst) (MC (v2-v1))) /\
    (translate_assgn (TMUL dst (Rg r) src) = MMUL (conv_reg dst) (conv_reg r) (conv_roc src)) /\
    (translate_assgn (TMUL dst (Cn v) (Rg r)) = MMUL (conv_reg dst) (conv_reg r) (MC v)) /\
    (translate_assgn (TMUL dst (Cn v1) (Cn v2)) = MMOV (conv_reg dst) (MC (v1*v2))) /\
    (translate_assgn (TAND dst (Rg r) src) = MAND (conv_reg dst) (conv_reg r) (conv_roc src)) /\
    (translate_assgn (TAND dst (Cn v) (Rg r)) = MAND (conv_reg dst) (conv_reg r) (MC v)) /\
    (translate_assgn (TAND dst (Cn v1) (Cn v2)) = MMOV (conv_reg dst) (MC (v1 && v2))) /\
    (translate_assgn (TORR dst (Rg r) src) = MORR (conv_reg dst) (conv_reg r) (conv_roc src)) /\
    (translate_assgn (TORR dst (Cn v) (Rg r)) = MORR (conv_reg dst) (conv_reg r) (MC v)) /\
    (translate_assgn (TORR dst (Cn v1) (Cn v2)) = MMOV (conv_reg dst) (MC (v1 !! v2))) /\
    (translate_assgn (TEOR dst (Rg r) src) = MEOR (conv_reg dst) (conv_reg r) (conv_roc src)) /\
    (translate_assgn (TEOR dst (Cn v) (Rg r)) = MEOR (conv_reg dst) (conv_reg r) (MC v)) /\
    (translate_assgn (TEOR dst (Cn v1) (Cn v2)) = MMOV (conv_reg dst) (MC (v1 ?? v2))) /\

    (translate_assgn (TLSL dst (Rg r) src2_num) = MLSL (conv_reg dst) (conv_reg r) src2_num) /\
    (translate_assgn (TLSL dst (Cn v) src2_num) = MMOV (conv_reg dst) (MC (v << w2n src2_num))) /\
    (translate_assgn (TLSR dst (Rg r) src2_num) = MLSR (conv_reg dst) (conv_reg r) src2_num) /\
    (translate_assgn (TLSR dst (Cn v) src2_num) = MMOV (conv_reg dst) (MC (v >>> w2n src2_num))) /\
    (translate_assgn (TASR dst (Rg r) src2_num) = MASR (conv_reg dst) (conv_reg r) src2_num) /\
    (translate_assgn (TASR dst (Cn v) src2_num) = MMOV (conv_reg dst) (MC (v >> w2n src2_num))) /\
    (translate_assgn (TROR dst (Rg r) src2_num) = MROR (conv_reg dst) (conv_reg r) src2_num) /\
    (translate_assgn (TROR dst (Cn v) src2_num) = MMOV (conv_reg dst) (MC (v #>> w2n src2_num)))
    `;

val translate_TCND_def = Define `
  translate_TCND (r, c, e) =
    (conv_reg r, c, conv_roc e)`;

val translate_hsl_def = Define `
    (translate_hsl (Blk stmL) = BLK (MAP translate_assgn stmL)) /\
    (translate_hsl (Sc S1 S2) =  
         SC (translate_hsl S1) (translate_hsl S2)) /\
    (translate_hsl (Cj cond Strue Sfalse) =
         CJ (translate_TCND cond) (translate_hsl Strue) (translate_hsl Sfalse)) /\
    (translate_hsl (Tr cond Sbody) =
         TR (translate_TCND cond) (translate_hsl Sbody))`;

(*---------------------------------------------------------------------------------*)
(*      Data registers are separate from pointer registers                         *)
(*---------------------------------------------------------------------------------*)

val data_reg_lem_1 = Q.store_thm (
    "data_reg_lem_1",
    `!r. index_of_reg (conv_reg r) = data_reg_index r`,
    Cases_on `r` THEN

    RW_TAC std_ss [data_reg_index_def, conv_reg_def, index_of_reg_def, from_reg_index_def, index_of_reg_def]
  );

val data_reg_lem_2 = Q.store_thm (
    "data_reg_lem_2",
    `!r r''. (data_reg_index r = data_reg_index r'') = (r = r'')`,
    Cases_on `r` THEN Cases_on `r''` THEN
    RW_TAC std_ss [data_reg_index_def]
  );

val data_reg_lem_3 = Q.store_thm (
    "data_reg_lem_3",
    `!r. (data_reg_index r < 9) /\ ~(data_reg_index r = 10) /\ ~(data_reg_index r = 11) /\
        ~(data_reg_index r = 12) /\ ~(data_reg_index r = 13) /\ ~(data_reg_index r = 14)`,
    Cases_on `r` THEN
    RW_TAC arith_ss [data_reg_index_def]
  );


val locate_ge_lem_3 = Q.store_thm (
    "locate_ge_lem_3",
    `!x k. locate_ge x (12 + k) ==>
      !i j. ~(i = j) /\ i < k /\ j < k ==>
            ~(w2n x - (12 + i) = w2n x - (12 + j))`,
    RW_TAC arith_ss [locate_ge_def]
   );

(*---------------------------------------------------------------------------------*)
(*      Decode assignment statement                                                *)
(*---------------------------------------------------------------------------------*)

val correspond_def = Define `
    correspond (rg,sk) st m =
      (!r. rg ' r = read st (REG (data_reg_index r))) /\
      (!i. i < m ==> (sk ' i = read st (MEM (toLocn i))))
    `;

(*---------------------------------------------------------------------------------*)
(*      Validation on the translation of single instructions                       *)
(*---------------------------------------------------------------------------------*)

val LDR_CORRESPOND_LEM = Q.store_thm (
  "LDR_CORRESPOND_LEM",
  `!rg sk st T' T0 m. 
       valid_assgn (TLDR T' T0) m /\ correspond (rg,sk) st m ==>
       correspond (tdecode (rg,sk) (TLDR T' T0)) (mdecode st (translate_assgn (TLDR T' T0))) m`,

      SIMP_TAC std_ss [FORALL_DSTATE] THEN
      FULL_SIMP_TAC std_ss [translate_assgn_def, toLocn_def, valid_assgn_def, within_bound_def] THEN
      RW_TAC finmap_ss [correspond_def, fp_def, tdecode_def, twrite_def, tread_def, mdecode_def, toREG_def, 
            toMEM_def, write_thm, toEXP_def, toEXP_def, read_thm, toLocn_def, data_reg_lem_1, data_reg_lem_2] THEN
      METIS_TAC [data_reg_lem_3]
);

val STR_CORRESPOND_LEM = Q.store_thm (
  "STR_CORRESPOND_LEM",
  `!rg sk st T' T0 m. 
         valid_assgn (TSTR T' T0) m /\ locate_ge (read st FP) (12 + m) /\
       correspond (rg,sk) st m ==>
       correspond (tdecode (rg,sk) (TSTR T' T0)) (mdecode st (translate_assgn (TSTR T' T0))) m`,

      SIMP_TAC std_ss [FORALL_DSTATE] THEN
      RW_TAC std_ss [translate_assgn_def, toLocn_def, valid_assgn_def, within_bound_def] THEN
      FULL_SIMP_TAC finmap_ss [correspond_def, FP_def, fp_def, tdecode_def, twrite_def, tread_def, mdecode_def, 
        toREG_def, toMEM_def, write_thm, toEXP_def, toEXP_def, read_thm, toLocn_def, data_reg_lem_1] THEN
      RW_TAC std_ss [] THEN
      METIS_TAC [locate_ge_lem_3]
);

val ASSGN_CORRESPOND = Q.store_thm (
  "ASSGN_CORRESPOND",
  `!rg sk st stm m. 
     valid_assgn stm m /\ locate_ge (read st FP) (12 + m) /\
       correspond (rg,sk) st m ==>
       correspond (tdecode (rg,sk) stm) (mdecode st (translate_assgn stm)) m`,

   let val tac1 =  
	 FULL_SIMP_TAC finmap_ss [correspond_def, translate_assgn_def, tdecode_def, twrite_def, tread_def, mdecode_def, 
            toREG_def, toMEM_def, write_thm, toEXP_def, conv_roc_def, toEXP_def, read_thm, roc_2_exp_def, 
            data_reg_lem_1, data_reg_lem_2, toLocn_def] THEN
         RW_TAC std_ss [data_reg_lem_3, fp_def] THEN
         RW_TAC std_ss [WORD_ADD_COMM, WORD_MULT_COMM, WORD_AND_COMM, WORD_OR_COMM, WORD_XOR_COMM]
   in

   SIMP_TAC std_ss [FORALL_DSTATE] THEN
   REPEAT STRIP_TAC THEN
   Cases_on `stm` THENL [                       
       METIS_TAC [LDR_CORRESPOND_LEM],                 (* LDR *)
       METIS_TAC [STR_CORRESPOND_LEM],                 (* STR *) 
       Cases_on `T0` THEN tac1,                        (* MOV *) 
       Cases_on `T0` THEN Cases_on `T1` THEN tac1,     (* ADD *)
       Cases_on `T0` THEN Cases_on `T1` THEN tac1,     (* SUB *)
       Cases_on `T0` THEN Cases_on `T1` THEN tac1,     (* RSB *)
       Cases_on `T0` THEN Cases_on `T1` THEN tac1,     (* MUL *)
       Cases_on `T0` THEN Cases_on `T1` THEN tac1,     (* AND *)
       Cases_on `T0` THEN Cases_on `T1` THEN tac1,     (* ORR *)
       Cases_on `T0` THEN Cases_on `T1` THEN tac1,     (* EOR *)
       Cases_on `T0` THEN tac1,                        (* LSL *)
       Cases_on `T0` THEN tac1,                        (* LSR *)
       Cases_on `T0` THEN tac1,                        (* ASR *)
       Cases_on `T0` THEN tac1                         (* ROR *)
  ]
  end
 );

(*---------------------------------------------------------------------------------*)
(*      All heap and stack operations in each instruction should be within the     *)
(*        predefined domains                                                       *)
(*      The heap area and the stack area are separate                              *)
(*      Data registers include only r0-r8                                          *)
(*---------------------------------------------------------------------------------*)

val ASSGN_SAME_BASE_REGS = Q.store_thm (
  "ASSGN_SAME_BASE_REGS",
  `!stm st. let st' = mdecode st (translate_assgn stm) in
        (read st FP = read st' FP) /\
        (read st IP = read st' IP) /\
        (read st SP = read st' SP) /\
        (read st LR = read st' LR) `,

   let val tac1 = SIMP_TAC std_ss [FORALL_DSTATE, translate_assgn_def, mdecode_def, LET_THM] THEN 
                  RW_TAC finmap_ss [valid_assgn_def, valid_TEXP_def, toREG_def, index_of_reg_def, read_thm, write_thm, 
                                    toLocn_def, toMEM_def, IP_def, FP_def, SP_def, LR_def, data_reg_lem_1,data_reg_lem_3]
   in
   Cases_on `stm` THENL [
      Cases_on `T'` THEN tac1,                                         (* LDR *)
      Cases_on `T'` THEN tac1,                                         (* STR *)
      Cases_on `T'` THEN tac1,                                         (* MOV *)
      Cases_on `T'` THEN Cases_on `T0` THEN Cases_on `T1` THEN tac1,   (* ADD *)
      Cases_on `T'` THEN Cases_on `T0` THEN Cases_on `T1` THEN tac1,   (* SUB *)
      Cases_on `T'` THEN Cases_on `T0` THEN Cases_on `T1` THEN tac1,   (* RSB *)
      Cases_on `T'` THEN Cases_on `T0` THEN Cases_on `T1` THEN tac1,   (* MUL *)
      Cases_on `T'` THEN Cases_on `T0` THEN Cases_on `T1` THEN tac1,   (* AND *)
      Cases_on `T'` THEN Cases_on `T0` THEN Cases_on `T1` THEN tac1,   (* ORR *)
      Cases_on `T'` THEN Cases_on `T0` THEN Cases_on `T1` THEN tac1,   (* EOR *)
      Cases_on `T'` THEN Cases_on `T0` THEN tac1,                      (* LSL *)
      Cases_on `T'` THEN Cases_on `T0` THEN tac1,                      (* LSR *)
      Cases_on `T'` THEN Cases_on `T0` THEN tac1,                      (* ASR *)
      Cases_on `T'` THEN Cases_on `T0` THEN tac1                       (* ROR *)
  ]
  end
 );


(*---------------------------------------------------------------------------------*)
(*      Correspondence for basic blocks                                            *)
(*---------------------------------------------------------------------------------*)

val  BLK_CORRESPONDENCE = Q.store_thm (
  "BLK_CORRESPONDENCE",
  `!rg sk st stmL m. 
     valid_struct (Blk stmL) m /\ locate_ge (read st FP) (12 + m) /\ 
       correspond (rg,sk) st m ==>
       correspond (run_hsl (Blk stmL) (rg,sk)) (run_cfl (translate_hsl (Blk stmL)) st) m`,

   Induct_on `stmL` THENL [
     RW_TAC list_ss [correspond_def, run_hsl_def, translate_hsl_def, CFL_SEMANTICS_BLK],
     RW_TAC list_ss [valid_struct_def, run_hsl_def, translate_hsl_def, CFL_SEMANTICS_BLK] THEN
       `?rg' sk'. (rg',sk') = tdecode (rg,sk) h` by  METIS_TAC [ABS_PAIR_THM] THEN
       Q.PAT_ASSUM `!rg sk st m.x` (ASSUME_TAC o SIMP_RULE std_ss [valid_struct_def, translate_hsl_def] o
           Q.SPECL [`rg'`,`sk'`,`mdecode st (translate_assgn h)`, `m`]) THEN
       METIS_TAC [ASSGN_CORRESPOND, ASSGN_SAME_BASE_REGS, ADD_SYM]
     ]
  );

val same_base_regs_def = Define `
    same_base_regs S_hsl = 
       !st. let st' = run_cfl (translate_hsl S_hsl) st in
        (read st FP = read st' FP) /\
        (read st IP = read st' IP) /\
        (read st SP = read st' SP) /\
        (read st LR = read st' LR)`; 


val BLK_SAME_BASE_REGS = Q.store_thm (
  "BLK_SAME_BASE_REGS",
  `!stm. same_base_regs (Blk stmL)`,

  Induct_on `stmL` THENL [
    RW_TAC list_ss [same_base_regs_def, valid_struct_def, translate_hsl_def, CFL_SEMANTICS_BLK],
    FULL_SIMP_TAC list_ss [same_base_regs_def, valid_struct_def, translate_hsl_def, CFL_SEMANTICS_BLK] THEN
      RW_TAC std_ss [LET_THM] THEN
      METIS_TAC [ASSGN_SAME_BASE_REGS]
  ]
  );

(*---------------------------------------------------------------------------------*)
(*      Well formedness of HSL programs                                            *)
(*---------------------------------------------------------------------------------*)

val Well_Formed_def = Define `
    Well_Formed S_hsl = WELL_FORMED (translate_hsl S_hsl)`;

val WELL_FORMED_SC = Q.store_thm (
  "WELL_FORMED_SC",
  `!S1 S2. Well_Formed (Sc S1 S2) = Well_Formed S1 /\ Well_Formed S2`,
  RW_TAC std_ss [Well_Formed_def, translate_hsl_def, CFL_SC_IS_WELL_FORMED]
  );


(*---------------------------------------------------------------------------------*)
(*      Semantics of a HSL program is preserved when it is translated to CFL       *)
(*---------------------------------------------------------------------------------*)

(* HSL_STRUCTURE_induction *)

val sem_preserve_def = Define `
    sem_preserve S_hsl = 
     !s st m. correspond s st m ==> 
     correspond (run_hsl S_hsl s) (run_cfl (translate_hsl S_hsl) st) m`;

(*---------------------------------------------------------------------------------*)
(*      Correspondence of Sc structures                                            *)
(*---------------------------------------------------------------------------------*)

val  SC_SEM_PRESERVE = Q.store_thm (
  "SC_SEM_PRESERVE",
  `!S1 S2 m. 
     Well_Formed (Sc S1 S2) ==>
       sem_preserve S1 /\ sem_preserve S2 ==>
         sem_preserve (Sc S1 S2)`,

    RW_TAC std_ss [Well_Formed_def, WELL_FORMED_def, sem_preserve_def, translate_hsl_def, 
          run_hsl_def, SEMANTICS_OF_CFL]
  );

val SC_SAME_BASE_REGS = Q.store_thm (
  "SC_SAME_BASE_REGS",
  `!S1 S2. same_base_regs S1 /\ same_base_regs S2 /\ 
           Well_Formed S1 /\ Well_Formed S2 ==> 
           same_base_regs (Sc S1 S2)`,
  RW_TAC std_ss [Well_Formed_def, same_base_regs_def, run_hsl_def, translate_hsl_def, SEMANTICS_OF_CFL] THEN
  METIS_TAC []
  );

(*---------------------------------------------------------------------------------*)
(*      Correspondence of Cj structures                                            *)
(*---------------------------------------------------------------------------------*)

val  conv_reg_lem_1 = Q.store_thm (
  "conv_reg_lem_1",
  `!r. (toREG (conv_reg r) = REG (data_reg_index r))`,
  Cases_on `r` THEN
  RW_TAC std_ss [data_reg_index_def, conv_reg_thm, toREG_def, index_of_reg_def]
 );

val  EVAL_TCND_THM = Q.store_thm (
  "EVAL_TCND_THM",
  `!cond s st m. correspond s st m ==>
      (eval_TCND cond s = eval_il_cond (translate_TCND cond) st)`,

  SIMP_TAC std_ss [FORALL_TSTATE, FORALL_DSTATE] THEN
  RW_TAC std_ss [correspond_def] THEN
  Cases_on `cond` THEN Cases_on `r` THEN
  Cases_on `q'` THEN Cases_on `r'` THEN
  RW_TAC std_ss [eval_TCND_def, translate_TCND_def, eval_il_cond_def, tread_def, translate_condition_def, 
            ARMCompositionTheory.eval_cond_def, roc_2_exp_def, conv_roc_def, toEXP_def, conv_reg_lem_1, read_thm]
  );

val  CJ_SEM_PRESERVE = Q.store_thm (
  "CJ_SEM_PRESERVE",
  `!cond S1 S2. 
     Well_Formed (Cj cond S1 S2) ==>
       sem_preserve S1 /\ sem_preserve S2 ==>
         sem_preserve (Cj cond S1 S2)`,

    RW_TAC std_ss [Well_Formed_def, WELL_FORMED_def, sem_preserve_def, translate_hsl_def, 
          run_hsl_def, SEMANTICS_OF_CFL] THEN
    METIS_TAC [EVAL_TCND_THM]
  );

(*
val CJ_SAME_BASE_REGS = Q.store_thm (
  "CJ_SAME_BASE_REGS",
  `!cond S1 S2. same_base_regs S1 /\ same_base_regs S2 /\ 
           Well_Formed S1 /\ Well_Formed S2 ==> 
           same_base_regs (CJ cond S1 S2)`,
  RW_TAC std_ss [Well_Formed_def, same_base_regs_def, run_hsl_def, translate_hsl_def, SEMANTICS_OF_CFL] THEN
  METIS_TAC []
  );
*)

(*---------------------------------------------------------------------------------*)
(*      Correspondence of Tr structures                                            *)
(*---------------------------------------------------------------------------------*)

(*
val  TR_SEM_PRESERVE = Q.store_thm (
  "TR_SEM_PRESERVE",
  `!cond S_hsl. 
     Well_Formed (Tr cond S_hsl) /\ sem_preserve S_hsl ==>
         sem_preserve (Tr cond S_hsl)`,

    RW_TAC std_ss [Well_Formed_def, WELL_FORMED_def, sem_preserve_def, translate_hsl_def, 
          run_hsl_def, SEMANTICS_OF_CFL] THEN
    METIS_TAC [EVAL_TCND_THM]
  );

*)
(*---------------------------------------------------------------------------------*)
(*      Operations on different stacks                                             *)
(*---------------------------------------------------------------------------------*)

(*

val transfer_def = Define `
    (transfer s1 s0 [] [] = s1) /\
    (transfer s1 s0 (dst::dstL) (src::srcL) = 
       transfer (twrite s1 dst (tread s0 src)) s0 dstL srcL)`;

val empty_s_def = Define `
    empty_s = (FEMPTY,FEMPTY,FEMPTY)`;


val run_fc_def = Define `
    run_fc (caller_i,callee_i) ir (caller_o,callee_o) s = 
        let s1 = transfer empty_s s callee_i caller_i in
        let s2 = run_ir1 ir s1 in
        transfer s s2 caller_o callee_o`;


val translate_fc_def = Define `
    translate_fc (caller_i,callee_i) ir (caller_o,callee_o) (transfer_ins,translate_f,transfer_outs) = 
        SC (SC (transfer_ins (caller_i,callee_i)) 
                (translate_f ir))
           (transfer_outs (caller_o,callee_o))
           `;

val FC_2_SC = Q.store_thm (
    "FC_2_SC",
     `!ir1 ir2 ir3 st. WELL_FORMED ir1 /\ WELL_FORMED ir2 /\WELL_FORMED ir3 ==>
             (run_ir (SC (SC ir1 ir2) ir3) st = run_ir ir3 (run_ir ir2 (run_ir ir1 st)))`,
     RW_TAC std_ss [] THEN
     `WELL_FORMED (SC ir1 ir2)` by METIS_TAC [IR_SC_IS_WELL_FORMED] THEN
      RW_TAC std_ss [SEMANTICS_OF_IR]
   );

val FC_BASIC_LEM = Q.store_thm (
    "FC_BASIC_LEM",
    `!hp_f sk_f hp_f' sk_f' s st. 
        WELL_FORMED (transfer_outs (caller_o,callee_o)) /\
        WELL_FORMED (translate_f ir) /\ 
        WELL_FORMED (transfer_ins (caller_i,callee_i)) /\
        data_correspond s st (hp_f,sk_f) /\
        (!s st s'. data_correspond s st (hp_f,sk_f) ==>
                   data_correspond (transfer s' s callee_i caller_i) (run_ir (transfer_ins (caller_i,callee_i)) st) (hp_f',sk_f')) /\
        (!s st. data_correspond s st (hp_f',sk_f') ==>
                   data_correspond (run_ir1 ir s) (run_ir (translate_f ir) st) (hp_f',sk_f')) /\
        (!s st s'. data_correspond s st (hp_f',sk_f') ==>
                   data_correspond (transfer s' s caller_o callee_o)  (run_ir (transfer_outs (caller_o,callee_o)) st) (hp_f,sk_f))
        ==> 
         data_correspond (run_fc (caller_i,callee_i) ir (caller_o,callee_o) s)
            (run_ir (translate_fc (caller_i,callee_i) ir (caller_o,callee_o) (transfer_ins,translate_f,transfer_outs)) st) (hp_f,sk_f)`,

     RW_TAC std_ss [run_fc_def, translate_fc_def, FC_2_SC, LET_THM]
    );     

*)

(*---------------------------------------------------------------------------------*)

val _ = export_theory();
