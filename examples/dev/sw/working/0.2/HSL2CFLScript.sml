
(*
quietdec := true;

app load ["arithmeticTheory", "wordsTheory", "wordsLib", "pairTheory", "listTheory", "whileTheory", "finite_mapTheory",
          "pred_setSimps", "pred_setTheory", "preARMTheory", "ARMCompositionTheory", "bigInstTheory", "funCallTheory", 
          "CFLTheory", "HSLTheory", "simplifier"];

open HolKernel Parse boolLib bossLib numLib arithmeticTheory wordsTheory wordsLib pairTheory listTheory whileTheory
       pred_setSimps pred_setTheory finite_mapTheory preARMTheory bigInstTheory funCallTheory 
       CFLTheory HSLTheory simplifier;

quietdec := false;
*)

open HolKernel Parse boolLib bossLib numLib arithmeticTheory wordsTheory wordsLib pairTheory listTheory whileTheory
       pred_setSimps pred_setTheory finite_mapTheory preARMTheory bigInstTheory funCallTheory 
       CFLTheory HSLTheory simplifier;

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
         TR (translate_TCND cond) (translate_hsl Sbody)) /\ 
    (translate_hsl (Fc (caller_i, callee_i) S_body (caller_o, callee_o) (m1,m2)) =
         SC (SC (BLK (pre_call_2 (MAP conv_exp caller_i, MAP conv_exp callee_i) 
                    (MAX (LENGTH caller_i) (LENGTH caller_o) - (LENGTH caller_i)) m2)) 
                (translate_hsl S_body)) 
            (BLK (post_call (MAP conv_exp caller_o, MAP conv_exp callee_o) m1)))`;

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
      !i j. ~(i = j) /\ (i < k) /\ (j < k) ==>
            ~(w2n x - (12 + i) = w2n x - (12 + j))`,
    RW_TAC arith_ss [locate_ge_def]
   );

(*---------------------------------------------------------------------------------*)
(*      Decode assignment statement                                                *)
(*---------------------------------------------------------------------------------*)

val correspond_def = Define `
    correspond (rg,sk) st m =
      (!r. rg ' (data_reg_index r) = read st (REG (data_reg_index r))) /\
      (!i. (i < m) ==> (sk ' i = read st (MEM (toLocn i))))
    `;

val CORRESPOND_SAME_CONTENT = Q.store_thm (
   "CORRESPOND_SAME_CONTENT",
   `correspond = same_content`,
   SIMP_TAC std_ss [FUN_EQ_THM, FORALL_TSTATE] THEN
   REPEAT STRIP_TAC THEN EQ_TAC THEN
   RW_TAC std_ss [correspond_def, same_content_def] THEN
   FULL_SIMP_TAC std_ss [read_thm, data_reg_index_def, conv_exp_def, reade_def, toLocn_def]
  );

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

val ASSGN_STATUS_INTACT = Q.store_thm (
  "ASSGN_STATUS_INTACT",
  `!stm st. let st' = mdecode st (translate_assgn stm) in
        status_intact st' st`,

   let val tac1 = SIMP_TAC std_ss [FORALL_DSTATE, translate_assgn_def, mdecode_def, LET_THM] THEN 
                  RW_TAC finmap_ss [valid_assgn_def, valid_TEXP_def, toREG_def, index_of_reg_def, read_thm, write_thm, 
                    reade_def, toLocn_def, toMEM_def, IP_def, FP_def, SP_def, LR_def, data_reg_lem_1, data_reg_lem_3]
                  THEN FULL_SIMP_TAC arith_ss [fp_def]
   in
   SIMP_TAC std_ss [status_intact_def, same_fp_ip_sp_def] THEN
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
       `read (mdecode st (translate_assgn h)) FP = read st FP` by 
          METIS_TAC [SIMP_RULE std_ss [LET_THM, status_intact_def, same_fp_ip_sp_def] ASSGN_STATUS_INTACT, w2n_11] THEN
       METIS_TAC [ASSGN_CORRESPOND, ADD_SYM]
     ]
  );

val STATUS_INTACT_TRANS = Q.store_thm (
  "STATUS_INTACT_TRANS",
  `!a b c. status_intact a b /\ status_intact b c ==> status_intact a c`,
  RW_TAC list_ss [status_intact_def, same_fp_ip_sp_def]
  );

val BLK_STATUS_INTACT = Q.store_thm (
  "BLK_STATUS_INTACT",
  `!stmL st. let st' = run_cfl (translate_hsl (Blk stmL)) st in
        status_intact st' st`,

  Induct_on `stmL` THENL [
    RW_TAC list_ss [status_intact_def, same_fp_ip_sp_def, valid_struct_def, translate_hsl_def, CFL_SEMANTICS_BLK],
    FULL_SIMP_TAC list_ss [LET_THM, valid_struct_def, translate_hsl_def, CFL_SEMANTICS_BLK] THEN
      METIS_TAC [ASSGN_STATUS_INTACT, STATUS_INTACT_TRANS]
  ]
  );

(*---------------------------------------------------------------------------------*)
(*      Well formedness of HSL programs                                            *)
(*---------------------------------------------------------------------------------*)

val Well_Formed_def = Define `
    Well_Formed S_hsl = 
     WELL_FORMED (translate_hsl S_hsl)
  `;

val Well_Formed_Blk = Q.store_thm (
  "Well_Formed_Blk",
  `!stmL. Well_Formed (Blk stmL)`,
  RW_TAC std_ss [Well_Formed_def, translate_hsl_def, WELL_FORMED_thm]
  );

val Well_Formed_Sc = Q.store_thm (
  "Well_Formed_Sc",
  `!S1 S2. Well_Formed (Sc S1 S2) = Well_Formed S1 /\ Well_Formed S2`,
  RW_TAC std_ss [Well_Formed_def, translate_hsl_def, CFL_SC_IS_WELL_FORMED]
  );

(*---------------------------------------------------------------------------------*)
(*      Semantics of a HSL program is preserved when it is translated to CFL       *)
(*---------------------------------------------------------------------------------*)

val sem_spec_def = Define `
    sem_spec P S_hsl Q = 
     !s st m. P st /\ correspond s st m ==> 
       let st' = run_cfl (translate_hsl S_hsl) st in
         correspond (run_hsl S_hsl s) st' m /\ Q st'`;

(*---------------------------------------------------------------------------------*)
(*      Correspondence of Sc structures                                            *)
(*---------------------------------------------------------------------------------*)

val SC_SEM_SPEC = Q.store_thm (
  "SC_SEM_SPEC",
  `!S1 S2 m P Q R. 
     Well_Formed (Sc S1 S2) ==> 
       sem_spec P S1 Q /\ sem_spec Q S2 R ==>
         sem_spec P (Sc S1 S2) R`,

    RW_TAC std_ss [Well_Formed_def, WELL_FORMED_def, sem_spec_def, translate_hsl_def, LET_THM, 
          run_hsl_def, SEMANTICS_OF_CFL] THEN
    METIS_TAC []
  );

(*
val SC_STATUS_INTACT = Q.store_thm (
  "SC_STATUS_INTACT",
  `!S1 S2 P Q. 
    Well_Formed (Sc S1 S2) ==>
     (!st. P st ==> let st' = run_cfl (translate_hsl S1) st in
        status_intact st' st /\ Q st') /\
     (!st. Q st ==> let st' = run_cfl (translate_hsl S2) st in
        status_intact st' st) ==> 
     (!st. P st ==> let st' = run_cfl (translate_hsl (Sc S1 S2)) st in
        status_intact st' st)`,
  RW_TAC std_ss [Well_Formed_def, same_base_regs_def, run_hsl_def, translate_hsl_def, SEMANTICS_OF_CFL] THEN
  METIS_TAC []
  );
*)

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

val  CJ_SEM_SPEC = Q.store_thm (
  "CJ_SEM_SPEC",
  `!cond S1 S2. 
     Well_Formed (Cj cond S1 S2) ==>
       sem_spec P S1 Q /\ sem_spec P S2 Q ==>
         sem_spec P (Cj cond S1 S2) Q`,

    RW_TAC std_ss [Well_Formed_def, WELL_FORMED_def, sem_spec_def, translate_hsl_def, LET_THM, 
          run_hsl_def, SEMANTICS_OF_CFL] THEN
    METIS_TAC [EVAL_TCND_THM]
  );

(*---------------------------------------------------------------------------------*)
(*      Correspondence of Tr structures                                            *)
(*---------------------------------------------------------------------------------*)

(*
val WF_TR_HSL_CFL = Q.store_thm (
   "WF_TR_HSL_CFL",
    `!cond S_hsl. WF (\s1 s0. ~eval_TCND cond s0 /\ (s1 = run_hsl S_hsl s0)) /\ 
           WELL_FORMED (translate_hsl S_hsl) ==>
         WF_TR (translate_condition (translate_TCND cond), translate (translate_hsl S_hsl))`,
    RW_TAC std_ss [] THEN
    MATCH_MP_TAC CFL_RulesTheory.WF_TR_LEM_1 THEN
    MATCH_MP_TAC relationTheory.WF_SUBSET THEN
    Q.EXISTS_TAC `\s1 s0. ~eval_TCND cond s0 /\ (s1 = run_hsl S_hsl s0)` THEN
    RW_TAC std_ss [EVAL_TCND_THM] THEN

  );
*)

val WF_LOOP_LEM_1 = Q.store_thm (
   "WF_LOOP_LEM_1",
   `!cond S_cfl. WF (\st1 st0. ~eval_il_cond cond st0 /\ (st1 = run_cfl S_cfl st0)) ==>
      WF_Loop (eval_il_cond cond, run_cfl S_cfl)`,
    RW_TAC std_ss [ARMCompositionTheory.WF_Loop_def] THEN
    Q.EXISTS_TAC `\st1 st0. ~eval_il_cond cond st0 /\ (st1 = run_cfl S_cfl st0)` THEN 
    RW_TAC std_ss []
    );

val UNROLL_WHILE_CFL = Q.store_thm (
   "UNROLL_WHILE_CFL",
   `!cond S_cfl st. WF (\st1 st0. ~eval_il_cond cond st0 /\ (st1 = run_cfl S_cfl st0)) ==>
       (WHILE (\st'. ~eval_il_cond cond st') (run_cfl S_cfl) st = 
        FUNPOW (run_cfl S_cfl) (shortest (\st'. eval_il_cond cond st') (run_cfl S_cfl) st) st)`,
   RW_TAC std_ss [] THEN
   IMP_RES_TAC WF_LOOP_LEM_1 THEN
   METIS_TAC [ARMCompositionTheory.UNROLL_LOOP]
  );

val TR_SEM_SPEC = Q.store_thm (
  "TR_SEM_SPEC",
  `!S_hsl cond. Well_Formed S_hsl /\ 
     WF (\st1 st0. ~eval_il_cond (translate_TCND cond) st0 /\ (st1 = run_cfl (translate_hsl S_hsl) st0)) /\
     sem_spec P S_hsl P ==>
       sem_spec P (Tr cond S_hsl) P`,

    SIMP_TAC std_ss [Well_Formed_def, sem_spec_def, translate_hsl_def, LET_THM, run_hsl_def] THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    Q.ABBREV_TAC `cnd1 = translate_TCND cond` THEN
    Q.ABBREV_TAC `S1 = translate_hsl S_hsl` THEN
    `WF_TR (translate_condition cnd1, translate S1)` by METIS_TAC [CFL_RulesTheory.WF_TR_LEM_1] THEN
    FULL_SIMP_TAC std_ss [CFL_SEMANTICS_TR, UNROLL_WHILE_CFL] THEN
    IMP_RES_TAC WF_LOOP_LEM_1 THEN
    IMP_RES_TAC ARMCompositionTheory.WF_LOOP_IMP_STOPAT THEN
    Induct_on `shortest (\st'. eval_il_cond cnd1 st') (run_cfl S1) st` THENL [
      REWRITE_TAC [Once EQ_SYM_EQ] THEN
        REPEAT GEN_TAC THEN NTAC 12 STRIP_TAC THEN
        `eval_il_cond cnd1 st /\ eval_TCND cond s` by METIS_TAC [SHORTEST_LEM, EVAL_TCND_THM] THEN
        FULL_SIMP_TAC arith_ss [Once WHILE, FUNPOW],

      REWRITE_TAC [Once EQ_SYM_EQ] THEN
        REPEAT GEN_TAC THEN NTAC 12 STRIP_TAC THEN
        Q.PAT_ASSUM `!cnd1 S1 st. a ==> b ==> c ==> d` (ASSUME_TAC o Q.SPECL [`cnd1`,`S1`,`run_cfl S1 st`]) THEN
        `(\st'. eval_il_cond cnd1 st') = eval_il_cond cnd1` by METIS_TAC [] THEN
        FULL_SIMP_TAC std_ss [] THEN 
        POP_ASSUM (K ALL_TAC) THEN 
        `stopAt (eval_il_cond cnd1) (run_cfl S1) st` by METIS_TAC [] THEN
        IMP_RES_TAC SHORTEST_INDUCTIVE THEN
        Q.ABBREV_TAC `k = shortest (eval_il_cond cnd1) (run_cfl S1) (run_cfl S1 st)` THEN
        RES_TAC THEN RES_TAC THEN
        `~eval_TCND cond s` by METIS_TAC [EVAL_TCND_THM] THEN 
        RW_TAC std_ss [Once WHILE, FUNPOW]
     ]
  );

(*---------------------------------------------------------------------------------*)
(*      Correspondence of Fc structures                                            *)
(*---------------------------------------------------------------------------------*)

val proper_frames_def = Define `
    proper_frames st (m1,m2) (n1,n2) = 
       (w2n (read st SP) = w2n (read st FP) - (12 + m1)) /\
       locate_ge (read st SP) (MAX n1 n2 + 13 + m2)`;

val MAP_LEM_4 = Q.store_thm (
    "MAP_LEM_4",
    `!l1 l2 f g. (MAP f l1 = MAP g l2) ==>
        (!i. (i < LENGTH l1) ==> (f (EL i l1) = g (EL i l2)))`,
    Induct_on `l1` THEN Induct_on `l2` THEN
    RW_TAC list_ss [] THEN
    Induct_on `i` THEN
    RW_TAC list_ss []
  );

(*
val PRE_CALL_SAME_CONTENT = Q.store_thm (
   "PRE_CALL_SAME_CONTENT",
   `!st m1 m2 caller_i callee_i caller_o callee_o.
     VALID_FC_1 (caller_i,callee_i,callee_o,caller_o) (m1,m2) /\
     locate_ge (read st SP) (MAX (LENGTH caller_i) (LENGTH caller_o) + 13 + m2) /\
     (w2n (read st SP) = w2n (read st FP) - (12 + m1)) /\
     (MAX (LENGTH caller_i) (LENGTH caller_o) - (LENGTH caller_i) = k) /\
     same_content s st m1 ==>
       same_content (transfer (empty_s,s) (callee_i,caller_i)) 
             (run_cfl (BLK (pre_call_2 (MAP conv_exp caller_i, MAP conv_exp callee_i) k m2)) st) m2`,

    REPEAT STRIP_TAC THEN
    `standard_frame st m1 /\ locate_ge (read st SP) (k + 13 + LENGTH caller_i + m2)` by 
       FULL_SIMP_TAC arith_ss [standard_frame_def, locate_ge_def, MAX_DEF] THEN
    FULL_SIMP_TAC std_ss [same_content_thm] THEN
    REPEAT STRIP_TAC THEN
    FULL_SIMP_TAC std_ss [VALID_FC_1_def] THEN
    Cases_on `MEM x callee_i` THENL [
      IMP_RES_TAC MEM_EL THEN
        `run_cfl (BLK (pre_call_2 (MAP conv_exp caller_i,MAP conv_exp callee_i) (MAX (LENGTH caller_i) 
           (LENGTH caller_o) - LENGTH caller_i) m2)) st '' conv_exp (EL n callee_i) = st '' conv_exp (EL n caller_i)` 
             by METIS_TAC [SIMP_RULE std_ss [rich_listTheory.EL_MAP] PRE_CALL_PASS_ARGUMENTS_THM_2] THEN
        `MAP (tread (transfer (empty_s,s) (callee_i,caller_i))) callee_i = MAP (tread s) caller_i` 
           by METIS_TAC [TRANSFER_THM] THEN
        FULL_SIMP_TAC std_ss [EVERY_EL] THEN 
        IMP_RES_TAC MAP_LEM_4 THEN 
        RW_TAC std_ss [] THEN METIS_TAC [],

       FULL_SIMP_TAC std_ss [valid_arg_list_def, run_hsl_def, LET_THM] THEN
         METIS_TAC [TRANSFER_INTACT]
    ]

*)

(*
val  FC_SEM_SPEC = Q.store_thm (
  "FC_SEM_SPEC",
  `!S_hsl cond. Well_Formed S_hsl /\
     VALID_FC_1 (caller_i,callee_i,callee_o,caller_o) (m1,m2) 
       ==>
     sem_spec P S_hsl Q ==>
       sem_spec (\st. P st /\ proper_frames st (m1,m2) (n1,n2) /\ 
          status_intact (run_cfl S_body st') st') 
          (Fc (caller_i, callee_i) S_hsl (caller_o, callee_o) (m1,m2)) Q`,

    SIMP_TAC std_ss [Well_Formed_def, sem_spec_def, translate_hsl_def, LET_THM, run_hsl_def] THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    Q.ABBREV_TAC `cnd1 = translate_TCND cond` THEN
    Q.ABBREV_TAC `S1 = translate_hsl S_hsl` THEN
    `WF_TR (translate_condition cnd1, translate S1)` by METIS_TAC [CFL_RulesTheory.WF_TR_LEM_1] THEN
    FULL_SIMP_TAC std_ss [CFL_SEMANTICS_TR, UNROLL_WHILE_CFL] THEN
    IMP_RES_TAC WF_LOOP_LEM_1 THEN
    IMP_RES_TAC WF_LOOP_IMP_STOPAT THEN
    Induct_on `shortest (\st'. eval_il_cond cnd1 st') (run_cfl S1) st` THENL [
      REWRITE_TAC [Once EQ_SYM_EQ] THEN
        REPEAT GEN_TAC THEN NTAC 12 STRIP_TAC THEN
        `eval_il_cond cnd1 st /\ eval_TCND cond s` by METIS_TAC [SHORTEST_LEM, EVAL_TCND_THM] THEN
        FULL_SIMP_TAC arith_ss [Once WHILE, FUNPOW],

      REWRITE_TAC [Once EQ_SYM_EQ] THEN
        REPEAT GEN_TAC THEN NTAC 12 STRIP_TAC THEN
        Q.PAT_ASSUM `!cnd1 S1 st. a ==> b ==> c ==> d` (ASSUME_TAC o Q.SPECL [`cnd1`,`S1`,`run_cfl S1 st`]) THEN
        `(\st'. eval_il_cond cnd1 st') = eval_il_cond cnd1` by METIS_TAC [] THEN
        FULL_SIMP_TAC std_ss [] THEN 
        POP_ASSUM (K ALL_TAC) THEN 
        `stopAt (eval_il_cond cnd1) (run_cfl S1) st` by METIS_TAC [] THEN
        IMP_RES_TAC SHORTEST_INDUCTIVE THEN
        Q.ABBREV_TAC `k = shortest (eval_il_cond cnd1) (run_cfl S1) (run_cfl S1 st)` THEN
        RES_TAC THEN RES_TAC THEN
        `~eval_TCND cond s` by METIS_TAC [EVAL_TCND_THM] THEN 
        RW_TAC std_ss [Once WHILE, FUNPOW]
     ]
  );
*)

(*---------------------------------------------------------------------------------*)

val _ = export_theory();
