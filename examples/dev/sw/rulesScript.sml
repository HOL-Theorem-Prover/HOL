
open HolKernel Parse boolLib bossLib numLib relationTheory arithmeticTheory preARMTheory pairTheory
     pred_setSimps pred_setTheory listTheory rich_listTheory whileTheory ARMCompositionTheory ILTheory;


val _ = new_theory "rules";

(*---------------------------------------------------------------------------------*)
(*      Simplifier on finite maps                                                  *) 
(*---------------------------------------------------------------------------------*)

val set_ss = std_ss ++ SET_SPEC_ss ++ PRED_SET_ss;

(*---------------------------------------------------------------------------------*)
(*      Inference based on Hoare Logic                                             *) 
(*---------------------------------------------------------------------------------*)

val _ = Globals.priming := NONE;

(*---------------------------------------------------------------------------------*)
(*      read from an data state                                                    *) 
(*---------------------------------------------------------------------------------*)

val mread_def = Define `
    (mread st mexp = read st (toEXP mexp))`;

val mread_thm = store_thm ("mread_thm",
        ``(!st r. mread st (MR r) = read st (toREG r)) /\
          (!st s c. mread st (MC s c) = read st (WCONST (w2w c #>> (2 * w2n s))))``,

        SIMP_TAC std_ss [mread_def, toEXP_def]);

       
val _ = add_rule {term_name = "mread", fixity = Suffix 60,
		  pp_elements = [TOK "<", TM, TOK ">"],
                  paren_style = OnlyIfNecessary,
                  block_style = (AroundSameName, (PP.INCONSISTENT, 0))} handle HOL_ERR e => print (#message e);


(*---------------------------------------------------------------------------------*)
(*      Hoare Logic Style Specification                                            *) 
(*---------------------------------------------------------------------------------*)

val HSPEC_def = Define `
    HSPEC P ir Q = !st. P st ==> Q (run_ir ir st)`;

val _ = type_abbrev("HSPEC_TYPE", type_of (Term `HSPEC`));

(*
val _ = add_rule {term_name = "HSPEC",
		  fixity = Infix (HOLgrammars.RIGHT, 3),
		  pp_elements = [HardSpace 1, TOK "(", TM, TOK ")", HardSpace 1],
		  paren_style = OnlyIfNecessary,
		  block_style = (AroundEachPhrase,
				 (PP.INCONSISTENT, 0))};
*)

(*---------------------------------------------------------------------------------*)
(*      Sequential Composition                                                     *) 
(*---------------------------------------------------------------------------------*)

val SC_RULE = Q.store_thm (
   "SC_RULE",
   `!P Q R ir1 ir2. WELL_FORMED ir1 /\ WELL_FORMED ir2 /\
      HSPEC P ir1 Q /\ HSPEC Q ir2 R ==> 
      HSPEC P (SC ir1 ir2) R`,
    RW_TAC std_ss [HSPEC_def] THEN 
    METIS_TAC [IR_SEMANTICS_SC]
   );

(*---------------------------------------------------------------------------------*)
(*      Block Rule                                                                 *)
(*      Block of assigment                                                         *) 
(*---------------------------------------------------------------------------------*)

val BLK_EQ_SC = Q.store_thm (
   "BLK_EQ_SC",
   `!stm stmL st. (run_ir (BLK (stm::stmL)) st = run_ir (SC (BLK [stm]) (BLK stmL)) st) /\ 
                  (run_ir (BLK (SNOC stm stmL)) st = run_ir (SC (BLK stmL) (BLK [stm])) st)`,

   REPEAT GEN_TAC THEN
   `WELL_FORMED (BLK [stm]) /\ WELL_FORMED (BLK stmL)` by
               METIS_TAC [BLOCK_IS_WELL_FORMED] THEN
   STRIP_TAC THENL [
       `run_ir (BLK [stm]) st = mdecode st stm` by (
               RW_TAC list_ss [run_ir_def, run_arm_def, translate_def, Once RUNTO_ADVANCE] THEN
               RW_TAC list_ss [GSYM uploadCode_def, UPLOADCODE_LEM] THEN
               RW_TAC list_ss [GSYM TRANSLATE_ASSIGMENT_CORRECT, ARMCompositionTheory.get_st_def, Once RUNTO_ADVANCE]
           ) THEN   
           RW_TAC list_ss [IR_SEMANTICS_BLK, IR_SEMANTICS_SC],

       RW_TAC list_ss [SNOC_APPEND, run_ir_def, translate_def] THEN
           `mk_SC (translate (BLK stmL)) [translate_assignment stm] = translate (BLK (stmL ++ [stm]))` by (
               RW_TAC list_ss [ARMCompositionTheory.mk_SC_def] THEN
               Induct_on `stmL` THENL [
                   RW_TAC list_ss [translate_def],
                   RW_TAC list_ss [translate_def] THEN
                       METIS_TAC [BLOCK_IS_WELL_FORMED]
               ]) THEN
            METIS_TAC []
       ]
   );

val EMPTY_BLK_AXIOM = Q.store_thm (
   "EMPTY_BLK_AXIOM",
   `!P Q. (!st. P st ==> Q st) ==>
        HSPEC P (BLK []) Q`,
    RW_TAC std_ss [HSPEC_def, IR_SEMANTICS_BLK]
  );

val BLK_RULE = Q.store_thm (
   "BLK_RULE",
   `!P Q R stm stmL. HSPEC Q (BLK [stm]) R /\ 
              HSPEC P (BLK stmL) Q ==>
                HSPEC P (BLK (SNOC stm stmL)) R`,
    RW_TAC std_ss [HSPEC_def] THEN
    RW_TAC std_ss [BLK_EQ_SC] THEN
    METIS_TAC [HSPEC_def, SC_RULE, BLOCK_IS_WELL_FORMED]
  );


(*---------------------------------------------------------------------------------*)
(*      Conditional Jumps                                                          *) 
(*---------------------------------------------------------------------------------*)

val CJ_RULE = Q.store_thm (
   "CJ_RULE",
   `!P Q cond ir1 ir2 st. WELL_FORMED ir1 /\ WELL_FORMED ir2 /\
      HSPEC (\st.eval_cond cond st /\ P st) ir1 Q /\ HSPEC (\st.~eval_cond cond st /\ P st) ir2 Q ==> 
      HSPEC P (CJ cond ir1 ir2) Q`,
    RW_TAC std_ss [HSPEC_def] THEN 
    METIS_TAC [IR_SEMANTICS_CJ]
   );


val CJ_RULE_2 = Q.store_thm (
   "CJ_RULE_2",
   `!P Q cond ir1 ir2 st. WELL_FORMED ir1 /\ WELL_FORMED ir2 /\
      HSPEC P ir1 Q /\ HSPEC P ir2 Q ==> 
      HSPEC P (CJ cond ir1 ir2) Q`,
    RW_TAC std_ss [HSPEC_def] THEN 
    METIS_TAC [IR_SEMANTICS_CJ]
   );

(*---------------------------------------------------------------------------------*)
(*      Tail Recursion                                                             *) 
(*---------------------------------------------------------------------------------*)

val TR_RULE = Q.store_thm (
   "TR_RULE",
   `!cond ir P Q.
        WELL_FORMED ir /\  WF_TR (cond, translate ir) /\
           HSPEC P ir P ==> HSPEC P (TR cond ir) P`,
   RW_TAC std_ss [HSPEC_def] THEN
   METIS_TAC [HOARE_TR_IR]
   );

(*---------------------------------------------------------------------------------*)
(*      Well-founded Tail Recursion                                                *) 
(*---------------------------------------------------------------------------------*)

val WF_DEF_2 = Q.store_thm (
   "WF_DEF_2",
   `WF R = !P. (?w. P w) ==> ?min. P min /\ !b. R b min ==> ~P b`,
   RW_TAC std_ss [relationTheory.WF_DEF]
  );

val WF_TR_LEM_1 = Q.store_thm (
   "WF_TR_LEM_1",
   `!cond ir st. WELL_FORMED ir /\
           WF (\st1 st0. ~eval_cond cond st0 /\ (st1 = run_ir ir st0)) ==>
           WF_TR (cond,translate ir)`,
   
   RW_TAC std_ss [WELL_FORMED_def, WF_TR_def, WF_Loop_def, run_ir_def, run_arm_def] THEN
   POP_ASSUM MP_TAC THEN Q.ABBREV_TAC `arm = translate ir` THEN STRIP_TAC THEN
   Q.EXISTS_TAC `\s1 s0. if eval_cond cond (get_st s0) then F else (get_st s1 = get_st (runTo (upload arm (\i. ARB) (FST (FST s0))) 
             (FST (FST s0) + LENGTH (translate ir)) s0))` THEN
   STRIP_TAC THENL [
      FULL_SIMP_TAC std_ss [WF_DEF_2, GSYM RIGHT_FORALL_IMP_THM] THEN
          STRIP_TAC THEN
          POP_ASSUM (ASSUME_TAC o Q.SPEC `\st. ?pc cpsr pcS. (P:STATEPCS->bool) (((pc,cpsr,st),pcS):STATEPCS)`) THEN
          STRIP_TAC THEN 
          FULL_SIMP_TAC std_ss [GSYM RIGHT_EXISTS_IMP_THM] THEN
          `?st pc cpsr pcS. w = ((pc,cpsr,st),pcS)` by METIS_TAC [ABS_PAIR_THM] THEN
          FULL_SIMP_TAC std_ss [] THEN RES_TAC THEN
          Q.EXISTS_TAC `((pc',cpsr',st0),pcS')` THEN
          RW_TAC std_ss [Once get_st_def] THEN RES_TAC THEN
          `get_st (runTo (upload arm (\i. ARB) pc') (pc'+LENGTH arm) ((pc',cpsr',st0),pcS')) =
              get_st (runTo (upload arm (\i. ARB) 0) (LENGTH arm) ((0,0w,st0),{}))` by 
              METIS_TAC [well_formed_def, get_st_def, DSTATE_IRRELEVANT_PCS, status_independent_def, FST, DECIDE (Term `!x.0 + x = x`)] THEN
          METIS_TAC [FST,SND,get_st_def, ABS_PAIR_THM],

      RW_TAC std_ss [get_st_def] THEN
          METIS_TAC [WELL_FORMED_INSTB]
      ]
   );

val WF_TR_LEM_2 = Q.store_thm (
   "WF_TR_LEM_2",
    `!cond ir prj_f f cond_f.
        (!st. cond_f (prj_f st) = eval_cond cond st) /\ (!st. prj_f (run_ir ir st) = f (prj_f st)) /\ 
        WF (\t1 t0. ~cond_f t0 /\ (t1 = f t0)) ==>
           WF (\st1 st0. ~eval_cond cond st0 /\ (st1 = run_ir ir st0))`,

   RW_TAC std_ss [WF_DEF_2] THEN
   Q.PAT_ASSUM `!P.p` (ASSUME_TAC o Q.SPEC `\t:'a. ?y:DSTATE. (prj_f y = t) /\ P y`) THEN
   FULL_SIMP_TAC std_ss [GSYM RIGHT_EXISTS_IMP_THM] THEN
   RES_TAC THEN
   Q.EXISTS_TAC `y` THEN
   RW_TAC std_ss [] THEN
   `~cond_f (prj_f y)` by METIS_TAC [] THEN 
   RES_TAC THEN
   Q.PAT_ASSUM `!t1.p` (ASSUME_TAC o Q.SPEC `prj_f (st1:DSTATE)`) THEN
   METIS_TAC []
  );

val WF_TR_LEM_3 = Q.store_thm (
   "WF_TR_LEM_3",
   `!cond_f f. (?R. WF R /\ !t0 t1. ~cond_f t0 ==> R (f t0) t0) ==>        
            WF (\t1 t0. ~cond_f t0 /\ (t1 = f t0))`,
   RW_TAC std_ss [] THEN
   MATCH_MP_TAC WF_SUBSET THEN
   Q.EXISTS_TAC `R` THEN
   RW_TAC std_ss []
   );

(*---------------------------------------------------------------------------------*)
(*      Hoare Rules on Projection on Inputs and Ouputs                             *)
(*      The pre-conditions and post-conditions (on data other than inputs and      *)
(*        outputs) are also specified                                              *) 
(*---------------------------------------------------------------------------------*)

val PSPEC_def = Define `
    PSPEC ir (pre_p,post_p) (in_f,f,out_f) = !v. HSPEC (\st. (in_f st = v) /\ pre_p st) ir (\st. (out_f st = f v) /\ post_p st)`;

val _ = type_abbrev("PSPEC_TYPE", type_of (Term `PSPEC`));

val PROJ_POST_RULE = Q.store_thm (
   "PROJ_POST_RULE",
   `!ir in_f out_f convert_f.
     PSPEC ir (pre_p,post_p) (in_f,f,out_f) 
       ==>
       PSPEC ir (pre_p, post_p) (in_f, convert_f o f, convert_f o out_f)`,
     RW_TAC std_ss [PSPEC_def, HSPEC_def]
   );

val PROJ_SC_RULE = Q.store_thm (
   "PROJ_SC_RULE",
   `!ir1 ir2 f1 f2 pre_p1 post_p1 post_p2 in_f1 out_f1 out_f2.
     WELL_FORMED ir1 /\ WELL_FORMED ir2 /\
     PSPEC ir1 (pre_p1,post_p1) (in_f1,f1,out_f1) /\ PSPEC ir2 (post_p1,post_p2) (out_f1,f2,out_f2) 
       ==>
       PSPEC (SC ir1 ir2) (pre_p1,post_p2) (in_f1,f2 o f1,out_f2)`,

     RW_TAC std_ss [PSPEC_def] THEN
     METIS_TAC [SC_RULE]
   );

(*
val PROJ_SC_RULE_2 = Q.store_thm (
   "PROJ_SC_RULE_2",
   `!ir1 ir2 f1 f2 in_f1 out_f1 in_f2 out_f2 convert_f.
     WELL_FORMED ir1 /\ WELL_FORMED ir2 /\ (convert_f o out_f1 = in_f2) /\ 
     PSPEC ir1 (pre_p1,post_p1) (in_f1,f1,out_f1) /\ PSPEC ir2 (post_p1,post_p2) (in_f2,f2,out_f2) 
       ==>
       PSPEC (SC ir1 ir2) (pre_p1,post_p2) (in_f1,f2 o convert_f o f1,out_f2)`,

     RW_TAC std_ss [PSPEC_def, HSPEC_def] THEN
     `!st. out_f2 (run_ir ir2 st) = (f2 o convert_f) (out_f1 st)` by RW_TAC std_ss [] THEN
     POP_ASSUM MP_TAC THEN
     POP_ASSUM (K ALL_TAC) THEN STRIP_TAC THEN
     IMP_RES_TAC (SIMP_RULE std_ss [PSPEC_def, HSPEC_def] PROJ_SC_RULE) THEN
     NTAC 14 (POP_ASSUM (K ALL_TAC)) THEN
     METIS_TAC [combinTheory.o_THM]
   );
*)

val PROJ_CJ_RULE = Q.store_thm (
   "PROJ_CJ_RULE",
   `!ir_t ir_f f1 f2 in_f out_f cond_f. 
     WELL_FORMED ir_t /\ WELL_FORMED ir_f /\
     PSPEC ir_t (pre_p,post_p) (in_f,f1,out_f) /\ PSPEC ir_f (pre_p, post_p) (in_f,f2,out_f) /\ (!st. cond_f (in_f st) = eval_cond cond st)
        ==>
       PSPEC (CJ cond ir_t ir_f) (pre_p,post_p) (in_f, (\v.if cond_f v then f1 v else f2 v), out_f)`,
     
     RW_TAC std_ss [PSPEC_def, HSPEC_def] THEN
     METIS_TAC [IR_SEMANTICS_CJ]
   );

(* Need the theorems in ARMCompositionTheory to prove the PROJ_TR_RULE *)

(* 
val PROJ_TR_RULE = Q.store_thm (
   "PROJ_TR_RULE",
   `!cond ir prj_f f cond_f.
        WELL_FORMED ir /\  WF (\st1 st0. ~eval_cond cond st0 /\ (st1 = run_ir ir st0)) /\
        (!st. cond_f (prj_f st) = eval_cond cond st) /\ PSPEC ir (pre_p,pre_p) (prj_f,f,prj_f) ==> 
          PSPEC (TR cond ir) (pre_p,pre_p) (prj_f, WHILE ($~ o cond_f) f, prj_f)`,

    RW_TAC std_ss [PSPEC_def, HSPEC_def] THEN
    `WF_TR (cond,translate ir)` by METIS_TAC [WF_TR_LEM_1] THEN
    FULL_SIMP_TAC std_ss [WELL_FORMED_def, run_ir_def, run_arm_def, translate_def] THEN
    Q.ABBREV_TAC `arm = translate ir` THEN
    IMP_RES_TAC (SIMP_RULE set_ss [] (Q.SPECL [`cond`,`arm`,`(\i. ARB)`,`(0,0w,st):STATE`,`{}`] ARMCompositionTheory.UNROLL_TR_LEM)) THEN
    POP_ASSUM (ASSUME_TAC o Q.SPEC `st`) THEN
    FULL_SIMP_TAC std_ss [FUNPOW, ARMCompositionTheory.get_st_def] THEN
    NTAC 2 (POP_ASSUM (K ALL_TAC)) THEN
    Induct_on `loopNum cond arm (\i.ARB) ((0,0w,st),{})` THENL [
        REWRITE_TAC [Once EQ_SYM_EQ] THEN RW_TAC std_ss [FUNPOW,ARMCompositionTheory.get_st_def] THEN
            IMP_RES_TAC ARMCompositionTheory.LOOPNUM_BASIC THEN
            FULL_SIMP_TAC arith_ss [Once WHILE, ARMCompositionTheory.get_st_def],

        REWRITE_TAC [Once EQ_SYM_EQ] THEN RW_TAC std_ss [FUNPOW] THEN
            IMP_RES_TAC ARMCompositionTheory.LOOPNUM_INDUCTIVE THEN
            `v = loopNum cond arm (\i.ARB) ((0,0w,SND (SND (FST (runTo (upload arm (\i.ARB) 0) (LENGTH arm) ((0,0w,st),{}))))),{})` by
                METIS_TAC [ABS_PAIR_THM,DECIDE (Term`!x.0+x=x`),ARMCompositionTheory.LOOPNUM_INDEPENDENT_OF_CPSR_PCS, ARMCompositionTheory.get_st_def, 
                        FST, SND, ARMCompositionTheory.DSTATE_IRRELEVANT_PCS,ARMCompositionTheory.well_formed_def] THEN
            RES_TAC THEN Q.PAT_ASSUM `v = x` (ASSUME_TAC o GSYM) THEN FULL_SIMP_TAC std_ss [] THEN POP_ASSUM (K ALL_TAC) THEN
            Q.PAT_ASSUM `v = x` (ASSUME_TAC o GSYM) THEN FULL_SIMP_TAC std_ss [] THEN POP_ASSUM (K ALL_TAC) THEN
            Q.PAT_ASSUM `~x` (ASSUME_TAC o SIMP_RULE std_ss [ARMCompositionTheory.get_st_def]) THEN
            RW_TAC std_ss [Once WHILE] THEN
            Q.UNABBREV_TAC `arm` THEN
            `run_ir ir st = SND (SND (FST (runTo (upload (translate ir) (\i. ARB) 0) (LENGTH (translate ir)) ((0,0w,st),{}))))` by RW_TAC arith_ss [
                   ARMCompositionTheory.get_st_def, run_ir_def, run_arm_def] THEN
            METIS_TAC [SND,FST,ARMCompositionTheory.get_st_def,ARMCompositionTheory.FUNPOW_DSTATE, ABS_PAIR_THM]
      ]
   );

val PROJ_TR_RULE_2 = Q.store_thm (
   "PROJ_TR_RULE_2",
   `!cond ir prj_f f cond_f.
        WELL_FORMED ir /\ (!st. cond_f (prj_f st) = eval_cond cond st) /\
        (?R. WF R /\ !t0 t1. ~cond_f t0 ==> R (f t0) t0) /\
           PSPEC ir (prj_f,f,prj_f) ==> PSPEC (TR cond ir) (prj_f, WHILE ($~ o cond_f) f, prj_f)`,

    RW_TAC std_ss [PSPEC_def, HSPEC_def] THEN
    `WF (\st1 st0. ~eval_cond cond st0 /\ (st1 = run_ir ir st0))` by METIS_TAC [WF_TR_LEM_2, WF_TR_LEM_3] THEN
    METIS_TAC [SIMP_RULE std_ss [PSPEC_def, HSPEC_def] PROJ_TR_RULE]
  );
*)

(*---------------------------------------------------------------------------------*)
(*      Rules for Context                                                          *) 
(*---------------------------------------------------------------------------------*)

val UNCHANGED_def = Define `
    UNCHANGED ir contextL = 
      !v. HSPEC (\st. MAP (mread st) contextL = v) ir (\st. MAP (mread st) contextL = v)`;

val CONTEXT_TR_RULE = Q.store_thm (
   "CONTEXT_TR_RULE",
   `!cond ir contextL.
        WELL_FORMED ir /\  WF (\st1 st0. ~eval_cond cond st0 /\ (st1 = run_ir ir st0)) /\
           UNCHANGED ir contextL ==> UNCHANGED (TR cond ir) contextL`,

    RW_TAC std_ss [UNCHANGED_def] THEN 
    METIS_TAC [TR_RULE, WF_TR_LEM_1]
   );

val CONTEXT_SC_RULE = Q.store_thm (
   "CONTEXT_SC_RULE",
   `!ir1 ir2 contextL.
        WELL_FORMED ir1 /\  WELL_FORMED ir2  /\ 
        UNCHANGED ir1 contextL /\ UNCHANGED ir2 contextL 
          ==> UNCHANGED (SC ir1 ir2) contextL`,

    RW_TAC std_ss [UNCHANGED_def] THEN 
    METIS_TAC [SC_RULE]
   );

val CONTEXT_CJ_RULE = Q.store_thm (
   "CONTEXT_CJ_RULE",
   `!ir1 ir2 cond contextL.
        WELL_FORMED ir1 /\  WELL_FORMED ir2  /\ 
        UNCHANGED ir1 contextL /\ UNCHANGED ir2 contextL 
          ==> UNCHANGED (CJ cond ir1 ir2) contextL`,

    RW_TAC std_ss [UNCHANGED_def] THEN
    METIS_TAC [CJ_RULE_2]
   );

(*---------------------------------------------------------------------------------*)
(*      Rules for Well-formedness                                    *) 
(*---------------------------------------------------------------------------------*)

val WELL_FORMED_TR_RULE = Q.store_thm (
   "WELL_FORMED_TR_RULE",
   `!cond ir context_f.
        WELL_FORMED ir /\  WF (\st1 st0. ~eval_cond cond st0 /\ (st1 = run_ir ir st0)) ==>
           WELL_FORMED (TR cond ir)`,

    RW_TAC std_ss [] THEN 
    METIS_TAC [IR_TR_IS_WELL_FORMED, WF_TR_LEM_1]
   );

val _ = export_theory();

