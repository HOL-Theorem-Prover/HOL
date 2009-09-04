(* interactive use:

quietdec := true;
loadPath := (concat Globals.HOLDIR "/examples/dev/sw") :: !loadPath;

app load ["numLib", "preARMTheory", "pred_setSimps", "pred_setTheory",
          "rich_listTheory", "ARMCompositionTheory", "ILTheory", "wordsTheory"];

quietdec := false;
*)


open HolKernel Parse boolLib bossLib numLib relationTheory arithmeticTheory preARMTheory pairTheory
     pred_setSimps pred_setTheory listTheory rich_listTheory whileTheory ARMCompositionTheory ILTheory wordsTheory;


val _ = new_theory "rules";
val _ = hide "cond";

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
val _ = Hol_datatype `
    REXP = RR of MREG
         | RM of MMEM
         | RC of DATA
         | PR of REXP # REXP
    `;


val mread_def = Define `
     (mread st (RR r) = read st (toREG r)) /\
     (mread st (RM m) = read st (toMEM m)) /\
     (mread st (RC c) = c)`;

val _ = add_rule {term_name = "mread", fixity = Suffix 60,
		  pp_elements = [TOK "<", TM, TOK ">"],
                  paren_style = OnlyIfNecessary,
                  block_style = (AroundSameName, (PP.INCONSISTENT, 0))} handle HOL_ERR e => print (#message e);


(*---------------------------------------------------------------------------------*)
(*      The fp and sp point to the default positions                               *)
(*---------------------------------------------------------------------------------*)

val proper_def = Define `
    proper = (\(regs,mem):DSTATE. (regs ' 11w = 100w) /\ (regs ' 13w = 100w))`;


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
      HSPEC (\st.eval_il_cond cond st /\ P st) ir1 Q /\ HSPEC (\st.~eval_il_cond cond st /\ P st) ir2 Q ==>
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
        WELL_FORMED ir /\  WF_TR (translate_condition cond, translate ir) /\
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
           WF (\st1 st0. ~eval_il_cond cond st0 /\ (st1 = run_ir ir st0)) ==>
           WF_TR (translate_condition cond,translate ir)`,

   RW_TAC std_ss [WELL_FORMED_SUB_thm, WF_TR_def, WF_Loop_def, run_ir_def, run_arm_def] THEN
   POP_ASSUM MP_TAC THEN Q.ABBREV_TAC `arm = translate ir` THEN STRIP_TAC THEN
   Q.EXISTS_TAC `\s1 s0. if eval_il_cond cond (get_st s0) then F else (get_st s1 = get_st (runTo (upload arm (\i. ARB) (FST (FST s0)))
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

      RW_TAC std_ss [get_st_def, eval_il_cond_def] THEN
          METIS_TAC [WELL_FORMED_INSTB]
      ]
   );

val WF_TR_LEM_2 = Q.store_thm (
   "WF_TR_LEM_2",
    `!cond ir prj_f f cond_f.
        (!st. cond_f (prj_f st) = eval_il_cond cond st) /\ (!st. prj_f (run_ir ir st) = f (prj_f st)) /\
        WF (\t1 t0. ~cond_f t0 /\ (t1 = f t0)) ==>
           WF (\st1 st0. ~eval_il_cond cond st0 /\ (st1 = run_ir ir st0))`,

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

val WF_TR_THM_1 = Q.store_thm (
   "WF_TR_THM_1",
    `!cond ir prj_f f cond_f pre_p.
        (!st. cond_f (prj_f st) = eval_il_cond cond st) /\
        (!st. pre_p st ==> (prj_f (run_ir ir st) = f (prj_f st))) /\
        WF (\t1 t0. ~cond_f t0 /\ (t1 = f t0)) ==>
           WF (\st1 st0. (pre_p st0) /\ ~(eval_il_cond cond st0) /\ (st1 = run_ir ir st0))`,

   RW_TAC std_ss [WF_DEF_2] THEN
   Q.PAT_ASSUM `!P.p` (ASSUME_TAC o Q.SPEC `\t:'a. ?y:DSTATE. (prj_f y = t) /\ P y`) THEN
   FULL_SIMP_TAC std_ss [GSYM RIGHT_EXISTS_IMP_THM] THEN
   RES_TAC THEN
   Q.EXISTS_TAC `y` THEN
   RW_TAC std_ss [] THEN
   `~cond_f (prj_f y)` by METIS_TAC [] THEN
   RES_TAC THEN
   Q.PAT_ASSUM `!y1.p` (ASSUME_TAC o Q.SPEC `prj_f (run_ir ir y)`) THEN
   METIS_TAC []
  );

(*---------------------------------------------------------------------------------*)
(*      Hoare Rules on Projection on Inputs and Ouputs (represented                *)
(*                    by projective functions                                      *)
(*      The pre-conditions and post-conditions (on data other than inputs and      *)
(*        outputs) are also specified                                              *)
(*---------------------------------------------------------------------------------*)

val PSPEC_def = Define `
    PSPEC ir (pre_p,post_p) stk_f (in_f,f,out_f) =
        !v x. HSPEC (\st. pre_p st /\ (stk_f st = x) /\ (in_f st = v))
                 ir (\st. post_p st /\ (stk_f st = x) /\ (out_f st = f v))`;

val _ = type_abbrev("PSPEC_TYPE", type_of (Term `PSPEC`));

val PSPEC_STACK = Q.store_thm (
   "PSPEC_STACK",
   `!ir pre_p post_p stk_f in_f f out_f x.
     PSPEC ir (pre_p,post_p) stk_f (in_f,f,out_f)
       ==>
       HSPEC (\st. pre_p st /\ (stk_f st = x)) ir (\st. post_p st /\ (stk_f st = x))`,
     RW_TAC std_ss [PSPEC_def, HSPEC_def]
   );

val PSPEC_CHARACTERISTIC = Q.store_thm (
   "PSPEC_CHARACTERISTIC",
   `!ir pre_p post_p stk_f in_f f out_f.
     PSPEC ir (pre_p,post_p) stk_f (in_f,f,out_f)
       ==>
       HSPEC (\st. pre_p st /\ (in_f st = v)) ir (\st. post_p st /\ (out_f st = f v))`,
     RW_TAC std_ss [PSPEC_def, HSPEC_def]
   );

val PRJ_SHUFFLE_RULE = Q.store_thm (
   "PRJ_SHUFFLE_RULE",
   `!ir pre_p post_p stk_f in_f f out_f shuffle_f.
     PSPEC ir (pre_p,post_p) stk_f (in_f,f,out_f)
       ==>
       PSPEC ir (pre_p, post_p) stk_f (in_f, shuffle_f o f, shuffle_f o out_f)`,
     RW_TAC std_ss [PSPEC_def, HSPEC_def]
   );

val PRJ_SHUFFLE_RULE2 = Q.store_thm (
   "PRJ_SHUFFLE_RULE2",
   `!ir pre_p post_p stk_f in_f f out_f g in_f'.
     PSPEC ir (pre_p, post_p) stk_f (in_f, f, out_f) /\ (g o in_f' = f o in_f)
       ==>
       PSPEC ir (pre_p,post_p) stk_f (in_f', g, out_f)`,
     RW_TAC std_ss [PSPEC_def, HSPEC_def] THEN
     METIS_TAC [FUN_EQ_THM, combinTheory.o_THM]
   );

val PRJ_SC_RULE = Q.store_thm (
   "PRJ_SC_RULE",
   `!ir1 ir2 pre_p1 post_p1 post_p2 stk_f in_f1 f1 f2 out_f1 out_f2.
     WELL_FORMED ir1 /\ WELL_FORMED ir2 /\
     PSPEC ir1 (pre_p1,post_p1) stk_f (in_f1,f1,out_f1) /\ PSPEC ir2 (post_p1,post_p2) stk_f (out_f1,f2,out_f2)
       ==>
       PSPEC (SC ir1 ir2) (pre_p1,post_p2) stk_f (in_f1,f2 o f1,out_f2)`,

     RW_TAC std_ss [PSPEC_def] THEN
     METIS_TAC [SC_RULE]
   );

val PRJ_CJ_RULE = Q.store_thm (
   "PRJ_CJ_RULE",
   `!cond ir_t ir_f pre_p post_p stk_f cond_f in_f f1 f2 out_f.
     WELL_FORMED ir_t /\ WELL_FORMED ir_f /\
     PSPEC ir_t (pre_p,post_p) stk_f (in_f,f1,out_f) /\
     PSPEC ir_f (pre_p, post_p) stk_f (in_f,f2,out_f) /\ (!st. cond_f (in_f st) = eval_il_cond cond st)
        ==>
       PSPEC (CJ cond ir_t ir_f) (pre_p,post_p) stk_f (in_f, (\v.if cond_f v then f1 v else f2 v), out_f)`,

     RW_TAC std_ss [PSPEC_def, HSPEC_def] THEN
     METIS_TAC [IR_SEMANTICS_CJ]
   );

(* Need the theorems in ARMCompositionTheory to prove the PROJ_TR_RULE *)
val PRJ_TR_RULE = Q.store_thm (
   "PRJ_TR_RULE",
   `!cond ir pre_p stk_f cond_f prj_f f.
        WELL_FORMED ir /\  WF (\st1 st0. ~eval_il_cond cond st0 /\ (st1 = run_ir ir st0)) /\
        (!st. cond_f (prj_f st) = eval_il_cond cond st) /\ PSPEC ir (pre_p,pre_p) stk_f (prj_f,f,prj_f) ==>
          PSPEC (TR cond ir) (pre_p,pre_p) stk_f (prj_f, WHILE ($~ o cond_f) f, prj_f)`,

    RW_TAC std_ss [PSPEC_def] THEN
    RW_TAC std_ss [HSPEC_def] THENL [
        FULL_SIMP_TAC std_ss [HSPEC_def] THEN
            METIS_TAC [SIMP_RULE std_ss [HSPEC_def] TR_RULE, WF_TR_LEM_1],

        IMP_RES_TAC (SIMP_RULE std_ss [PSPEC_def] PSPEC_STACK) THEN
            POP_ASSUM (ASSUME_TAC o Q.SPEC `(stk_f:DSTATE->'a) st`) THEN
            IMP_RES_TAC WF_TR_LEM_1 THEN
            IMP_RES_TAC (Q.SPECL [`cond`,`ir`,`\st1. pre_p st1 /\ ((stk_f:DSTATE->'a)
			          st1 = (stk_f:DSTATE->'a) st)`] TR_RULE) THEN
            POP_ASSUM (ASSUME_TAC o Q.SPEC `st` o SIMP_RULE std_ss [HSPEC_def]) THEN
            METIS_TAC [],

        IMP_RES_TAC (SIMP_RULE std_ss [PSPEC_def] PSPEC_CHARACTERISTIC) THEN
            Q.PAT_ASSUM `!v x.p` (K ALL_TAC) THEN
            `WF_TR (translate_condition cond,translate ir)` by METIS_TAC [WF_TR_LEM_1] THEN
	    FULL_SIMP_TAC std_ss [WELL_FORMED_SUB_thm, HSPEC_def, run_ir_def, run_arm_def, translate_def, eval_il_cond_def] THEN
	    Q.ABBREV_TAC `arm = translate ir` THEN
	    IMP_RES_TAC (SIMP_RULE set_ss [] (Q.SPECL [`translate_condition cond`,`arm`,`(\i. ARB)`,`(0,0w,st):STATE`,`{}`]
                              ARMCompositionTheory.UNROLL_TR_LEM)) THEN
	    POP_ASSUM (ASSUME_TAC o Q.SPEC `st`) THEN
	    FULL_SIMP_TAC std_ss [FUNPOW, ARMCompositionTheory.get_st_def] THEN
	    NTAC 2 (POP_ASSUM (K ALL_TAC)) THEN
	    Induct_on `loopNum (translate_condition cond) arm (\i.ARB) ((0,0w,st),{})` THENL [
	      REWRITE_TAC [Once EQ_SYM_EQ] THEN RW_TAC std_ss [FUNPOW,ARMCompositionTheory.get_st_def] THEN
	      IMP_RES_TAC ARMCompositionTheory.LOOPNUM_BASIC THEN
	      FULL_SIMP_TAC arith_ss [Once WHILE, ARMCompositionTheory.get_st_def],

	    REWRITE_TAC [Once EQ_SYM_EQ] THEN RW_TAC std_ss [FUNPOW] THEN
        IMP_RES_TAC ARMCompositionTheory.LOOPNUM_INDUCTIVE THEN
	      `v = loopNum (translate_condition cond) arm (\i.ARB) ((0,0w,SND (SND (FST (runTo (upload arm (\i.ARB) 0) (LENGTH arm)
                   ((0,0w,st),{}))))),{})` by METIS_TAC [ABS_PAIR_THM,DECIDE (Term`!x.0+x=x`),
                       ARMCompositionTheory.LOOPNUM_INDEPENDENT_OF_CPSR_PCS, ARMCompositionTheory.get_st_def,
                       FST, SND, ARMCompositionTheory.DSTATE_IRRELEVANT_PCS,ARMCompositionTheory.well_formed_def] THEN
	      RES_TAC THEN Q.PAT_ASSUM `v = x` (ASSUME_TAC o GSYM) THEN
              FULL_SIMP_TAC std_ss [] THEN POP_ASSUM (K ALL_TAC) THEN
	      Q.PAT_ASSUM `v = x` (ASSUME_TAC o GSYM) THEN FULL_SIMP_TAC std_ss [] THEN POP_ASSUM (K ALL_TAC) THEN
	      Q.PAT_ASSUM `~x` (ASSUME_TAC o SIMP_RULE std_ss [ARMCompositionTheory.get_st_def]) THEN
	      RW_TAC std_ss [Once WHILE] THEN
	      Q.UNABBREV_TAC `arm` THEN
	      `run_ir ir st = SND (SND (FST (runTo (upload (translate ir) (\i. ARB) 0) (LENGTH (translate ir))
                  ((0,0w,st),{}))))` by RW_TAC arith_ss [
                   ARMCompositionTheory.get_st_def, run_ir_def, run_arm_def] THEN
	      METIS_TAC [SND,FST,ARMCompositionTheory.get_st_def,ARMCompositionTheory.FUNPOW_DSTATE, ABS_PAIR_THM]
	    ]
     ]
   );

val PRJ_TR_RULE_2 = Q.store_thm (
   "PRJ_TR_RULE_2",
   `!cond ir stk_f cond_f prj_f f.
        WELL_FORMED ir /\ (!st. cond_f (prj_f st) = eval_il_cond cond st) /\
        (?R. WF R /\ !t0 t1. ~cond_f t0 ==> R (f t0) t0) /\
           PSPEC ir ((\st.T),(\st.T)) stk_f (prj_f,f,prj_f) ==>
		    PSPEC (TR cond ir) ((\st.T),(\st.T)) stk_f (prj_f, WHILE ($~ o cond_f) f, prj_f)`,

    SIMP_TAC std_ss [PSPEC_def, HSPEC_def] THEN
    REPEAT GEN_TAC THEN NTAC 2 STRIP_TAC THEN
    `WF (\st1 st0. ~eval_il_cond cond st0 /\ (st1 = run_ir ir st0))` by METIS_TAC [WF_TR_LEM_2, WF_TR_LEM_3] THEN
    METIS_TAC [SIMP_RULE std_ss [PSPEC_def, HSPEC_def] (Q.SPECL [`cond`,`ir`,`\st.T`] PRJ_TR_RULE)]
  );


(*---------------------------------------------------------------------------------*)
(*      Rules for Conditions (projective function version)                         *)
(*---------------------------------------------------------------------------------*)

val PRJ_STRENGTHEN_RULE = Q.store_thm (
   "PRJ_STRENGTHEN_RULE",
   `!ir pre_p pre_p' post_p stk_f in_f f out_f.
     WELL_FORMED ir /\
     PSPEC ir (pre_p,post_p) stk_f (in_f,f,out_f) /\ (!st. pre_p' st ==> pre_p st) ==>
       PSPEC ir (pre_p',post_p) stk_f (in_f,f,out_f)`,
     RW_TAC std_ss [PSPEC_def, HSPEC_def]
   );

val PRJ_WEAKEN_RULE = Q.store_thm (
   "PRJ_WEAKEN_RULE",
   `!ir pre_p post_p post_p' stk_f in_f f out_f.
     WELL_FORMED ir /\
     PSPEC ir (pre_p,post_p) stk_f (in_f,f,out_f) /\ (!st. post_p st ==> post_p' st) ==>
       PSPEC ir (pre_p,post_p') stk_f (in_f,f,out_f)`,
     RW_TAC std_ss [PSPEC_def, HSPEC_def]
   );

(*---------------------------------------------------------------------------------*)
(*      Rules for Stack (projective function version)                              *)
(*---------------------------------------------------------------------------------*)

val valid_push_def = Define `
    valid_push (stk_f,in_f,f,out_f) (stk_f',in_f',g,out_f') =
      !st st'. (stk_f st' = stk_f st) /\ (out_f st' = f (in_f st)) ==>
         (stk_f' st' = stk_f' st) /\ (out_f' st' = g (in_f' st))`;

val PRJ_POP_RULE = Q.store_thm (
   "PRJ_POP_RULE",
   `!ir pre_p post_p stk_f in_f f out_f stk_f' in_f' g out_f'.
      PSPEC ir (pre_p,post_p) stk_f (in_f,f,out_f) /\
	valid_push (stk_f,in_f,f,out_f) (stk_f',in_f',g,out_f')
       ==>
        PSPEC ir (pre_p,post_p) stk_f' (in_f', g, out_f')`,
    RW_TAC list_ss [PSPEC_def, HSPEC_def, valid_push_def]
   );

val P_intact_def = Define `
    P_intact (P,Q) (stk_f,stk_g) =
     !st st'. (stk_f st' = stk_f st) /\ P st /\ Q st'
           ==> (stk_g st' = stk_g st)`;

val PRJ_PUSH_RULE = Q.store_thm (
   "PRJ_PUSH_RULE",
   `!ir pre_p post_p stk_f in_f f out_f e_f stk_g.
      PSPEC ir (pre_p,post_p) stk_f (in_f,f,out_f) /\
        P_intact (pre_p,post_p) (stk_f,stk_g)
      ==> PSPEC ir (pre_p,post_p) stk_g (in_f, f, out_f)`,
    RW_TAC list_ss [PSPEC_def, HSPEC_def, P_intact_def]
   );

(*---------------------------------------------------------------------------------*)
(*      Hoare Rules on Projection on Inputs and Ouputs (represented by vectors)    *)
(*      To overcome the type restriction on tuples in HOL definitions              *)
(*---------------------------------------------------------------------------------*)

(*   Vectors *)

val _ = Hol_datatype `
    VEXP = SG of DATA                (* registers *)
         | VT of VEXP # VEXP         (* pairs     *)
    `;

val readv_def = Define `
     (readv st (PR (a,b)) = VT (readv st a, readv st b)) /\
     (readv st x = SG (mread st x))`;


(* Vector Stack, modelled as a list of expression vectors *)

val push_def = Define `
    push x stk = x :: stk`;

val top_def = Define `
    top  = HD`;

val pop_def = Define `
    pop  = TL`;

(* Specification on vectors *)

val VSPEC_def = Define `
    VSPEC ir (pre_p,post_p) stk (iv,f,ov) =
        PSPEC ir (pre_p,post_p) (\st. MAP (readv st) stk) ((\st.readv st iv), f, (\st.readv st ov))
    `;

val _ = type_abbrev("VSPEC_TYPE", type_of (Term `VSPEC`));

val V_SHUFFLE_RULE = Q.store_thm (
   "V_SHUFFLE_RULE",
   `!ir stk iv f ov g iv'.
     VSPEC ir (pre_p,post_p) stk (iv,f,ov) /\ (!st. g (readv st iv') = f (readv st iv))
       ==>
       VSPEC ir (pre_p,post_p) stk (iv', g, ov)`,
     RW_TAC std_ss [VSPEC_def, PSPEC_def, HSPEC_def]
   );

val V_SC_RULE = Q.store_thm (
   "V_SC_RULE",
   `!ir1 ir2 pre_p1 post_p1 post_p2 stk vi1 f1 vo1 f2 vo2.
     WELL_FORMED ir1 /\ WELL_FORMED ir2 /\
     VSPEC ir1 (pre_p1,post_p1) stk (vi1,f1,vo1) /\ VSPEC ir2 (post_p1,post_p2) stk (vo1,f2,vo2)
       ==>
       VSPEC (SC ir1 ir2) (pre_p1,post_p2) stk (vi1,f2 o f1,vo2)`,
     RW_TAC std_ss [VSPEC_def] THEN
     METIS_TAC [PRJ_SC_RULE]
   );

val V_CJ_RULE = Q.store_thm (
   "V_CJ_RULE",
   `!cond ir_t ir_f pre_p post_p stk cond_f iv f1 f2 ov.
     WELL_FORMED ir_t /\ WELL_FORMED ir_f /\
     VSPEC ir_t (pre_p,post_p) stk (iv,f1,ov) /\
     VSPEC ir_f (pre_p, post_p) stk (iv,f2,ov) /\ (!st. cond_f (readv st iv) = eval_il_cond cond st)
        ==>
       VSPEC (CJ cond ir_t ir_f) (pre_p,post_p) stk (iv, (\v.if cond_f v then f1 v else f2 v), ov)`,
     RW_TAC std_ss [VSPEC_def] THEN
     FULL_SIMP_TAC std_ss [PRJ_CJ_RULE]
   );

(* Need the theorems in ARMCompositionTheory to prove the PROJ_TR_RULE *)

val V_TR_RULE = Q.store_thm (
   "V_TR_RULE",
   `!cond ir pre_p stk cond_f iv f.
        WELL_FORMED ir /\  WF (\st1 st0. ~eval_il_cond cond st0 /\ (st1 = run_ir ir st0)) /\
        (!st. cond_f (readv st iv) = eval_il_cond cond st) /\ VSPEC ir (pre_p,pre_p) stk (iv,f,iv) ==>
          VSPEC (TR cond ir) (pre_p,pre_p) stk (iv, WHILE ($~ o cond_f) f, iv)`,

    RW_TAC std_ss [VSPEC_def] THEN
    FULL_SIMP_TAC std_ss [PRJ_TR_RULE]
   );

(*---------------------------------------------------------------------------------*)
(*      Rules for Conditions (vector version)                                      *)
(*---------------------------------------------------------------------------------*)

val V_STRENGTHEN_RULE = Q.store_thm (
   "V_STRENGTHEN_RULE",
   `!ir pre_p pre_p' post_p stk iv f ov.
     WELL_FORMED ir /\
     VSPEC ir (pre_p,post_p) stk (iv,f,ov) /\ (!st. pre_p' st ==> pre_p st) ==>
       VSPEC ir (pre_p',post_p) stk (iv,f,ov)`,
     RW_TAC std_ss [VSPEC_def] THEN
     METIS_TAC [PRJ_STRENGTHEN_RULE]
   );

val V_WEAKEN_RULE = Q.store_thm (
   "V_WEAKEN_RULE",
   `!ir pre_p post_p post_p' stk iv f ov.
     WELL_FORMED ir /\
     PSPEC ir (pre_p,post_p) stk (iv,f,ov) /\ (!st. post_p st ==> post_p' st) ==>
       PSPEC ir (pre_p,post_p') stk (iv,f,ov)`,
     RW_TAC std_ss [VSPEC_def] THEN
     METIS_TAC [PRJ_WEAKEN_RULE]
   );

(*---------------------------------------------------------------------------------*)
(*      Rules for Stack (vector version)                                           *)
(*---------------------------------------------------------------------------------*)

val V_POP_RULE = Q.store_thm (
   "V_POP_RULE",
   `!ir pre_p post_p stk iv f ov e g.
      VSPEC ir (pre_p,post_p) (e::stk) (iv,f,ov) /\
       (!st. g (readv st (PR(iv,e))) = VT (f (readv st iv), readv st e)) ==>
         VSPEC ir (pre_p,post_p) stk (PR(iv,e), g, PR(ov,e))`,
    RW_TAC list_ss [VSPEC_def, PSPEC_def, HSPEC_def, readv_def]
   );

val V_intact_def = Define `
    V_intact (P,Q,e) =
      ?x. (!st.P st ==> (readv st e = x)) /\ (!st.Q st ==> (readv st e = x))`;


val V_PUSH_RULE = Q.store_thm (
   "V_PUSH_RULE",
   `!ir pre_p post_p stk iv f ov e.
      VSPEC ir (pre_p,post_p) stk (iv,f,ov) /\ V_intact(pre_p, post_p, e)
      ==>
         VSPEC ir (pre_p,post_p) (e::stk) (iv, f, ov)`,
    RW_TAC list_ss [VSPEC_def, PSPEC_def, HSPEC_def, V_intact_def, readv_def] THEN
    METIS_TAC []
   );


(*---------------------------------------------------------------------------------*)
(*      Rules for Well-formedness                                                  *)
(*---------------------------------------------------------------------------------*)

val WELL_FORMED_TR_RULE = Q.store_thm (
   "WELL_FORMED_TR_RULE",
   `!cond ir context_f.
        WELL_FORMED ir /\  WF (\st1 st0. ~eval_il_cond cond st0 /\ (st1 = run_ir ir st0)) ==>
           WELL_FORMED (TR cond ir)`,

    RW_TAC std_ss [] THEN
    METIS_TAC [IR_TR_IS_WELL_FORMED, WF_TR_LEM_1]
   );



val IR_CJ_UNCHANGED = store_thm ("IR_CJ_UNCHANGED",
``!cond ir_t ir_f s.
	(WELL_FORMED ir_t /\ WELL_FORMED ir_f /\
	UNCHANGED s ir_t /\ UNCHANGED s ir_f)  ==>
	UNCHANGED s (CJ cond ir_t ir_f)``,


REWRITE_TAC[UNCHANGED_def] THEN
REPEAT STRIP_TAC THEN
ASM_SIMP_TAC std_ss [SEMANTICS_OF_IR]  THEN
PROVE_TAC[]);


val IR_SC_UNCHANGED = store_thm ("IR_SC_UNCHANGED",
``!ir1 ir2 s.
	(WELL_FORMED ir1 /\ WELL_FORMED ir2 /\
	UNCHANGED s ir1 /\ UNCHANGED s ir2)  ==>
	UNCHANGED s (SC ir1 ir2)``,


REWRITE_TAC[UNCHANGED_def] THEN
REPEAT STRIP_TAC THEN
ASM_SIMP_TAC std_ss [SEMANTICS_OF_IR]  THEN
PROVE_TAC[])

val UNCHANGED_TR_RULE = store_thm ("UNCHANGED_TR_RULE",
``!c ir s.
	(WELL_FORMED (TR c ir) /\ UNCHANGED s ir) ==>
	UNCHANGED s (TR c ir)``,

  REWRITE_TAC [UNCHANGED_def, WELL_FORMED_def] THEN
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC std_ss [IR_SEMANTICS_TR___FUNPOW] THEN
  Q.ABBREV_TAC `n = (shortest (eval_il_cond c) (run_ir ir) st)` THEN
  POP_ASSUM (fn x => ALL_TAC) THEN
  Induct_on `n` THENL [
	 REWRITE_TAC[FUNPOW],
	 REWRITE_TAC[FUNPOW_SUC] THEN PROVE_TAC[]
  ]);




val IR_CJ_USED_STACK = store_thm ("IR_CJ_USED_STACK",
``!cond ir_t ir_f s s'.
	(WELL_FORMED ir_t /\ WELL_FORMED ir_f /\
	USED_STACK s' ir_f /\ USED_STACK s ir_t)  ==>
	USED_STACK (MAX s s') (CJ cond ir_t ir_f)``,


REPEAT STRIP_TAC THEN
`(s <= MAX s s') /\ (s' <= MAX s s')` by SIMP_TAC arith_ss [] THEN
`(USED_STACK (MAX s s') ir_f) /\
 (USED_STACK (MAX s s') ir_t)` by PROVE_TAC [USED_STACK_ENLARGE] THEN

FULL_SIMP_TAC std_ss [USED_STACK_THM, SEMANTICS_OF_IR] THEN
METIS_TAC[])


val IR_CJ_UNCHANGED_STACK = store_thm ("IR_CJ_UNCHANGED_STACK",
``!cond ir_t ir_f l s s'.
	(WELL_FORMED ir_t /\ WELL_FORMED ir_f /\
	UNCHANGED_STACK l s' ir_f /\ UNCHANGED_STACK l s ir_t)  ==>
	UNCHANGED_STACK l (MAX s s') (CJ cond ir_t ir_f)``,

SIMP_TAC std_ss [UNCHANGED_STACK_def, IR_CJ_USED_STACK, IR_CJ_UNCHANGED])



val IR_SC_USED_STACK = store_thm ("IR_SC_USED_STACK",
``!x ir1 ir2 s s'.
	(WELL_FORMED ir1 /\ WELL_FORMED ir2 /\
	 USED_STACK s ir1 /\ USED_STACK s' ir2 /\
	 (s' + x < 2**30) /\ (s < 2**30) /\
	 (!r m. read (run_ir ir1 (r,m)) (REG 13) =
			 read (r,m) (REG 13) - n2w (4*x)))  ==>
	 USED_STACK (MAX s (s'+x)) (SC ir1 ir2)``,


	REPEAT STRIP_TAC THEN
	FULL_SIMP_TAC std_ss [USED_STACK_THM, SEMANTICS_OF_IR] THEN
	REPEAT STRIP_TAC THEN

	`read (run_ir ir1 (r,m)) (REG 13) = (read (r,m) (REG 13) - (n2w (4*x)))` by METIS_TAC[] THEN
	`?r'' m''. run_ir ir1 (r,m) = (r'',m'')` by METIS_TAC[pairTheory.PAIR] THEN
	FULL_SIMP_TAC std_ss [toREG_def, read_thm, index_of_reg_def, MEM_MAP, MEM_LIST_COUNT] THEN
	`m ' l = m'' ' l` by METIS_TAC[] THEN
	ASM_SIMP_TAC std_ss [] THEN
	RES_TAC THEN
	POP_ASSUM MATCH_MP_TAC THEN
	FULL_SIMP_TAC arith_ss [word_sub_def, word_2comp_n2w, dimword_32,
		dimword_30] THEN
	GEN_TAC THEN
	Q.PAT_ASSUM `!off:num. P off` (fn thm => MP_TAC
		(SPEC ``(off:num) + (x:num)`` thm)) THEN
	Cases_on `off < s'` THEN ASM_REWRITE_TAC[] THEN
	ONCE_REWRITE_TAC [prove(``(4294967296:num - 4 * x) = (1073741824 - x)*4``, DECIDE_TAC)] THEN
	ASM_SIMP_TAC arith_ss [MEM_ADDR_ADD_CONST_MULT, GSYM WORD_ADD_ASSOC, word_add_n2w] THEN
	ONCE_REWRITE_TAC[GSYM n2w_mod] THEN
	SIMP_TAC arith_ss [dimword_30, dimword_4] THEN
	`((2147483648 - (off + x)) =
	 (1073741824 + (1073741824 - (off + x))))` by DECIDE_TAC THEN
	ASM_SIMP_TAC std_ss [ADD_MODULUS_RIGHT])





val IR_SC_USED_STACK = store_thm ("IR_SC_USED_STACK",
``!x y ir1 ir2 s s'.
	(WELL_FORMED ir1 /\ WELL_FORMED ir2 /\
	 USED_STACK s ir1 /\ USED_STACK s' ir2 /\
	 (s' + x < 2**30) /\ (s < 2**30) /\  (y <= x) /\
	 (!r m. read (run_ir ir1 (r,m)) (REG 13) =
			 read (r,m) (REG 13) - n2w (4*y)))  ==>
	 USED_STACK (MAX s (s'+x)) (SC ir1 ir2)``,

	REPEAT STRIP_TAC THEN
	FULL_SIMP_TAC std_ss [USED_STACK_THM, SEMANTICS_OF_IR] THEN
	REPEAT STRIP_TAC THEN

	`read (run_ir ir1 (r,m)) (REG 13) = (read (r,m) (REG 13) - (n2w (4*y)))` by METIS_TAC[] THEN
	`?r'' m''. run_ir ir1 (r,m) = (r'',m'')` by METIS_TAC[pairTheory.PAIR] THEN
	FULL_SIMP_TAC std_ss [toREG_def, read_thm, index_of_reg_def, MEM_MAP, MEM_LIST_COUNT] THEN
	`m ' l = m'' ' l` by METIS_TAC[] THEN
	ASM_SIMP_TAC std_ss [] THEN
	RES_TAC THEN
	POP_ASSUM MATCH_MP_TAC THEN
	FULL_SIMP_TAC arith_ss [word_sub_def, word_2comp_n2w, dimword_32,
		dimword_30] THEN
	GEN_TAC THEN
	Q.PAT_ASSUM `!off:num. P off` (fn thm => MP_TAC
		(SPEC ``(off:num) + (y:num)`` thm)) THEN
	Cases_on `off < s'` THEN ASM_REWRITE_TAC[] THEN
	ONCE_REWRITE_TAC [prove(``(4294967296:num - 4 * y) = (1073741824 - y)*4``, DECIDE_TAC)] THEN
	ASM_SIMP_TAC arith_ss [MEM_ADDR_ADD_CONST_MULT, GSYM WORD_ADD_ASSOC, word_add_n2w] THEN
	ONCE_REWRITE_TAC[GSYM n2w_mod] THEN
	SIMP_TAC arith_ss [dimword_30, dimword_4] THEN
	`((2147483648 - (off + y)) =
	 (1073741824 + (1073741824 - (off + y))))` by DECIDE_TAC THEN
	ASM_SIMP_TAC std_ss [ADD_MODULUS_RIGHT])



val IR_SC_USED_STACK___FC_CASE1 = store_thm ("IR_SC_USED_STACK___FC_CASE1",
``!ir1 ir2 s s' s''.
	(USED_STACK (s+s') ir1 /\ (USED_STACK s'' ir2 /\
	 WELL_FORMED ir1 /\ WELL_FORMED ir2  /\
	 (s + s' + s'' < 2**30) /\
	 (!r m. read (run_ir ir1 (r,m)) (REG 13) =
			 read (r,m) (REG 13) - n2w (4*s))))  ==>
	 USED_STACK (s+s'+s'') (SC ir1 ir2)``,

	REPEAT STRIP_TAC THEN
	`(s:num) + s' + s'' = MAX (s+s') (s'' + (s+s'))` by ALL_TAC THEN1 (
		SIMP_TAC arith_ss [MAX_DEF]
	) THEN
	ASM_REWRITE_TAC[] THEN
	MATCH_MP_TAC IR_SC_USED_STACK THEN
	Q_TAC EXISTS_TAC `s` THEN
	FULL_SIMP_TAC std_ss [])


val IR_SC_USED_STACK___FC_CASE2 = store_thm ("IR_SC_USED_STACK___FC_CASE2",
``!ir1 ir2 s s'.
	(USED_STACK s ir1 /\ (USED_STACK s' ir2 /\
	 WELL_FORMED ir1 /\ WELL_FORMED ir2  /\
	 (s + s' < 2**30) /\
	 (!r m. read (run_ir ir1 (r,m)) (REG 13) =
			 read (r,m) (REG 13) - n2w (4*s))))  ==>
	 USED_STACK (s+s') (SC ir1 ir2)``,

	REPEAT STRIP_TAC THEN
	`(s:num) + s' = MAX s (s' + s)` by ALL_TAC THEN1 (
		SIMP_TAC std_ss [MAX_DEF] THEN
		Cases_on `0 < s'` THEN ASM_SIMP_TAC arith_ss []
	) THEN
	ASM_REWRITE_TAC[] THEN
	MATCH_MP_TAC IR_SC_USED_STACK THEN
	Q_TAC EXISTS_TAC `s` THEN
	FULL_SIMP_TAC std_ss [])


val IR_SC_UNCHANGED_STACK = store_thm ("IR_SC_UNCHANGED_STACK",
``!ir1 ir2 l s s'.
	(WELL_FORMED ir1 /\ WELL_FORMED ir2 /\
	 UNCHANGED_STACK l s ir1 /\ UNCHANGED_STACK l s' ir2 /\
	 MEM R13 l)  ==>
	 UNCHANGED_STACK l (MAX s s') (SC ir1 ir2)``,


	SIMP_TAC std_ss [UNCHANGED_STACK_def, IR_SC_UNCHANGED] THEN
	REPEAT STRIP_TAC THEN
	`(s <= MAX s s') /\ (s' <= MAX s s')` by SIMP_TAC arith_ss [] THEN
	`(USED_STACK (MAX s s') ir1) /\
	 (USED_STACK (MAX s s') ir2)` by PROVE_TAC [USED_STACK_ENLARGE] THEN
	FULL_SIMP_TAC std_ss [USED_STACK_THM, UNCHANGED_THM, EVERY_MEM,
		SEMANTICS_OF_IR] THEN
	REPEAT STRIP_TAC THEN

	FULL_SIMP_TAC std_ss [read_thm] THEN
	`(read (r,m) (toREG R13) =
    read (run_ir ir1 (r,m)) (toREG R13))` by METIS_TAC[] THEN
	`?r'' m''. run_ir ir1 (r,m) = (r'',m'')` by METIS_TAC[pairTheory.PAIR] THEN
	FULL_SIMP_TAC std_ss [toREG_def, read_thm, index_of_reg_def] THEN
	METIS_TAC[])

val UNCHANGED_STACK_TR_RULE = store_thm ("UNCHANGED_STACK_TR_RULE",
``!c ir l s.
	(WELL_FORMED (TR c ir) /\ UNCHANGED_STACK l s ir /\ MEM R13 l) ==>
	UNCHANGED_STACK l s (TR c ir)``,


  SIMP_TAC std_ss [UNCHANGED_STACK_def] THEN
  REPEAT GEN_TAC THEN
  MATCH_MP_TAC (prove (``((X ==> A) /\ (X /\ A ==> b)) ==> (X ==> (A /\ b))``, METIS_TAC[])) THEN
  STRIP_TAC THEN1 SIMP_TAC std_ss [UNCHANGED_TR_RULE] THEN
  SIMP_TAC std_ss [UNCHANGED_THM, EVERY_MEM, WELL_FORMED_def] THEN
  REPEAT STRIP_TAC THEN
  SIMP_TAC std_ss [USED_STACK_THM] THEN
  NTAC 2 GEN_TAC THEN

  `read (r,m) (toREG R13) = read (run_ir (TR c ir) (r,m)) (toREG R13)` by PROVE_TAC[] THEN
  POP_ASSUM MP_TAC THEN
  POP_ASSUM (fn thm => ALL_TAC) THEN
  `!st. read (run_ir ir st) (toREG R13) = read st (toREG R13)` by PROVE_TAC[pairTheory.PAIR] THEN
  POP_ASSUM MP_TAC THEN
  Q.PAT_ASSUM `!r. MEM r l ==> P r` (fn thm => ALL_TAC) THEN
  ASM_SIMP_TAC std_ss [IR_SEMANTICS_TR___FUNPOW, toREG_def, index_of_reg_def] THEN
  Q.ABBREV_TAC `n = (shortest (eval_il_cond c) (run_ir ir) (r, m))` THEN
  POP_ASSUM (fn x => ALL_TAC) THEN
  FULL_SIMP_TAC std_ss [USED_STACK_THM] THEN
  REPEAT DISCH_TAC THEN
  Induct_on `n` THENL [
	 SIMP_TAC std_ss [FUNPOW],

	 ASM_SIMP_TAC std_ss [FUNPOW_SUC] THEN
	 REPEAT STRIP_TAC THEN
	 `?r'' m''. (FUNPOW (run_ir ir) n (r,m)) = (r'',m'')` by METIS_TAC[pairTheory.PAIR] THEN
	 FULL_SIMP_TAC std_ss [read_thm] THEN
	 METIS_TAC[]
  ]);


val UNCHANGED_STACK___READ_STACK_IMP =
	store_thm ("UNCHANGED_STACK___READ_STACK_IMP",
``!s st l ir n. ((0 < n) /\ (n + l < 2**30) /\ MEM R13 s) ==>
(UNCHANGED_STACK s l ir ==>
(read (run_ir ir st) (toMEM (R13, POS n)) = read st (toMEM (R13, POS n))))``,

REPEAT STRIP_TAC THEN
`read (run_ir ir st) (REG 13) = read st (REG 13)` by ALL_TAC THEN1 (
	FULL_SIMP_TAC std_ss [UNCHANGED_STACK_def, UNCHANGED_THM, EVERY_MEM] THEN
	RES_TAC THEN
	Cases_on `st` THEN
	FULL_SIMP_TAC std_ss [toREG_def, index_of_reg_def]
) THEN

`?r m. run_ir ir st = (r, m)` by METIS_TAC[pairTheory.PAIR] THEN
Cases_on `st` THEN
FULL_SIMP_TAC std_ss [toMEM_def, index_of_reg_def, read_thm,
	UNCHANGED_STACK_def, USED_STACK_def, MEM_MAP, MEM_LIST_COUNT] THEN
Q.PAT_ASSUM `!r''. P r''` (fn thm => MP_TAC (SPECL [
	``q:REGISTER |-> DATA``,
	``r':ADDR |-> DATA``,
	``r:REGISTER |-> DATA``,
	``m:ADDR |-> DATA``] thm)) THEN
ASM_SIMP_TAC std_ss [prove (``(a \/ b) = (~a ==> b)``, PROVE_TAC[])] THEN
STRIP_TAC THEN
POP_ASSUM (fn thm => MATCH_MP_TAC (GSYM thm)) THEN
GEN_TAC THEN
SIMP_TAC std_ss [WORD_EQ_ADD_LCANCEL, word_sub_def, word_2comp_n2w,
	n2w_11, dimword_30] THEN
Cases_on `off < l` THEN ASM_SIMP_TAC std_ss [] THEN
Cases_on `off = 0` THEN
ASM_SIMP_TAC arith_ss [])

val _ = export_theory();
