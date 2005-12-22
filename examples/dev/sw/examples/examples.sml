
(* For interactive work *)
 loadPath := "cps/" :: !loadPath;

  quietdec := true;
  app load ["word32Theory","ANF"];
  open word32Theory pairTheory arithmeticTheory ANF;
  quietdec := false;

(*---------------------------------------------------------------------------*)
(* Addition 	                                                             *)
(*---------------------------------------------------------------------------*)

val test0_def = Define
  `test0 (t1:word32,t2:word32,t3:word32,t4:word32,t5:word32,t6:word32) =
            (let k1 = UNCURRY $+ (t1,t5) in
             let k2 = UNCURRY $- (k1, t6) in
                (k1,k2,t5,t6)
            )
    `;


val test0a_def = Define
  `test0a (t1,t2) =
            (let (k1,k2,k3,k4) = test0 (t1,t2,t1,t2,t1,t2) in
                (k1,k2)
            )
    `;


val test1_def = Define
  `test1 (t1:word32,t2:word32) =
            (let k1 = UNCURRY $+ (t1,t2) in
	     let k2 = UNCURRY $- (t1,t2) in
                (k1,k2)
            )
    `;

val test2_def = Define
  `test2 (t1:word32,t2:word32) =
            (let (k1,k2) = test1 (t1,t2) in
             let k3 = UNCURRY $* (k1,k2) in
                k3
            )
    `;


val test3_def = Define
  `test3 (t1:word32,t2:word32,t3:word32,t4:word32,t5:word32,t6:word32) =
            (let k1 = UNCURRY $+ (t1,t5) in
	     let (k2,k3) = test1 (k1, t6) in
                (k2,k3)
            )
    `;



(*
    val arm1 = link2 test1_def;
    printarm arm1;
    val ARM1 = mk_ARM arm1;

        simT ARM1;

    TAC0 [] THEN
    REPEAT STRIP_TAC THEN 
    IMP_RES_TAC (Q.SPEC `3` TERRUN_THM) THEN 	(* could be any number larger than 3 *)
    ONCE_ASM_REWRITE_TAC [] THEN    
    POP_ASSUM (K ALL_TAC) THEN
    NTAC 3 TAC1 THEN
    RW_TAC list_ss [TERRUN_STOP, test1_def,run_def]
    

*)

(*---------------------------------------------------------------------------*)
(* Factorial Function                                                        *)
(*---------------------------------------------------------------------------*)

val (f6_def, f6_ind) = Defn.tprove
 (Hol_defn
   "f6"
   `f6 (x,a) = if x=0w then a else f6(x-1w,x*a)`,
  WF_REL_TAC `measure (w2n o FST)` THEN METIS_TAC [WORD_PRED_THM] );

(*
Name: f6
Arguments:
    R3 R1
Body:
    0:        MOV R0, 0w
    1:        CMP R0, R3, R0
    2:        BEQ +(10)
    3:        MOV R0, 1w
    4:        SUB R2, R3, R0
    5:        MUL R0, R3, R1
    6:        STR R2, [0]
    7:        STR R0, [1]
    8:        LDR R1, [1]
    9:        LDR R3, [0]
   10:        BL -(10)
   11:        BAL +(2)
   12:        MOV R0, R1
   13:        SWI 17
Return:
    R0 
*)


(*
    val env6 = toANF [] f6_def;
    val arm6 = compileEnv env6;
    val ARM6 = mk_ARM arm6;
	
	simT ARM6;

val thm = fetch "-" "instB_def";

val instB_thm = Q.prove
(`(instB 0 =  ((MOV,NONE,F),SOME (REG 12),[REG 13],NONE)) /\
  (instB 1 = ((STMFD,NONE,F),SOME (WREG 13), [REG 0; REG 2; REG 3; REG 11; REG 12; REG 14; REG 15],NONE)) /\
  (instB 2 = ((SUB,NONE,F),SOME (REG 11),[REG 12; NCONST 1], NONE)) /\
  (instB 3 = ((MOV,NONE,F),SOME (REG 2),[WCONST 0w],NONE)) /\
  (instB 4 = ((CMP,NONE,F),NONE,[REG 0; REG 2],NONE)) /\
  (instB 5 = ((B,SOME EQ,F),NONE,[REG 2],SOME (POS 8))) /\
  (instB 6 = ((MOV,NONE,F),SOME (REG 2),[WCONST 1w],NONE)) /\
  (instB 7 = ((SUB,NONE,F),SOME (REG 3), [REG 0; REG 2],NONE)) /\
  (instB 8 = ((MUL,NONE,F),SOME (REG 2), [REG 0; REG 1],NONE)) /\
  (instB 9 = ((STMFD,NONE,F),SOME (WREG 13), [REG 3; REG 2],NONE)) /\
  (instB 10 = ((LDMFD,NONE,F),SOME (REG 13),[REG 0; REG 1],NONE)) /\
  (instB 11 = ((ADD,NONE,F),SOME (REG 13),[REG 13; NCONST 2],NONE)) /\
  (instB 12 = ((B,SOME AL,F),NONE,[],SOME (NEG 9))) /\
  (instB 13 = ((MOV,NONE,F),SOME (REG 0),[REG 1],NONE)) /\
  (instB 14 = ((SUB,NONE,F),SOME (REG 13),[REG 11; NCONST 5],NONE)) /\
  (instB 15 = ((LDMFD,NONE,F),SOME (REG 13), [REG 0; REG 2; REG 3; REG 11; REG 13; REG 15],SOME INR))`
,
 REPEAT CONJ_TAC THEN EVAL_TAC); 

  TAC0 [] THEN
  Induct_on `w2n Ir3` THEN REPEAT STRIP_TAC THENL [
	`Ir3 = 0w` by RW_TAC list_ss [w2n_ELIM] THEN
	RW_TAC list_ss [Q.SPEC `15` TERRUN_THM] THEN
	PAT_ASSUM ``0 = w2n Ir3`` (K ALL_TAC) THEN 
	NTAC 6 TAC1 THEN
	RW_TAC list_ss [TERRUN_STOP, Once f6_def],

	`(v = w2n (reg0 3 - 1w)) /\ ~(reg0 3 = 0w) /\ ~(reg0 3 < 0w)` by REWRITE_TAC [] THENL [
		...
		...
	

	RW_TAC list_ss [Q.SPEC `11` TERRUN_THM] THEN

	`?pc' cpsr' reg' mem'. (pc',cpsr',reg',mem') = run 11 (instB,14) (0,cpsr0,reg0,mem0)` by ALL_TAC THENL [
	    Q.ABBREV_TAC `s' = run 11 (instB,14) (0,cpsr0,reg0,mem0)` THEN
	    `s' = (FST s', FST (SND s'), FST (SND (SND s')), SND (SND (SND s')))` by METIS_TAC [PAIR] THEN 
	    METIS_TAC [],

	`terminated (instB,14) (pc',cpsr',reg',mem') /\ 
		(w2n (reg' 14) = 14) /\ (pc' = 0) /\ (reg' 3 = reg0 3 - 1w) /\ (reg' 1 = reg0 3 * reg0 1)` by ALL_TAC THENL [
		STRIP_TAC THENL [
			RW_TAC list_ss [TERMINATED_THM],
			POP_ASSUM MP_TAC THEN
			FULL_SIMP_TAC list_ss [WORD_ADD_SUB, w2n_11] THEN
			NTAC 12 TAC1 THEN RW_TAC list_ss []
		]
	
		FULL_SIMP_TAC list_ss [w2n_11] THEN
		RW_TAC list_ss [Once f6_def] THEN

		RES_TAC THEN
		NTAC 6 (POP_ASSUM (K ALL_TAC)) THEN 
		POP_ASSUM MP_TAC THEN 
		PAT_ASSUM ``(0,cpsr',reg',mem') = run 11 (instB,14) (0,cpsr0,reg0,mem0)`` (ASSUME_TAC o SYM) THEN
		ONCE_ASM_REWRITE_TAC [] THEN 
		Q.ABBREV_TAC `ss = terRun (instB,14) (0,cpsr',reg',mem')` THEN
		`ss = (FST ss, FST (SND ss), FST (SND (SND ss)), SND (SND (SND ss)))` by METIS_TAC [PAIR] THEN

		REWRITE_TAC [LET_THM] THEN
		ONCE_ASM_REWRITE_TAC [] THEN
		GEN_BETA_TAC THEN RW_TAC list_ss []
		]]		    

*)		


(*---------------------------------------------------------------------------*)
(* Factorial Function                                                        *)
(*---------------------------------------------------------------------------*)


val (f7_def, f7_ind) = Defn.tprove
 (Hol_defn
   "f7"
   `f7 (x:num,a:num) = if x=0 then a else 
	let k = x + 1 in f7(x-1,k*a)`,
  WF_REL_TAC `measure FST`);

