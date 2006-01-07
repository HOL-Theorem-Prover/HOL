use "compiler";

(*---------------------------------------------------------------------------*)
(* Addition 	                                                             *)
(*---------------------------------------------------------------------------*)

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

Arguments:
    r0 r1
Body:
    0:          mov     ip, sp
    1:          stmfd   sp!, {fp,ip,lr,pc}
    2:          sub     fp, ip, #1
    3:          add     r2, r0, r1
    4:          sub     r0, r0, r1
    5:          sub     sp, fp, #2
    6:          ldmfd   sp, {fp,sp,pc}
Return:
    r2 r0 

Initial goal:
         !pc0 cpsr0 regs0 mems0.
           (regs0 14 = 7w) /\ (regs0 13 = 100w) /\ (pc0 = 0) /\
           terminated (instB,7) (pc0,cpsr0,regs0,mems0) ==>
           (let (pc1,cpsr1,regs1,mems1) =
                  terRun (instB,7) (pc0,cpsr0,regs0,mems0)
            in
              ((pc1 = 7) /\ T) /\
              ((read (regs1,mems1) (REG 2),read (regs1,mems1) (REG 0)) =
               test1
                 (read (regs0,mems0) (REG 0),read (regs0,mems0) (REG 1))))


    simT (mk_ARM arm1);

    ARM_TAC [test1_def];

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
Arguments:
    r0 r1
Body:
    0:          mov     ip, sp
    1:          stmfd   sp!, {fp,ip,lr,pc}
    2:          sub     fp, ip, #1
    3:          mov     r2, #0w
    4:          cmp     r0, r2
    5:          beq     + (8)
    6:          mov     r2, #1w
    7:          sub     r3, r0, r2
    8:          mul     r2, r0, r1
    9:          stmfd   sp!, {r3,r2}
   10:          ldmfd   sp, {r0,r1}
   11:          add     sp, sp, #2
   12:          bal     - (9)
   13:          mov     r0, r1
   14:          sub     sp, fp, #2
   15:          ldmfd   sp, {fp,sp,pc}
Return:
    r0

 Initial goal:
         !pc0 cpsr0 regs0 mems0.
           (regs0 14 = 16w) /\ (regs0 13 = 100w) /\ (pc0 = 0) /\
           terminated (instB,16) (pc0,cpsr0,regs0,mems0) ==>
           (let (pc1,cpsr1,regs1,mems1) =
                  terRun (instB,16) (pc0,cpsr0,regs0,mems0)
            in
              ((pc1 = 16) /\ T) /\
              (read (regs1,mems1) (REG 0) =
               f6 (read (regs0,mems0) (REG 0),read (regs0,mems0) (REG 1))))

*)


(*
    val env6 = toANF [] f6_def;
    val arm6 = compileEnv env6;
	
    simT (mk_ARM arm6);

  simT (mk_ARM arm6),


  The proof:

val fact_tac = 

  REWRITE_TAC [read_thm] THEN
  REPEAT STRIP_TAC THEN

        (*  Process the first three instructions :
		    0:          mov     ip, sp
		    1:          stmfd   sp!, {fp,ip,lr,pc}
    		    2:          sub     fp, ip, #1
        *)

  `?pc' cpsr' regs' mems'. run 3 (instB,16) (pc0,cpsr0,regs0,mems0) = (pc',cpsr',regs',mems')` 
		by METIS_TAC [ABS_PAIR_THM] THEN
  `terminated (instB,16) (pc',cpsr',regs',mems')` by METIS_TAC [TERMINATED_THM] THEN
  `terRun (instB,16) (0,cpsr0,regs0,mems0) = terRun (instB,16) (pc',cpsr',regs',mems')` by METIS_TAC [TERRUN_THM] THEN
  ASM_REWRITE_TAC [] THEN 

  Q.PAT_ASSUM `run 3 (instB,16) x = y` MP_TAC THEN    
  NTAC 3 ONE_STEP_TAC THEN
  REWRITE_TAC [run_def] THEN STRIP_TAC THEN 

  POP_ASSUM (ASSUME_TAC o SYM) THEN 
  FULL_SIMP_TAC std_ss [] THEN
  NTAC 5 (POP_ASSUM (K ALL_TAC)) THEN

  	(*  Process the recursive body			*)

  `!cpsr mems. ?k. let (pc',cpsr',regs',mems') = run k (instB,16) (3,cpsr,
				(\k. k = 15 => 3w | k = 11 => 99w | k = 13 => 96w | k = 12 => 100w | regs0 k), mems) in
	   			(pc' = 14) /\  (regs' 0 = f6(regs0 0,regs0 1)) /\ 
	   			(regs' 11 = 99w) /\ (regs' 12 = 100w) /\ (regs' 13 = 96w)` by ALL_TAC THENL [

	NTAC 5 (POP_ASSUM (K ALL_TAC)) THEN	
	Induct_on `w2n (regs0 0)` THEN REPEAT STRIP_TAC THENL [

		(* Basic case					*)

		`regs0 0 = n2w 0` by METIS_TAC [w2n_ELIM] THEN
		Q.PAT_ASSUM  `0 = i` (K ALL_TAC) THEN
		Q.EXISTS_TAC `4` THEN 
		NTAC 4 ONE_STEP_TAC THEN REWRITE_TAC [Once f6_def, run_def] THEN
		RW_TAC list_ss [ABS_PAIR_THM],

                (* Inductive case                                   *)

		FULL_SIMP_TAC list_ss [GSYM RIGHT_FORALL_IMP_THM] THEN
		`?pc1 cpsr1 regs1 mems1. run 10 (instB,16) (3,cpsr,(\k. k = 15 => 3w | k = 11 => 99w | k = 13 => 96w | k 
					= 12 => 100w | regs0 k),mems) = (pc1,cpsr1,regs1,mems1)`
                        by METIS_TAC [ABS_PAIR_THM] THEN
		PAT_ASSUM ``!regs01 cpsr mems.x`` (ASSUME_TAC o Q.SPECL [`regs1`,`cpsr1`,`mems1`]) THEN 
		FULL_SIMP_TAC list_ss [GSYM RIGHT_EXISTS_IMP_THM] THEN
 
		Q.EXISTS_TAC `10 + k` THEN REWRITE_TAC [RUN_THM_1] THEN 
		Q.ABBREV_TAC `runf = run k (instB,16)` THEN ASM_REWRITE_TAC [] THEN 

		IMP_RES_TAC WORD_IND_LEM THEN
		Q.PAT_ASSUM `run 10 (instB,16) x = y` (MP_TAC) THEN
		NTAC 10 ONE_STEP_TAC THEN
		REWRITE_TAC [Once run_def] THEN STRIP_TAC THEN

		PAT_ASSUM (Term `v = w2n (regs0 0 - 1w)`) (ASSUME_TAC o WORD_RULE) THEN
		`v = w2n (regs1 0)` by RW_TAC list_ss [] THEN reduceLib.REDUCE_TAC THEN
		FULL_SIMP_TAC list_ss [ABS_PAIR_THM] THEN 

		`(\k1. k1 = 15 => n2w pc1 | k1 = 11 => 99w | k1 = 13 => 96w | k1 = 12 => 100w | regs1 k1) = regs1` by 
			RW_TAC arith_ss [FUN_EQ_THM] THENL [
				NTAC 6 (POP_ASSUM (K ALL_TAC)) THEN RW_TAC arith_ss [] THEN
				FULL_SIMP_TAC arith_ss [],  

			REWRITE_TAC [Once f6_def] THEN
			WORD_TAC THEN
			`(regs1 0 = regs0 0 + 4294967295w) /\ (regs1 1 = regs0 0 * regs0 1)` by RW_TAC arith_ss [] THEN
			FULL_SIMP_TAC list_ss [ABS_PAIR_THM, LET_THM]
			]
		],
	
	(*  Process the last two instructions :
		  14:          sub     sp, fp, #2
   		  15:          ldmfd   sp, {fp,sp,pc}
	*)

	POP_ASSUM (STRIP_ASSUME_TAC o REWRITE_RULE [LET_THM] o (Q.SPECL [`cpsr0`, `(\addr. addr = 97 => regs0 11
             				| addr = 98 => 100w
               				| addr = 99 => 16w | addr = 100 => 1w | mems0 addr)`])) THEN
	Q.PAT_ASSUM `terminated (instB,16) (pc0,cpsr0,regs0,mems0)` (K ALL_TAC) THEN 
	IMP_RES_TAC (Q.SPEC `k` TERRUN_THM) THEN
	POP_ASSUM (ASSUME_TAC o Q.SPEC `k`) THEN 
  	ONCE_ASM_REWRITE_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN	

        `?pc1 cpsr1 regs1 mems1. run k (instB,16)
               (3,cpsr0, (\k. k = 15 => 3w | k = 11 => 99w | k = 13 => 96w | k = 12 => 100w | regs0 k),
                (\addr. addr = 97 => regs0 11 | addr = 98 => 100w | addr = 99 => 16w | addr = 100 => 1w | mems0 addr)) 
			= (pc1,cpsr1,regs1,mems1)` by METIS_TAC [ABS_PAIR_THM] THEN
	`terminated (instB,16) (pc1,cpsr1,regs1,mems1)` by METIS_TAC [TERMINATED_THM] THEN
	FULL_SIMP_TAC list_ss [] THEN
	`terRun (instB,16) (14,cpsr1,regs1,mems1) =
           terRun (instB,16) (run 2 (instB,16) (pc1,cpsr1,regs1,mems1))` by METIS_TAC [TERRUN_THM] THEN
  	ONCE_ASM_REWRITE_TAC [] THEN
  	POP_ASSUM (K ALL_TAC) THEN
  	NTAC 2 ONE_STEP_TAC THEN
  	RW_TAC std_ss [run_def, TERRUN_STOP]
    ] 		

*)
(*---------------------------------------------------------------------------*)
(* Calling the Factorial Function                                            *)
(*---------------------------------------------------------------------------*)


val (f7_def, f7_ind) = Defn.tprove
 (Hol_defn
   "f7"
   `f7 (x:num,a:num) = if x=0 then a else 
	let k = x + 1 in f7(x-1,k*a)`,
  WF_REL_TAC `measure FST`);

