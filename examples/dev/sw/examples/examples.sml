(* 
 loadPath := ".." :: !loadPath;
*)

use "compiler";

(*---------------------------------------------------------------------------*)
(* Example 1: A simple program						     *)
(* It implements the addition of two word32s                                 *)
(*---------------------------------------------------------------------------*)

val test1_def = Define
  `test1 (t1:word32,t2:word32) =
            (let k1 = UNCURRY $+ (t1,t2) in
	     let k2 = UNCURRY $- (t1,t2) in
                (k1,k2)
            )
    `;
(*
  Name              : test1
  Arguments         : r0 r1 
  Modified Registers: r0 r2 
  Returns           : r2 r0 
  Body: 
    0:          mov     ip, sp
    1:          stmfd   sp!, {fp,ip,lr,pc}
    2:          sub     fp, ip, #1i
    3:          add     r2, r0, r1
    4:          sub     r0, r0, r1
    5:          sub     sp, fp, #3i
    6:          ldmfd   sp, {fp,sp,pc}

  Initial goal:
         !pc0 cpsr0 regs0 pc1 cpsr1 regs1 mems1.
           ((regs0 ' 14 = 7w) /\ (regs0 ' 13 = 100w) /\ (pc0 = 0) /\
            terminated (instB,7) (pc0,cpsr0,regs0,mems0)) /\
           ((pc1,cpsr1,regs1,mems1) =
            terRun (instB,7) (pc0,cpsr0,regs0,mems0)) ==>
           (pc1 = 7) /\
           ((regs1 ' 2,regs1 ' 0) = test1 (regs0 ' 0,regs0 ' 1))

  val arm1 = link2 test1_def;
  
  simT (mk_ARM arm1);

  SEQ_TAC [test1_def];
  
*)

(*---------------------------------------------------------------------------*)
(* Example 2: A functions calls another function                             *)
(* The proving is performed by "unrolling" the callee                        *)
(*---------------------------------------------------------------------------*)

val test2_def = Define
  `test2 (t1:word32,t2:word32) =
            (let (k1,k2) = test1 (t1,t2) in
             let k3 = UNCURRY $* (k1,k2) in
                k3
            )
    `;

(******************************************************************
  Name              : test2
  Arguments         : r0 r1 
  Modified Registers: r0 r1 
  Returns           : r0 
  Body: 
    0:          mov     ip, sp
    1:          stmfd   sp!, {fp,ip,lr,pc}
    2:          sub     fp, ip, #1i
    3:          sub     sp, sp, #2i
    4:          stmfd   sp!, {r0,r1}
    5:          bl      + (7)
    6:          add     sp, sp, #2i
    7:          ldmfd   sp, {r1,r0}
    8:          add     sp, sp, #2i
    9:          mul     r0, r1, r0
   10:          sub     sp, fp, #3i
   11:          ldmfd   sp, {fp,sp,pc}
  *****************************************************************
  Name              : test1
  Arguments         : r0 r1 
  Modified Registers: r0 r2 
  Returns           : r2 r0 
  Body: 
   12:          mov     ip, sp
   13:          stmfd   sp!, {r0,r2,fp,ip,lr,pc}
   14:          sub     fp, ip, #1i
   15:          ldmfd   ip, {r0,r1}
   16:          add     r2, r0, r1
   17:          sub     r0, r0, r1
   18:          add     sp, fp, #5i
   19:          stmfd   sp!, {r2,r0}
   20:          sub     sp, fp, #5i
   21:          ldmfd   sp, {r0,r2,fp,sp,pc}

  or,

  print_structure := false
 
  *****************************************************************
  Name              : test2
  Arguments         : r0 r1 
  Modified Registers: r0 r1 
  Returns           : r0 
  Body: 
    0:          mov     ip, sp
    1:          stmfd   sp!, {fp,ip,lr,pc}
    2:          sub     fp, ip, #1i
    3:          sub     sp, sp, #2i
    4:          stmfd   sp!, {r0,r1}
    5:          bl      + (7)
    6:          add     sp, sp, #2i
    7:          ldmfd   sp, {r1,r0}
    8:          add     sp, sp, #2i
    9:          mul     r0, r1, r0
   10:          sub     sp, fp, #3i
   11:          ldmfd   sp, {fp,sp,pc}
   12:          mov     ip, sp
   13:          stmfd   sp!, {r0,r2,fp,ip,lr,pc}
   14:          sub     fp, ip, #1i
   15:          ldmfd   ip, {r0,r1}
   16:          add     r2, r0, r1
   17:          sub     r0, r0, r1
   18:          add     sp, fp, #5i
   19:          stmfd   sp!, {r2,r0}
   20:          sub     sp, fp, #5i
   21:          ldmfd   sp, {r0,r2,fp,sp,pc}

  val arm2 = link2 test2_def;
  simT (mk_ARM arm2);

  SEQ_TAC [test1_def, test2_def]  
  
*)


(*---------------------------------------------------------------------------*)
(* Example 3: Conditional Jumps                                              *)
(*                                  					     *)
(*---------------------------------------------------------------------------*)



(*---------------------------------------------------------------------------*)
(* Example 4: Tail Recursive Functions					     *)
(* This example works on the Factorial Function                              *)
(*---------------------------------------------------------------------------*)

val (f6_def, f6_ind) = Defn.tprove
 (Hol_defn
   "f6"
   `f6 (x,a) = if x=0w then a else f6(x-1w,x*a)`,
  WF_REL_TAC `measure (w2n o FST)` THEN METIS_TAC [WORD_PRED_THM] );

(******************************************************************
  Name              : f6
  Arguments         : r0 r1 
  Modified Registers: r0 r2 r3 
  Returns           : r0 
  Body: 
    0:          mov     ip, sp
    1:          stmfd   sp!, {fp,ip,lr,pc}
    2:          sub     fp, ip, #1i
    3:          cmp     r0, #0iw
    4:          beq     + (7)
    5:          sub     r3, r0, #1iw
    6:          mul     r2, r0, r1
    7:          stmfd   sp!, {r3,r2}
    8:          ldmfd   sp, {r0,r1}
    9:          add     sp, sp, #2i
   10:          bal     - (7)
   11:          mov     r0, r1
   12:          sub     sp, fp, #3i
   13:          ldmfd   sp, {fp,sp,pc}

 Initial goal:
     !pc0 cpsr0 regs0 pc1 cpsr1 regs1 mems1.
           ((regs0 ' 14 = 14w) /\ (regs0 ' 13 = 100w) /\ (pc0 = 0) /\
            terminated (instB,14) (pc0,cpsr0,regs0,mems0)) /\
           ((pc1,cpsr1,regs1,mems1) =
            terRun (instB,14) (pc0,cpsr0,regs0,mems0)) ==>
           (pc1 = 14) /\ (regs1 ' 0 = f6 (regs0 ' 0,regs0 ' 1))


    val env6 = toANF [] f6_def;
    val arm6 = compileEnv env6;
	
    simT (mk_ARM arm6);


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
  REPEAT VAR_EQ_TAC

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
(*
REPEAT VAR_EQ_TAC THEN REPEAT (POP_ASSUM (K ALL_TAC))
THEN SIMP_TAC std_ss [FUN_EQ_THM] 
THEN GEN_TAC THEN 
REPEAT (COND_CASES_TAC THEN TRY (VAR_EQ_TAC THEN REDUCE_TAC))
THEN REWRITE_TAC []
*)
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
(* Example 5: Calling a recursive function				     *) 
(* In this example, the Factorial Function is called                         *)
(*---------------------------------------------------------------------------*)


val f7_def = Define
   `f7 x =  
	let t = f6 (x-1w, 1w) in
	let k = t + t in
	k`;
