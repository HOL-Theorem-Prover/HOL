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

    simT (mk_ARM arm1);

    prove_arm [test1_def];

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

*)


(*
    val env6 = toANF [] f6_def;
    val arm6 = compileEnv env6;
	
    simR (mk_ARM arm6);


  REWRITE_TAC [read_thm] THEN
  REPEAT STRIP_TAC THEN
  
  Induct_on `w2n (regs0 0)` THEN REPEAT STRIP_TAC THENL [
	`regs0 0 = n2w 0` by METIS_TAC [w2n_ELIM] THEN
	Q.PAT_ASSUM  `0 = i` (K ALL_TAC) THEN
	IMP_RES_TAC (SPEC ``15`` TERRUN_THM) THEN
  	ONCE_ASM_REWRITE_TAC [] THEN
  	POP_ASSUM (K ALL_TAC)
	(*
	prove_arm [Once f6_def],	(* This would prove the basic case *)
	*)

	IMP_RES_TAC WORD_IND_LEM THEN
	IMP_RES_TAC (SPEC ``13`` TERRUN_THM) THEN
        ONCE_ASM_REWRITE_TAC [] THEN
        POP_ASSUM (K ALL_TAC) THEN
	`?pc' cpsr' reg' mem'. (pc',cpsr',reg',mem') = run 13 (instB,16) (0,cpsr0,regs0,mems0)` 
		by METIS_TAC [ABS_PAIR_THM] THEN

	`terminated (instB,16) (pc',cpsr',reg',mem') /\ 
		((pc' = 3) /\ (reg' 3 = regs0 3 - 1w) /\ (reg' 1 = regs0 3 * regs0 1)` by 
							ALL_TAC THENL [
		STRIP_TAC THENL [
			RW_TAC list_ss [TERMINATED_THM],
			POP_ASSUM MP_TAC THEN
			FULL_SIMP_TAC list_ss [WORD_ADD_SUB, w2n_11] THEN
			...			


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

