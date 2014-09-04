open HolKernel boolLib bossLib Parse proofManagerLib;
open arm_coretypesTheory arm_seq_monadTheory arm_opsemTheory arm_stepTheory;
open MMUTheory MMU_SetupTheory inference_rulesTheory switching_lemma_helperTheory
	       tacticsLib ARM_prover_extLib;

val _ =  new_theory("priv_constraints_lr");


(****************************************************************)
(*         CONSTRAINTS ON LINK REGISTER IN PRIVILEGED MODE       *)
(*                        Narges                                *)
(****************************************************************)

val let_ss = simpLib.mk_simpset [boolSimps.LET_ss] ;
val _ = goalStack.chatting := !Globals.interactive

val prove_abs_LR_const_action =
 fn (a, thms, abody_thm, expr) =>
    let
	val _ =  set_goal([], ``
    			 (priv_LR_constraints_abs ^a ^expr (mode:bool[5]) ) ``)
	val (a_abs,a_body) = pairLib.dest_pabs a;
	val unbeta_thm= (PairRules.UNPBETA_CONV a_abs a_body)
	val unbeta_a = mk_comb (a, a_abs)
	val snd = get_type_inst (type_of(a_body) , false)
	val a_body_type = get_type_inst (snd, true);
	val proved_unbeta_lemma = prove(
					     ``(priv_LR_constraints ^a_body ^expr mode)=
				  (priv_LR_constraints ^unbeta_a ^expr mode)``,
					     (ASSUME_TAC (SPECL [a_body,``^unbeta_a``, expr,``mode:bool[5]``]
								(INST_TYPE [beta |-> a_body_type,
									    alpha |-> ``:arm_state``]
									   (List.nth(thms,0)))))
						 THEN ASSUME_TAC unbeta_thm
						 THEN RES_TAC);

	val proved_preserve_unbeta_a =
	    prove(`` (priv_LR_constraints ^unbeta_a ^expr mode )``,
		       (ASSUME_TAC (proved_unbeta_lemma))
			   THEN (ASSUME_TAC abody_thm)
			   THEN (FULL_SIMP_TAC (srw_ss()) []));

	val abs_type = type_of a_abs
	val (abs_args, abs_body)  = generate_uncurry_abs a
	val tacs =  (ASSUME_TAC proved_preserve_unbeta_a)
	val gen_preserve_unbeta_thm = generalize_theorem proved_preserve_unbeta_a a;
	val tacs = tacs THEN (ASSUME_TAC gen_preserve_unbeta_thm)
			THEN (ASSUME_TAC (
			      SPECL[a, expr,``mode:bool[5]``]
				   (INST_TYPE [alpha |-> abs_type,
					       beta  |-> ``:arm_state``,
					       gamma |-> a_body_type]
					      (List.nth(thms,1)))))
			THEN (RW_TAC (srw_ss()) [])
			THEN (FULL_SIMP_TAC (srw_ss()) [])
			THEN (UNDISCH_ALL_TAC THEN
					      (RW_TAC (srw_ss()) [])
					      THEN (FULL_SIMP_TAC (srw_ss()) []))
	val _ = e (tacs)
	val proved_thm = top_thm()
	val _ = proofManagerLib.drop();
    in
	(proved_thm,tacs)
    end

val untouched_LR_abs_def =
    Define `untouched_LR_abs f mode  =
	   !s a c s'. (f a s = ValueState c s') ==>
	   let lr = get_lr_by_mode mode
	    	 in
    	       (((s'.psrs (0,CPSR)).M=(s.psrs (0,CPSR)).M) /\
                (s'.registers (0, lr) =
		s.registers (0, lr)))`;

val untouched_LR_def =
    Define `untouched_LR f mode =
	   !s c s'. (f s = ValueState c s') ==>
              (* (ARM_MODE s' = 19w) ==> *)
	   let lr = get_lr_by_mode mode
	    	 in
    	       (((s'.psrs (0,CPSR)).M=(s.psrs (0,CPSR)).M) /\
                (s'.registers (0, lr) =
		s.registers (0, lr)))`;

val priv_LR_constraints_def =
    Define `priv_LR_constraints f lr_value mode =
	    ! s s' a . (f s = ValueState a s') ==>
	        (~access_violation s') ==>
    	       ((s'.psrs (0,CPSR)).M= mode) ==>
	    let lr = get_lr_by_mode mode
	    in
    	  	(*((s'.psrs(0,CPSR)).M = 19w) ==>*)
		((s'.registers (0, lr) =
		  lr_value))`;


val priv_LR_constraints_abs_def =
    Define `priv_LR_constraints_abs f lr_value mode =
		! s s' a c. (f c s = ValueState a s') ==>
	        (~access_violation s') ==>
    	       ((s'.psrs (0,CPSR)).M= mode) ==>
	    let lr = get_lr_by_mode mode
	    in
    	  	(*((s'.psrs(0,CPSR)).M = 19w) ==>*)
		((s'.registers (0, lr) =
		  lr_value))`;


(*********************   proof rules *******************************)

val seqT_priv_LR_constraints_before_thm =
    store_thm("seqT_priv_LR_constraints_before_thm",
	      `` ! g f pc mode . priv_LR_constraints_abs f pc mode  ==>
	     priv_LR_constraints (g >>= f) pc  mode ``,
	      (RW_TAC (srw_ss()) [seqT_def,
				  priv_LR_constraints_def,
				  priv_LR_constraints_abs_def])
		  THEN FULL_SIMP_TAC (let_ss) []
		  THEN ASSUME_TAC
		  (SPECL [``g:'a M``, ``f: 'a -> 'b M``,
			  ``s:arm_state``,``a:'b``,
			  ``s':arm_state``(* ,``b:arm_state``, *)
			 (* ``a':'a`` *)]
			 seqT_access_violation_thm)
		  THEN FULL_SIMP_TAC (srw_ss()) [seqT_def]
		  THEN Cases_on `g s`
		  THEN FULL_SIMP_TAC (srw_ss()) []
		  THEN Cases_on `access_violation b`
		  (* THEN Q.UNABBREV_TAC `spsr` *)
		  THEN PAT_ASSUM ``! s s' a c .X ==> Z``
		  (fn thm => ASSUME_TAC
				 (SPECL [``b:arm_state``,``s':arm_state``,
					 ``a:'b``,``a':'a``] thm))
		  THEN FULL_SIMP_TAC (srw_ss()) []
		  THEN RES_TAC
		  THEN FULL_SIMP_TAC (srw_ss()) [seqT_def]
	     );

val parT_priv_LR_constraints_before_thm =
    store_thm("parT_priv_LR_constraints_before_thm",
	      `` ! g f pc mode . priv_LR_constraints f pc mode ==>
	     priv_LR_constraints (g ||| f) pc mode ``,
	      RW_TAC (srw_ss())
		      [parT_def,seqT_def,
		       priv_LR_constraints_def,
		       untouched_LR_def,constT_def]
		  THEN FULL_SIMP_TAC (let_ss) []
		  THEN IMP_RES_TAC
		  (SIMP_RULE bool_ss
			     [seqT_def,parT_def,constT_def]
			     (SPECL [``g:'a M``, ``f: 'b M``,
				     ``s:arm_state``,``a:('a#'b)``,
				     ``s':arm_state`` ,``b:arm_state``,
				     ``a':'a``  ]
				    parT_access_violation_thm))
		  THEN Cases_on `g s`
		  THEN Cases_on `f b`
		  (* THEN Q.UNABBREV_TAC `spsr`  *)
		  THEN FULL_SIMP_TAC (srw_ss()) []
		  THEN PAT_ASSUM ``! s s' a  .(f s = ValueState a s') ==> Z`` (fn thm => ASSUME_TAC
		  (SPECL [``b:arm_state``,``b':arm_state``,``a'':'b``] thm))
		  THEN Cases_on `access_violation b`
		  THEN Cases_on `access_violation b'`
		  THEN RES_TAC
		  THEN FULL_SIMP_TAC (srw_ss()) []
		  THEN FIRST_PROVE [ FULL_SIMP_TAC (srw_ss()) []
						   THEN RW_TAC (srw_ss()) [] ,
				     (UNDISCH_ALL_TAC
					  THEN  RW_TAC (srw_ss()) []
					  THEN FULL_SIMP_TAC (srw_ss()) [])]);

val seqT_priv_LR_constraints_after_thm =
    store_thm("seqT_priv_LR_constraints_after_thm",
	      `` ! g f pc mode .
	     priv_LR_constraints g pc  mode ==>
	     (  untouched_LR_abs f mode ) ==>
	     priv_LR_constraints (g >>= f) pc mode ``,
	      (RW_TAC (srw_ss()) [seqT_def,
				  priv_LR_constraints_def,
				  priv_LR_constraints_abs_def,
				  untouched_LR_abs_def]) THEN
			FULL_SIMP_TAC (let_ss) [] THEN
			Cases_on `g s` THEN
			FULL_SIMP_TAC (srw_ss()) [] THEN
			Cases_on `access_violation b`
			THEN Q.UNABBREV_TAC `lr`
			THEN PAT_ASSUM ``! s s' a  .X ==> Z``
			(fn thm => ASSUME_TAC
				       (SPECL [``s:arm_state``,``b:arm_state``,
					       ``a':'a``] thm))

			THEN PAT_ASSUM ``! s1 a c s2. X``
			(fn thm => ASSUME_TAC
				       (SPECL [``b:arm_state``,``a':'a``,
					       ``a:'b``,``s':arm_state``] thm))

			THEN RES_TAC
			THEN UNDISCH_ALL_TAC
			THEN RW_TAC (srw_ss()) []
			THEN FULL_SIMP_TAC (srw_ss()) [get_lr_by_mode_def]
			THEN FULL_SIMP_TAC (srw_ss()) []);

val parT_priv_LR_constraints_after_thm =
    store_thm("parT_priv_LR_constraints_after_thm",
`` ! g f pc mode . priv_LR_constraints g pc mode ==>
	     (untouched_LR f mode ) ==>
	     priv_LR_constraints (g ||| f) pc mode ``,
	      (RW_TAC (srw_ss())
		      [parT_def,seqT_def,
		       priv_LR_constraints_def,
		       untouched_LR_def,constT_def])
		  THEN FULL_SIMP_TAC (let_ss) []THEN
		  Cases_on `g s` THEN
		  Cases_on `f b` THEN
		  Cases_on `access_violation b` THEN
		  Cases_on `access_violation b'`   THEN
		   Q.UNABBREV_TAC `lr` THEN
		  FULL_SIMP_TAC (srw_ss()) [] THEN
		  PAT_ASSUM ``! s a s' .(f s = ValueState a s') ==> Z``
		  (fn thm => ASSUME_TAC
				 (SPECL [``b:arm_state``,``a'':'b``,``b':arm_state``] thm))
		  THEN PAT_ASSUM ``! s1 c s2. X``
		  (fn thm => ASSUME_TAC
				 (SPECL [``s:arm_state``,``b:arm_state``,``a':'a``] thm))
		  THEN RES_TAC
		  THEN UNDISCH_ALL_TAC
		  THEN  RW_TAC (srw_ss()) []
		  THEN  FULL_SIMP_TAC (srw_ss()) [get_lr_by_mode_def]
		);


val seqT_LR_trans_untouched_thm =
    store_thm("seqT_LR_trans_untouched_thm",
	      `` !f g mode .
	     (untouched_LR f mode ) ==>
	     (untouched_LR_abs g mode ) ==>
	     (untouched_LR (f>>=g) mode)``,
	      (RW_TAC (srw_ss()) [seqT_def,untouched_LR_abs_def,
				  untouched_LR_def])
THEN Cases_on `f s`
		  THEN FULL_SIMP_TAC (let_ss) []
		  THEN PAT_ASSUM ``! s1 c s2. (f s = ValueState c s') ==> X``
		  (fn thm => ASSUME_TAC
				 (SPECL [``s:arm_state``,``a:'a``,``b:arm_state``] thm))
		  THEN RES_TAC
		  THEN Cases_on `access_violation b`
		  THEN FULL_SIMP_TAC (srw_ss()) []
		  THEN RW_TAC (srw_ss()) []
		  THEN PAT_ASSUM ``! s a c s'. X``
		  (fn thm => ASSUME_TAC
				 (SPECL [``b:arm_state``,``a:'a``,
					 ``c:'b``,``s':arm_state``] thm))
		  THEN RES_TAC
		  THEN FULL_SIMP_TAC (srw_ss()) []
		  THEN RW_TAC (srw_ss()) []);

val parT_LR_trans_untouched_thm =
    store_thm("parT_LR_trans_untouched_thm",
	      `` !f g mode.
	     (untouched_LR f mode ) ==>
	     (untouched_LR g mode ) ==>
	     (untouched_LR (f ||| g) mode )``,
	      (RW_TAC (srw_ss()) [seqT_def,parT_def,constT_def,
				  untouched_LR_def])
		  THEN Cases_on `f s`
		  THEN Cases_on `access_violation b`
		  THEN Cases_on `g b`
		  THEN Cases_on `access_violation b'`
		  THEN FULL_SIMP_TAC (let_ss) []
		  THEN PAT_ASSUM ``! s c s'. X``
		  (fn thm => ASSUME_TAC
				 (SPECL [``b:arm_state``,``a':'b``,
					 ``b':arm_state``] thm))
		  THEN PAT_ASSUM ``! s1 c s2. (f s = ValueState c s') ==> X``
		  (fn thm => ASSUME_TAC
				 (SPECL [``s:arm_state``,``a:'a``,``b:arm_state``] thm))
		  THEN RES_TAC
		  THEN FULL_SIMP_TAC (srw_ss()) []
		  THEN RW_TAC (srw_ss()) []
		  );


val LR_first_abs_lemma =
    store_thm ("LR_first_abs_lemma",
	       ``!f g x mode . (f=g) ==> ((priv_LR_constraints f x mode) =
				    (priv_LR_constraints g x mode))``,
	       RW_TAC (srw_ss()) []);


val LR_second_abs_lemma =
    store_thm ("LR_second_abs_lemma",
	       ``! f x mode . (! y. priv_LR_constraints (f y) x mode ) =
    priv_LR_constraints_abs f x mode ``,
	       RW_TAC (srw_ss()) [priv_LR_constraints_def,priv_LR_constraints_abs_def]
		      THEN METIS_TAC []);


(********************* end of proof rules *******************************)
(******************* basic lemmas **************************************)

val read_cpsr_fixed_lem =
    store_thm("read_cpsr_fixed_lem",
``!s . read_cpsr <|proc := 0|> s = ValueState (s.psrs (0,CPSR)) s``,
	      EVAL_TAC
		  THEN RW_TAC (srw_ss()) []);

val write_lr_reg_lrc_thm =
    store_thm("write_lr_reg_lrc_thm",
``! value mode.  priv_LR_constraints (write_reg <|proc:=0|> 14w value) value mode``,

RW_TAC (bool_ss) [write_reg_def,
		  seqT_def,errorT_def,priv_LR_constraints_def]
       THEN Cases_on `read_cpsr <|proc := 0|> s`
       THEN FULL_SIMP_TAC (srw_ss()) []
       THEN Cases_on `access_violation b`
       THENL [
       FULL_SIMP_TAC (srw_ss()) []
		     THEN RW_TAC (srw_ss()) []
		     THEN FULL_SIMP_TAC (srw_ss()) [],
       Q.UNABBREV_TAC `lr`
		      THEN ( NTAC 3 (UNDISCH_ALL_TAC
				       THEN EVAL_TAC
				       THEN FULL_SIMP_TAC (srw_ss()) []
				       THEN RW_TAC (srw_ss()) []))
	     ]);

val read_cpsr_lrc_ut_thm =
    store_thm("read_cpsr_lrc_ut_thm",
	      `` ! mode.
	     (untouched_LR (read_cpsr <|proc:=0|> ) mode)``,
EVAL_TAC
THEN RW_TAC (srw_ss()) [] );

val branch_to_lrc_ut_thm =
    store_thm("branch_to_lrc_ut_thm",
``!adr mode . untouched_LR (
 branch_to <|proc:=0|> adr) mode ``,
EVAL_TAC
THEN RW_TAC (srw_ss()) []
THEN UNDISCH_ALL_TAC
THEN EVAL_TAC
THEN RW_TAC (srw_ss()) []
THEN FULL_SIMP_TAC (srw_ss()) []);

val constT_lrc_ut_thm =
    store_thm("constT_lrc_ut_thm",
`` untouched_LR_abs (λ(u1:unit,u2:unit,u3:unit,u4:unit). constT ()) mode``,
EVAL_TAC
THEN RW_TAC (srw_ss()) [] );

val ui_write_cpsr_LR_ut_thm =
    store_thm("ui_write_cpsr_LR_ut_thm",
``untouched_LR (
	   read_cpsr <|proc:=0|> >>=
		(λcpsr.
		write_cpsr <|proc:=0|>
                 (cpsr with
                  <|I := T; IT := 0w; J := F; T := sctlr.TE;
                    E := sctlr.EE|>))) mode``,
EVAL_TAC
THEN RW_TAC (srw_ss()) []
THEN UNDISCH_ALL_TAC
THEN EVAL_TAC
THEN RW_TAC (srw_ss()) []
THEN FULL_SIMP_TAC (srw_ss()) []);

val irq_write_cpsr_LR_ut_thm =
    store_thm("irq_write_cpsr_LR_ut_thm",
``untouched_LR (
	   read_cpsr <|proc:=0|> >>=
              (λcpsr.
                     write_cpsr <|proc:=0|>
                       (cpsr with
                        <|I := T;
                          A :=
                            ((¬have_security_exta ∨ ¬scr.NS ∨ scr.AW) ∨
                             cpsr.A); IT := 0w; J := F; T := sctlr.TE;
                          E := sctlr.EE|>))) mode``,
EVAL_TAC
THEN RW_TAC (srw_ss()) []
THEN UNDISCH_ALL_TAC
THEN EVAL_TAC
THEN RW_TAC (srw_ss()) []
THEN FULL_SIMP_TAC (srw_ss()) []);

val fiq_write_cpsr_LR_ut_thm =
    store_thm("fiq_write_cpsr_LR_ut_thm",
``untouched_LR (
	   read_cpsr <|proc:=0|> >>=
                 (λcpsr.
                     write_cpsr <|proc:=0|>
                       (cpsr with
                        <|I := T;
                          F :=
                            ((¬have_security_exta ∨ ¬scr.NS ∨ scr.AW) ∨
                             cpsr.F);
                          A :=
                            ((¬have_security_exta ∨ ¬scr.NS ∨ scr.AW) ∨
                             cpsr.A); IT := 0w; J := F; T := sctlr.TE;
                          E := sctlr.EE|>))) mode``,
EVAL_TAC
THEN RW_TAC (srw_ss()) []
THEN UNDISCH_ALL_TAC
THEN EVAL_TAC
THEN RW_TAC (srw_ss()) []
THEN FULL_SIMP_TAC (srw_ss()) []);



val ab_write_cpsr_LR_ut_thm =
    store_thm("ab_write_cpsr_LR_ut_thm",
``untouched_LR (
	   read_cpsr <|proc:=0|> >>=
                  (λcpsr.
                     write_cpsr <|proc:=0|>
                       (cpsr with
                        <|I := T;
                          A :=
                            ((¬have_security_exta ∨ ¬scr.NS ∨ scr.AW) ∨
                             cpsr.A); IT := 0w; J := F; T := sctlr.TE;
                          E := sctlr.EE|>))) mode``,
EVAL_TAC
THEN RW_TAC (srw_ss()) []
THEN UNDISCH_ALL_TAC
THEN EVAL_TAC
THEN RW_TAC (srw_ss()) []
THEN FULL_SIMP_TAC (srw_ss()) []);


fun get_take_exp_writing_part_LR_thm a' rw_cpsr_thm lr_arg vt =

    let
	val (l,r,rb1)= decompose_term a';
	val (l2,r2,rb2)= decompose_term rb1
	val (l3,r3,rb3)= decompose_term rb2
	val (l4,r4,rb4)= decompose_term l3
	val (l5,r5,rb5)= decompose_term r4
	val (l6,r6,rb6)= decompose_term r5;

		  (* proof of r5 *)
	val thm1 = LIST_MP [ rw_cpsr_thm,
			     (SPECL [vt,
				     ``mode:bool[5]``]
				    branch_to_lrc_ut_thm)]
			   (SPECL [l6,r6,``mode:bool[5]``]
				  (INST_TYPE [alpha |-> ``:unit``,
					      beta |-> ``:unit``]
					     parT_LR_trans_untouched_thm));
		  (* proof of r4 *)
	val thm2 = LIST_MP [
		   (SPECL [lr_arg,
			   ``mode:bool[5]``]
			  write_lr_reg_lrc_thm),
		   thm1]
			   (SPECL [l5,r5,lr_arg,
				   ``mode:bool[5]``]
				  (INST_TYPE [alpha |-> ``:unit``,
					      beta |-> ``:(unit#unit)``]
					     parT_priv_LR_constraints_after_thm));
		  (* proof of l3 *)
	val thm3 =
	    MP (SPECL [l4,r4,lr_arg,``mode:bool[5]``]
		      (INST_TYPE [alpha |-> ``:unit``,
				  beta |-> ``:(unit#unit#unit)``]
				 parT_priv_LR_constraints_before_thm)) thm2;
		  (* proof of rb2 *)
	val thm4 = LIST_MP [
		   thm3,
		   constT_lrc_ut_thm]
			   (SPECL [l3,r3,lr_arg,``mode:bool[5]``]
				  (INST_TYPE [beta |-> ``:unit``,
					      alpha |-> ``:(unit#unit#unit#unit)``]
					     seqT_priv_LR_constraints_after_thm));
	(* proof of rb1 *)
	val (thm5 , _) = prove_abs_LR_const_action
			     (r2, [LR_first_abs_lemma,
				   LR_second_abs_lemma],
			      thm4, lr_arg);
	val thm6 = MP (SPECL [l2,r2,lr_arg,``mode:bool[5]``]
			     (INST_TYPE [beta |-> ``:unit``,
					 alpha |-> ``:(unit#unit)``]
					seqT_priv_LR_constraints_before_thm)) thm5;
    in
	(GEN_ALL thm6)
    end


val take_undef_writing_part_LR_thm =
    save_thm ("take_undef_writing_part_LR_thm",
	      let
		  val vt = ``(ExcVectorBase + 4w:bool[32])``
		  val rw_cpsr_thm = ui_write_cpsr_LR_ut_thm
		  val a = SIMP_CONV (bool_ss) [take_undef_instr_exception_def]
				    ``take_undef_instr_exception <|proc:=0|> ``
		  val (_, a') =  (dest_eq (concl a))
	      in
		  get_take_exp_writing_part_LR_thm a' rw_cpsr_thm ``(if cpsr:ARMpsr.T then
						(pc:word32) − 2w else pc − 4w)`` vt
	      end
	     );


val take_data_abort_writing_part_LR_thm =
    save_thm ("take_data_abort_writing_part_LR_thm",
	      let val vt = ``(ExcVectorBase + 16w:bool[32])``
		  val rw_cpsr_thm = ab_write_cpsr_LR_ut_thm;
		   val a = SIMP_CONV (bool_ss) [take_data_abort_exception_def]
				    ``take_data_abort_exception <|proc:=0|> ``
		  val (_, a') =  (dest_eq (concl a))
		  val lr_arg = ``(if cpsr:ARMpsr.T then
						(pc:word32) else pc − 4w)``;
	      in
		  get_take_exp_writing_part_LR_thm a' rw_cpsr_thm lr_arg  vt
	      end
	     );


val take_fiq_writing_part_LR_thm =
    save_thm ("take_fiq_writing_part_LR_thm",
	      let val vt = ``(ExcVectorBase + 28w:bool[32])``
		  val rw_cpsr_thm = fiq_write_cpsr_LR_ut_thm
		   val a = SIMP_CONV (bool_ss) [take_fiq_exception_def]
				    ``take_fiq_exception <|proc:=0|> ``
		  val (_, a') =  (dest_eq (concl a))
		  val lr_arg = ``(if cpsr:ARMpsr.T then
				      (pc:word32) else pc − 4w)``
	      in
		  get_take_exp_writing_part_LR_thm a' rw_cpsr_thm lr_arg vt
	      end
	     );

val take_irq_writing_part_LR_thm =
    save_thm ("take_irq_writing_part_LR_thm",
	      let val vt = ``(ExcVectorBase + 24w:bool[32])``
		  val rw_cpsr_thm = irq_write_cpsr_LR_ut_thm
		   val a = SIMP_CONV (bool_ss) [take_irq_exception_def]
				    ``take_irq_exception <|proc:=0|> ``
		  val (_, a') =  (dest_eq (concl a))
		  val lr_arg = ``(if cpsr:ARMpsr.T then
				      (pc:word32) else pc − 4w)``
	      in
		  get_take_exp_writing_part_LR_thm a' rw_cpsr_thm lr_arg vt
	      end
	     );

val take_prefetch_abort_writing_part_LR_thm =
    save_thm ("take_prefetch_abort_writing_part_LR_thm",
	      let val vt = ``(ExcVectorBase + 12w:bool[32])``
		  val rw_cpsr_thm = ab_write_cpsr_LR_ut_thm
		   val a = SIMP_CONV (bool_ss) [take_prefetch_abort_exception_def]
				    ``take_prefetch_abort_exception <|proc:=0|> ``
		  val (_, a') =  (dest_eq (concl a))
		  val lr_arg = ``(if cpsr:ARMpsr.T then
				      (pc:word32) else pc − 4w)``
	      in
		  get_take_exp_writing_part_LR_thm a' rw_cpsr_thm lr_arg vt
	      end
	     );


val take_svc_writing_part_LR_thm =
    save_thm ("take_svc_writing_part_LR_thm",
	      let val vt = ``(ExcVectorBase + 8w:bool[32])``
		  val rw_cpsr_thm = ui_write_cpsr_LR_ut_thm
		  val a = SIMP_CONV (bool_ss) [take_svc_exception_def]
				    ``take_svc_exception <|proc:=0|> ``
		  val (_, a') =  (dest_eq (concl a))
		  val (_,_,rb) = decompose_term a'
		  val lr_arg = 	``(if cpsr:ARMpsr.T then
				       ((pc:word32) - 2w) else pc − 4w)``

	      in
		  get_take_exp_writing_part_LR_thm rb rw_cpsr_thm lr_arg vt
	      end);


val satisfy_LR_constraints_def =
    Define ` satisfy_LR_constraints f mode value =
		! s s' a .
		  (f s = ValueState a s') ==>
		  ((s'.psrs(0,CPSR)).M = mode) ==>
		  (~access_violation s') ==>
		  (s'.registers (0, get_lr_by_mode (mode)) =
		   (if (s.psrs (0,CPSR)).T then
			(get_pc_value s - 2w) + value
		    else
			(get_pc_value s) - 4w))`;

val satisfy_LR_constraints_abs_def =
    Define ` satisfy_LR_constraints_abs f mode value =
		! s c s' a .
		  (f c s = ValueState a s') ==>
		  ((s'.psrs(0,CPSR)).M = mode) ==>
		  (~access_violation s') ==>
		  (s'.registers (0, get_lr_by_mode (mode)) =
		   (if (s.psrs (0,CPSR)).T then
			(get_pc_value s - 2w) + value
		    else
			(get_pc_value s) - 4w ))`;



fun prove_take_exception_LR_constraints te te_def wp_thm fixed_rp_thm fixed_cpsr_thm
					fixed_pc_thm2 const_comp_rp_thm sl_elm2
					spec_lists  ltype =
 let
     val (l,r,rb1)= decompose_term te
     val sl_elm2 =  ``(a':(word32 # word32 # ARMpsr # CP15scr # CP15sctlr))``
     val spec_list = List.nth(spec_lists,0)
     val spec_list2 = List.nth(spec_lists,1)
     val spec_list3 = List.nth(spec_lists,2)
 in
     RW_TAC (bool_ss) [te_def,
		       satisfy_LR_constraints_def
		      ]
	    THEN Cases_on [QUOTE ("("^(term_to_string l) ^ ") s")]
	    THEN IMP_RES_TAC seqT_access_violation_thm
	    THEN IMP_RES_SIMP_TAC [const_comp_def] const_comp_rp_thm
	    THEN RW_TAC (bool_ss) []
	    THEN FIRST_PROVE
	    [
	     IMP_RES_TAC hlp_seqT_thm
	     		 THEN TRY (PAT_ASSUM ``!a. X`` (fn thm => ASSUME_SPEC_TAC sl_elm2 thm))
	     		 THEN PAT_ASSUM ``X a' b'= ValueState a s'``
			 (fn thm => ASSUME_TAC (PairRules.PBETA_RULE thm))
			 THEN ASSUME_TAC ( SPECL
					       spec_list  (GEN_ALL  (SIMP_RULE (bool_ss) [priv_LR_constraints_def]
									       wp_thm)))
			 THEN ASSUME_TAC (SPECL spec_list3 fixed_cpsr_thm)
			 THEN ASSUME_TAC (SPECL spec_list3 fixed_pc_thm2)
			THEN RES_TAC
			THEN FULL_SIMP_TAC (let_ss) []
			THEN FULL_SIMP_TAC (srw_ss()) []
			THEN RES_TAC
	   ,
	   IMP_RES_TAC (SPEC r (
			INST_TYPE [beta |-> ``:unit``,
				   alpha |-> ltype ]
				  hlp_errorT_thm))
		       THEN
		       PAT_ASSUM ``! (s:arm_state) . X ``
		       (fn thm => ASSUME_TAC (SPEC ``s:arm_state`` thm))
		       THEN RW_TAC (srw_ss()) []
		       THEN FULL_SIMP_TAC (srw_ss()) []
	    ]
 end;

val take_undef_instr_exception_LR_thm =
    store_thm ("take_undef_instr_exception_LR_thm",
	       `` ! mode.
	      satisfy_LR_constraints (take_undef_instr_exception <|proc:=0|>  )
	     mode (0w:word32)``,
	       let
		   val athm = SIMP_CONV (bool_ss) [take_undef_instr_exception_def]
					``take_undef_instr_exception <|proc:=0|>``
		   val (_, te) =  (dest_eq (concl athm))
		   val te_def = take_undef_instr_exception_def
		   val sl_elm2 =  ``(a':(word32 # word32 # ARMpsr # CP15scr # CP15sctlr))``
		   val spec_list = (mk_spec_list sl_elm2)@
				   [``b:arm_state``, ``s':arm_state``,``a:unit``]
		   val spec_list2 = [``b:arm_state``] @ (mk_spec_list2 (sl_elm2))
		   val spec_list3 = [``b:arm_state``] @ (rev (mk_spec_list2 (sl_elm2)))
		   val spec_lists = [spec_list]@[spec_list2]@[spec_list3]
		   val wp_thm = take_undef_writing_part_LR_thm
		   val fixed_rp_thm = fixed_undef_svc_exception_rp_thm2;
		   val fixed_cpsr_thm = fixed_cpsr_undef_svc_thm2
		   val const_comp_rp_thm = const_comp_take_undef_svc_exception_rp_thm
		   val ltype = ``:(word32 # word32 # ARMpsr # CP15scr # CP15sctlr)``
	 	   val fixed_pc_thm2 = fixed_pc_undef_svc_thm2
	       in
		   prove_take_exception_LR_constraints te te_def
						       take_undef_writing_part_LR_thm
						       fixed_rp_thm
						       fixed_cpsr_thm fixed_pc_thm2
						       const_comp_rp_thm
						       sl_elm2 spec_lists ltype
	       end);

val take_svc_exception_LR_thm =
    store_thm ("take_svc_exception_LR_thm",
	       let
		   val athm = SIMP_CONV (bool_ss) [take_svc_exception_def]
					``take_svc_exception <|proc:=0|> ``;
		   val (_, a) =  (dest_eq (concl athm))
		   val (l,r,rb1)= decompose_term a
	       in
		   `` ! mode. satisfy_LR_constraints ^rb1  mode 0w``
		  end
,
	       let
		   val athm = SIMP_CONV (bool_ss) [take_svc_exception_def]
					``take_svc_exception <|proc:=0|> ``;
		   val (_, a) =  (dest_eq (concl athm))
		   val (l,r,te)= decompose_term a
		   val te_def = take_svc_exception_def
		   val sl_elm2 =  ``(a':(word32 # word32 # ARMpsr # CP15scr # CP15sctlr))``
		   val spec_list = (mk_spec_list sl_elm2)@
				   [``b:arm_state``, ``s':arm_state``,``a:unit``]
		   val spec_list2 = [``b:arm_state``] @ (mk_spec_list2 (sl_elm2))
		   val spec_list3 = [``b:arm_state``] @ (rev (mk_spec_list2 (sl_elm2)))
		   val spec_lists = [spec_list]@[spec_list2]@[spec_list3];
		   val wp_thm = take_svc_writing_part_LR_thm
	     	     val fixed_rp_thm = fixed_undef_svc_exception_rp_thm2
		   val fixed_cpsr_thm = fixed_cpsr_undef_svc_thm2
		   val const_comp_rp_thm = const_comp_take_undef_svc_exception_rp_thm
		   val ltype = ``:(word32 # word32 # ARMpsr # CP15scr # CP15sctlr)``
	 	   val fixed_pc_thm2 = fixed_pc_undef_svc_thm2
	    in
		  prove_take_exception_LR_constraints te te_def
						       wp_thm
						       fixed_rp_thm
						       fixed_cpsr_thm fixed_pc_thm2
						       const_comp_rp_thm
						       sl_elm2 spec_lists ltype
	       end);



val take_data_abort_exception_LR_thm =
    store_thm ("take_data_abort_exception_LR_thm",
	       `` ! mode. satisfy_LR_constraints (take_data_abort_exception <|proc:=0|>)  mode 2w ``
	     ,
	     let
		 val athm = SIMP_CONV (bool_ss) [take_data_abort_exception_def]
				      ``take_data_abort_exception <|proc:=0|> ``;
		 val (_, te) =  (dest_eq (concl athm))
		 val te_def = take_data_abort_exception_def
		 val sl_elm2 =  ``(a':(word32 # word32 # bool# ARMpsr # CP15scr # CP15sctlr))``;
		 val spec_list = (mk_spec_list3 sl_elm2)@
				 [``b:arm_state``, ``s':arm_state``,``a:unit``];
		 val spec_list2 = [``b:arm_state``] @ (mk_spec_list4 (sl_elm2))
		 val spec_list3 = [``b:arm_state``] @ (rev (mk_spec_list4 (sl_elm2)))
		 val spec_lists = [spec_list]@[spec_list2]@[spec_list3];
		 val wp_thm = take_data_abort_writing_part_LR_thm
	    	 val fixed_rp_thm = fixed_abort_irq_exception_rp_thm2
		 val fixed_cpsr_thm = fixed_cpsr_abt_irq_thm2;
	   	 val ltype = ``:(word32 # word32 # bool # ARMpsr # CP15scr # CP15sctlr)``
		 val const_comp_rp_thm = const_comp_take_abort_irq_exception_rp_thm
		 val fixed_pc_thm2 = fixed_pc_abt_irq_thm2
	     in
		 prove_take_exception_LR_constraints te te_def
						     wp_thm
						     fixed_rp_thm
						     fixed_cpsr_thm
						     fixed_pc_thm2
						     const_comp_rp_thm
						     sl_elm2 spec_lists
						     ltype
	     end);


val take_prefetch_abort_exception_LR_thm =
    store_thm ("take_prefetch_abort_exception_LR_thm",
	       `` ! mode. satisfy_LR_constraints (take_prefetch_abort_exception <|proc:=0|>)  mode 2w ``
	     ,
	     let
		 val athm = SIMP_CONV (bool_ss) [take_prefetch_abort_exception_def]
				      ``take_prefetch_abort_exception <|proc:=0|> ``;
		 val (_, te) =  (dest_eq (concl athm))
		 val te_def = take_prefetch_abort_exception_def
		 val sl_elm2 =  ``(a':(word32 # word32 # bool# ARMpsr # CP15scr # CP15sctlr))``;
		 val spec_list = (mk_spec_list3 sl_elm2)@
				 [``b:arm_state``, ``s':arm_state``,``a:unit``];
		 val spec_list2 = [``b:arm_state``] @ (mk_spec_list4 (sl_elm2))
		 val spec_list3 = [``b:arm_state``] @ (rev (mk_spec_list4 (sl_elm2)))
		 val spec_lists = [spec_list]@[spec_list2]@[spec_list3];
		 val wp_thm = take_prefetch_abort_writing_part_LR_thm
	    	 val fixed_rp_thm = fixed_abort_irq_exception_rp_thm2
		 val fixed_cpsr_thm = fixed_cpsr_abt_irq_thm2;
	   	 val ltype = ``:(word32 # word32 # bool # ARMpsr # CP15scr # CP15sctlr)``
		 val const_comp_rp_thm = const_comp_take_abort_irq_exception_rp_thm
		 val fixed_pc_thm2 = fixed_pc_abt_irq_thm2
	     in
		 prove_take_exception_LR_constraints te te_def
						     wp_thm
						     fixed_rp_thm
						     fixed_cpsr_thm
						     fixed_pc_thm2
						     const_comp_rp_thm
						     sl_elm2 spec_lists
						     ltype
	     end);

val take_irq_exception_LR_thm =
    store_thm ("take_irq_exception_LR_thm",
	       `` ! mode. satisfy_LR_constraints (take_irq_exception <|proc:=0|>)  mode 2w ``
	     ,
	     let
		 val athm = SIMP_CONV (bool_ss) [take_irq_exception_def]
				      ``take_irq_exception <|proc:=0|> ``;
		 val (_, te) =  (dest_eq (concl athm))
		 val te_def = take_irq_exception_def
		 val sl_elm2 =  ``(a':(word32 # word32 # bool# ARMpsr # CP15scr # CP15sctlr))``;
		 val spec_list = (mk_spec_list3 sl_elm2)@
				 [``b:arm_state``, ``s':arm_state``,``a:unit``];
		 val spec_list2 = [``b:arm_state``] @ (mk_spec_list4 (sl_elm2))
		 val spec_list3 = [``b:arm_state``] @ (rev (mk_spec_list4 (sl_elm2)))
		 val spec_lists = [spec_list]@[spec_list2]@[spec_list3];
		 val wp_thm = take_irq_writing_part_LR_thm
	    	 val fixed_rp_thm = fixed_abort_irq_exception_rp_thm2
		 val fixed_cpsr_thm = fixed_cpsr_abt_irq_thm2;
	   	 val ltype = ``:(word32 # word32 # bool # ARMpsr # CP15scr # CP15sctlr)``
		 val const_comp_rp_thm = const_comp_take_abort_irq_exception_rp_thm
		 val fixed_pc_thm2 = fixed_pc_abt_irq_thm2
	     in
		 prove_take_exception_LR_constraints te te_def
						     wp_thm
						     fixed_rp_thm
						     fixed_cpsr_thm
						     fixed_pc_thm2
						     const_comp_rp_thm
						     sl_elm2 spec_lists
						     ltype
	     end);


val _ = export_theory();
