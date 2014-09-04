open HolKernel boolLib bossLib Parse proofManagerLib;
open arm_coretypesTheory arm_seq_monadTheory arm_opsemTheory arm_stepTheory;
open MMUTheory MMU_SetupTheory inference_rulesTheory switching_lemma_helperTheory tacticsLib ARM_prover_extLib;

val _ =  new_theory("priv_constraints_spsr");

val _ = diminish_srw_ss ["one"]
val _ = augment_srw_ss [rewrites [oneTheory.FORALL_ONE]]

(****************************************************************)
(*         CONSTRAINTS ON SPSR FLAGS IN PRIVILEGED MODE         *)
(*                        Narges                                *)
(****************************************************************)

val let_ss = simpLib.mk_simpset [boolSimps.LET_ss] ;

val prove_abs_spsr_flags_const_action =
 fn (a, thms, abody_thm, expr,mode) =>
    let
	val _ =  set_goal([], ``
    			 (priv_spsr_flags_constraints_abs ^a ^expr ^mode) ``)
	val (a_abs,a_body) = pairLib.dest_pabs a;
	val unbeta_thm= (PairRules.UNPBETA_CONV a_abs a_body)
	val unbeta_a = mk_comb (a, a_abs)
	val snd = get_type_inst (type_of(a_body) , false)
	val a_body_type = get_type_inst (snd, true);
	val proved_unbeta_lemma = store_thm ("proved_unbeta_lemma",
					     ``(priv_spsr_flags_constraints ^a_body ^expr ^mode)=
				  (priv_spsr_flags_constraints ^unbeta_a ^expr ^mode)``,
					     (ASSUME_TAC (SPECL [a_body,``^unbeta_a``, expr,mode]
								(INST_TYPE [beta |-> a_body_type,
									    alpha |-> ``:arm_state``]
									   (List.nth(thms,0)))))
						 THEN ASSUME_TAC unbeta_thm
						 THEN RES_TAC);

	val proved_preserve_unbeta_a =
	    store_thm ("proved_preserve_unbeta_a",
		       `` (priv_spsr_flags_constraints ^unbeta_a ^expr ^mode)``,
		       (ASSUME_TAC (proved_unbeta_lemma))
			   THEN (ASSUME_TAC abody_thm)
			   THEN (FULL_SIMP_TAC (srw_ss()) []));

	val abs_type = type_of a_abs
	val (abs_args, abs_body)  = generate_uncurry_abs a
	val tacs =  (ASSUME_TAC proved_preserve_unbeta_a)
	val gen_preserve_unbeta_thm = generalize_theorem proved_preserve_unbeta_a a;
	val tacs = tacs THEN (ASSUME_TAC gen_preserve_unbeta_thm)
			THEN (ASSUME_TAC (
			      SPECL[a, expr,mode]
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



val untouched_spsr_flags_abs_def =
    Define `untouched_spsr_flags_abs f (mode:bool[5]) =
	   !s a c s'. (f a s = ValueState c s') ==>
		let spsr =
	       case mode of
	    	 17w => SPSR_fiq
	       | 18w => SPSR_irq
	       | 19w => SPSR_svc
	       | 22w => SPSR_mon
	       | 23w => SPSR_abt
	       | 27w => SPSR_und
	       | _   => CPSR
	    	 in (*(spsr<>CPSR) ==>*)
		    (
           ((*! spsr.  (spsr<>CPSR) ==>*)
		   (((s'.psrs(0,spsr)).I = (s.psrs(0,spsr)).I) /\
			   ((s'.psrs(0,spsr)).F = (s.psrs(0,spsr)).F) /\
                           ((s'.psrs (0,spsr)).M=(s.psrs (0,spsr)).M) /\
                           ((s'.psrs (0,CPSR)).M=(s.psrs (0,CPSR)).M)) ))
			   `;

val untouched_spsr_flags_def =
    Define `untouched_spsr_flags f (mode:bool[5]) =
	   !s c s'. (f s = ValueState c s') ==>
	   let spsr =
	       case mode of
	         17w => SPSR_fiq
	       | 18w => SPSR_irq
	       | 19w => SPSR_svc
	       | 22w => SPSR_mon
	       | 23w => SPSR_abt
	       | 27w => SPSR_und
	       | _   => CPSR
	    	 in (*(spsr<>CPSR) ==>*)
		    ((*! spsr. (spsr<>CPSR) ==>*)
		           (((s'.psrs(0,spsr)).I = (s.psrs(0,spsr)).I) /\
			   ((s'.psrs(0,spsr)).F = (s.psrs(0,spsr)).F) /\
                           ((s'.psrs (0,spsr)).M=(s.psrs (0,spsr)).M)/\
                           ((s'.psrs (0,CPSR)).M=(s.psrs (0,CPSR)).M)) )
			   `;


val priv_spsr_flags_constraints_def =
    Define `priv_spsr_flags_constraints f cpsr mode =
	    ! s s' a . (f s = ValueState a s') ==>
	        (~access_violation s') ==>
		((s'.psrs(0,CPSR)).M = mode) ==>
	 (  let spsr =
		case mode of
	    	 17w => SPSR_fiq
	       | 18w => SPSR_irq
	       | 19w => SPSR_svc
	       | 22w => SPSR_mon
	       | 23w => SPSR_abt
	       | 27w => SPSR_und
	       | _   => CPSR
	    	 in (*(spsr<>CPSR) ==>*)
			      ( ((s'.psrs(0,spsr)).I = cpsr.I) /\
			   ((s'.psrs(0,spsr)).F = cpsr.F)/\
                           ((s'.psrs (0,spsr)).M=cpsr.M))

	      )`;


val priv_spsr_flags_constraints_abs_def =
    Define `priv_spsr_flags_constraints_abs f cpsr mode =
			     ! s s' a c. (f c s = ValueState a s') ==>
			       (~access_violation s') ==>
			      ((s'.psrs(0,CPSR)).M = mode) ==>
	 (  let spsr =
		case mode of
	         17w => SPSR_fiq
	       | 18w => SPSR_irq
	       | 19w => SPSR_svc
	       | 22w => SPSR_mon
	       | 23w => SPSR_abt
	       | 27w => SPSR_und
	       | _   => CPSR

	    	      		in

		(*  (spsr<>CPSR) ==>*)
			       (((s'.psrs(0,spsr)).I = cpsr.I) /\
			   ((s'.psrs(0,spsr)).F = cpsr.F)/\
                           ((s'.psrs (0,spsr)).M=cpsr.M)))
			       `;


(*********************   proof rules *******************************)

val seqT_priv_spsr_flags_constraints_before_thm =
    store_thm("seqT_priv_spsr_flags_constraints_before_thm",
	      `` ! g f cpsr spsr. priv_spsr_flags_constraints_abs f cpsr spsr ==>
	     priv_spsr_flags_constraints (g >>= f) cpsr spsr ``,
	      (RW_TAC (srw_ss()) [seqT_def,
				  priv_spsr_flags_constraints_def,
				  priv_spsr_flags_constraints_abs_def])
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



val parT_priv_spsr_flags_constraints_before_thm =
    store_thm("parT_priv_spsr_flags_constraints_before_thm",
	      `` !f g cpsr spsr . priv_spsr_flags_constraints f cpsr spsr ==>
	     priv_spsr_flags_constraints (g ||| f) cpsr spsr ``,
	      RW_TAC (srw_ss())
		      [parT_def,seqT_def,
		       priv_spsr_flags_constraints_def,
		       untouched_spsr_flags_def,constT_def]
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
		  (SPECL [``b:arm_state``,``b':arm_state``,``a'':'a``] thm))
		  THEN Cases_on `access_violation b`
		  THEN Cases_on `access_violation b'`
		  THEN RES_TAC
		  THEN FULL_SIMP_TAC (srw_ss()) []
		  THEN FIRST_PROVE [ FULL_SIMP_TAC (srw_ss()) []
						   THEN RW_TAC (srw_ss()) [] ,
				     (UNDISCH_ALL_TAC
					  THEN  RW_TAC (srw_ss()) []
					  THEN FULL_SIMP_TAC (srw_ss()) [])]);



val seqT_priv_spsr_flags_constraints_after_thm =
    store_thm("seqT_priv_spsr_flags_constraints_after_thm",
	      `` !f g cpsr mode. priv_spsr_flags_constraints g cpsr mode ==>
	     (  untouched_spsr_flags_abs f mode) ==>
	     priv_spsr_flags_constraints (g >>= f) cpsr mode``,
	      (RW_TAC (srw_ss()) [seqT_def,
				  priv_spsr_flags_constraints_def,
				  priv_spsr_flags_constraints_abs_def,
untouched_spsr_flags_abs_def]) THEN
			FULL_SIMP_TAC (let_ss) [] THEN
			Cases_on `g s` THEN
			FULL_SIMP_TAC (srw_ss()) [] THEN
			Cases_on `access_violation b`
			THEN Q.UNABBREV_TAC `spsr`
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
			THEN FULL_SIMP_TAC (srw_ss()) []
			THEN FULL_SIMP_TAC (srw_ss()) []);

val parT_priv_spsr_flags_constraints_after_thm =
    store_thm("parT_priv_spsr_flags_constraints_after_thm",
`` !f g cpsr spsr. priv_spsr_flags_constraints g cpsr spsr ==>
	     (untouched_spsr_flags f spsr) ==>
	     priv_spsr_flags_constraints (g ||| f) cpsr spsr``,
	      (RW_TAC (srw_ss())
		      [parT_def,seqT_def,
		       priv_spsr_flags_constraints_def,
		       untouched_spsr_flags_def,constT_def])
		  THEN FULL_SIMP_TAC (let_ss) []THEN
		  Cases_on `g s` THEN
		  Cases_on `f b` THEN
		  Cases_on `access_violation b` THEN
		  Cases_on `access_violation b'`   THEN
		  FULL_SIMP_TAC (srw_ss()) [] THEN
		  PAT_ASSUM ``! s a s' .(f s = ValueState a s') ==> Z``
		  (fn thm => ASSUME_TAC
				 (SPECL [``b:arm_state``,``a'':'a``,``b':arm_state``] thm))
		  THEN PAT_ASSUM ``! s1 c s2. X``
		  (fn thm => ASSUME_TAC
				 (SPECL [``s:arm_state``,``b:arm_state``,``a':'b``] thm))
		  THEN RES_TAC
		  THEN UNDISCH_ALL_TAC
		  THEN  RW_TAC (srw_ss()) []
		  THEN  FULL_SIMP_TAC (srw_ss()) []
		);


val seqT_trans_untouched_thm =
    store_thm("seqT_trans_untouched_thm",
	      `` !f g mode.
	     (untouched_spsr_flags f mode) ==>
	     (untouched_spsr_flags_abs g mode) ==>
	     (untouched_spsr_flags (f>>=g) mode)``,
	      (RW_TAC (srw_ss()) [seqT_def,untouched_spsr_flags_abs_def,
				  untouched_spsr_flags_def])
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

val parT_trans_untouched_thm =
    store_thm("parT_trans_untouched_thm",
	      `` !f g spsr.
	     (untouched_spsr_flags f spsr) ==>
	     (untouched_spsr_flags g spsr) ==>
	     (untouched_spsr_flags (f ||| g) spsr)``,
	      (RW_TAC (srw_ss()) [seqT_def,parT_def,constT_def,
				  untouched_spsr_flags_def])
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


val spfc_first_abs_lemma =
    store_thm ("spfc_first_abs_lemma",
	       ``!f g x y. (f=g) ==> ((priv_spsr_flags_constraints f x y) =
				    (priv_spsr_flags_constraints g x y))``,
	       RW_TAC (srw_ss()) []);


val spfc_second_abs_lemma =
    store_thm ("spfc_second_abs_lemma",
	       ``! f x z. (! y. priv_spsr_flags_constraints (f y) x z) =
    priv_spsr_flags_constraints_abs f x z``,
	       RW_TAC (srw_ss()) [priv_spsr_flags_constraints_def,priv_spsr_flags_constraints_abs_def]
		      THEN METIS_TAC []);


(********************* end of proof rules *******************************)
(******************* basic lemmas **************************************)

val read_cpsr_fixed_lem =
    store_thm("read_cpsr_fixed_lem",
	      ``!s. read_cpsr <|proc := 0|> s = ValueState (s.psrs (0,CPSR)) s``,
	      EVAL_TAC
		  THEN RW_TAC (srw_ss()) []);

(* if possible, try to optimize it *)
val write_spsr_sfc_thm =
    store_thm("write_spsr_sfc_thm",
	      ``! cpsr mode. priv_spsr_flags_constraints (write_spsr <|proc := 0|> cpsr)
	     cpsr mode ``,

	      RW_TAC (bool_ss) [write_spsr_def,seqT_def,priv_spsr_flags_constraints_def]
		     THEN Cases_on `read_cpsr <|proc := 0|> s`
		     THEN FIRST_PROVE [
	      FULL_SIMP_TAC (srw_ss()) []
			    THEN ASSUME_TAC (SPEC ``s:arm_state`` read_cpsr_fixed_lem)
			    THEN Cases_on `access_violation b`
			    THENL [
			    FULL_SIMP_TAC (srw_ss()) []
					  THEN RW_TAC (srw_ss()) []
					  THEN FULL_SIMP_TAC (srw_ss()) [],
			    Cases_on ` bad_mode <|proc := 0|> a'.M b`
				     THENL
				     [
				      FULL_SIMP_TAC (srw_ss()) []
						    THEN Cases_on `access_violation b'`
						    THENL[
						    FULL_SIMP_TAC (srw_ss()) []
								  THEN RW_TAC (srw_ss()) []
								  THEN FULL_SIMP_TAC (srw_ss()) []
						  ,
						  FULL_SIMP_TAC (srw_ss()) []
								THEN Cases_on `a''`
								THENL [
								FULL_SIMP_TAC (srw_ss()) []
									      (* THEN Q.UNABBREV_TAC `spsr`  *)
									      THEN UNDISCH_ALL_TAC
									      THEN EVAL_TAC,
								TRY (Q.UNABBREV_TAC `spsr`)
								    THEN  UNDISCH_ALL_TAC
									       THEN EVAL_TAC
									       THEN RW_TAC (srw_ss()) [] THEN
									       FULL_SIMP_TAC (srw_ss()) []
									       THEN UNDISCH_ALL_TAC
									       THEN EVAL_TAC
									       THEN RW_TAC (srw_ss()) [] THEN
									       FULL_SIMP_TAC (srw_ss()) []]],
				      FULL_SIMP_TAC (srw_ss()) []]],
	      FULL_SIMP_TAC (srw_ss()) []]);


val write_lr_reg_sfc_ut_thm =
    store_thm("write_lr_reg_sfc_ut_thm",
	      ``! value mode.
	     (untouched_spsr_flags (write_reg <|proc:=0|> 14w value) mode)``,
	      EVAL_TAC
		  THEN RW_TAC (srw_ss()) []
		  THEN UNDISCH_ALL_TAC
		  THEN EVAL_TAC
		  THEN RW_TAC (srw_ss()) []
		  THEN FULL_SIMP_TAC (srw_ss()) []);

val read_cpsr_sfc_ut_thm =
    store_thm("read_cpsr_sfc_ut_thm",
	      `` !mode.
	     (untouched_spsr_flags (read_cpsr <|proc:=0|> ) mode )``,
	      EVAL_TAC
		  THEN RW_TAC (srw_ss()) [] );

val branch_to_sfc_ut_thm =
    store_thm("branch_to_sfc_ut_thm",
	      ``!adr mode. untouched_spsr_flags (
    branch_to <|proc:=0|> adr) mode``,
	      EVAL_TAC
		  THEN RW_TAC (srw_ss()) []
		  THEN UNDISCH_ALL_TAC
		  THEN EVAL_TAC
		  THEN RW_TAC (srw_ss()) []
		  THEN FULL_SIMP_TAC (srw_ss()) []);

val constT_sfc_ut_thm =
    store_thm("constT_sfc_ut_thm",
	      ``! mode. untouched_spsr_flags_abs (λ(u1:unit,u2:unit,u3:unit,u4:unit). constT ()) mode``,
	      EVAL_TAC
		  THEN RW_TAC (srw_ss()) [] );

val write_cpsr_sfc_ut_thm =
    store_thm("write_cpsr_sfc_ut_thm",
	      ``untouched_spsr_flags (
    read_cpsr <|proc:=0|> >>=
		       (λcpsr.
			    write_cpsr <|proc:=0|>
						(cpsr with
<|I := T; IT := 0w; J := F; T := sctlr.TE;
E := sctlr.EE|>))) 27w``,
	      EVAL_TAC
		  THEN RW_TAC (srw_ss()) []
		  THEN UNDISCH_ALL_TAC
		  THEN EVAL_TAC
		  THEN RW_TAC (srw_ss()) []
		  THEN FULL_SIMP_TAC (srw_ss()) []);

val take_undef_writing_part_spf_thm =
    save_thm ("take_undef_writing_part_spf_thm",
	      let
		  val a = SIMP_CONV (bool_ss) [take_undef_instr_exception_def]
				    ``take_undef_instr_exception <|proc:=0|> ``;
		  val (_, a') =  (dest_eq (concl a))
		  val (l,r,rb1)= decompose_term a';
		  val (l2,r2,rb2)= decompose_term rb1
		  val (l3,r3,rb3)= decompose_term rb2
		  val (l4,r4,rb4)= decompose_term l3
		  val (l5,r5,rb5)= decompose_term r4
		  val (l6,r6,rb6)= decompose_term r5;
		  (* proof of r5 *)
		  val thm1 = LIST_MP [ write_cpsr_sfc_ut_thm,
				     (SPECL [``(ExcVectorBase + 4w:bool[32])``,
					     ``27w:bool[5]``] branch_to_sfc_ut_thm)]
				     (SPECL [l6,r6,``27w:bool[5]``]
					    (INST_TYPE [alpha |-> ``:unit``,
							beta |-> ``:unit``]
						       parT_trans_untouched_thm));
		  (* proof of r4 *)
		  val thm2 = LIST_MP [
			     (SPECL [``(if cpsr:ARMpsr.T then
					    (pc:word32) − 2w else pc − 4w)``,
				     ``27w:word5``] write_lr_reg_sfc_ut_thm),
			     thm1]
				     (SPECL [l5,r5,``27w:bool[5]``]
					    (INST_TYPE [alpha |-> ``:unit``,
							beta |-> ``:(unit#unit)``]
						       parT_trans_untouched_thm));
		  (* proof of l3 *)
		  val thm3 = LIST_MP [
			     (SPECL [``cpsr:ARMpsr``,``27w:word5``] write_spsr_sfc_thm),
			     thm2]
				     (SPECL [r4,l4,``cpsr:ARMpsr``,``27w:word5``]
					    (INST_TYPE [beta |-> ``:unit``,
							alpha |-> ``:(unit#unit#unit)``]
						       parT_priv_spsr_flags_constraints_after_thm));
		  (* proof of rb2 *)
		  val thm4 = LIST_MP [
			     thm3,
			     SPEC ``27w:word5`` constT_sfc_ut_thm]
				     (SPECL [r3,l3,``cpsr:ARMpsr``,``27w:word5``]
					    (INST_TYPE [beta |-> ``:unit``,
							alpha |-> ``:(unit#unit#unit#unit)``]
						       seqT_priv_spsr_flags_constraints_after_thm));
		  (* proof of rb1 *)
		  val (thm5 , _) = prove_abs_spsr_flags_const_action (r2, [spfc_first_abs_lemma,
									   spfc_second_abs_lemma],
								      thm4, ``cpsr:ARMpsr``,
								      ``27w:word5``);
		  val thm6 = MP (SPECL [l2,r2,``cpsr:ARMpsr``,``27w:word5``]
				       (INST_TYPE [beta |-> ``:unit``,
						   alpha |-> ``:(unit#unit)``]
						  seqT_priv_spsr_flags_constraints_before_thm)) thm5;
	      in
		  (GEN_ALL thm6)
	      end
);

(* to be replaced *)
val r' = ``(λ(pc,ExcVectorBase,cpsr:ARMpsr,scr,sctlr).
          (condT ((s.psrs (0,CPSR)).M = 22w)
             (write_scr <|proc := 0|> (scr with NS := F)) |||
           write_cpsr <|proc := 0|> (s.psrs (0,CPSR) with M := 27w)) >>=
          (λ(u1,u2).
             (write_spsr <|proc := 0|> (s.psrs (0,CPSR)) |||
              write_reg <|proc := 0|> 14w
                (if (s.psrs (0,CPSR)).T then
                   pc + 0xFFFFFFFEw
                 else
                   pc + 0xFFFFFFFCw) |||
              read_cpsr <|proc := 0|> >>=
              (λcpsr.
                 write_cpsr <|proc := 0|>
                   (cpsr with
                    <|IT := 0w; J := F; E := sctlr.EE; I := T;
                      T := sctlr.TE|>)) |||
              branch_to <|proc := 0|> (ExcVectorBase + 4w)) >>=
             (λ(u1,u2,u3,u4). constT ())))``;

(*
val take_undef_instr_exception_spsr_flags_thm =
    store_thm ("take_undef_instr_exception_spsr_flags_thm",
      `` ! s a s' . (take_undef_instr_exception <|proc:=0|> s = ValueState a s') ==>
	         (~access_violation s') ==>
		 ((s'.psrs(0,CPSR)).M = 27w) ==>
		 ( ( ((s'.psrs(0,SPSR_und)).I = (s.psrs(0,CPSR)).I)
		     /\
			  ((s'.psrs(0,SPSR_und)).F = (s.psrs(0,CPSR)).F)
		     /\
			  ((s'.psrs (0,SPSR_und)).M=(s.psrs(0,CPSR)).M)))``,
        let val athm = SIMP_CONV (bool_ss) [take_undef_instr_exception_def]
			  ``take_undef_instr_exception <|proc:=0|> ``
	val (_, a) =  (dest_eq (concl athm))
	val (l,r,_)= decompose_term a
	val sl_elm2 =  ``(a':(word32 # word32 # ARMpsr # CP15scr # CP15sctlr))``
	val spec_list = (mk_spec_list sl_elm2)@[``b:arm_state``, ``s':arm_state``,``a:unit``]
	val spec_list2 = [``b:arm_state``] @ List.rev (mk_spec_list2 (sl_elm2))
    in
	RW_TAC (bool_ss) [take_undef_instr_exception_def]
	       THEN ASSUME_TAC (SPECL [``s:arm_state``,r]
				      (INST_TYPE [alpha |-> ``:unit``] fixed_cpsr_thm))
	       THEN FULL_SIMP_TAC (srw_ss()) []
	       THEN FULL_SIMP_TAC (let_ss) []
	       THEN PAT_ASSUM ``X=Y`` (fn thm => THROW_AWAY_TAC (concl thm))
	       THEN ASSUME_TAC const_comp_take_undef_exception_rp_thm
	       THEN RW_TAC (srw_ss()) [priv_spsr_flags_constraints_def,
				       priv_spsr_flags_constraints_abs_def]
	       THEN FULL_SIMP_TAC (srw_ss()) [const_comp_def]
	       THEN NTAC 3
	       (Cases_on [QUOTE ("("^(term_to_string l) ^ ") s")]
	       THEN IMP_RES_TAC seqT_access_violation_thm
	       THENL
	       [ RES_TAC
		    THEN RW_TAC (srw_ss()) []
		    THEN IMP_RES_TAC hlp_seqT_thm
		    THEN PAT_ASSUM ``X a' b= ValueState a s'``
		    (fn thm => ASSUME_TAC (PairRules.PBETA_RULE thm))
		    THEN
		    ASSUME_SPECL_TAC spec_list  (GEN_ALL
						     (SIMP_RULE (bool_ss)
								[priv_spsr_flags_constraints_def]
								take_undef_writing_part_spf_thm))
		    THEN PAT_ASSUM ``X ==> Y`` (fn thm => ASSUME_TAC (PairRules.PBETA_RULE thm))
		    THEN
		    ASSUME_TAC (SPECL spec_list2 fixed_cpsr_thm2)
		    THEN RES_TAC
		    THEN RES_TAC
		    THEN FULL_SIMP_TAC (srw_ss()) [get_spsr_by_mode_def]
		    THEN FULL_SIMP_TAC (let_ss) []
		    THEN RW_TAC (srw_ss()) []
	       ,
	       IMP_RES_TAC (SPEC r' (
			    INST_TYPE [beta |-> ``:unit``,
				       alpha |-> ``:(word32 # word32 # ARMpsr # CP15scr # CP15sctlr)`` ]
				      hlp_errorT_thm))
			   THEN
			   PAT_ASSUM ``! (s:arm_state) . X ``
			   (fn thm => ASSUME_TAC (SPEC ``s:arm_state`` thm))
			   THEN RW_TAC (srw_ss()) []
			   THEN FULL_SIMP_TAC (srw_ss()) []
	       ])
    end);
*)

val _ = export_theory();
