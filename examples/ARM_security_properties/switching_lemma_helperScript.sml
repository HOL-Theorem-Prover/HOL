open HolKernel boolLib bossLib Parse proofManagerLib;
open arm_opsemTheory arm_seq_monadTheory arm_coretypesTheory arm_stepTheory;
open inference_rulesTheory tacticsLib ARM_prover_extLib;

val _ =  new_theory("switching_lemma_helper");


(****************************************************************)
(*         HELPING LEMMAS TO PROVE SWITCHING LEMMA                *)
(*                        Narges                                *)
(****************************************************************)

val get_security_ext_def =
    Define `get_security_ext s =
			     (((ARMarch2num s.information.arch = 5) ∨
                           (ARMarch2num s.information.arch = 7)) ∧
                          Extension_Security ∈ s.information.extensions)`;


val vector_table_address_def =
    Define ` vector_table_address (ExcVectorBase:bool[32]) (mode:bool[5]) =
if (mode = 17w:bool[5])
then
    [ExcVectorBase + 28w]
else if (mode = 18w:bool[5])
then
    [ExcVectorBase + 24w]
else if (mode = 19w:bool[5])
then
    [ExcVectorBase + 8w]
else if (mode = 23w:bool[5])
then [ExcVectorBase + 16w; ExcVectorBase + 12w]
else (*if (mode = 27w)*)
    [ExcVectorBase + 4w]
			`;

val get_pc_value_def =
Define `get_pc_value s1 =
let is = (if (s1.psrs (0,CPSR)).J then
	  2 + if (s1.psrs (0,CPSR)).T then 1 else 0
      else if (s1.psrs (0,CPSR)).T then
	  1
      else
	  0) in
(if InstrSet2num (if is MOD 4 =
     0
 then
     InstrSet_ARM
 else if is MOD 4 =
	 1
     then
	 InstrSet_Thumb
     else if is MOD 4 =
	     2
	 then
	     InstrSet_Jazelle
	 else if is MOD 4 =
		 3
	     then
		 InstrSet_ThumbEE
	     else
			 ARB) =
    0
 then
     s1.registers (0,RName_PC) + 8w
 else
     (s1.registers (0,RName_PC) + 4w))`;

(*
val get_base_vector_table_def =
    Define `get_base_vector_table y =
    if (y.coprocessors.state.cp15.SCTLR.V)
    then
	0xFFFF0000w
    else
	if
	    (((ARMarch2num y.information.arch = 5)
		  ∨
		  (ARMarch2num y.information.arch = 7))
		 ∧
		 Extension_Security ∈ y.information.extensions)
	then
	    (if
	 (¬y.coprocessors.state.cp15.SCR.NS
		      ∨
         ((y.psrs (0,CPSR)).M = 22w))
	     then
		 y.coprocessors.state.cp15.VBAR.secure
	     else
		 y.coprocessors.state.cp15.VBAR.non_secure)
	else
	    0w:word32`;
*)
val get_base_vector_table_def =
    Define `get_base_vector_table y =
    if (y.coprocessors.state.cp15.SCTLR.V)
    then
	0xFFFF0000w
    else
	if
	    (((ARMarch2num y.information.arch = 5)
		  ∨
		  (ARMarch2num y.information.arch = 7))
		 ∧
		 Extension_Security ∈ y.information.extensions)
	then
	    (if
	 (¬y.coprocessors.state.cp15.SCR.NS
		      ∨
         ((y.psrs (0,CPSR)).M = 22w))
	     then
		 y.coprocessors.state.cp15.VBAR
	     else
		 y.coprocessors.state.cp15.VBAR)
	else
	    0w:word32`;


fun define_pfc_goal a expr =
    set_goal([], ``
	    (priv_flags_constraints ^a ^expr) ``);

fun define_pfc_goal_abs a expr =
    set_goal([], ``
	    (priv_flags_constraints_abs ^a ^expr) ``);


val const_comp_def = Define `const_comp G = (!s s' x. ((G s = ValueState x s') ==> (s=s')))`;

val read_reg_constlem =
    store_thm(
    "read_reg_constlem",
    ``!n. const_comp (read_reg <|proc:=0|> n)``,
    FULL_SIMP_TAC (srw_ss()) [const_comp_def]
		  THEN EVAL_TAC THEN (REPEAT (RW_TAC (srw_ss()) []
						     THEN FULL_SIMP_TAC (srw_ss()) []
						     THEN UNDISCH_ALL_TAC

						     THEN RW_TAC (srw_ss()) [])));

val read_sctlr_constlem =
    store_thm(
    "read_sctlr_constlem",
    ``const_comp (read_sctlr <|proc:=0|> )``,
    FULL_SIMP_TAC (srw_ss()) [const_comp_def]
		  THEN EVAL_TAC
		  THEN (REPEAT (RW_TAC (srw_ss()) []
				       THEN FULL_SIMP_TAC (srw_ss()) []
				       THEN UNDISCH_ALL_TAC
				       THEN RW_TAC (srw_ss()) [])));


val read_scr_constlem =
    store_thm(
    "read_scr_constlem",
    ``const_comp (read_scr <|proc:=0|> )``,
    FULL_SIMP_TAC (srw_ss()) [const_comp_def]
		  THEN EVAL_TAC
		  THEN (REPEAT
			    (RW_TAC (srw_ss()) []
				    THEN FULL_SIMP_TAC (srw_ss()) []
				    THEN UNDISCH_ALL_TAC
				    THEN RW_TAC (srw_ss()) [])));

val exc_vector_base_constlem =
    store_thm(
    "exc_vector_base_constlem",
    ``const_comp (exc_vector_base <|proc:=0|> )``,
    FULL_SIMP_TAC (srw_ss()) [const_comp_def]
		  THEN EVAL_TAC
		  THEN RW_TAC (srw_ss()) []
		  THEN NTAC 2 (UNDISCH_ALL_TAC
		  THEN RW_TAC (srw_ss()) []));


val read_cpsr_quintuple_par_effect_lem = store_thm(
    "read_cpsr_quintule_par_effect_lem",
    ``!s A B C D H . (const_comp A) ==>  (const_comp B) ==>  (const_comp C) ==>
                     ((((A ||| B ||| C ||| read_cpsr <|proc:=0|> ||| D) >>= (\ (a, b, c, cpsr, d). H (a, b, c, cpsr, d))) s)
                    = (((A ||| B ||| C ||| read_cpsr <|proc:=0|> ||| D) >>= (\ (a, b, c, cpsr, d). H (a, b, c, (s.psrs (0, CPSR)), d))) s))``,
    RW_TAC (srw_ss()) [parT_def, seqT_def, constT_def]
       THEN Cases_on `A s`
       THEN FULL_SIMP_TAC (srw_ss()) [const_comp_def]
       THEN Cases_on `B b`
       THEN FULL_SIMP_TAC (srw_ss()) [const_comp_def]
       THEN Cases_on `C b'`
       THEN FULL_SIMP_TAC (srw_ss()) [const_comp_def]
       THEN RES_TAC
       THEN RW_TAC (srw_ss()) [read_cpsr_def, read__psr_def, constT_def, arm_seq_monadTheory.readT_def]
       THEN Cases_on `D b`
       THEN RW_TAC (srw_ss()) []);

val cpsr_quintuple_simp_lem = store_thm(
    "cpsr_quintuple_simp_lem",
    ``!s a n m H . (assert_mode 16w s) ==>
       ((((read_reg <|proc:=0|> a ||| read_reg <|proc:=0|> n ||| read_reg <|proc:=0|> m ||| read_cpsr <|proc:=0|> ||| read_teehbr <|proc:=0|>) >>= (\ (a, b, c, cpsr, d). H (a, b, c, cpsr, d))) s)
      = (((read_reg <|proc:=0|> a ||| read_reg <|proc:=0|> n ||| read_reg <|proc:=0|> m ||| read_cpsr <|proc:=0|> ||| read_teehbr <|proc:=0|>) >>= (\ (a, b, c, cpsr, d). H (a, b, c, ((s.psrs (0, CPSR)) with M := 16w), d))) s))``,
    RW_TAC (srw_ss()) [assert_mode_def, ARM_MODE_def, read_reg_constlem, read_cpsr_quintuple_par_effect_lem, ARM_READ_CPSR_def]
       THEN `((s.psrs (0,CPSR)).M = 16w) ==> ((s.psrs (0,CPSR)) = ((s.psrs (0,CPSR)) with M:= 16w))` by RW_TAC (srw_ss()) [arm_coretypesTheory.ARMpsr_component_equality]
       THEN METIS_TAC []);


val read_cpsr_quintuple_par_effect_with_16_lem = store_thm(
    "read_cpsr_quintule_par_effect_with_16_lem",
    ``!s A B C D H . (const_comp A) ==>  (const_comp B) ==>  (const_comp C) ==>
                     ((((A ||| B ||| C ||| read_cpsr <|proc:=0|> ||| D) >>= (\ (a, b, c, cpsr, d). H (a, b, c, (cpsr with M := 16w), d))) s)
                    = (((A ||| B ||| C ||| read_cpsr <|proc:=0|> ||| D) >>= (\ (a, b, c, cpsr, d). H (a, b, c, ((s.psrs (0, CPSR)) with M := 16w), d))) s))``,
    RW_TAC (srw_ss()) [parT_def, seqT_def, constT_def]
       THEN Cases_on `A s`
       THEN FULL_SIMP_TAC (srw_ss()) [const_comp_def]
       THEN Cases_on `B b`
       THEN FULL_SIMP_TAC (srw_ss()) [const_comp_def]
       THEN Cases_on `C b'`
       THEN FULL_SIMP_TAC (srw_ss()) [const_comp_def]
       THEN RES_TAC
       THEN RW_TAC (srw_ss()) [read_cpsr_def, read__psr_def, constT_def, arm_seq_monadTheory.readT_def]
       THEN Cases_on `D b`
       THEN RW_TAC (srw_ss()) []);


val cpsr_quintuple_simp_rel_lem = store_thm(
    "cpsr_quintuple_simp_rel_lem",
    ``!a n m H inv2 uf uy.
       (preserve_relation_mmu ((read_reg <|proc:=0|> a ||| read_reg <|proc:=0|> n ||| read_reg <|proc:=0|> m ||| read_cpsr <|proc:=0|> ||| read_teehbr <|proc:=0|>) >>= (\ (pc, b, c, cpsr, d). H (pc, b, c, cpsr, d))) (assert_mode 16w) (inv2) uf uy)
      = (preserve_relation_mmu ((read_reg <|proc:=0|> a ||| read_reg <|proc:=0|> n ||| read_reg <|proc:=0|> m ||| read_cpsr <|proc:=0|> ||| read_teehbr <|proc:=0|>) >>= (\ (pc, b, c, cpsr, d). H (pc, b, c, (cpsr with M := 16w), d))) (assert_mode 16w) (inv2) uf uy)``,
    RW_TAC (srw_ss()) [cpsr_quintuple_simp_lem, preserve_relation_mmu_def, read_reg_constlem, read_cpsr_quintuple_par_effect_with_16_lem]);


val read_cpsr_quintuple_par_effect_lem2 = store_thm(
    "read_cpsr_quintule_par_effect_lem2",
    ``!s A B D E H . (const_comp A) ==>  (const_comp B) ==>
                     ((((A ||| B ||| read_cpsr <|proc:=0|> ||| D ||| E) >>= (\ (a, b, cpsr, d, e). H (a, b, cpsr, d, e))) s)
                    = (((A ||| B ||| read_cpsr <|proc:=0|> ||| D ||| E) >>= (\ (a, b, cpsr, d, e). H (a, b, (s.psrs (0, CPSR)), d, e))) s))``,
    RW_TAC (srw_ss()) [parT_def, seqT_def, constT_def]
       THEN Cases_on `A s`
       THEN FULL_SIMP_TAC (srw_ss()) [const_comp_def]
       THEN Cases_on `B b`
       THEN FULL_SIMP_TAC (srw_ss()) [const_comp_def]
       THEN RES_TAC
       THEN RW_TAC (srw_ss()) [read_cpsr_def, read__psr_def, constT_def, arm_seq_monadTheory.readT_def]
       THEN Cases_on `D b`
       THEN FULL_SIMP_TAC (srw_ss()) [const_comp_def]
       THEN Cases_on `E b'`
       THEN RW_TAC (srw_ss()) []);

val read_cpsr_quintuple_par_effect_with_16_lem2 = store_thm(
    "read_cpsr_quintule_par_effect_with_16_lem2",
    ``!s A B D E H . (const_comp A) ==>  (const_comp B) ==>
                     ((((A ||| B ||| read_cpsr <|proc:=0|> ||| D ||| E) >>= (\ (a, b, cpsr, d, e). H (a, b, (cpsr with M := 16w), d, e))) s)
                    = (((A ||| B ||| read_cpsr <|proc:=0|> ||| D ||| E) >>= (\ (a, b, cpsr, d, e). H (a, b, ((s.psrs (0, CPSR)) with M := 16w), d, e))) s))``,
    RW_TAC (srw_ss()) [parT_def, seqT_def, constT_def]
       THEN Cases_on `A s`
       THEN FULL_SIMP_TAC (srw_ss()) [const_comp_def]
       THEN Cases_on `B b`
       THEN FULL_SIMP_TAC (srw_ss()) [const_comp_def]
       THEN RES_TAC
       THEN RW_TAC (srw_ss()) [read_cpsr_def, read__psr_def, constT_def, arm_seq_monadTheory.readT_def]
       THEN Cases_on `D b`
       THEN FULL_SIMP_TAC (srw_ss()) [const_comp_def]
       THEN Cases_on `E b'`
       THEN RW_TAC (srw_ss()) []);


val cpsr_quintuple_simp_lem2 = store_thm(
    "cpsr_quintuple_simp_lem2",
    ``!s x H . (assert_mode 16w s) ==>
       ((((read_reg <|proc:=0|> x ||| exc_vector_base <|proc:=0|> ||| read_cpsr <|proc:=0|> ||| read_scr <|proc:=0|> ||| read_sctlr <|proc:=0|>) >>= (\ (a, b, cpsr, d, e). H (a, b, cpsr, d, e))) s)
      = (((read_reg <|proc:=0|> x ||| exc_vector_base <|proc:=0|> ||| read_cpsr <|proc:=0|> ||| read_scr <|proc:=0|> ||| read_sctlr <|proc:=0|>) >>= (\ (a, b, cpsr, d, e). H (a, b, ((s.psrs (0, CPSR)) with M := 16w), d, e))) s))``,
    RW_TAC (srw_ss()) [assert_mode_def, ARM_MODE_def, read_reg_constlem, exc_vector_base_constlem, read_cpsr_quintuple_par_effect_lem2, ARM_READ_CPSR_def]
       THEN `((s.psrs (0,CPSR)).M = 16w) ==> ((s.psrs (0,CPSR)) = ((s.psrs (0,CPSR)) with M:= 16w))` by RW_TAC (srw_ss()) [arm_coretypesTheory.ARMpsr_component_equality]
       THEN METIS_TAC []);


val cpsr_quintuple_simp_rel_lem2 = store_thm(
    "cpsr_quintuple_simp_rel_lem2",
    ``!x H inv2 uf uy.
       (preserve_relation_mmu (((read_reg <|proc:=0|> x ||| exc_vector_base <|proc:=0|> ||| read_cpsr <|proc:=0|> ||| read_scr <|proc:=0|> ||| read_sctlr <|proc:=0|>) >>= (\ (pc, ExcVectorBase, cpsr, scr, sctlr). H (pc, ExcVectorBase, cpsr, scr, sctlr)))) (assert_mode 16w) (inv2) uf uy)
      = (preserve_relation_mmu (((read_reg <|proc:=0|> x ||| exc_vector_base <|proc:=0|> ||| read_cpsr <|proc:=0|> ||| read_scr <|proc:=0|> ||| read_sctlr <|proc:=0|>) >>= (\ (pc, ExcVectorBase, cpsr, scr, sctlr). H (pc, ExcVectorBase, (cpsr with M := 16w), scr, sctlr))))(assert_mode 16w) (inv2) uf uy)``,
    RW_TAC (srw_ss()) [cpsr_quintuple_simp_lem2, preserve_relation_mmu_def, read_reg_constlem, exc_vector_base_constlem, read_cpsr_quintuple_par_effect_with_16_lem2]);


val read_cpsr_effect_lem = store_thm(
    "read_cpsr_effect_lem",
    ``!s H .  ((read_cpsr <|proc:=0|> >>= (\ (cpsr). H (cpsr))) s = (read_cpsr <|proc:=0|> >>= (\ (cpsr). H (s.psrs (0, CPSR)))) s)``,
    RW_TAC (srw_ss()) [parT_def, seqT_def, constT_def]
       THEN FULL_SIMP_TAC (srw_ss()) []
       THEN RES_TAC
       THEN RW_TAC (srw_ss()) [read_cpsr_def, read__psr_def, constT_def, arm_seq_monadTheory.readT_def]);


val cpsr_simp_lem = store_thm(
    "cpsr_simp_lem",
    ``!s H u. (assert_mode u s) ==>
       (((read_cpsr <|proc:=0|> >>= (\ (cpsr). H (cpsr))) s)
      = ((read_cpsr <|proc:=0|> >>= (\ (cpsr). H (cpsr with M := u))) s))``,
    RW_TAC (srw_ss()) [assert_mode_def, ARM_MODE_def, read_cpsr_effect_lem, ARM_READ_CPSR_def]
       THEN `s.psrs (0,CPSR) = s.psrs (0,CPSR) with M := (s.psrs (0,CPSR)).M` by RW_TAC (srw_ss()) [arm_coretypesTheory.ARMpsr_component_equality]
       THEN METIS_TAC []);

val cpsr_simp_rel_lem = store_thm(
    "cpsr_simp_rel_lem",
    ``!H inv2 uf uy u.
       (preserve_relation_mmu (read_cpsr <|proc:=0|> >>= (\ (cpsr). H (cpsr))) (assert_mode u) (inv2) uf uy)
      = (preserve_relation_mmu (read_cpsr <|proc:=0|> >>= (\ (cpsr). H (cpsr with M := u)))(assert_mode u) (inv2) uf uy)``,
     RW_TAC (srw_ss()) [preserve_relation_mmu_def]
	    THEN  METIS_TAC [cpsr_simp_lem]);

(* End of borrowed theorems *)

val read_cpsr_constlem =
    store_thm(
    "read_cpsr_constlem",
    ``const_comp (read_cpsr <|proc:=0|> )``,
    FULL_SIMP_TAC (srw_ss()) [const_comp_def]
		  THEN EVAL_TAC
		  THEN (REPEAT (RW_TAC (srw_ss()) []
				       THEN FULL_SIMP_TAC (srw_ss()) []
				       THEN UNDISCH_ALL_TAC
				       THEN RW_TAC (srw_ss()) [])));

val  parT_const_comp_thm =
     store_thm(
     "parT_const_comp_thm",
     ``! f h. const_comp f ==>
	      const_comp h ==>
	      const_comp (f ||| h)``
   ,
   RW_TAC (srw_ss()) [parT_def,seqT_def,const_comp_def,constT_def] THEN
	  Cases_on ` f s ` THEN
	  RES_TAC THEN
	  FULL_SIMP_TAC (srw_ss()) [] THEN
	  Cases_on ` h b ` THEN
	  RES_TAC THEN
	  FULL_SIMP_TAC (srw_ss()) [] THEN
	  RW_TAC (srw_ss()) [] THEN
	  Cases_on ` access_violation b` THEN
	  FULL_SIMP_TAC (srw_ss()) []);


val  fixed_sctrl_undef_svc_thm1 =
     store_thm(
     "fixed_sctrl_undef_svc_thm1",
     ``!s A B C D H .
	      (const_comp A) ==>
	      (const_comp B) ==>
	      (const_comp C) ==>
	      (const_comp D) ==>
	      ((((A ||| B ||| C ||| D
		    ||| read_sctlr <|proc:=0|>) >>=
					   (\ (a, b, c, d, e). H (a, b, c, d, e))) s)
	       = (((A ||| B ||| C ||| D |||
		      read_sctlr <|proc:=0|>) >>=
				 (\ (a, b, c, d, e). H (a, b, c, d, s.coprocessors.state.cp15.SCTLR))) s))
``,
     RW_TAC (srw_ss()) [parT_def, seqT_def, constT_def]
	    THEN Cases_on `A s`
	    THEN FULL_SIMP_TAC (srw_ss())  [const_comp_def]
	    THEN RES_TAC
	    THEN Cases_on `B s`
	    THEN FULL_SIMP_TAC (srw_ss())  [const_comp_def]
	    THEN RES_TAC
	    THEN Cases_on `C s`
	    THEN FULL_SIMP_TAC (srw_ss())  [const_comp_def]
	    THEN RES_TAC
	    THEN Cases_on `D s`
	    THEN FULL_SIMP_TAC (srw_ss())  [const_comp_def]
	    THEN RES_TAC
	    THEN FULL_SIMP_TAC (srw_ss()) [read_sctlr_def,arm_seq_monadTheory.readT_def]
	    THEN RW_TAC (srw_ss())  []
     );

val  fixed_cpsr_undef_svc_thm1 =
     store_thm(
     "fixed_cpsr_undef_svc_thm1",
     ``!s A B C D H .
	      (const_comp A) ==>
	      (const_comp B) ==>
	      ((((A ||| B ||| read_cpsr <|proc := 0|> ||| C ||| D) >>=
					   (\ (a, b, c, d, e). H (a, b, c, d, e))) s)
	       = (((A ||| B ||| read_cpsr <|proc := 0|> ||| C ||| D) >>=
				 (\ (a, b, c, d, e). H (a, b, s.psrs (0,CPSR), d, e))) s))
``,
     RW_TAC (srw_ss()) [parT_def, seqT_def, constT_def]
	    THEN Cases_on `A s`
	    THEN FULL_SIMP_TAC (srw_ss())  [const_comp_def]
	    THEN RES_TAC
	    THEN Cases_on `B s`
	    THEN FULL_SIMP_TAC (srw_ss())  [const_comp_def]
	    THEN RES_TAC
	    THEN FULL_SIMP_TAC (srw_ss()) [read_cpsr_def,read__psr_def,arm_seq_monadTheory.readT_def]
	    THEN RW_TAC (srw_ss())  []
	    THEN Cases_on `C b`
	    THEN Cases_on ` access_violation b'`
	    THEN FULL_SIMP_TAC (srw_ss())  []
	    THEN Cases_on `D b'`
	    THEN Cases_on ` access_violation b''`
	    THEN FULL_SIMP_TAC (srw_ss())  []

     );

val  fixed_sctrl_abt_irq_thm1 =
     store_thm(
     "fixed_sctrl_abt_irq_thm1",
     ``!s A B C D E H .
	      (const_comp A) ==>
	      (const_comp B) ==>
	      (const_comp C) ==>
	      (const_comp D) ==>
	      (const_comp E) ==>
	      ((((A ||| B ||| C ||| D ||| E
		    ||| read_sctlr <|proc:=0|>) >>=
					   (\ (a, b, c, d, e,f). H (a, b, c, d, e,f))) s)
	       = (((A ||| B ||| C ||| D ||| E |||
		      read_sctlr <|proc:=0|>) >>=
				 (\ (a, b, c, d, e,f). H (a, b, c, d, e, s.coprocessors.state.cp15.SCTLR))) s))
``,
     RW_TAC (srw_ss()) [parT_def, seqT_def, constT_def]
	    THEN Cases_on `A s`
	    THEN FULL_SIMP_TAC (srw_ss())  [const_comp_def]
	    THEN RES_TAC
	    THEN Cases_on `B s`
	    THEN FULL_SIMP_TAC (srw_ss())  [const_comp_def]
	    THEN RES_TAC
	    THEN Cases_on `C s`
	    THEN FULL_SIMP_TAC (srw_ss())  [const_comp_def]
	    THEN RES_TAC
	    THEN Cases_on `D s`
	    THEN FULL_SIMP_TAC (srw_ss())  [const_comp_def]
	    THEN RES_TAC
	    THEN Cases_on `E s`
	    THEN FULL_SIMP_TAC (srw_ss())  [const_comp_def]
	    THEN RES_TAC
	    THEN FULL_SIMP_TAC (srw_ss()) [read_sctlr_def,arm_seq_monadTheory.readT_def]
	    THEN RW_TAC (srw_ss())  []
     );


val  fixed_undef_svc_exception_rp_thm2 = store_thm(
    "fixed_undef_svc_exception_rp_thm2",
    ``!s e d c b a.
	  (~access_violation s) ==>
	  (((read_reg <|proc:=0|> 15w ||| exc_vector_base <|proc:=0|> |||
	   read_cpsr <|proc:=0|> ||| read_scr <|proc:=0|> |||
           read_sctlr <|proc:=0|>) s)
	= ValueState (a, b, c, d, e) s) ==>
	  ((a = get_pc_value s)
	   /\
		(b=get_base_vector_table s)
	   /\
		(c=s.psrs (0,CPSR ))
	   /\
		(d=s.coprocessors.state.cp15.SCR)
	   /\
		(e=s.coprocessors.state.cp15.SCTLR))``,
    EVAL_TAC
	THEN RW_TAC (srw_ss())  []
				       );


val  fixed_abort_irq_exception_rp_thm2 = store_thm(
    "fixed_abort_irq_exception_rp_thm2",
    ``!s f e d c b a .
	  (~access_violation s) ==>
	  (* (Extension_Security ∉ s.information.extensions) ==> *)
	  (((read_reg <|proc:=0|> 15w ||| exc_vector_base <|proc:=0|> ||| have_security_ext <|proc:=0|>
        ||| read_cpsr <|proc:=0|> ||| read_scr <|proc:=0|> ||| read_sctlr <|proc:=0|>) s)
	= (ValueState (a, b, c, d, e, f) s)) ==>
	  ((a = get_pc_value s)
	   /\
		(b=get_base_vector_table s)
	   /\
	   	(c = (((ARMarch2num s.information.arch = 5) ∨
         (ARMarch2num s.information.arch = 7)) ∧
        Extension_Security ∈ s.information.extensions))
	   /\
	(d=s.psrs (0,CPSR ))
	   /\
		(e=s.coprocessors.state.cp15.SCR)
	   /\
		(f=s.coprocessors.state.cp15.SCTLR))``,
    EVAL_TAC
	THEN RW_TAC (srw_ss())  []);

val have_security_ext_constlem =
    store_thm(
    "have_security_ext_constlem",
    ``const_comp (have_security_ext <|proc := 0|>)``,
    FULL_SIMP_TAC (srw_ss()) [const_comp_def]
		  THEN EVAL_TAC THEN (REPEAT (RW_TAC (srw_ss()) []
						     THEN FULL_SIMP_TAC (srw_ss()) []
						     THEN UNDISCH_ALL_TAC

						     THEN RW_TAC (srw_ss()) [])));

val const_comp_take_undef_svc_exception_rp_thm =
    store_thm(
    "const_comp_take_undef_svc_exception_rp_thm",
    ``const_comp (read_reg <|proc := 0|> 15w
	          ||| exc_vector_base <|proc := 0|>
		  ||| read_cpsr <|proc := 0|> ||| read_scr <|proc := 0|>
		  ||| read_sctlr <|proc := 0|>)``,
    ASSUME_TAC (SPEC ``15w:bool[4]`` read_reg_constlem)
	       THEN ASSUME_TAC read_cpsr_constlem
	       THEN ASSUME_TAC exc_vector_base_constlem
	       THEN ASSUME_TAC read_scr_constlem
	       THEN ASSUME_TAC read_sctlr_constlem
	       THEN
	       `const_comp (read_scr <|proc := 0|>
						||| read_sctlr <|proc := 0|>)` by
	       IMP_RES_TAC parT_const_comp_thm
	       THEN
	       `const_comp ( read_cpsr <|proc := 0|> ||| read_scr <|proc := 0|>
			  ||| read_sctlr <|proc := 0|>)` by
	       IMP_RES_TAC parT_const_comp_thm
	       THEN
	       `const_comp (exc_vector_base <|proc := 0|>
			||| read_cpsr <|proc := 0|> ||| read_scr <|proc := 0|>
													   ||| read_sctlr <|proc := 0|>)` by
	       IMP_RES_TAC parT_const_comp_thm
	       THEN
	       `const_comp (read_reg <|proc := 0|> 15w
			||| exc_vector_base <|proc := 0|>
			    ||| read_cpsr <|proc := 0|> ||| read_scr <|proc := 0|>
																   ||| read_sctlr <|proc := 0|>)`
	       by IMP_RES_TAC parT_const_comp_thm);




val const_comp_take_abort_irq_exception_rp_thm =
    store_thm(
    "const_comp_take_abort_irq_exception_rp_thm",
    ``const_comp (read_reg <|proc := 0|> 15w ||| exc_vector_base <|proc := 0|>
          ||| have_security_ext <|proc := 0|>
          ||| read_cpsr <|proc := 0|> ||| read_scr <|proc := 0|>
          ||| read_sctlr <|proc := 0|>)``,
    ASSUME_TAC (SPEC ``15w:bool[4]`` read_reg_constlem)
	       THEN ASSUME_TAC read_cpsr_constlem
	       THEN ASSUME_TAC exc_vector_base_constlem
	       THEN ASSUME_TAC read_scr_constlem
	       THEN ASSUME_TAC have_security_ext_constlem
	       THEN ASSUME_TAC read_sctlr_constlem
	       THEN
	       `const_comp (read_scr <|proc := 0|>
						||| read_sctlr <|proc := 0|>)` by
	       IMP_RES_TAC parT_const_comp_thm
	       THEN
	       `const_comp ( read_cpsr <|proc := 0|> ||| read_scr <|proc := 0|>
			  ||| read_sctlr <|proc := 0|>)` by
	       IMP_RES_TAC parT_const_comp_thm
	       THEN
	       `const_comp (have_security_ext <|proc := 0|> ||| read_cpsr <|proc := 0|>
     ||| read_scr <|proc := 0|> ||| read_sctlr <|proc := 0|>)` by
	       IMP_RES_TAC parT_const_comp_thm
	       THEN
	       `const_comp (exc_vector_base <|proc := 0|>
                           ||| have_security_ext <|proc := 0|> |||
                          read_cpsr <|proc := 0|>
                          ||| read_scr <|proc := 0|> ||| read_sctlr <|proc := 0|>)`
	       by IMP_RES_TAC parT_const_comp_thm
	       THEN METIS_TAC [parT_const_comp_thm]);




val  fixed_undef_svc_exception_rp_thm3 = store_thm(
    "fixed_undef_svc_exception_rp_thm3",
    ``!s H.
          ((s.psrs (0,CPSR)).M = 16w:bool[5] ) ==>
	  (~access_violation s) ==>
	  ((((read_reg <|proc:=0|> 15w ||| exc_vector_base <|proc:=0|> |||
	   read_cpsr <|proc:=0|> ||| read_scr <|proc:=0|> |||
           read_sctlr <|proc:=0|>) >>=
				   (\ (a, b, c, d, e). (H:
	    (bool[32]#bool[32]#ARMpsr#CP15scr#CP15sctlr -> unit M)) (a, b, c, d, e))) s)
	= (((read_reg <|proc:=0|> 15w ||| exc_vector_base <|proc:=0|> |||
	   read_cpsr <|proc:=0|> ||| read_scr <|proc:=0|> |||
           read_sctlr <|proc:=0|>) >>=
				   (\ (a, b, c, d, e). H (
				    get_pc_value s,
				    get_base_vector_table s,
				    s.psrs (0,CPSR ) with M := 16w ,
				    s.coprocessors.state.cp15.SCR,
				    s.coprocessors.state.cp15.SCTLR))) s))``,
    EVAL_TAC
	THEN RW_TAC (srw_ss())  []
	THEN `((s.psrs (0,CPSR)).M = 16w) ==> ((s.psrs (0,CPSR)) = ((s.psrs (0,CPSR)) with M:= 16w))` by RW_TAC (srw_ss()) [arm_coretypesTheory.ARMpsr_component_equality]
       THEN METIS_TAC []
 );


val  fixed_abt_irq_exception_rp_thm3 = store_thm(
    "fixed_abt_irq_exception_rp_thm3",
    ``!s H.
          ((s.psrs (0,CPSR)).M = 16w:bool[5] ) ==>
	  (~access_violation s) ==>
	  ((((read_reg <|proc:=0|> 15w ||| exc_vector_base <|proc:=0|> ||| have_security_ext <|proc := 0|> |||
	   read_cpsr <|proc:=0|> ||| read_scr <|proc:=0|> |||
           read_sctlr <|proc:=0|>) >>=
				   (\ (a, b, c, d, e,f). (H:
	    (bool[32]#bool[32]#bool#ARMpsr#CP15scr#CP15sctlr -> unit M)) (a, b, c, d, e,f))) s)
	= (((read_reg <|proc:=0|> 15w ||| exc_vector_base <|proc:=0|> ||| have_security_ext <|proc := 0|> |||
	   read_cpsr <|proc:=0|> ||| read_scr <|proc:=0|> |||
           read_sctlr <|proc:=0|>) >>=
				   (\ (a, b, c, d, e,f). H (
				    get_pc_value s,
				    get_base_vector_table s,
				    get_security_ext s,
				    s.psrs (0,CPSR ) with M := 16w ,
				    s.coprocessors.state.cp15.SCR,
				    s.coprocessors.state.cp15.SCTLR))) s))``,
    EVAL_TAC
	THEN RW_TAC (srw_ss())  []
				THEN `((s.psrs (0,CPSR)).M = 16w) ==> ((s.psrs (0,CPSR)) = ((s.psrs (0,CPSR)) with M:= 16w))` by RW_TAC (srw_ss()) [arm_coretypesTheory.ARMpsr_component_equality]
       THEN METIS_TAC []
 );



val  fixed_VectorBase_undef_instr_exception_thm1 = store_thm(
    "fixed_VectorBase_undef_instr_exception_thm1",
    ``! e d c b a s.
	  (~access_violation s) ==>
	  (* (Extension_Security ∉ s.information.extensions) ==> *)
	  (((read_reg <|proc:=0|> 15w ||| exc_vector_base <|proc:=0|> |||
	   read_cpsr <|proc:=0|> ||| read_scr <|proc:=0|> |||
           read_sctlr <|proc:=0|>) s)
	= ValueState (a, b, c, d, e) s) ==>
	  (b=get_base_vector_table s)``,
    EVAL_TAC
	THEN RW_TAC (srw_ss())  []
					       );

val  fixed_VectorBase_undef_instr_exception_thm2 = store_thm(
    "fixed_VectorBase_undef_instr_exception_thm2",
    ``!s H.
	  (~access_violation s) ==>
	  ((((read_reg <|proc:=0|> 15w ||| exc_vector_base <|proc:=0|> |||
	   read_cpsr <|proc:=0|> ||| read_scr <|proc:=0|> |||
           read_sctlr <|proc:=0|>) >>=
				   (\ (a, b, c, d, e). (H:
	    (bool[32]#bool[32]#ARMpsr#CP15scr#CP15sctlr -> unit M)) (a, b, c, d, e))) s)
	= (((read_reg <|proc:=0|> 15w ||| exc_vector_base <|proc:=0|> |||
	   read_cpsr <|proc:=0|> ||| read_scr <|proc:=0|> |||
           read_sctlr <|proc:=0|>) >>=
				   (\ (a, b, c, d, e). H (
				    a , (get_base_vector_table s)
				  ,
				    c,
				    d,
				    e))) s))``,
    EVAL_TAC
	THEN RW_TAC (srw_ss())  []

 );

val  fixed_VectorBase_abort_irq_exception_thm1 = store_thm(
    "fixed_VectorBase_abort_irq_exception_thm1",
    ``! f e d c b a s.
	  (~access_violation s) ==>
	  (((read_reg <|proc:=0|> 15w ||| exc_vector_base <|proc:=0|> |||
	      have_security_ext <|proc:=0|> |||
	   read_cpsr <|proc:=0|> ||| read_scr <|proc:=0|> |||
           read_sctlr <|proc:=0|>) s)
	= ValueState (a, b, c, d, e,f) s) ==>
	  (b=get_base_vector_table s
	  )``,
    EVAL_TAC
	THEN RW_TAC (srw_ss())  []
					       );

val  fixed_VectorBase_abort_irq_exception_thm2 = store_thm(
    "fixed_VectorBase_abort_irq_exception_thm2",
    ``!s H.
	  (~access_violation s) ==>
	  ((((read_reg <|proc:=0|> 15w ||| exc_vector_base <|proc:=0|> |||
              have_security_ext <|proc:=0|> |||
	   read_cpsr <|proc:=0|> ||| read_scr <|proc:=0|> |||
           read_sctlr <|proc:=0|>) >>=
				   (\ (a, b, c, d, e,f). (H:
	    (bool[32]#bool[32]#bool#ARMpsr#CP15scr#CP15sctlr -> unit M)) (a, b, c, d, e,f))) s)
	= (((read_reg <|proc:=0|> 15w ||| exc_vector_base <|proc:=0|> |||
	      have_security_ext <|proc:=0|> |||
	   read_cpsr <|proc:=0|> ||| read_scr <|proc:=0|> |||
           read_sctlr <|proc:=0|>) >>=
				   (\ (a, b, c, d, e,f). H (
				    a ,(get_base_vector_table s)
				  ,
				    c,
				    d,
				    e, f))) s))``,
    EVAL_TAC
	THEN RW_TAC (srw_ss())  []

 );


val  fixed_sctrl_undef_svc_thm2 =
     store_thm(
     "fixed_sctrl_undef_svc_thm2",
     ``!s e d c b a.
	      (~access_violation s) ==>
	      (((read_reg <|proc:=0|> 15w |||
				   exc_vector_base <|proc:=0|> |||
							    read_cpsr <|proc:=0|> ||| read_scr <|proc:=0|> ||| read_sctlr <|proc:=0|>) s)
	       = ValueState (a, b, c, d, e) s) ==>
	      (e = s.coprocessors.state.cp15.SCTLR) ``,
     RW_TAC (srw_ss()) [parT_def, seqT_def, constT_def] THEN
	    ASSUME_TAC (SPEC ``15w:bool[4]`` read_reg_constlem) THEN
	    ASSUME_TAC exc_vector_base_constlem THEN
	    ASSUME_TAC read_cpsr_constlem THEN
	    ASSUME_TAC read_scr_constlem
	    THEN FULL_SIMP_TAC (srw_ss())  [const_comp_def]
	    THEN Cases_on `read_reg <|proc:=0|> 15w s`
	    THEN FULL_SIMP_TAC (srw_ss())  []
	    THEN RES_TAC
	    THEN RW_TAC (srw_ss())  []
	    THEN Cases_on `exc_vector_base <|proc:=0|> b'`
	    THEN RW_TAC (srw_ss())  [const_comp_def]
	    THEN RES_TAC
	    THEN Cases_on `read_cpsr <|proc:=0|>  b'`
	    THEN RW_TAC (srw_ss())  [const_comp_def]
	    THEN RES_TAC
	    THEN Cases_on `read_scr <|proc:=0|> b'`
	    THEN RW_TAC (srw_ss())  [const_comp_def]
	    THEN RES_TAC
	    THEN FULL_SIMP_TAC (srw_ss()) [read_sctlr_def,readT_def]
	    THEN RW_TAC (srw_ss())  []
	    THEN Cases_on `access_violation b'`
	    THEN FULL_SIMP_TAC (srw_ss()) [read_sctlr_def,readT_def]
	    THEN RW_TAC (srw_ss())  []);



val  fixed_sctrl_abt_irq_thm2 =
     store_thm(
     "fixed_sctrl_abt_irq_thm2",
     ``!s f e d c b a.
	      (~access_violation s) ==>
	      (((read_reg <|proc:=0|> 15w |||
		 exc_vector_base <|proc:=0|>
                 ||| have_security_ext <|proc:=0|> |||
              read_cpsr <|proc:=0|> ||| read_scr <|proc:=0|> ||| read_sctlr <|proc:=0|>) s)
	       = ValueState (a, b, c, d, e,f) s) ==>
	      (f = s.coprocessors.state.cp15.SCTLR) ``,
     RW_TAC (srw_ss()) [parT_def, seqT_def, constT_def] THEN
	    ASSUME_TAC (SPEC ``15w:bool[4]`` read_reg_constlem) THEN
	    ASSUME_TAC exc_vector_base_constlem THEN
	    ASSUME_TAC read_cpsr_constlem THEN
	    ASSUME_TAC read_scr_constlem THEN
	    ASSUME_TAC have_security_ext_constlem
	    THEN FULL_SIMP_TAC (srw_ss())  [const_comp_def]
	    THEN Cases_on `read_reg <|proc:=0|> 15w s`
	    THEN FULL_SIMP_TAC (srw_ss())  []
	    THEN RES_TAC
	    THEN RW_TAC (srw_ss())  []
	    THEN Cases_on `exc_vector_base <|proc:=0|> b'`
	    THEN RW_TAC (srw_ss())  [const_comp_def]
	    THEN RES_TAC
	    THEN Cases_on `read_cpsr <|proc:=0|>  b'`
	    THEN RW_TAC (srw_ss())  [const_comp_def]
	    THEN RES_TAC
	    THEN Cases_on `read_scr <|proc:=0|> b'`
	    THEN RW_TAC (srw_ss())  [const_comp_def]
	    THEN RES_TAC
	    THEN Cases_on `have_security_ext <|proc:=0|> b'`
	    THEN RW_TAC (srw_ss())  [const_comp_def]
	    THEN RES_TAC
	    THEN FULL_SIMP_TAC (srw_ss()) [read_sctlr_def,readT_def]
	    THEN RW_TAC (srw_ss())  []
	    THEN Cases_on `access_violation b'`
	    THEN FULL_SIMP_TAC (srw_ss()) [read_sctlr_def,readT_def]
	    THEN RW_TAC (srw_ss())  []);



val  fixed_sctrl_undef_svc_thm = store_thm(
		       "fixed_sctrl_undef_svc_thm",
		       ``!s H .
				((((read_reg <|proc:=0|> 15w |||
				   exc_vector_base <|proc:=0|> |||
				   read_cpsr <|proc:=0|> ||| read_scr <|proc:=0|> |||
				   read_sctlr <|proc:=0|>) >>= (\ (pc,ExcVectorBase,cpsr,scr,sctlr). H (pc,ExcVectorBase,cpsr,scr,sctlr))) s)
				 =
				 (((read_reg <|proc:=0|> 15w ||| exc_vector_base <|proc:=0|> |||
				   read_cpsr <|proc:=0|> ||| read_scr <|proc:=0|> ||| read_sctlr <|proc:=0|>) >>=
				   (\(pc,ExcVectorBase,cpsr,scr,sctlr). H (pc,ExcVectorBase,cpsr,scr, s.coprocessors.state.cp15.SCTLR))) s))``,
		       MP_TAC (SPEC ``15w:bool[4]`` read_reg_constlem)
			      THEN MP_TAC read_cpsr_constlem
			      THEN MP_TAC exc_vector_base_constlem
			      THEN MP_TAC read_scr_constlem
			      THEN RW_TAC (srw_ss()) [fixed_sctrl_undef_svc_thm1]
		       );

val fixed_cpsr_undef_svc_thm =
    store_thm ("fixed_cpsr_undef_svc_thm",
	       ``!s H .
				((((read_reg <|proc:=0|> 15w |||
				    exc_vector_base <|proc:=0|> |||
				    read_cpsr <|proc:=0|> ||| read_scr <|proc:=0|> |||
				    read_sctlr <|proc:=0|>) >>=
                (\ (pc,ExcVectorBase,cpsr,scr,sctlr). H (pc,ExcVectorBase,cpsr,scr,sctlr))) s)
				 = (((read_reg <|proc:=0|> 15w |||
				     exc_vector_base <|proc:=0|> |||
				     read_cpsr <|proc:=0|> |||
				     read_scr <|proc:=0|> |||
				     read_sctlr <|proc:=0|>) >>=
		(\ (pc,ExcVectorBase,cpsr,scr,sctlr). H (pc,ExcVectorBase,s.psrs (0,CPSR),scr,sctlr))) s))``,
	       MP_TAC (SPEC ``15w:bool[4]`` read_reg_constlem)
		      THEN MP_TAC read_cpsr_constlem
		      THEN MP_TAC exc_vector_base_constlem
		      THEN MP_TAC read_scr_constlem
		      THEN RW_TAC (srw_ss()) [fixed_cpsr_undef_svc_thm1]
		      );


val  fixed_sctrl_abt_irq_thm = store_thm(
		       "fixed_sctrl_abt_irq_thm",
		       ``!s H .
				((((read_reg <|proc:=0|> 15w |||
				   exc_vector_base <|proc:=0|> |||
                                   have_security_ext <|proc := 0|> |||
				   read_cpsr <|proc:=0|> ||| read_scr <|proc:=0|> |||
				   read_sctlr <|proc:=0|>) >>= (\ (pc,ExcVectorBase,have_security_ext1,cpsr,scr,sctlr). H (pc,ExcVectorBase,have_security_ext1,cpsr,scr,sctlr))) s)
				 =
				 (((read_reg <|proc:=0|> 15w ||| exc_vector_base <|proc:=0|> |||
                                   have_security_ext <|proc := 0|> |||
				   read_cpsr <|proc:=0|> ||| read_scr <|proc:=0|> ||| read_sctlr <|proc:=0|>) >>=
				   (\(pc,ExcVectorBase,have_security_ext1,cpsr,scr,sctlr). H (pc,ExcVectorBase,have_security_ext1,cpsr,scr, s.coprocessors.state.cp15.SCTLR))) s))``,
		       MP_TAC (SPEC ``15w:bool[4]`` read_reg_constlem)
			      THEN MP_TAC read_cpsr_constlem
			      THEN MP_TAC exc_vector_base_constlem
			      THEN MP_TAC read_scr_constlem
			      THEN MP_TAC have_security_ext_constlem
			      THEN RW_TAC (srw_ss()) [fixed_sctrl_abt_irq_thm1]
		       );

val read_cpsr_quintuple_par_effect_lem1 = store_thm(
    "read_cpsr_quintule_par_effect_lem1",
    ``!s A B C D H . (const_comp A) ==>  (const_comp B) ==>  (const_comp C) ==>
                     ((((A ||| B ||| C ||| read_cpsr <|proc:=0|> ||| D ||| E) >>= (\ (a, b, c, cpsr, d,e). H (a, b, c, cpsr, d,e))) s)
                    = (((A ||| B ||| C ||| read_cpsr <|proc:=0|> ||| D ||| E) >>= (\ (a, b, c, cpsr, d,e). H (a, b, c, (s.psrs (0, CPSR)), d,e))) s))``,
    RW_TAC (srw_ss()) [parT_def, seqT_def, constT_def]
       THEN Cases_on `A s`
       THEN FULL_SIMP_TAC (srw_ss()) [const_comp_def]
       THEN Cases_on `B b`
       THEN FULL_SIMP_TAC (srw_ss()) [const_comp_def]
       THEN Cases_on `C b'`
       THEN FULL_SIMP_TAC (srw_ss()) [const_comp_def]
       THEN RES_TAC
       THEN RW_TAC (srw_ss()) [read_cpsr_def, read__psr_def, constT_def, arm_seq_monadTheory.readT_def]
       THEN Cases_on `D b`
       THEN RW_TAC (srw_ss()) []
       THEN Cases_on `E b'`
       THEN RW_TAC (srw_ss()) []
);


val  fixed_cpsr_abt_irq_thm = store_thm(
		       "fixed_cpsr_abt_irq_thm",
		       ``!s H .
				((((read_reg <|proc:=0|> 15w |||
				    exc_vector_base <|proc:=0|> |||
                                    have_security_ext <|proc := 0|> |||
				    read_cpsr <|proc:=0|> ||| read_scr <|proc:=0|> |||
				    read_sctlr <|proc:=0|>) >>=
                (\ (pc,ExcVectorBase,have_security_ext1,cpsr,scr,sctlr).
                 H (pc,ExcVectorBase,have_security_ext1,cpsr,scr,sctlr))) s)
				 = (((read_reg <|proc:=0|> 15w |||
				     exc_vector_base <|proc:=0|> |||
                                     have_security_ext <|proc := 0|> |||
				     read_cpsr <|proc:=0|> |||
				     read_scr <|proc:=0|> |||
				     read_sctlr <|proc:=0|>) >>=
		(\ (pc,ExcVectorBase,have_security_ext1,cpsr,scr,sctlr).
                 H (pc,ExcVectorBase,have_security_ext1,s.psrs (0,CPSR),scr,sctlr))) s))``,
RW_TAC (srw_ss()) [read_reg_constlem, exc_vector_base_constlem, have_security_ext_constlem, read_cpsr_quintuple_par_effect_lem1, ARM_READ_CPSR_def]
);


val  fixed_cpsr_undef_svc_thm2 =
     store_thm("fixed_cpsr_undef_svc_thm2",
			``!s a b c d e.
				 (~access_violation s) ==>
				 (((read_reg <|proc:=0|> 15w |||
				    exc_vector_base <|proc:=0|> |||
				    read_cpsr <|proc:=0|> ||| read_scr <|proc:=0|> ||| read_sctlr <|proc:=0|>) s)
				  = ValueState (a, b, c, d, e) s) ==>
				 (c = s.psrs (0,CPSR)) ``,
RW_TAC (srw_ss()) [fixed_undef_svc_exception_rp_thm2]);


val  fixed_cpsr_abt_irq_thm2 =
     store_thm("fixed_cpsr_abt_irq_thm2",
	       ``!s a b c d e f.
	      (~access_violation s) ==>
	      (((read_reg <|proc := 0|> 15w ||| exc_vector_base <|proc := 0|>
                ||| have_security_ext <|proc := 0|> ||| read_cpsr <|proc := 0|>
                ||| read_scr <|proc := 0|> ||| read_sctlr <|proc := 0|>) s)
				  = ValueState (a, b, c, d, e ,f) s) ==>
				 (d = s.psrs (0,CPSR)) ``
,
RW_TAC (srw_ss()) [fixed_abort_irq_exception_rp_thm2]);


val  fixed_pc_undef_svc_thm2 =
     store_thm("fixed_pc_undef_svc_thm2",
	       ``!s a b c d e.
	      (~access_violation s) ==>
	      (((read_reg <|proc:=0|> 15w |||
				   exc_vector_base <|proc:=0|> |||
				    read_cpsr <|proc:=0|> ||| read_scr <|proc:=0|> ||| read_sctlr <|proc:=0|>) s)
				  = ValueState (a, b, c, d, e) s) ==>
				 (a = get_pc_value s)``,
RW_TAC (srw_ss()) [fixed_undef_svc_exception_rp_thm2]);

val  fixed_pc_abt_irq_thm2 =
     store_thm("fixed_pc_abt_irq_thm2",
	       ``!s a b c d e f.
	      (~access_violation s) ==>
	      (((read_reg <|proc:=0|> 15w |||
				   exc_vector_base <|proc:=0|>
||| have_security_ext <|proc := 0|> |||
				    read_cpsr <|proc:=0|> ||| read_scr <|proc:=0|> ||| read_sctlr <|proc:=0|>) s)
				  = ValueState (a, b, c, d, e,f) s) ==>
				 (a = get_pc_value s)``
,
RW_TAC (srw_ss()) [fixed_abort_irq_exception_rp_thm2]);


(******************************************************)
(*******************GENERAL THEOREMS ******************)
(******************************************************)

val hlp_seqT_thm =
store_thm ("hlp_seqT_thm",
			      ``!f g s a s' a'. ((f >>= g) s = ValueState a s') ⇒
			     (f s = ValueState a' s) ⇒
			     ¬access_violation s ⇒
			     (g a' s = ValueState a s')``,
			      RW_TAC (srw_ss()) [seqT_def]
				     THEN FULL_SIMP_TAC (srw_ss()) []
			     );

val hlp_errorT_thm =
store_thm ("hlp_errorT_thm",
				``! g f s e.
			       (f s = Error e) ⇒
			       ((f >>= g) s = Error e)``,
				RW_TAC (srw_ss()) [seqT_def]
				       THEN FULL_SIMP_TAC (srw_ss()) []
			       );

val seqT_access_violation_thm =
store_thm ("seqT_access_violation_thm",
	   ``! g f s a s' s'' a'.
	  ((g >>= f) s = ValueState a s') ⇒
	  (g s = ValueState a' s'') ==>
	  ¬access_violation s' ⇒
	  (¬access_violation s'')``,
	   RW_TAC (srw_ss()) [seqT_def]
		  THEN FULL_SIMP_TAC (srw_ss()) []
		  THEN Cases_on `access_violation s''`
		  THEN UNDISCH_ALL_TAC
		  THEN RW_TAC (srw_ss()) [seqT_def]
		  THEN FULL_SIMP_TAC (srw_ss()) []
	  );

val parT_access_violation_thm =
store_thm ("parT_access_violation_thm",
	   ``! g f s a s' s'' a'.
	  ((g ||| f) s = ValueState a s') ⇒
	  (g s = ValueState a' s'') ==>
	  ¬access_violation s' ⇒
	  (¬access_violation s'')
	  ``,
	   RW_TAC (srw_ss()) [seqT_def,parT_def,constT_def]
		  THEN FULL_SIMP_TAC (srw_ss()) []
		  THEN Cases_on `access_violation s''`
		  THEN UNDISCH_ALL_TAC
		  THEN RW_TAC (srw_ss()) [seqT_def]
		  THEN FULL_SIMP_TAC (srw_ss()) []
	  );


val const_comp_hlp_thm =
    store_thm("const_comp_hlp_thm",
``! f s s' a g.
	 (const_comp f) ==>
	 (f s = ValueState a s') ==>
     (~access_violation s) ==>
((f >>= g) s = g a s)``
	    ,
	    RW_TAC (srw_ss()) [const_comp_def,seqT_def]
THEN RES_TAC
THEN FULL_SIMP_TAC (srw_ss()) [const_comp_def,seqT_def]
);

val hlp_seqT2_thm =
    store_thm ("hlp_seqT2_thm",
    ``!f g s a s' b s1 e. ((f >>= g) s = ValueState a s') ==>
	      ((f s = ValueState b s1) ==>
	      (~access_violation s1) ==>
	      (g b s1 = ValueState a s'))
    /\ ~(f s = Error e)
``,
RW_TAC (srw_ss()) [seqT_def]
THEN Cases_on `f s`
THEN FULL_SIMP_TAC (srw_ss()) [seqT_def]
);

val hlp_seqT3_thm =
    store_thm ("hlp_seqT3_thm",
    ``!g f s e.
	      (f s = Error e) ==>
	      ((f >>= g) s = Error e)
``,
RW_TAC (srw_ss()) [seqT_def]
);


val hlp_seqT4_thm =
    store_thm ("hlp_seqT4_thm",
	       ``!f H s1 s2 s1' s2' a1 g invr1 invr2 uf uy.
              (~access_violation s1') ==>
	      (~access_violation s2') ==>
	      (f s1 = ValueState a1 s1') ==>
	      (f s2 = ValueState a1 s2') ==>
	      (preserve_relation_mmu_abs H invr1 invr2 uf uy) ==>
              (mmu_requirements s1' g) ⇒
              (mmu_requirements s2' g) ⇒
              (similar g s1' s2') ⇒
              (uy g s1' s2' )⇒
              (invr1 s1' )⇒
              (invr1 s2' )⇒
	      ((?a s1'' s2''. ((f >>= H) s1 = ValueState a s1'')
		/\
		     ((f >>= H) s2 = ValueState a s2''))
			     \/
	      (?e .((f >>= H) s1 = Error e)
	       /\
		    ((f >>= H) s2 = Error e)))

	      ``,
	       RW_TAC (srw_ss()) [preserve_relation_mmu_abs_def,seqT_def]
		      THEN RES_TAC
		      THEN PAT_ASSUM ``!c. X`` (fn thm => ASSUME_TAC (SPEC ``a1:'a`` thm))
		      THEN FULL_SIMP_TAC (srw_ss()) [seqT_def]
	      );

val similar_states_have_same_pc_thm =
    store_thm ("similar_states_have_same_pc_thm",
	       ``! s1 s2 g.
	      similar g s1 s2 ==>
	      (s2.registers (0,RName_PC)=
	       s1.registers (0,RName_PC))``,
	       RW_TAC (srw_ss()) [similar_def,equal_user_register_def]
	      );

val similar_states_have_same_cpsr_thm =
    store_thm ("similar_states_have_same_cpsr_thm",
	       ``! s1 s2 g.
	      similar g s1 s2 ==>
	      (s2.psrs (0,CPSR)=
	       s1.psrs (0,CPSR))``,
	       RW_TAC (srw_ss()) [similar_def,equal_user_register_def]
	      );
val similar_states_have_same_mode_thm =
    store_thm ("similar_states_have_same_mode_thm",
	       ``! u s1 s2 g.
	      similar g s1 s2 ==>
	      ((s2.psrs (0,CPSR)).M = u) ⇒
       ((s1.psrs (0,CPSR)).M = u)``,
	       RW_TAC (srw_ss()) [similar_def]
	      );

val similar_states_have_same_av_thm1 =
    store_thm ("similar_states_have_same_av_thm1",
	       ``! s1 s2 g.
	      similar g s1 s2 ==>
	      (
	       ((~access_violation s2) ==>
	      (~access_violation s1))
	       /\
		    ((~access_violation s1) ==>
		    (~access_violation s2)))
	      ``,
	       RW_TAC (srw_ss()) [similar_def]
	      );

val similar_states_have_same_vec_tab_thm =
    store_thm ("similar_states_have_same_vec_tab_thm",
	       ``! s1 s2 g.
	      similar g s1 s2 ==>
	      (
	       get_base_vector_table s1 =
	       get_base_vector_table s2)
	      ``,
	       RW_TAC (srw_ss()) [similar_def, get_base_vector_table_def]
	      );


val similar_states_have_same_security_ext_thm =
    store_thm ("similar_states_have_same_security_ext_thm",
	       ``! s1 s2 g.
	      similar g s1 s2 ==>
	      (
	       get_security_ext s1 =
	       get_security_ext s2)
	      ``,
	       RW_TAC (srw_ss()) [similar_def, get_security_ext_def]
	      );

val similar_states_have_same_read_pc_thm =
    store_thm ("similar_states_have_same_read_pc_thm",
	       ``! s1 s2 g.
	      similar g s1 s2 ==>
	      (
	       get_pc_value s1 =
	       get_pc_value s2)
	      ``,
	       RW_TAC (srw_ss()) [similar_def, get_pc_value_def,equal_user_register_def]
			     THEN UNABBREV_ALL_TAC
			     THEN EVAL_TAC
			     THEN RW_TAC (srw_ss()) []
	      );

val similar_states_have_same_av_thm2 =
    store_thm ("similar_states_have_same_av_thm2",
	       ``! s1 s2 g.
	        similar g s1 s2 ==>
	      (
	       ((access_violation s2) ==>
	      (access_violation s1))
	       /\
		    ((access_violation s1) ==>
		    (access_violation s2)))``,
	       RW_TAC (srw_ss()) [similar_def]
	      );

val untouched_states_implies_mmu_setup_thm =
    store_thm ("untouched_states_implies_mmu_setup_thm",
	       ``! s1 t g.
	      untouched g s1 t ==>
	      ((s1.coprocessors.state.cp15.C1 =
          t.coprocessors.state.cp15.C1) /\
         (s1.coprocessors.state.cp15.C2 =
          t.coprocessors.state.cp15.C2) /\
         (s1.coprocessors.state.cp15.C3 =
          t.coprocessors.state.cp15.C3))``,
	       RW_TAC (srw_ss()) [untouched_def]
	      );


(* only for arm_next: no svc constraints *)
val priv_mode_constraints_v1_def =
    Define `priv_mode_constraints_v1 (g:bool[32]) (state0:arm_state) state1 =
(state1.coprocessors.state.cp15 =
 state0.coprocessors.state.cp15)

/\
(state1.information =
 state0.information)

/\
((state1.psrs (0, CPSR)).F =
 (state0.psrs (0, CPSR)).F)

/\
((ARM_MODE state0 <> 16w) ==>
(ARM_MODE state1 <> 16w))

/\
((ARM_MODE state1 <> 16w) ==>
(ARM_MODE state0 = 16w))

/\
((ARM_MODE state1 = 16w) ==>
((state1.psrs (0, CPSR)).I =
 (state0.psrs (0, CPSR)).I))

/\
((ARM_MODE state1 <> 16w) ==>
 (let spsr = get_spsr_by_mode (ARM_MODE state1)
 in
 ((state1.psrs (0, CPSR)).I = T)

/\
   ((state1.psrs (0, CPSR)).J = F)

/\
   ((state1.psrs (0, CPSR)).IT = 0w)

/\
   ((state1.psrs (0, CPSR)).E =
    (state0.coprocessors.state.cp15.SCTLR.EE))

/\
~ (ARM_MODE state1 = 22w)

/\
~ (ARM_MODE state1 = 17w)

/\
~ (ARM_MODE state1 = 31w)

/\
(* program point to the handler of exception/interrupt in the vector table*)
((state1.registers (0, RName_PC) =
	     (HD (vector_table_address (get_base_vector_table state0)
				  ((state1.psrs (0, CPSR)).M))))
\/
(state1.registers (0, RName_PC) =
	     (HD (TL (vector_table_address (get_base_vector_table state0)
				  ((state1.psrs (0, CPSR)).M))))))

/\
(* in non-abort modes, we have no access violations *)
((* (ARM_MODE state1 <> 23w) ==>  *)
~(access_violation state1)) /\
((state1.psrs(0,spsr)).M = 16w) /\
((state1.psrs(0,spsr)).I = (state0.psrs(0,CPSR)).I)
 /\
((state1.psrs(0,spsr)).F = (state0.psrs(0,CPSR)).F)))
`;

(* only for arm_next : svc based on pc of previous state *)
val priv_mode_constraints_v2_def =
    Define `priv_mode_constraints_v2 (g:bool[32]) (state0:arm_state) state1 =
priv_mode_constraints_v1 g state0 state1
/\
(* in svc mode, the link register is equal to old PC minus offset *)
((ARM_MODE state1 = 19w) ==>
              		 ((state1.registers (0, RName_LRsvc) =
			  (if (state0.psrs (0,CPSR)).T
			   then
			       get_pc_value(state0) -2w
			   else
			       get_pc_value(state0) -4w
			  ))
                         /\ ((state1.psrs(0,SPSR_svc)) = (state0.psrs(0,CPSR)))))
`;

(* only for arm_next : svc based on pc of previous state *)
val priv_mode_constraints_v2a_def =
    Define `priv_mode_constraints_v2a (g:bool[32]) (state0:arm_state) state1 =
priv_mode_constraints_v1 g state0 state1
/\
(* in svc mode, the link register is equal to old PC minus offset *)
((ARM_MODE state1 = 19w) ==>
              		 ((state1.registers (0, RName_LRsvc) =
			  (if (state0.psrs (0,CPSR)).T
			   then
			       get_pc_value(state0) -2w
			   else
			       get_pc_value(state0) -4w
			  ))
                         /\ ((state1.psrs(0,SPSR_svc)) =
			     if (((ARMarch2num state0.information.arch = 6) ∨
				  version_number state0.information.arch ≥ 7) /\
				 (((state0.psrs (0,CPSR)).IT = 0w) ∨ (state0.psrs (0,CPSR)).T))
			     then
				 (state0.psrs(0,CPSR) with IT := ITAdvance ((state0.psrs(0,CPSR)).IT))
			     else
				 (state0.psrs(0,CPSR)))))
`;


(* svc based on the borders *)
val priv_mode_constraints_v3_def =
Define `priv_mode_constraints_v3 (g:bool[32]) (state0:arm_state) state1 =
    priv_mode_constraints_v2a g state0 state1
/\  ((ARM_MODE state1 = 19w) ==>
     (
       ((g = guest1) ==>
            ((((state1.psrs (0,SPSR_svc)).T) ==> (((state1.registers (0, RName_LRsvc) -2w) >=+ guest1_min_adr) /\ ((state1.registers (0, RName_LRsvc) -2w) <=+ guest1_max_adr)))
       /\   ((((state1.psrs (0,SPSR_svc)).T = F) /\ ((state1.psrs (0,SPSR_svc)).J = F)) ==> (((state1.registers (0, RName_LRsvc) -4w) >=+ guest1_min_adr) /\ ((state1.registers (0, RName_LRsvc) -4w) <=+ guest1_max_adr)))))
     /\
       ((g = guest2) ==>
            ((((state1.psrs (0,SPSR_svc)).T) ==> (((state1.registers (0, RName_LRsvc) -2w) >=+ guest2_min_adr) /\ ((state1.registers (0, RName_LRsvc) -2w) <=+ guest2_max_adr)))
       /\   ((((state1.psrs (0,SPSR_svc)).T = F) /\ ((state1.psrs (0,SPSR_svc)).J = F)) ==> (((state1.registers (0, RName_LRsvc) -4w) >=+ guest2_min_adr) /\ ((state1.registers (0, RName_LRsvc) -4w) <=+ guest2_max_adr)))))
     ))`;


(* svc based on accessible bytes *)
val priv_mode_constraints_v4_def =
    Define `priv_mode_constraints_v4 (g:bool[32]) (state0:arm_state) state1 =
    priv_mode_constraints_v2a g state0 state1
/\  ((ARM_MODE state1 = 19w) ==>
     (
            (((state1.psrs (0,SPSR_svc)).T) ==> aligned_word_readable state1 T (state1.registers (0, RName_LRsvc) -2w))
       /\   ((((state1.psrs (0,SPSR_svc)).T = F) /\ ((state1.psrs (0,SPSR_svc)).J = F)) ==> aligned_word_readable state1 F (state1.registers (0, RName_LRsvc) -4w))
     ))`;


val satisfy_priv_constraints_v3_def =
Define `satisfy_priv_constraints_v3 f m n =
 !g s1 s1' a .
     mmu_requirements s1 g ⇒
       (ARM_MODE s1 = m) ==>
     (ARM_MODE s1' = n) ==>
     (f s1 = ValueState a s1') ==>
     (¬access_violation s1) ==>
     (¬access_violation s1') ==>
     priv_mode_constraints_v3 g s1 s1'`;

val satisfy_priv_constraints_v2_def =
Define `satisfy_priv_constraints_v2 f m n =
 !g s1 s1' a .
     mmu_requirements s1 g ⇒
     (ARM_MODE s1 = m) ==>
     (ARM_MODE s1' = n) ==>
     (f s1 = ValueState a s1') ==>
     (¬access_violation s1) ==>
     (¬access_violation s1') ==>
     priv_mode_constraints_v2 g s1 s1'`;

val satisfy_priv_constraints_v2a_def =
Define `satisfy_priv_constraints_v2a f m n =
 !g s1 s1' a .
     mmu_requirements s1 g ⇒
     (ARM_MODE s1 = m) ==>
     (ARM_MODE s1' = n) ==>
     (f s1 = ValueState a s1') ==>
     (¬access_violation s1) ==>
     (¬access_violation s1') ==>
     priv_mode_constraints_v2a g s1 s1'`;


val IT_advance_untouch_mmu_setup_thm =
    store_thm ("IT_advance_untouch_mmu_setup_thm",
	       ``!s a s'.
	      (IT_advance <|proc := 0|> s = ValueState a s') ==>
	      ((s.coprocessors = s'.coprocessors)
	       /\
	    (s.memory = s'.memory)
	       /\
		    (s.accesses = s'.accesses))
	      ``
	     ,
	     EVAL_TAC
		 THEN RW_TAC (srw_ss()) []
		 THEN UNDISCH_ALL_TAC
		 THEN (NTAC 2 (RW_TAC (srw_ss()) []))
);


val IT_advance_keep_access_violation_thm =
    store_thm ("IT_advance_keep_access_violation_thm",
	       ``!s a s' g. mmu_requirements s g ==>
	      ¬access_violation s ==>
	      (IT_advance <|proc := 0|> s = ValueState a s') ==>
	      ¬access_violation s'``
	     ,
	     RW_TAC (srw_ss()) [seqT_def]
		    THEN IMP_RES_TAC IT_advance_untouch_mmu_setup_thm
		    THEN IMP_RES_TAC (SPECL [``s:arm_state``,
					     ``s':arm_state``,
					     ``g:bool[32]``]
					    trivially_untouched_av_lem2)
		    THEN UNDISCH_ALL_TAC
		    THEN RW_TAC (srw_ss()) []
	      );

val IT_advance_untouch_security_ex_thm =
    store_thm ("IT_advance_untouch_security_ex_thm",
	       ``!y s.
	      Extension_Security ∉ s.information.extensions ==>
	        (IT_advance <|proc := 0|> s = ValueState a s') ==>
	    Extension_Security ∉ s'.information.extensions

	      ``
	     ,
	    EVAL_TAC
		 THEN RW_TAC (srw_ss()) []
		 THEN UNDISCH_ALL_TAC
		 THEN (NTAC 2 (RW_TAC (srw_ss()) []))
);


val _ = export_theory();






