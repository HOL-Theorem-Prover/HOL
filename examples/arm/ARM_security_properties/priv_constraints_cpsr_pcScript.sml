open HolKernel boolLib bossLib Parse proofManagerLib;
open arm_coretypesTheory arm_seq_monadTheory arm_opsemTheory arm_stepTheory;
open MMUTheory MMU_SetupTheory inference_rulesTheory switching_lemma_helperTheory tacticsLib ARM_prover_extLib;
(*open arm_parserLib arm_encoderLib arm_disassemblerLib;*)


val _ =  new_theory("priv_constraints_cpsr_pc");
val _ = diminish_srw_ss ["one"]
val _ = augment_srw_ss [rewrites [oneTheory.FORALL_ONE]]

val _ = goalStack.chatting := !Globals.interactive

(**** the problem: vector table is based on mode not exception type ******)


(****************************************************************)
(*         CONSTRAINTS ON CPSR FLAGS IN PRIVILEGED MODE         *)
(*                        Narges                                *)
(****************************************************************)
val priv_cpsr_flags_constraints_def =
    Define `priv_cpsr_flags_constraints f sctlr  =
                             ! s s' a . (f s = ValueState a s') ==>
                               (~access_violation s') ==>
                               (((s'.psrs (0, CPSR)).I = T)
                                /\
                                     ((s'.psrs (0, CPSR)).J = F)
                                /\
                                     ((s'.psrs (0, CPSR)).IT = 0w) /\
                                ((s'.psrs (0,CPSR)).E = sctlr.EE)
                               )`;

val priv_cpsr_flags_constraints_abs_def =
    Define `priv_cpsr_flags_constraints_abs f sctlr =
                             ! s s' a c. (f c s = ValueState a s') ==>
                               (~access_violation s') ==>
                               (((s'.psrs (0, CPSR)).I = T)
                                /\
                                     ((s'.psrs (0, CPSR)).J = F)
                                /\
                                     ((s'.psrs (0, CPSR)).IT = 0w)
                                /\
                                     ((s'.psrs (0,CPSR)).E = sctlr.EE)
                               )`;


fun define_cfc_goal a expr =
    let val sctlr = List.nth(expr,0)
    in
        set_goal([], ``
            (priv_cpsr_flags_constraints ^a ^sctlr) ``)
    end;

fun define_cfc_goal_abs a expr =
    let val sctlr = List.nth(expr,0)
    in
        set_goal([], ``
            (priv_cpsr_flags_constraints_abs ^a ^sctlr) ``)
    end;

val seqT_priv_cpsr_flags_constraints_thm =
    store_thm("seqT_priv_cpsr_flags_constraints_thm",
              `` !f g sctlr. priv_cpsr_flags_constraints_abs f sctlr ==>
             priv_cpsr_flags_constraints (g >>= f) sctlr``,
              (RW_TAC (srw_ss()) [priv_cpsr_flags_constraints_def,
                                  priv_cpsr_flags_constraints_abs_def])
                  THEN Cases_on `g s`
                  THEN IMP_RES_TAC switching_lemma_helperTheory.seqT_access_violation_thm
                  THEN FULL_SIMP_TAC (srw_ss()) [arm_seq_monadTheory.seqT_def]
                  THEN Cases_on `access_violation b`
                  THEN PAT_X_ASSUM ``! s s' a c.X ==> Z``
                  (fn thm => ASSUME_TAC
                                 (SPECL [``b:arm_state``,``s':arm_state``,
                                         ``a:'b``,``a':'a``] thm))
                  THEN FULL_SIMP_TAC (srw_ss()) []
                  THEN RES_TAC
                  THEN FULL_SIMP_TAC (srw_ss()) []
             );

val parT_priv_cpsr_flags_constraints_thm =
    store_thm("parT_priv_cpsr_flags_constraints_thm",
              `` !f g  ee. priv_cpsr_flags_constraints f ee ==>
             priv_cpsr_flags_constraints (g ||| f)  ee``,
              (RW_TAC (srw_ss())
                      [
                       priv_cpsr_flags_constraints_def])
                  THEN Cases_on `g s`
                  THEN IMP_RES_TAC switching_lemma_helperTheory.parT_access_violation_thm
                  THEN FULL_SIMP_TAC (srw_ss()) [parT_def,seqT_def]
                  THEN Cases_on `f b`
                  THEN Cases_on `access_violation b`
                  THEN Cases_on `access_violation b'`
                  THEN FULL_SIMP_TAC (srw_ss()) []
                  THEN  PAT_X_ASSUM ``! s s' a.(f s = ValueState a s') ==> Z``
                  (fn thm => ASSUME_TAC
                                 (SPECL [``b:arm_state``,``b':arm_state``,``a'':'a``] thm))
                  THEN FIRST_PROVE [RES_TAC
                                        THEN FULL_SIMP_TAC (srw_ss()) []
                                        THEN RW_TAC (srw_ss()) [] ,
                                    (UNDISCH_ALL_TAC
                                         THEN  EVAL_TAC
                                         THEN  RW_TAC (srw_ss()) [])]);

val write_cpsr_cfc_thm =
    store_thm("write_cpsr_cfc_thm",
              ``! sctlr.
             (priv_cpsr_flags_constraints
                      ( write_cpsr <|proc:=0|>
                          (cpsr with
                          <|IT := 0w; J := F; E := sctlr.EE; I := T;
                            T := sctlr.TE|>)) sctlr)
/\
     (priv_cpsr_flags_constraints
          ( write_cpsr <|proc:=0|>
                                (cpsr with
                        <|I := T;
                          A :=
                            ((¬have_security_exta ∨ ¬scr.NS ∨ scr.AW) ∨
                             cpsr.A); IT := 0w; J := F; T := sctlr.TE;
                          E := sctlr.EE|>)) sctlr)
/\
     (priv_cpsr_flags_constraints
                      (write_cpsr <|proc:=0|>
                       (cpsr with
                        <|I := T;
                          F :=
                            ((¬have_security_exta ∨ ¬scr.NS ∨ scr.AW) ∨
                             cpsr.F);
                          A :=
                            ((¬have_security_exta ∨ ¬scr.NS ∨ scr.AW) ∨
                             cpsr.A); IT := 0w; J := F; T := sctlr.TE;
                          E := sctlr.EE|>)) sctlr)
             ``,
              EVAL_TAC
                  THEN RW_TAC (srw_ss()) [priv_cpsr_flags_constraints_def]
                  THEN EVAL_TAC
                  THEN RW_TAC (srw_ss()) []);


val cfc_first_abs_lemma =
    store_thm ("cfc_first_abs_lemma",
               ``!f g x. (f=g) ==> ((priv_cpsr_flags_constraints f x) =
                                    (priv_cpsr_flags_constraints g x))``,
               RW_TAC (srw_ss()) []);


val cfc_second_abs_lemma =
    store_thm ("cfc_second_abs_lemma",
               ``! f x. (! y. priv_cpsr_flags_constraints (f y) x ) =
    priv_cpsr_flags_constraints_abs f x``,
               RW_TAC (srw_ss()) [priv_cpsr_flags_constraints_def,
                                  priv_cpsr_flags_constraints_abs_def]
                      THEN METIS_TAC []);

val branch_to_ut_cfc_thm =
    store_thm ("branch_to_ut_cfc_thm",
               ``! s s' a x ee.
              (((s.psrs (0, CPSR)).I = T)
               /\
                    ((s.psrs (0, CPSR)).J = F)
               /\
                    ((s.psrs (0, CPSR)).IT = 0w) /\
                                                      ((s.psrs (0,CPSR)).E = ee)
              ) ==>
              (branch_to <|proc:=0|> x s = ValueState a s') ==>
              (((s'.psrs (0, CPSR)).I = T)
               /\
                    ((s'.psrs (0, CPSR)).J = F)
               /\
                    ((s'.psrs (0, CPSR)).IT = 0w) /\
                                                       ((s'.psrs (0,CPSR)).E = ee)
              )``,
               EVAL_TAC THEN
                        RW_TAC (srw_ss()) [] THEN
                        RW_TAC (srw_ss()) []);

val constT_cfc_ut_thm =
    store_thm ("constT_cfc_ut_thm",
               ``! s s' a ii x.
              (((s.psrs (ii.proc, CPSR)).I = T)
               /\
                    ((s.psrs (ii.proc, CPSR)).J = F)
               /\
                    ((s.psrs (ii.proc, CPSR)).IT = 0w)) ==>
              (branch_to ii x s = ValueState a s') ==>
              (((s'.psrs (ii.proc, CPSR)).I = T)
               /\
                    ((s'.psrs (ii.proc, CPSR)).J = F)
               /\
                    ((s'.psrs (ii.proc, CPSR)).IT = 0w))``,
               EVAL_TAC THEN
                        RW_TAC (srw_ss()) [] THEN
                        RW_TAC (srw_ss()) []);

val branch_cfc_thm =
    store_thm("branch_cfc_thm",
              `` !f sctlr x . priv_cpsr_flags_constraints f sctlr ==>
             (priv_cpsr_flags_constraints (f ||| branch_to <|proc:=0|> x) sctlr)``,
              (RW_TAC (srw_ss()) [parT_def,
                                  seqT_def,priv_cpsr_flags_constraints_def])
                  THEN
                  Cases_on `f s` THEN
                  Cases_on `branch_to <|proc:=0|> x b` THEN
                  Cases_on `access_violation b` THEN
                  Cases_on `access_violation b'` THEN
                  FULL_SIMP_TAC (srw_ss()) [] THEN
                  PAT_X_ASSUM ``! s s' a.(f s = ValueState a s') ==> Z`` (fn thm => ASSUME_TAC
                                                                                      (SPECL [``s:arm_state``,``b:arm_state``,``a':'a``] thm))
                  THEN ASSUME_TAC
                  (SPECL [``b:arm_state``,``b':arm_state``,
                          ``a'':unit``,``x:bool[32]``, ``sctlr.EE:bool``]
                         branch_to_ut_cfc_thm)
                  THEN FIRST_PROVE [
              RES_TAC
                  THEN FULL_SIMP_TAC (srw_ss()) []
                  THEN RW_TAC (srw_ss()) [] ,
              (UNDISCH_ALL_TAC
                   THEN  EVAL_TAC
                   THEN  RW_TAC (srw_ss()) [])]
             );

val constT_cfc_thm =
    store_thm("constT_cfc_thm",
              `` !f  ee . priv_cpsr_flags_constraints f ee ==>
             (priv_cpsr_flags_constraints (f >>= (λ(u1:unit,u2:unit,u3:unit,u4:unit). constT ()))) ee ``,
              (RW_TAC (srw_ss()) [seqT_def,priv_cpsr_flags_constraints_def,
                                  priv_cpsr_flags_constraints_abs_def,constT_def])
                  THEN Cases_on `f s`
                  THEN Cases_on `access_violation b`
                  THEN Cases_on `access_violation b'`
                  THEN FULL_SIMP_TAC (srw_ss()) []
                  THEN PAT_X_ASSUM ``! s s' a.(f s = ValueState a s') ==> Z``
                  (fn thm => ASSUME_TAC
                                 (SPECL [``s:arm_state``,``b:arm_state``,
                                         ``a:(unit#unit#unit#unit)``] thm))
                  THEN (UNDISCH_ALL_TAC
                            THEN  EVAL_TAC
                            THEN  RW_TAC (srw_ss()) []));

val joint_point_cfc_thm =
    store_thm("joint_point_cfc_thm",
              ``!H sctlr. (priv_cpsr_flags_constraints H sctlr) ==>
             (priv_cpsr_flags_constraints_abs ((\(pc,ExcVectorBase,cpsr,scr,sctlr). H ):(word32 # word32 # ARMpsr # CP15scr # CP15sctlr -> unit M)) sctlr)``,
    UNDISCH_ALL_TAC THEN
                    EVAL_TAC THEN
                    RW_TAC (srw_ss()) [priv_cpsr_flags_constraints_def,priv_cpsr_flags_constraints_abs_def]THEN
                    (PAT_X_ASSUM ``! s s' a. X`` (fn thm => (ASSUME_TAC (SPECL [``s:'a``,``s':arm_state``,``a:'b``] thm)))) THEN
                    FULL_SIMP_TAC (srw_ss()) [priv_cpsr_flags_constraints_def,priv_cpsr_flags_constraints_abs_def] THEN
                    RW_TAC (srw_ss()) [priv_cpsr_flags_constraints_def,priv_cpsr_flags_constraints_abs_def]);

val base_thms = [priv_cpsr_flags_constraints_def,
                 seqT_priv_cpsr_flags_constraints_thm,
                 parT_priv_cpsr_flags_constraints_thm,
                 cfc_first_abs_lemma,
                 cfc_second_abs_lemma,
                 constT_cfc_thm
                ];


fun prove_base_cfc base_cfc bv =

    let val (thm1,_) =
            ARM_prover_extLib.prove_const base_cfc
                        [define_cfc_goal,define_cfc_goal_abs]
                        [``sctlr:CP15sctlr``]
                        ``0w:bool[5]``
                        "_cfc_thm" base_thms
      ;
    in
        MP (SPECL [base_cfc, ``(sctlr:CP15sctlr)``, ``(ExcVectorBase + ^bv:bool[32])``]
                            (INST_TYPE[alpha |-> ``:(unit)``] branch_cfc_thm )) thm1
    end



val undef_read_write_cpsr_cfc_thm =
    save_thm ("undef_read_write_cpsr_cfc_thm" ,
              let
                  val base_cfc = ``(read_cpsr <|proc:=0|> >>=
                                       (λcpsr.
                                           write_cpsr <|proc:=0|>
                                              (cpsr with
                                                 <|I := T; IT := 0w; J := F; T := sctlr.TE;
                                                    E := sctlr.EE|>))
                                   )``

              in
                  prove_base_cfc base_cfc ``4w:bool[32]``
              end
             );

val svc_read_write_cpsr_cfc_thm =
    save_thm ("svc_read_write_cpsr_cfc_thm" ,
              let
                  val base_cfc = ``(read_cpsr <|proc:=0|> >>=
                                       (λcpsr.
                                           write_cpsr <|proc:=0|>
                                              (cpsr with
                                                 <|I := T; IT := 0w; J := F; T := sctlr.TE;
                                                    E := sctlr.EE|>))
                                   )``

              in
                  prove_base_cfc base_cfc ``8w:bool[32]``
              end
             );

val data_abt_read_write_cpsr_cfc_thm =
    save_thm ("data_abt_read_write_cpsr_cfc_thm" ,
              let
                  val base_cfc =
                      ``(read_cpsr <|proc:=0|> >>=
                                            (λcpsr.
                                                 write_cpsr <|proc:=0|>
                                (cpsr with
                                <|I := T;
                                  A :=
                                    ((¬have_security_exta ∨ ¬scr.NS ∨ scr.AW) ∨
                                     cpsr.A); IT := 0w; J := F; T := sctlr.TE;
                                  E := sctlr.EE|>)))``
              in
                  prove_base_cfc base_cfc ``16w:bool[32]``
              end
             );

val prefetch_abt_read_write_cpsr_cfc_thm =
    save_thm ("prefetch_abt_read_write_cpsr_cfc_thm" ,
              let
                  val base_cfc =
                      ``(read_cpsr <|proc:=0|> >>=
                                            (λcpsr.
                                                 write_cpsr <|proc:=0|>
                                (cpsr with
                                <|I := T;
                                  A :=
                                    ((¬have_security_exta ∨ ¬scr.NS ∨ scr.AW) ∨
                                     cpsr.A); IT := 0w; J := F; T := sctlr.TE;
                                  E := sctlr.EE|>)))``
              in
                  prove_base_cfc base_cfc ``12w:bool[32]``
              end
             );


val irq_read_write_cpsr_cfc_thm =
    save_thm ("irq_read_write_cpsr_cfc_thm" ,
              let
                  val base_cfc =
                      ``(read_cpsr <|proc:=0|> >>=
                                            (λcpsr.
                                                 write_cpsr <|proc:=0|>
                                (cpsr with
                                <|I := T;
                                  A :=
                                    ((¬have_security_exta ∨ ¬scr.NS ∨ scr.AW) ∨
                                     cpsr.A); IT := 0w; J := F; T := sctlr.TE;
                                  E := sctlr.EE|>)))``
              in
                  prove_base_cfc base_cfc ``24w:bool[32]``
              end
             );

val fiq_read_write_cpsr_cfc_thm =
    save_thm ("fiq_read_write_cpsr_cfc_thm" ,
              let
                  val base_cfc =
                      ``(read_cpsr <|proc:=0|> >>=
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
                          E := sctlr.EE|>)))``
              in
                  prove_base_cfc base_cfc ``4w:bool[32]``
              end
             );

val const_comp_seqT_priv_cpsr_flags_constraints_thm =
    store_thm(
    "const_comp_seqT_priv_cpsr_flags_constraints_thm",
    ``! f g s s' a x.
             (const_comp f) ==>
             ¬access_violation s' ==>
             priv_cpsr_flags_constraints_abs g x ==>
             ((f>>=g) s = ValueState a s') ==>
             ((((s'.psrs (0,CPSR)).I ⇔ T) ∧ ((s'.psrs (0,CPSR)).J ⇔ F) ∧
                                          ((s'.psrs (0,CPSR)).IT = 0w) ∧ ((s'.psrs (0,CPSR)).E ⇔ x.EE)))``,
    RW_TAC (srw_ss()) [const_comp_def,priv_cpsr_flags_constraints_def,
                       priv_cpsr_flags_constraints_abs_def]
           THEN FULL_SIMP_TAC (srw_ss()) []
           THEN Cases_on ` f s`
           THEN IMP_RES_TAC seqT_access_violation_thm
           THEN FULL_SIMP_TAC (srw_ss()) [seqT_def]
           THEN PAT_X_ASSUM ``∀s s' a c. X`` (fn thm => ASSUME_TAC (
                                                      SPECL [``b:arm_state``,``s':arm_state``,
                                                             ``a:'b``,``a':'a``] thm ))
           THEN RES_TAC
           THEN FULL_SIMP_TAC (srw_ss()) []
    );


fun prove_take_exception_cfc_thm
        read_write_cpsr_cfc_thm
        body
        sl_elm
        sl_elm2
        spec_list
        spec_list2
        te_def
        const_comp_rp_thm
        fixed_sctrl_thm
        fixed_sctrl_thm2 ltype
  =
  let
      val thms1 = [priv_cpsr_flags_constraints_def,
                   seqT_priv_cpsr_flags_constraints_thm,
                   parT_priv_cpsr_flags_constraints_thm,
                   cfc_first_abs_lemma,
                   cfc_second_abs_lemma,
                   read_write_cpsr_cfc_thm,
                   constT_cfc_thm
                  ];

      val (l,r,rbody)= ARM_prover_extLib.decompose_term body;
      val (rbody_thm,_) = ARM_prover_extLib.prove_const rbody
                                      [define_cfc_goal,define_cfc_goal_abs]
                                      [``sctlr:CP15sctlr``]
                                      ``(12w:bool[5])``  "_cfc_thm" thms1;

      val (_,sr) = dest_eq ( concl (SIMP_RULE (srw_ss()) []
                                              (SPECL [``s:arm_state``,r]
                                                     (INST_TYPE [alpha |-> ``:unit``]
                                                                fixed_sctrl_thm))));
      val (_,simpr,_) = ARM_prover_extLib.decompose_term sr;
      val (rabs,rbody) = pairLib.dest_pabs r;
      val unbeta_thm= (PairRules.UNPBETA_CONV rabs rbody);
      val unbeta_a = mk_comb (r, rabs)
      val snd = get_type_inst (type_of(rbody) , false)
      val rbody_type = get_type_inst (snd, true);

      val thm4 = prove(
                            ``(priv_cpsr_flags_constraints
                               ^rbody (sctlr:CP15sctlr))=
                 (priv_cpsr_flags_constraints ^unbeta_a
                                                   (sctlr:CP15sctlr))``,
                            (ASSUME_TAC (SPECL [rbody,
                                                ``^unbeta_a``,
                                                ``sctlr:CP15sctlr``]
                                               (INST_TYPE
                                                    [beta |-> rbody_type,
                                                     alpha |-> ``:arm_state``]
                                                    (cfc_first_abs_lemma))))
                                THEN ASSUME_TAC unbeta_thm
                                THEN RES_TAC);
      val thm5 = SIMP_RULE (bool_ss) [thm4] rbody_thm;
  in
      RW_TAC (srw_ss()) [te_def]
             THEN ASSUME_TAC (SPECL [``s:arm_state``,r]
                                    (INST_TYPE [alpha |-> ``:unit``]
                                               fixed_sctrl_thm))
             THEN FULL_SIMP_TAC (srw_ss()) []
             THEN POP_ASSUM (fn thm => THROW_AWAY_TAC (concl thm))
             THEN ASSUME_TAC const_comp_rp_thm
             THEN RW_TAC (srw_ss()) [priv_cpsr_flags_constraints_def,
                                     priv_cpsr_flags_constraints_abs_def]
             THEN NTAC 4
             ( FULL_SIMP_TAC (srw_ss()) [const_comp_def]
                             THEN Cases_on [QUOTE ("("^(term_to_string l) ^ ") s")]
                             THENL
                             [
                              IMP_RES_TAC seqT_access_violation_thm
                                          THEN RES_TAC
                                          THEN RW_TAC (srw_ss()) []
                                          THEN IMP_RES_TAC hlp_seqT_thm
                                          THEN PAT_X_ASSUM ``X a' b= ValueState a s'``
                                          (fn thm => ASSUME_TAC (PairRules.PBETA_RULE thm))
                                          THEN ASSUME_TAC
                                          ( SPECL spec_list
                                                  (GEN_ALL  (SIMP_RULE (bool_ss)
                                                                       [priv_cpsr_flags_constraints_def] thm5)))
                                          THEN PAT_X_ASSUM ``X ==> Y``
                                          (fn thm => ASSUME_TAC (PairRules.PBETA_RULE thm))
                                          THEN ASSUME_TAC (SPECL spec_list2 fixed_sctrl_thm2)
                                          THEN RES_TAC
                                          THEN FULL_SIMP_TAC (srw_ss()) [],

                              IMP_RES_TAC (SPEC simpr
                                                (INST_TYPE [beta |-> ``:unit``,
                                                            alpha |-> ltype]
                                                           hlp_errorT_thm))
                                          THEN  PAT_X_ASSUM ``! (s''':arm_state) . X ``
                                          (fn thm => ASSUME_TAC (SPEC ``s:arm_state`` thm))
                                          THEN RW_TAC (srw_ss()) []
                                          THEN FULL_SIMP_TAC (srw_ss()) [] ])
  end



val take_undef_instr_exception_cfc_thm =
    store_thm ("take_undef_instr_exception_cfc_thm",
               ``!s a s'.
              (¬access_violation s')==>
              (take_undef_instr_exception <|proc:=0|> s = ValueState a s') ==>
              (((s'.psrs (0,CPSR)).I ⇔ T)
                   ∧((s'.psrs (0,CPSR)).J ⇔ F) ∧
                   ((s'.psrs (0,CPSR)).IT = 0w) ∧
                   ((s'.psrs (0,CPSR)).E ⇔ s.coprocessors.state.cp15.SCTLR.EE))``,
               let
                   val athm = SIMP_CONV (bool_ss) [take_undef_instr_exception_def]
                                        ``take_undef_instr_exception <|proc:=0|> ``;
                   val (_, body) =  (dest_eq (concl athm))
                   val sl_elm2 =  ``(a':(word32 # word32 # ARMpsr # CP15scr # CP15sctlr))``;
                   val sl_elm =  ``(a:(word32 # word32 # ARMpsr # CP15scr # CP15sctlr))``;
                   val const_comp_rp_thm =
                       const_comp_take_undef_svc_exception_rp_thm;
                   val fixed_sctrl_thm2 = fixed_sctrl_undef_svc_thm2;
                   val fixed_sctrl_thm = fixed_sctrl_undef_svc_thm;
                   val spec_list =   (mk_spec_list sl_elm2) @
                                     [``b:arm_state``,
                                      ``s':arm_state``,
                                      ``a:unit``];
                   val spec_list2 = [``b:arm_state``]@ ( (mk_spec_list2 sl_elm2));
                   val ltype = ``:(word32 # word32 # ARMpsr # CP15scr # CP15sctlr)`` ;
                   (* val read_write_cpsr_cfc_thm = undef_read_write_cpsr_cfc_thm; *)
               in
                   prove_take_exception_cfc_thm
                       undef_read_write_cpsr_cfc_thm
                       body  sl_elm sl_elm2
                       spec_list spec_list2
                       take_undef_instr_exception_def
                       const_comp_rp_thm fixed_sctrl_thm
                       fixed_sctrl_thm2 ltype
               end
);

val take_data_abort_exception_cfc_thm =
    store_thm ("take_data_abort_exception_cfc_thm",
               ``!s a s'.
              (¬access_violation s')==>
              (take_data_abort_exception <|proc:=0|> s = ValueState a s') ==>
              (((s'.psrs (0,CPSR)).I ⇔ T)
                   ∧((s'.psrs (0,CPSR)).J ⇔ F) ∧
                   ((s'.psrs (0,CPSR)).IT = 0w) ∧
                   ((s'.psrs (0,CPSR)).E ⇔ s.coprocessors.state.cp15.SCTLR.EE))``,
               let
                   val athm = SIMP_CONV (bool_ss) [take_data_abort_exception_def]
                                        ``take_data_abort_exception <|proc:=0|> ``;
                   val (_, body) =  (dest_eq (concl athm));
                   val sl_elm2 =  ``(a':(word32 # word32 # bool # ARMpsr # CP15scr # CP15sctlr))``;
                   val sl_elm =  ``(a:(word32 # word32 # bool # ARMpsr # CP15scr # CP15sctlr))``;
                   val read_write_cpsr_cfc_thm = data_abt_read_write_cpsr_cfc_thm;
                   val const_comp_rp_thm = const_comp_take_abort_irq_exception_rp_thm
                   val fixed_sctrl_thm2 = fixed_sctrl_abt_irq_thm2;
                   val fixed_sctrl_thm1 = fixed_sctrl_abt_irq_thm;
                   val spec_list =   (mk_spec_list3 sl_elm2) @
                                     [``b:arm_state``,
                                      ``s':arm_state``,
                                      ``a:unit``];
                   val spec_list2 = [``b:arm_state``]@ ( (mk_spec_list4 sl_elm2));
                   val ltype = ``:(word32 # word32 # bool # ARMpsr # CP15scr # CP15sctlr)`` ;
               in
                   prove_take_exception_cfc_thm
                       data_abt_read_write_cpsr_cfc_thm
                       body
                       sl_elm
                       sl_elm2
                       spec_list
                       spec_list2
                       take_data_abort_exception_def
                       const_comp_rp_thm
                       fixed_sctrl_thm1
                       fixed_sctrl_thm2 ltype
               end
);


val take_prefetch_abort_exception_cfc_thm =
    store_thm ("take_prefetch_abort_exception_cfc_thm",
               ``!s a s'.
              (¬access_violation s')==>
              (take_prefetch_abort_exception <|proc:=0|> s = ValueState a s') ==>
              (((s'.psrs (0,CPSR)).I ⇔ T)
                   ∧((s'.psrs (0,CPSR)).J ⇔ F) ∧
                   ((s'.psrs (0,CPSR)).IT = 0w) ∧
                   ((s'.psrs (0,CPSR)).E ⇔ s.coprocessors.state.cp15.SCTLR.EE))``,
               let
                   val athm = SIMP_CONV (bool_ss) [take_prefetch_abort_exception_def]
                                        ``take_prefetch_abort_exception <|proc:=0|> ``;
                   val (_, body) =  (dest_eq (concl athm));
                   val sl_elm2 =  ``(a':(word32 # word32 # bool # ARMpsr # CP15scr # CP15sctlr))``;
                   val sl_elm =  ``(a:(word32 # word32 # bool # ARMpsr # CP15scr # CP15sctlr))``;
                   val read_write_cpsr_cfc_thm = prefetch_abt_read_write_cpsr_cfc_thm;
                   val const_comp_rp_thm = const_comp_take_abort_irq_exception_rp_thm
                   val fixed_sctrl_thm2 = fixed_sctrl_abt_irq_thm2;
                   val fixed_sctrl_thm1 = fixed_sctrl_abt_irq_thm;
                   val spec_list =   (mk_spec_list3 sl_elm2) @
                                     [``b:arm_state``,
                                      ``s':arm_state``,
                                      ``a:unit``];
                   val spec_list2 = [``b:arm_state``]@ ( (mk_spec_list4 sl_elm2));
                   val ltype = ``:(word32 # word32 # bool # ARMpsr # CP15scr # CP15sctlr)`` ;
              in
                   prove_take_exception_cfc_thm
                       prefetch_abt_read_write_cpsr_cfc_thm
                       body
                       sl_elm
                       sl_elm2
                       spec_list
                       spec_list2
                       take_prefetch_abort_exception_def
                       const_comp_rp_thm
                       fixed_sctrl_thm1
                       fixed_sctrl_thm2 ltype
               end
);



val take_irq_exception_cfc_thm =
    store_thm ("take_irq_exception_cfc_thm",
               ``!s a s'.
              (¬access_violation s')==>
              (take_irq_exception <|proc:=0|> s = ValueState a s') ==>
              (((s'.psrs (0,CPSR)).I ⇔ T)
                   ∧((s'.psrs (0,CPSR)).J ⇔ F) ∧
                   ((s'.psrs (0,CPSR)).IT = 0w) ∧
                   ((s'.psrs (0,CPSR)).E ⇔ s.coprocessors.state.cp15.SCTLR.EE))``,
               let
                   val athm = SIMP_CONV (bool_ss) [take_irq_exception_def]
                                        ``take_irq_exception <|proc:=0|> ``;
                   val (_, body) =  (dest_eq (concl athm));
                   val sl_elm2 =  ``(a':(word32 # word32 # bool # ARMpsr # CP15scr # CP15sctlr))``;
                   val sl_elm =  ``(a:(word32 # word32 # bool # ARMpsr # CP15scr # CP15sctlr))``;
                   val read_write_cpsr_cfc_thm = irq_read_write_cpsr_cfc_thm;
                   val const_comp_rp_thm = const_comp_take_abort_irq_exception_rp_thm
                   val fixed_sctrl_thm2 = fixed_sctrl_abt_irq_thm2;
                   val fixed_sctrl_thm1 = fixed_sctrl_abt_irq_thm;
                   val spec_list =   (mk_spec_list3 sl_elm2) @
                                     [``b:arm_state``,
                                      ``s':arm_state``,
                                      ``a:unit``];
                   val spec_list2 = [``b:arm_state``]@ ( (mk_spec_list4 sl_elm2));
                   val ltype = ``:(word32 # word32 # bool # ARMpsr # CP15scr # CP15sctlr)`` ;
              in
                   prove_take_exception_cfc_thm
                       irq_read_write_cpsr_cfc_thm
                       body
                       sl_elm
                       sl_elm2
                       spec_list
                       spec_list2
                       take_irq_exception_def
                       const_comp_rp_thm
                       fixed_sctrl_thm1
                       fixed_sctrl_thm2 ltype
               end
);


(* TO DO SVC *)

val take_svc_exception_cfc_thm =
    store_thm ("take_svc_exception_cfc_thm",
         let
             val athm = SIMP_CONV (bool_ss) [take_svc_exception_def]
                                  ``take_svc_exception <|proc:=0|> ``;
             val (_, body) =  (dest_eq (concl athm))
             val (_,_,a) = ARM_prover_extLib.decompose_term body;
         in
             ``!s a s'.
              (¬access_violation s')==>
              (^a s = ValueState a s') ==>
              (((s'.psrs (0,CPSR)).I ⇔ T)
                   ∧((s'.psrs (0,CPSR)).J ⇔ F) ∧
                   ((s'.psrs (0,CPSR)).IT = 0w) ∧
                   ((s'.psrs (0,CPSR)).E ⇔ s.coprocessors.state.cp15.SCTLR.EE))``
         end,
               let
                   val athm = SIMP_CONV (bool_ss) [take_svc_exception_def]
                                        ``take_svc_exception <|proc:=0|> ``
                   val (_, a) =  (dest_eq (concl athm))
                   val (_,_,body) = ARM_prover_extLib.decompose_term a

                   val sl_elm2 =  ``(a':(word32 # word32 # ARMpsr # CP15scr # CP15sctlr))``
                   val sl_elm =  ``(a:(word32 # word32 # ARMpsr # CP15scr # CP15sctlr))``
                   val const_comp_rp_thm =
                       const_comp_take_undef_svc_exception_rp_thm
                   val fixed_sctrl_thm2 = fixed_sctrl_undef_svc_thm2
                   val fixed_sctrl_thm = fixed_sctrl_undef_svc_thm
                   val spec_list =   (mk_spec_list sl_elm2) @
                                     [``b:arm_state``,
                                      ``s':arm_state``,
                                      ``a:unit``];
                   val spec_list2 = [``b:arm_state``]@ ( (mk_spec_list2 sl_elm2))
                   val ltype = ``:(word32 # word32 # ARMpsr # CP15scr # CP15sctlr)``
               in
                   prove_take_exception_cfc_thm
                       svc_read_write_cpsr_cfc_thm
                       body  sl_elm sl_elm2
                       spec_list spec_list2
                       take_svc_exception_def
                       const_comp_rp_thm fixed_sctrl_thm
                       fixed_sctrl_thm2 ltype
               end
              );















(**************************************************************)
(*         SET PROGRAM TO AN ADDRESS IN VECTOR TABLE          *)
(**************************************************************)
val set_pc_to_def =
    Define `set_pc_to f (m:bool[5]) vt =
            !s1 s2 c .
                (f s1 = ValueState c s2) ==>
                (¬access_violation s2) ==>
                ((s2.registers (0, RName_PC) =  HD(vector_table_address vt m)) \/
                (s2.registers (0, RName_PC) =  HD (TL(vector_table_address vt m)))) `;

val set_pc_to_abs_def =
    Define `set_pc_to_abs f (m:bool[5]) vt =
            !s1 s2 c a .
                (f a s1 = ValueState c s2) ==>
                (¬access_violation s2) ==>
                ((s2.registers (0, RName_PC) =  HD(vector_table_address vt m)) \/
                (s2.registers (0, RName_PC) =  HD (TL(vector_table_address vt m)))) `;

val branch_to_spc_thm =
    store_thm("branch_to_spc_thm",
              ``! m adr  . (adr = HD(vector_table_address ExcVectorBase m))
                         \/ (adr = HD(TL(vector_table_address ExcVectorBase m))) ==>
             set_pc_to (branch_to <|proc := 0|> adr) m ExcVectorBase``,
              EVAL_TAC THEN
                       FULL_SIMP_TAC (srw_ss()) [] THEN
                       RW_TAC (srw_ss()) [] THEN
                       EVAL_TAC THEN
                       FULL_SIMP_TAC (srw_ss()) []);

val seqT_set_pc_to_thm =
    store_thm("seqT_set_pc_to_thm",
              `` !g f m vt. set_pc_to_abs g m vt ==>
             set_pc_to (f >>=  g) m vt``,
              (RW_TAC (srw_ss()) [seqT_def,set_pc_to_abs_def,
                                  set_pc_to_def])
                  THEN Cases_on `f s1`
                  THEN FULL_SIMP_TAC (srw_ss()) []
                  THEN Cases_on `access_violation b`
                  THEN (RW_TAC (srw_ss()) [])
                  THEN FULL_SIMP_TAC (srw_ss()) []
                  THEN RW_TAC (srw_ss()) []
                  THEN FULL_SIMP_TAC (srw_ss()) []
                  THEN FULL_SIMP_TAC (srw_ss()) []
                  THEN PAT_X_ASSUM ``! s1 s2 c.t``
                  (fn thm => ASSUME_TAC
                                 (SPECL [``b:arm_state``,``s2:arm_state``,``c:('b)``] thm))
                  THEN RES_TAC
                  THEN FULL_SIMP_TAC (srw_ss()) []);

val parT_set_pc_to_thm =
    store_thm("parT_set_pc_to_thm",
              `` !g f m vt. set_pc_to g m vt ==>
             set_pc_to (f ||| g) m vt ``,
              (RW_TAC (srw_ss()) [parT_def,seqT_def,set_pc_to_def])
                  THEN  Cases_on `f s1`
                  THEN  Cases_on `g b`
                  THEN  Cases_on `access_violation b`
                  THEN  Cases_on `access_violation b'`
                  THEN  FULL_SIMP_TAC (srw_ss()) []
                  THEN  RES_TAC
                  THEN  UNDISCH_ALL_TAC
                  THEN  EVAL_TAC
                  THEN  (RW_TAC (srw_ss()) []));

val pc_first_abs_lemma =
    store_thm ("pc_first_abs_lemma",
               ``!f g m vt . (f=g) ==> ((set_pc_to f m vt) =
                                    (set_pc_to  g m vt))``,
               RW_TAC (srw_ss()) []);

val pc_second_abs_lemma =
    store_thm ("pc_second_abs_lemma",
               ``! f m vt. (! y. set_pc_to (f y) m vt) =
    set_pc_to_abs f m vt``,
               RW_TAC (srw_ss()) [set_pc_to_def,set_pc_to_abs_def]
                      THEN METIS_TAC []);

val  vector_table_adr_thm =
     store_thm(
     "vector_table_adr_thm",
     ``!vt.
      (HD (vector_table_address vt (19w:bool[5])) = (vt + 8w:bool[32] ))
     /\
      (HD (vector_table_address vt (23w:bool[5])) = (vt + 16w:bool[32] ))
     /\
      (HD (TL(vector_table_address vt (23w:bool[5]))) = (vt + 12w:bool[32] ))
     /\
        (HD (vector_table_address vt (27w:bool[5])) = (vt + 4w:bool[32]))``,
     EVAL_TAC
         THEN RW_TAC (srw_ss()) []);


val constT_spc_thm =
    store_thm("constT_spc_thm",
              `` !f m vt. set_pc_to f m vt ==>
             (set_pc_to (f >>= (λ(u1:unit,u2:unit,u3:unit,u4:unit). constT ())) m vt)``,
              (RW_TAC (srw_ss())
                      [seqT_def,set_pc_to_def,constT_def])
                  THEN
                  Cases_on `f s1` THEN
                  Cases_on `access_violation b` THEN
                  PAT_X_ASSUM ``! s1 s2 c. Z`` (fn thm => ASSUME_TAC (SPECL [``s1:arm_state``,``b:arm_state``,``a:(unit#unit#unit#unit)``] thm))
                  THEN  FULL_SIMP_TAC (srw_ss()) []
                  THENL [RW_TAC (srw_ss()) [] THEN
                                RES_TAC,
                         UNDISCH_ALL_TAC
                             THEN  EVAL_TAC
                             THEN  RW_TAC (srw_ss()) []]);

fun define_set_pc_goal a [expr,vt] =
    set_goal([], ``
            (set_pc_to ^a  ^expr  ^vt) ``);

fun define_set_pc_goal_abs a [expr,vt] =
   set_goal([], `` (set_pc_to_abs ^a  ^expr ^vt) ``);

fun get_action_body a thm =
    let val (_,body) = (dest_eq o concl) (REWRITE_CONV [thm]
                                                       ``^a <|proc:=0|> ``)
    in
        body
    end;


val (_,take_undef_exception_body) = (dest_eq o concl) (REWRITE_CONV [take_undef_instr_exception_def]
                                          ``take_undef_instr_exception <|proc:=0|> ``);

fun get_joint_write_body_spc_thm body mode vb =
    let
        val set_pc_thms = [set_pc_to_def,
                           seqT_set_pc_to_thm,
                           parT_set_pc_to_thm,
                           pc_first_abs_lemma,
                           pc_second_abs_lemma,
                           REWRITE_RULE [vector_table_address_def] branch_to_spc_thm,
                           constT_spc_thm
                          ];
        val postfix = "_spc_thm"
        val (l,r,rb) = (ARM_prover_extLib.decompose_term body);
        val (l1,r1,rb1) = ARM_prover_extLib.decompose_term rb;
        val (wp1,r2,rb1) = ARM_prover_extLib.decompose_term rb1;

        val (wp1_thm,_) = ARM_prover_extLib.prove_const  wp1
                                       [define_set_pc_goal,define_set_pc_goal_abs]
                                       [mode,``(ExcVectorBase:bool[32])``]
                                       vb
                                       "_spc_thm"
                                       set_pc_thms;

        val writing_part_spc_thm =  (MP  (SPECL [wp1 ,
                                                 mode,
                                                 ``(ExcVectorBase:bool[32])``]
                                                constT_spc_thm) wp1_thm);
        val writing_part_abs_spc_thm =
            TAC_PROOF (([], “set_pc_to_abs ^r1 ^mode ExcVectorBase”),
                       MP_TAC writing_part_spc_thm
                       THEN RW_TAC (srw_ss()) [set_pc_to_def,set_pc_to_abs_def]
                       THEN PAT_X_ASSUM ``! s1 s2. X``
                               (fn thm =>
                                  ASSUME_TAC (SPECL [“s1:arm_state”,
                                                     “s2:arm_state”] thm))
                       THEN PAT_X_ASSUM ``X a s1 = ValueState () s2``
                              (fn thm => ASSUME_TAC (PairRules.PBETA_RULE thm))
                       THEN RES_TAC
                       THEN RW_TAC (srw_ss()) []
                      )

        val thm = MP (SPECL [r1,l1,
                             mode,
                             ``(ExcVectorBase:bool[32])``]
                            (INST_TYPE [alpha |-> ``:unit#unit``,
                                        beta |-> ``:unit``
                                       ]
                                       seqT_set_pc_to_thm)) writing_part_abs_spc_thm;
    in
        thm
    end;

val joint_write_body_data_abort_spc_thm =
    save_thm ("joint_write_body_data_abort_spc_thm",
              let  val body =
                       get_action_body ``take_data_abort_exception``
                                       take_data_abort_exception_def
              in
                  get_joint_write_body_spc_thm body ``23w:bool[5]`` ``16w:bool[5]``
              end
             );


val joint_write_body_irq_spc_thm =
    save_thm ("joint_write_body_irq_spc_thm",
              let  val body =
                       get_action_body ``take_irq_exception``
                                       take_irq_exception_def
              in
                  get_joint_write_body_spc_thm body ``18w:bool[5]`` ``24w:bool[5]``
              end
             );

val joint_write_body_svc_spc_thm =
    save_thm ("joint_write_body_svc_spc_thm",
              let  val a =
                       get_action_body ``take_svc_exception``
                                       take_svc_exception_def
                   val (l,r,body)= ARM_prover_extLib.decompose_term a
              in
                  get_joint_write_body_spc_thm body ``19w:bool[5]`` ``8w:bool[5]``
              end
             );

val joint_write_body_undef_instr_spc_thm =
    save_thm ("joint_write_body_undef_instr_spc_thm",
              let  val body =
                       get_action_body ``take_undef_instr_exception``
                                       take_undef_instr_exception_def
              in
                  get_joint_write_body_spc_thm body ``27w:bool[5]`` ``4w:bool[5]``
              end
             );

val joint_write_body_prefetch_abort_spc_thm =
    save_thm ("joint_write_body_prefetch_abort_spc_thm",
              let
                  val body =
                       get_action_body ``take_prefetch_abort_exception``
                                       take_prefetch_abort_exception_def
              in
                  get_joint_write_body_spc_thm body ``23w:bool[5]`` ``12w:bool[5]``
              end
             );

fun prove_take_exception_spc
        body def_thm sl_elm
        const_rp_thm  fixed_vb_rp_thm2
        fixed_vb_rp_thm1 joint_write_body_spc_thm
        l_type spec_list1 spec_list2 =
    let
        val (l,r,rb) = ARM_prover_extLib.decompose_term body;
    in
        FULL_SIMP_TAC (srw_ss())
                      [def_thm]
                      THEN (REPEAT DISCH_TAC)
                      THEN ASSUME_SPECL_INST_TAC
                      [``s:arm_state``,r]
                      [alpha |-> ``:unit``]
                      fixed_vb_rp_thm2
                      THEN FULL_SIMP_TAC (srw_ss()) []
                      THEN WEAKEN_TAC (is_imp)
                      THEN ASSUME_TAC const_rp_thm
                      THEN RW_TAC (srw_ss()) []
                      THEN FULL_SIMP_TAC (srw_ss()) [const_comp_def]
                      THEN Cases_on [QUOTE ("("^(term_to_string l) ^ ") s")]

                      THENL
                      [
                       RES_TAC
                           THEN
                           RW_TAC (srw_ss()) []
                           THEN IMP_RES_TAC hlp_seqT_thm
                           THEN PAT_X_ASSUM ``X a' b= ValueState a s'``
                           (fn thm => ASSUME_TAC (PairRules.PBETA_RULE thm))
                           THEN  IMP_RES_TAC (SPECL (spec_list2@[``b:arm_state``])
                                                    fixed_vb_rp_thm1)
                           THEN PAT_X_ASSUM ``!a.X`` (fn thm => ASSUME_TAC (SPEC sl_elm thm))
                           THEN ASSUME_SPECL_GEN_REWRITE_TAC
                           (spec_list1@ [``b:arm_state``,
                                         ``s':arm_state``,
                                         ``():unit``],
                            joint_write_body_spc_thm, [set_pc_to_def])
                           THEN FULL_SIMP_TAC (srw_ss()) []
                           THEN RES_TAC
                           THEN RW_TAC (srw_ss()) []
                     ,
                     IMP_RES_TAC (SPEC r (INST_TYPE [beta |-> ``:unit``,
                                                     alpha |-> l_type ]
                                                    hlp_errorT_thm))
                                 THEN  PAT_X_ASSUM ``! (s''':arm_state). X ``
                                 (fn thm => ASSUME_TAC (SPEC ``s':arm_state``thm))
                                 THEN RW_TAC (srw_ss()) []
                                 THEN FULL_SIMP_TAC (srw_ss()) [] ]
    end;


val take_data_abort_exception_spc_thm =
    store_thm ("take_data_abort_exception_spc_thm",
               ``!s a s'.
              (¬access_violation s')==>
              (¬access_violation s)==>
              (take_data_abort_exception <|proc:=0|> s =
                                                  ValueState a s') ==>
              ((s'.registers (0,RName_PC) =
               (HD (vector_table_address
                    (get_base_vector_table s) 23w)))
              \/
              (s'.registers (0,RName_PC) =
               (HD (TL (vector_table_address
                (get_base_vector_table s) 23w)))))
              ``,
               let
                   val body =
                       get_action_body ``take_data_abort_exception``
                                       take_data_abort_exception_def;
                   val sl_elm =  ``(a:(word32 # word32 # bool # ARMpsr # CP15scr # CP15sctlr))``;
                   val def_thm = take_data_abort_exception_def;
                   val const_rp_thm = const_comp_take_abort_irq_exception_rp_thm;
                   val fixed_vb_rp_thm2 = fixed_VectorBase_abort_irq_exception_thm2;
                   val fixed_vb_rp_thm1 = fixed_VectorBase_abort_irq_exception_thm1;
                   val joint_write_body_spc_thm = joint_write_body_data_abort_spc_thm;

                   val l_type = ``:(word32 # word32 # bool # ARMpsr # CP15scr # CP15sctlr)``;
                   val spec_list1 = mk_spec_list3(sl_elm);
                   val spec_list2 = mk_spec_list4(sl_elm);
               in
                 prove_take_exception_spc
                     body def_thm sl_elm
                     const_rp_thm  fixed_vb_rp_thm2
                     fixed_vb_rp_thm1 joint_write_body_spc_thm
                     l_type spec_list1 spec_list2
               end
);

val take_prefetch_abort_exception_spc_thm =
    store_thm ("take_prefetch_abort_exception_spc_thm",
               ``!s a s'.
              (¬access_violation s')==>
              (¬access_violation s)==>
              (take_prefetch_abort_exception <|proc:=0|> s =
                                                  ValueState a s') ==>
             ((s'.registers (0,RName_PC) =
               HD (vector_table_address (get_base_vector_table s) 23w)) ∨
              (s'.registers (0,RName_PC) =
               HD (TL (vector_table_address (get_base_vector_table s) 23w))))
              ``,
               let
                   val body =
                       get_action_body ``take_prefetch_abort_exception``
                                       take_prefetch_abort_exception_def;
                   val sl_elm =  ``(a:(word32 # word32 # bool # ARMpsr # CP15scr # CP15sctlr))``;
                   val def_thm = take_prefetch_abort_exception_def;
                   val const_rp_thm = const_comp_take_abort_irq_exception_rp_thm;
                   val fixed_vb_rp_thm2 = fixed_VectorBase_abort_irq_exception_thm2;
                   val fixed_vb_rp_thm1 = fixed_VectorBase_abort_irq_exception_thm1;
                   val joint_write_body_spc_thm = joint_write_body_prefetch_abort_spc_thm;

                   val l_type = ``:(word32 # word32 # bool # ARMpsr # CP15scr # CP15sctlr)``;
                   val spec_list1 = mk_spec_list3(sl_elm);
                   val spec_list2 = mk_spec_list4(sl_elm);
               in
                 prove_take_exception_spc
                     body def_thm sl_elm
                     const_rp_thm  fixed_vb_rp_thm2
                     fixed_vb_rp_thm1 joint_write_body_spc_thm
                     l_type spec_list1 spec_list2
               end
);


val take_undef_instr_exception_spc_thm =
    store_thm ("take_undef_instr_exception_spc_thm",
               ``!s a s'.
              (¬access_violation s')==>
              (¬access_violation s)==>
              (take_undef_instr_exception <|proc:=0|> s =
                                                  ValueState a s') ==>
                ((s'.registers (0,RName_PC) =
               (HD (vector_table_address
                    (get_base_vector_table s) 27w)))
              \/
              (s'.registers (0,RName_PC) =
               (HD (TL (vector_table_address
                (get_base_vector_table s) 27w)))))
              ``,
               let
                   val body =
                       get_action_body ``take_undef_instr_exception``
                                       take_undef_instr_exception_def;
                   val sl_elm =  ``(a:(word32 # word32 # ARMpsr # CP15scr # CP15sctlr))``;
                   val const_rp_thm = const_comp_take_undef_svc_exception_rp_thm;
                   val fixed_vb_rp_thm2 = fixed_VectorBase_undef_instr_exception_thm2;
                   val fixed_vb_rp_thm1 = fixed_VectorBase_undef_instr_exception_thm1;
                   val l_type = ``:(word32 # word32 # ARMpsr # CP15scr # CP15sctlr)``;
                   val spec_list1 = mk_spec_list(sl_elm);
                   val spec_list2 = mk_spec_list2(sl_elm);
               in
                   prove_take_exception_spc
                     body take_undef_instr_exception_def  sl_elm
                     const_rp_thm  fixed_vb_rp_thm2
                     fixed_vb_rp_thm1 joint_write_body_undef_instr_spc_thm
                     l_type spec_list1 spec_list2
               end
              );


val take_irq_exception_spc_thm =
    store_thm ("take_irq_exception_spc_thm",
               ``!s a s'.
              (¬access_violation s')==>
              (¬access_violation s)==>
              (take_irq_exception <|proc:=0|> s =
                                                  ValueState a s') ==>
             ((s'.registers (0,RName_PC) =
               (HD (vector_table_address
                    (get_base_vector_table s) 18w)))
              \/
              (s'.registers (0,RName_PC) =
               (HD (TL (vector_table_address
                (get_base_vector_table s) 18w)))))``,
               let
                   val body =
                       get_action_body ``take_irq_exception``
                                       take_irq_exception_def;
                   val sl_elm =  ``(a:(word32 # word32 # bool # ARMpsr # CP15scr # CP15sctlr))``;
                   val const_rp_thm = const_comp_take_abort_irq_exception_rp_thm;
                   val fixed_vb_rp_thm2 = fixed_VectorBase_abort_irq_exception_thm2;
                   val fixed_vb_rp_thm1 = fixed_VectorBase_abort_irq_exception_thm1;
                   val joint_write_body_spc_thm = joint_write_body_irq_spc_thm;

                   val l_type = ``:(word32 # word32 # bool # ARMpsr # CP15scr # CP15sctlr)``;
                   val spec_list1 = mk_spec_list3(sl_elm);
                   val spec_list2 = mk_spec_list4(sl_elm);

               in
                   prove_take_exception_spc
                     body take_irq_exception_def  sl_elm
                     const_rp_thm  fixed_vb_rp_thm2
                     fixed_vb_rp_thm1 joint_write_body_irq_spc_thm
                     l_type spec_list1 spec_list2
               end
              );


val take_svc_exception_spc_thm =
    store_thm ("take_svc_exception_spc_thm",
               let
                   val athm = SIMP_CONV (bool_ss) [take_svc_exception_def]
                                        ``take_svc_exception <|proc:=0|> ``
                   val (_, a) =  (dest_eq (concl athm))
                   val (_,_,rb)= decompose_term a;
               in
                   ``!s a s'.
              (¬access_violation s')==>
              (¬access_violation s)==>
              (^rb s = ValueState a s') ==>
              ((s'.registers (0,RName_PC) =
               (HD (vector_table_address
                    (get_base_vector_table s) 19w)))
              \/
              (s'.registers (0,RName_PC) =
               (HD (TL (vector_table_address
                (get_base_vector_table s) 19w)))))
              ``
               end,
               let
                   val athm = SIMP_CONV (bool_ss) [take_svc_exception_def]
                                        ``take_svc_exception <|proc:=0|> ``
                   val (_, a) =  (dest_eq (concl athm))
                   val (_,_,body)= decompose_term a;

                   val sl_elm =  ``(a:(word32 # word32 # ARMpsr # CP15scr # CP15sctlr))``;
                   val const_rp_thm = const_comp_take_undef_svc_exception_rp_thm;
                   val fixed_vb_rp_thm2 = fixed_VectorBase_undef_instr_exception_thm2;
                   val fixed_vb_rp_thm1 = fixed_VectorBase_undef_instr_exception_thm1;
                   val l_type = ``:(word32 # word32 # ARMpsr # CP15scr # CP15sctlr)``;
                   val spec_list1 = mk_spec_list(sl_elm);
                   val spec_list2 = mk_spec_list2(sl_elm);
               in
                   prove_take_exception_spc
                     body take_undef_instr_exception_def  sl_elm
                     const_rp_thm  fixed_vb_rp_thm2
                     fixed_vb_rp_thm1 joint_write_body_svc_spc_thm
                     l_type spec_list1 spec_list2
               end
              );


val _ = export_theory();
