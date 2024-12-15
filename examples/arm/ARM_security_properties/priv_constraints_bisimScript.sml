open HolKernel boolLib bossLib Parse proofManagerLib;
open arm_coretypesTheory arm_seq_monadTheory arm_opsemTheory arm_stepTheory;
open MMUTheory MMU_SetupTheory inference_rulesTheory switching_lemma_helperTheory;
open priv_constraints_lrTheory priv_constraints_spsrTheory;
open tacticsLib ARM_prover_extLib;

(*********************************************************************************)
(*         checking bisimulation for take exceptions in privileged mode          *)
(*                    Narges                                                     *)
(*********************************************************************************)

val _ =  new_theory("priv_constraints_bisim");

val let_ss = simpLib.mk_simpset [boolSimps.LET_ss] ;
val _ = diminish_srw_ss ["one"]
val _ = augment_srw_ss [rewrites [oneTheory.FORALL_ONE]]

val prove_abs_spsr_const_action =
 fn (a, thms, abody_thm, expr,mode) =>
    let
        val _ =  set_goal([], ``
                         (priv_spsr_constraints_abs ^a ^expr ^mode) ``)
        val (a_abs,a_body) = pairLib.dest_pabs a;
        val unbeta_thm= (PairRules.UNPBETA_CONV a_abs a_body)
        val unbeta_a = mk_comb (a, a_abs)
        val snd = get_type_inst (type_of(a_body) , false)
        val a_body_type = get_type_inst (snd, true);
        val proved_unbeta_lemma =
          TAC_PROOF(([],
                     “priv_spsr_constraints ^a_body ^expr ^mode =
                      priv_spsr_constraints ^unbeta_a ^expr ^mode”),
                     (ASSUME_TAC (SPECL [a_body,``^unbeta_a``, expr,mode]
                                        (INST_TYPE [beta |-> a_body_type,
                                                    alpha |-> ``:arm_state``]
                                                   (List.nth(thms,0)))))
                     THEN ASSUME_TAC unbeta_thm
                     THEN RES_TAC)

        val proved_preserve_unbeta_a =
            TAC_PROOF (
                       ([], `` (priv_spsr_constraints ^unbeta_a ^expr ^mode)``),
                       (ASSUME_TAC (proved_unbeta_lemma))
                           THEN (ASSUME_TAC abody_thm)
                           THEN (FULL_SIMP_TAC (srw_ss()) []))

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


val untouched_spsr_abs_def =
    Define `untouched_spsr_abs f (mode:bool[5]) =
           !s a c s'. (f a s = ValueState c s') ==>
                let spsr = get_spsr_by_mode mode
                 in
                    ((s'.psrs (0,spsr))=(s.psrs (0,spsr)))
                    /\
                    ((s'.psrs (0,CPSR)).M=(s.psrs (0,CPSR)).M)
                           `;

val untouched_spsr_def =
    Define `untouched_spsr f (mode:bool[5]) =
           !s c s'. (f s = ValueState c s') ==>
           let spsr = get_spsr_by_mode mode
           in (*(spsr<>CPSR) ==>*)
                    ((s'.psrs (0,spsr))=(s.psrs (0,spsr)))
                    /\
                    ((s'.psrs (0,CPSR)).M=(s.psrs (0,CPSR)).M)
                           `;

val priv_spsr_constraints_def =
    Define `priv_spsr_constraints f cpsr mode =
            ! s s' a . (f s = ValueState a s') ==>
                (~access_violation s') ==>
                ((s'.psrs(0,CPSR)).M = mode) ==>
         (  let spsr = get_spsr_by_mode mode
            in (*(spsr<>CPSR) ==>*)
                           ((s'.psrs(0,spsr)) = cpsr )

              )`;


val priv_spsr_constraints_abs_def =
    Define `priv_spsr_constraints_abs f cpsr mode =
            ! s s' a c . (f c s = ValueState a s') ==>
                (~access_violation s') ==>
                ((s'.psrs(0,CPSR)).M = mode) ==>
         (  let spsr = get_spsr_by_mode mode
            in (*(spsr<>CPSR) ==>*)
                           ((s'.psrs(0,spsr)) = cpsr )

              )`;

(*********************   proof rules *******************************)

val seqT_priv_spsr_constraints_before_thm =
    store_thm("seqT_priv_spsr_constraints_before_thm",
              `` ! g f cpsr spsr. priv_spsr_constraints_abs f cpsr spsr ==>
             priv_spsr_constraints (g >>= f) cpsr spsr ``,
              (RW_TAC (srw_ss()) [seqT_def,
                                  priv_spsr_constraints_def,
                                  priv_spsr_constraints_abs_def])
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
                  THEN PAT_X_ASSUM ``! s s' a c .X ==> Z``
                  (fn thm => ASSUME_TAC
                                 (SPECL [``b:arm_state``,``s':arm_state``,
                                         ``a:'b``,``a':'a``] thm))
                  THEN FULL_SIMP_TAC (srw_ss()) []
                  THEN RES_TAC
                  THEN FULL_SIMP_TAC (srw_ss()) [seqT_def]
             );

val parT_priv_spsr_constraints_before_thm =
    store_thm("parT_priv_spsr_constraints_before_thm",
              `` !f g cpsr spsr . priv_spsr_constraints f cpsr spsr ==>
             priv_spsr_constraints (g ||| f) cpsr spsr ``,
              RW_TAC (srw_ss())
                      [parT_def,seqT_def,
                       priv_spsr_constraints_def,
                       untouched_spsr_def,constT_def]
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
                  THEN PAT_X_ASSUM ``! s s' a. (f s = ValueState a s') ==> Z`` (fn thm => ASSUME_TAC
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

val seqT_priv_spsr_constraints_after_thm =
    store_thm("seqT_priv_spsr_constraints_after_thm",
              `` !f g cpsr mode.
             priv_spsr_constraints g cpsr mode ==>
             (untouched_spsr_abs f mode) ==>
             priv_spsr_constraints (g >>= f) cpsr mode``,
              (RW_TAC (srw_ss()) [seqT_def,
                                  priv_spsr_constraints_def,
                                  priv_spsr_constraints_abs_def,
                                  untouched_spsr_abs_def]) THEN
                        FULL_SIMP_TAC (let_ss) [] THEN
                        Cases_on `g s` THEN
                        FULL_SIMP_TAC (srw_ss()) [] THEN
                        Cases_on `access_violation b`
                        THEN Q.UNABBREV_TAC `spsr`
                        THEN PAT_X_ASSUM ``! s s' a  .X ==> Z``
                        (fn thm => ASSUME_TAC
                                       (SPECL [``s:arm_state``,``b:arm_state``,
                                               ``a':'a``] thm))

                        THEN PAT_X_ASSUM ``! s1 a c s2. X``
                        (fn thm => ASSUME_TAC
                                       (SPECL [``b:arm_state``,``a':'a``,
                                               ``a:'b``,``s':arm_state``] thm))

                        THEN RES_TAC
                        THEN UNDISCH_ALL_TAC
                        THEN RW_TAC (srw_ss()) []
                        THEN FULL_SIMP_TAC (srw_ss()) []
                        THEN FULL_SIMP_TAC (srw_ss()) []);

val parT_priv_spsr_constraints_after_thm =
    store_thm("parT_priv_spsr_constraints_after_thm",
`` !f g cpsr spsr. priv_spsr_constraints g cpsr spsr ==>
             (untouched_spsr f spsr) ==>
             priv_spsr_constraints (g ||| f) cpsr spsr``,
              (RW_TAC (srw_ss())
                      [parT_def,seqT_def,
                       priv_spsr_constraints_def,
                       untouched_spsr_def,constT_def])
                  THEN FULL_SIMP_TAC (let_ss) []THEN
                  Cases_on `g s` THEN
                  Cases_on `f b` THEN
                  Cases_on `access_violation b` THEN
                  Cases_on `access_violation b'`   THEN
                  (* Q.UNABBREV_TAC `spsr` THEN *)
                  FULL_SIMP_TAC (srw_ss()) [] THEN
                  PAT_X_ASSUM ``! s a s' .(f s = ValueState a s') ==> Z``
                  (fn thm => ASSUME_TAC
                                 (SPECL [``b:arm_state``,``a'':'a``,``b':arm_state``] thm))
                  THEN PAT_X_ASSUM ``! s1 c s2. X``
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
             (untouched_spsr f mode) ==>
             (untouched_spsr_abs g mode) ==>
             (untouched_spsr (f>>=g) mode)``,
              (RW_TAC (srw_ss()) [seqT_def,untouched_spsr_abs_def,
                                  untouched_spsr_def])
THEN Cases_on `f s`
                  THEN FULL_SIMP_TAC (let_ss) []
                  THEN PAT_X_ASSUM ``! s1 c s2. (f _ = ValueState _ _) ==> _``
                  (fn thm => ASSUME_TAC
                                 (SPECL [``s:arm_state``,``a:'a``,``b:arm_state``] thm))
                  THEN RES_TAC
                  THEN Cases_on `access_violation b`
                  THEN FULL_SIMP_TAC (srw_ss()) []
                  THEN RW_TAC (srw_ss()) []
                  THEN PAT_X_ASSUM ``! s a c s'. X``
                  (fn thm => ASSUME_TAC
                                 (SPECL [``b:arm_state``,``a:'a``,
                                         ``c:'b``,``s':arm_state``] thm))
                  THEN RES_TAC
                  THEN FULL_SIMP_TAC (srw_ss()) []
                  THEN RW_TAC (srw_ss()) []);

val parT_trans_untouched_thm =
    store_thm("parT_trans_untouched_thm",
              `` !f g spsr.
             (untouched_spsr f spsr) ==>
             (untouched_spsr g spsr) ==>
             (untouched_spsr (f ||| g) spsr)``,
              (RW_TAC (srw_ss()) [seqT_def,parT_def,constT_def,
                                  untouched_spsr_def])
                  THEN Cases_on `f s`
                  THEN Cases_on `access_violation b`
                  THEN Cases_on `g b`
                  THEN Cases_on `access_violation b'`
                  THEN FULL_SIMP_TAC (let_ss) []
                  THEN PAT_X_ASSUM ``! s c s'. X``
                  (fn thm => ASSUME_TAC
                                 (SPECL [``b:arm_state``,``a':'b``,
                                         ``b':arm_state``] thm))
                  THEN PAT_X_ASSUM ``! s1 c s2. (f _ = ValueState _ _) ==> _``
                  (fn thm => ASSUME_TAC
                                 (SPECL [``s:arm_state``,``a:'a``,``b:arm_state``] thm))
                  THEN RES_TAC
                  THEN FULL_SIMP_TAC (srw_ss()) []
                  THEN RW_TAC (srw_ss()) []
                  );

val spfc_first_abs_lemma =
    store_thm ("spfc_first_abs_lemma",
               ``!f g x y. (f=g) ==> ((priv_spsr_constraints f x y) =
                                    (priv_spsr_constraints g x y))``,
               RW_TAC (srw_ss()) []);


val spfc_second_abs_lemma =
    store_thm ("spfc_second_abs_lemma",
               ``! f x z. (! y. priv_spsr_constraints (f y) x z) =
    priv_spsr_constraints_abs f x z``,
               RW_TAC (srw_ss()) [priv_spsr_constraints_def,priv_spsr_constraints_abs_def]
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
              ``! cpsr mode. priv_spsr_constraints (write_spsr <|proc := 0|> cpsr)
             cpsr mode ``,

              RW_TAC (bool_ss) [write_spsr_def,seqT_def,priv_spsr_constraints_def]
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
                                                                (* Q.UNABBREV_TAC `spsr`  *)
                                                                (* THEN *) UNDISCH_ALL_TAC
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
             (untouched_spsr (write_reg <|proc:=0|> 14w value) mode)``,
              EVAL_TAC
                  THEN RW_TAC (srw_ss()) []
                  THEN UNDISCH_ALL_TAC
                  THEN EVAL_TAC
                  THEN RW_TAC (srw_ss()) []
                  THEN FULL_SIMP_TAC (srw_ss()) []);

val read_cpsr_sfc_ut_thm =
    store_thm("read_cpsr_sfc_ut_thm",
              `` !mode.
             (untouched_spsr (read_cpsr <|proc:=0|> ) mode )``,
              EVAL_TAC
                  THEN RW_TAC (srw_ss()) [] );

val branch_to_sfc_ut_thm =
    store_thm("branch_to_sfc_ut_thm",
              ``!adr mode. untouched_spsr (
    branch_to <|proc:=0|> adr) mode``,
              EVAL_TAC
                  THEN RW_TAC (srw_ss()) []
                  THEN UNDISCH_ALL_TAC
                  THEN EVAL_TAC
                  THEN RW_TAC (srw_ss()) []
                  THEN FULL_SIMP_TAC (srw_ss()) []);

val constT_sfc_ut_thm =
    store_thm("constT_sfc_ut_thm",
              ``! mode. untouched_spsr_abs (λ(u1:unit,u2:unit,u3:unit,u4:unit).
                                             constT ()) mode``,
              EVAL_TAC
                  THEN RW_TAC (srw_ss()) [] );

val ui_write_cpsr_spsr_ut_thm =
    store_thm("ui_write_cpsr_spsr_ut_thm",
``untouched_spsr (
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

val svc_write_cpsr_spsr_ut_thm =
    store_thm("svc_write_cpsr_spsr_ut_thm",
``untouched_spsr (
           read_cpsr <|proc:=0|> >>=
                (λcpsr.
                write_cpsr <|proc:=0|>
                 (cpsr with
                  <|I := T; IT := 0w; J := F; T := sctlr.TE;
                    E := sctlr.EE|>))) 19w``,
EVAL_TAC
THEN RW_TAC (srw_ss()) []
THEN UNDISCH_ALL_TAC
THEN EVAL_TAC
THEN RW_TAC (srw_ss()) []
THEN FULL_SIMP_TAC (srw_ss()) []);

val irq_write_cpsr_spsr_ut_thm =
    store_thm("irq_write_cpsr_spsr_ut_thm",
``untouched_spsr (
           read_cpsr <|proc:=0|> >>=
              (λcpsr.
                     write_cpsr <|proc:=0|>
                       (cpsr with
                        <|I := T;
                          A :=
                            ((¬have_security_exta ∨ ¬scr.NS ∨ scr.AW) ∨
                             cpsr.A); IT := 0w; J := F; T := sctlr.TE;
                          E := sctlr.EE|>))) 18w``,
EVAL_TAC
THEN RW_TAC (srw_ss()) []
THEN UNDISCH_ALL_TAC
THEN EVAL_TAC
THEN RW_TAC (srw_ss()) []
THEN FULL_SIMP_TAC (srw_ss()) []);


val ab_write_cpsr_spsr_ut_thm =
    store_thm("ab_write_cpsr_spsr_ut_thm",
``untouched_spsr (
           read_cpsr <|proc:=0|> >>=
                  (λcpsr.
                     write_cpsr <|proc:=0|>
                       (cpsr with
                        <|I := T;
                          A :=
                            ((¬have_security_exta ∨ ¬scr.NS ∨ scr.AW) ∨
                             cpsr.A); IT := 0w; J := F; T := sctlr.TE;
                          E := sctlr.EE|>))) 23w``,
EVAL_TAC
THEN RW_TAC (srw_ss()) []
THEN UNDISCH_ALL_TAC
THEN EVAL_TAC
THEN RW_TAC (srw_ss()) []
THEN FULL_SIMP_TAC (srw_ss()) []);


val fiq_write_cpsr_spsr_ut_thm =
    store_thm("fiq_write_cpsr_spsr_ut_thm",
``untouched_spsr (
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
                          E := sctlr.EE|>))) 17w``,

EVAL_TAC
THEN RW_TAC (srw_ss()) []
THEN UNDISCH_ALL_TAC
THEN EVAL_TAC
THEN RW_TAC (srw_ss()) []
THEN FULL_SIMP_TAC (srw_ss()) []);


fun get_take_undef_writing_part_spsr_thm a' wr_sfc_ut_thm lr vt_index mode =

    let   val (l,r,rb1)= decompose_term a';
          val (l2,r2,rb2)= decompose_term rb1
          val (l3,r3,rb3)= decompose_term rb2
          val (l4,r4,rb4)= decompose_term l3
          val (l5,r5,rb5)= decompose_term r4
          val (l6,r6,rb6)= decompose_term r5;
          (* proof of r5 *)
          val thm1 = LIST_MP [ wr_sfc_ut_thm,
                               (SPECL [``(ExcVectorBase + ^vt_index)``,
                                       mode ] branch_to_sfc_ut_thm)]
                             (SPECL [l6,r6,mode]
                                    (INST_TYPE [alpha |-> ``:unit``,
                                                beta |-> ``:unit``]
                                               parT_trans_untouched_thm));
          (* proof of r4 *)
          val thm2 = LIST_MP [
                     (SPECL [lr,
                             mode] write_lr_reg_sfc_ut_thm),
                     thm1]
                             (SPECL [l5,r5,mode]
                                    (INST_TYPE [alpha |-> ``:unit``,
                                                beta |-> ``:(unit#unit)``]
                                               parT_trans_untouched_thm));
          (* proof of l3 *)
          val thm3 = LIST_MP [
                     (SPECL [``cpsr:ARMpsr``,mode] write_spsr_sfc_thm),
                     thm2]
                             (SPECL [r4,l4,``cpsr:ARMpsr``,mode]
                                    (INST_TYPE [beta |-> ``:unit``,
                                                alpha |-> ``:(unit#unit#unit)``]
                                               parT_priv_spsr_constraints_after_thm));
          (* proof of rb2 *)
          val thm4 = LIST_MP [
                     thm3,
                     SPEC mode constT_sfc_ut_thm]
                             (SPECL [r3,l3,``cpsr:ARMpsr``,mode]
                                    (INST_TYPE [beta |-> ``:unit``,
                                                alpha |-> ``:(unit#unit#unit#unit)``]
                                               seqT_priv_spsr_constraints_after_thm));
          (* proof of rb1 *)
          val (thm5 , _) = prove_abs_spsr_const_action (r2, [spfc_first_abs_lemma,
                                                             spfc_second_abs_lemma],
                                                        thm4, ``cpsr:ARMpsr``,
                                                        mode);
          val thm6 = MP (SPECL [l2,r2,``cpsr:ARMpsr``,mode]
                               (INST_TYPE [beta |-> ``:unit``,
                                           alpha |-> ``:(unit#unit)``]
                                          seqT_priv_spsr_constraints_before_thm)) thm5;
    in
        (GEN_ALL thm6)
    end

val take_undef_writing_part_spf_thm =
    save_thm ("take_undef_writing_part_spf_thm",
              let
                  val a = SIMP_CONV (bool_ss) [take_undef_instr_exception_def]
                                    ``take_undef_instr_exception <|proc:=0|> ``;
                  val (_, a') =  (dest_eq (concl a))
              in
                  get_take_undef_writing_part_spsr_thm a'
                                    ui_write_cpsr_spsr_ut_thm ``(if cpsr.T
                         then
                             pc − 2w:bool[32]
                         else
                             pc − 4w)`` ``4w:bool[32]`` ``27w:bool[5]``
              end
);


val take_data_abort_writing_part_spf_thm =
    save_thm ("take_data_abort_writing_part_spf_thm",
              let
                  val a = SIMP_CONV (bool_ss) [take_data_abort_exception_def]
                                    ``take_data_abort_exception <|proc:=0|> ``;
                  val (_, a') =  (dest_eq (concl a));
              in
                  get_take_undef_writing_part_spsr_thm a'
                              ab_write_cpsr_spsr_ut_thm
                      ``(if cpsr.T
                         then
                             pc:bool[32]
                         else
                             pc − 4w)`` ``16w:bool[32]`` ``23w:bool[5]``
              end
);

val take_prefetch_abort_writing_part_spf_thm =
    save_thm ("take_prefetch_abort_writing_part_spf_thm",
              let
                  val a = SIMP_CONV (bool_ss) [take_prefetch_abort_exception_def]
                                    ``take_prefetch_abort_exception <|proc:=0|> ``
                  val (_, a') =  (dest_eq (concl a))
              in
                  get_take_undef_writing_part_spsr_thm a'
                              ab_write_cpsr_spsr_ut_thm
                      ``(if cpsr.T
                         then
                             pc:bool[32]
                         else
                             pc − 4w)`` ``12w:bool[32]`` ``23w:bool[5]``
              end
);

val take_irq_writing_part_spf_thm =
    save_thm ("take_irq_writing_part_spf_thm",
              let
                  val a = SIMP_CONV (bool_ss) [take_irq_exception_def]
                                    ``take_irq_exception <|proc:=0|> ``;
                  val (_, a') =  (dest_eq (concl a));
              in
                  get_take_undef_writing_part_spsr_thm a'
                              irq_write_cpsr_spsr_ut_thm
                      ``(if cpsr.T
                         then
                             pc:bool[32]
                         else
                             pc − 4w)`` ``24w:bool[32]`` ``18w:bool[5]``
              end
);

val take_svc_writing_part_spf_thm =
    save_thm ("take_svc_writing_part_spf_thm",
              let
                  val a = SIMP_CONV (bool_ss) [take_svc_exception_def]
                                    ``take_svc_exception <|proc:=0|> ``;
                  val (_, a') =  (dest_eq (concl a))
                  val (l,r,rbody) = decompose_term a';
              in
                  get_take_undef_writing_part_spsr_thm rbody
                            svc_write_cpsr_spsr_ut_thm ``(if cpsr.T
                         then
                             pc − 2w:bool[32]
                         else
                             pc − 4w)`` ``8w:bool[32]`` ``19w:bool[5]``
              end
);


val satisfy_SPSR_constraints_def =
    Define ` satisfy_SPSR_constraints f m =
                ! s s' a.
                  (f s = ValueState a s') ==>
                 (~access_violation s') ==>
                 ((s'.psrs(0,CPSR)).M = m) ==>
                 ((s'.psrs (0,get_spsr_by_mode(m))) = (s.psrs(0,CPSR)))`;


fun prove_take_exception_spsr_constraints te te_def fixed_cpsr_thm fixed_cpsr_thm2
                                          wp_thm const_comp_rp_thm sl_elm2 spec_lists
                                          ltype =
 let
     val (l,r,rb1)= decompose_term te;
     val spec_list = List.nth(spec_lists,0)
     val spec_list2 = List.nth(spec_lists,1)
     val (_,sr) = dest_eq ( concl (SIMP_RULE (srw_ss()) []
                                             (SPECL [``s:arm_state``,r]
                                                    (INST_TYPE [alpha |-> ``:unit``]
                                                               fixed_cpsr_thm))));
     val (_,simpr,_) = decompose_term sr;

 in
     RW_TAC (bool_ss) [te_def,
                       satisfy_SPSR_constraints_def]
               THEN ASSUME_TAC (SPECL [``s:arm_state``,r]
                                      (INST_TYPE [alpha |-> ``:unit``]
                                                 fixed_cpsr_thm))
               THEN FULL_SIMP_TAC (srw_ss()) []
               THEN FULL_SIMP_TAC (let_ss) []
               THEN PAT_X_ASSUM ``X=Y`` (fn thm => THROW_AWAY_TAC (concl thm))
               THEN ASSUME_TAC const_comp_rp_thm
               THEN RW_TAC (srw_ss()) [priv_spsr_constraints_def,
                                       priv_spsr_constraints_abs_def]
               THEN FULL_SIMP_TAC (srw_ss()) [const_comp_def]
               THEN (Cases_on [QUOTE ("("^(term_to_string l) ^ ") s")]
               THEN IMP_RES_TAC seqT_access_violation_thm
               THENL
               [ RES_TAC
                    THEN RW_TAC (srw_ss()) []
                    THEN IMP_RES_TAC hlp_seqT_thm
                    THEN PAT_X_ASSUM ``X a' b= ValueState a s'``
                    (fn thm => ASSUME_TAC (PairRules.PBETA_RULE thm))
                    THEN
                    ASSUME_TAC ( SPECL
                                     spec_list  (GEN_ALL  (SIMP_RULE (bool_ss) [priv_spsr_constraints_def]
                                                                     wp_thm)))
                    THEN PAT_X_ASSUM ``X ==> Y`` (fn thm => ASSUME_TAC (PairRules.PBETA_RULE thm))
                    THEN
                    ASSUME_TAC (SPECL spec_list2 fixed_cpsr_thm2)
                    THEN RES_TAC
                    THEN RES_TAC
                    THEN FULL_SIMP_TAC (srw_ss()) [get_spsr_by_mode_def]
                    THEN FULL_SIMP_TAC (let_ss) []
                    THEN RW_TAC (srw_ss()) []
               ,
               IMP_RES_TAC (SPEC simpr (
                            INST_TYPE [beta |-> ``:unit``,
                                       alpha |-> ltype ]
                                      hlp_errorT_thm))
                           THEN
                           PAT_X_ASSUM ``! (s:arm_state) . X ``
                           (fn thm => ASSUME_TAC (SPEC ``s:arm_state`` thm))
                           THEN RW_TAC (srw_ss()) []
                           THEN FULL_SIMP_TAC (srw_ss()) []
               ])
    end;

val take_svc_exception_spsr_thm =
    store_thm ("take_svc_exception_spsr_thm",
    let
        val athm = SIMP_CONV (bool_ss) [take_svc_exception_def]
                             ``take_svc_exception <|proc:=0|> ``
        val (_, a) =  (dest_eq (concl athm))
        val (_,_,rb)= decompose_term a;
    in
        `` satisfy_SPSR_constraints
              ^rb  19w``
    end,
    let
        val athm = SIMP_CONV (bool_ss) [take_svc_exception_def]
                          ``take_svc_exception <|proc:=0|> ``
        val (_, a) =  (dest_eq (concl athm));
        val (_,_,te)= decompose_term a;
        val sl_elm2 =  ``(a':(word32 # word32 # ARMpsr # CP15scr # CP15sctlr))``
        val spec_list = (mk_spec_list sl_elm2)@[``b:arm_state``, ``s':arm_state``,``a:unit``]
        val spec_list2 = [``b:arm_state``] @ List.rev (mk_spec_list2 (sl_elm2))
        val spec_lists = [spec_list] @ [spec_list2];
        val te_def = take_svc_exception_def;
        val fixed_cpsr_thm = fixed_cpsr_undef_svc_thm;
        val fixed_cpsr_thm2 = fixed_cpsr_undef_svc_thm2;
        val wp_thm = take_svc_writing_part_spf_thm;
        val const_comp_rp_thm =  const_comp_take_undef_svc_exception_rp_thm;
        val ltype = ``:(word32 # word32 # ARMpsr # CP15scr # CP15sctlr)``;

    in
 prove_take_exception_spsr_constraints te te_def fixed_cpsr_thm fixed_cpsr_thm2
                                          wp_thm const_comp_rp_thm sl_elm2 spec_lists
                                          ltype
    end);

val take_undef_instr_exception_spsr_thm =
    store_thm ("take_undef_instr_exception_spsr_thm",
      `` satisfy_SPSR_constraints
              (take_undef_instr_exception <|proc:=0|>)  27w``,
    let
        val athm = SIMP_CONV (bool_ss) [take_undef_instr_exception_def]
                          ``take_undef_instr_exception <|proc:=0|> ``
        val (_, te) =  (dest_eq (concl athm));
        val sl_elm2 =  ``(a':(word32 # word32 # ARMpsr # CP15scr # CP15sctlr))``
        val spec_list = (mk_spec_list sl_elm2)@[``b:arm_state``, ``s':arm_state``,``a:unit``]
        val spec_list2 = [``b:arm_state``] @ List.rev (mk_spec_list2 (sl_elm2))
        val spec_lists = [spec_list] @ [spec_list2];
        val te_def = take_undef_instr_exception_def;
        val fixed_cpsr_thm = fixed_cpsr_undef_svc_thm;
        val fixed_cpsr_thm2 = fixed_cpsr_undef_svc_thm2;
        val wp_thm = take_undef_writing_part_spf_thm;
        val const_comp_rp_thm =  const_comp_take_undef_svc_exception_rp_thm;
        val ltype = ``:(word32 # word32 # ARMpsr # CP15scr # CP15sctlr)``;

    in
 prove_take_exception_spsr_constraints te te_def fixed_cpsr_thm fixed_cpsr_thm2
                                          wp_thm const_comp_rp_thm sl_elm2 spec_lists
                                          ltype
    end);


val take_data_abort_exception_spsr_thm =
    store_thm ("take_data_abort_exception_spsr_thm",
      `` satisfy_SPSR_constraints
              (take_data_abort_exception <|proc:=0|>)  23w``,
    let
        val athm = SIMP_CONV (bool_ss) [take_data_abort_exception_def]
                          ``take_data_abort_exception <|proc:=0|> ``
        val (_, te) =  (dest_eq (concl athm));
        val sl_elm2 =  ``(a':(word32 # word32 # bool# ARMpsr # CP15scr # CP15sctlr))``
        val spec_list = (mk_spec_list3 sl_elm2)@[``b:arm_state``, ``s':arm_state``,``a:unit``]
        val spec_list2 = [``b:arm_state``] @ List.rev (mk_spec_list4 (sl_elm2))
        val spec_lists = [spec_list] @ [spec_list2];
        val te_def = take_data_abort_exception_def;
        val fixed_cpsr_thm = fixed_cpsr_abt_irq_thm;
        val fixed_cpsr_thm2 = fixed_cpsr_abt_irq_thm2;
        val wp_thm = take_data_abort_writing_part_spf_thm;
        val const_comp_rp_thm = const_comp_take_abort_irq_exception_rp_thm
        val ltype = ``:(word32 # word32 # bool# ARMpsr # CP15scr # CP15sctlr)``;

    in
 prove_take_exception_spsr_constraints te te_def fixed_cpsr_thm fixed_cpsr_thm2
                                          wp_thm const_comp_rp_thm sl_elm2 spec_lists
                                          ltype
    end);


val take_prefetch_abort_exception_spsr_thm =
    store_thm ("take_prefetch_abort_exception_spsr_thm",
      `` satisfy_SPSR_constraints
              (take_prefetch_abort_exception <|proc:=0|>)  23w``,
    let
        val athm = SIMP_CONV (bool_ss) [take_prefetch_abort_exception_def]
                          ``take_prefetch_abort_exception <|proc:=0|> ``
        val (_, te) =  (dest_eq (concl athm));
        val sl_elm2 =  ``(a':(word32 # word32 # bool# ARMpsr # CP15scr # CP15sctlr))``
        val spec_list = (mk_spec_list3 sl_elm2)@[``b:arm_state``, ``s':arm_state``,``a:unit``]
        val spec_list2 = [``b:arm_state``] @ List.rev (mk_spec_list4 (sl_elm2))
        val spec_lists = [spec_list] @ [spec_list2];
        val te_def = take_prefetch_abort_exception_def;
        val fixed_cpsr_thm = fixed_cpsr_abt_irq_thm;
        val fixed_cpsr_thm2 = fixed_cpsr_abt_irq_thm2;
        val wp_thm = take_prefetch_abort_writing_part_spf_thm;
        val const_comp_rp_thm =  const_comp_take_abort_irq_exception_rp_thm;
        val ltype = ``:(word32 # word32 # bool# ARMpsr # CP15scr # CP15sctlr)``;

    in
 prove_take_exception_spsr_constraints te te_def fixed_cpsr_thm fixed_cpsr_thm2
                                          wp_thm const_comp_rp_thm sl_elm2 spec_lists
                                          ltype
    end);


val take_irq_exception_spsr_thm =
    store_thm ("take_irq_exception_spsr_thm",
      `` satisfy_SPSR_constraints
              (take_irq_exception <|proc:=0|>)  18w``,
    let
        val athm = SIMP_CONV (bool_ss) [take_irq_exception_def]
                          ``take_irq_exception <|proc:=0|> ``
        val (_, te) =  (dest_eq (concl athm));
        val sl_elm2 =  ``(a':(word32 # word32 # bool# ARMpsr # CP15scr # CP15sctlr))``
        val spec_list = (mk_spec_list3 sl_elm2)@[``b:arm_state``, ``s':arm_state``,``a:unit``]
        val spec_list2 = [``b:arm_state``] @ List.rev (mk_spec_list4 (sl_elm2))
        val spec_lists = [spec_list] @ [spec_list2];
        val te_def = take_irq_exception_def;
        val fixed_cpsr_thm = fixed_cpsr_abt_irq_thm;
        val fixed_cpsr_thm2 = fixed_cpsr_abt_irq_thm2;
        val wp_thm = take_irq_writing_part_spf_thm;
        val const_comp_rp_thm =  const_comp_take_abort_irq_exception_rp_thm;
        val ltype = ``:(word32 # word32 # bool# ARMpsr # CP15scr # CP15sctlr)``;

    in
 prove_take_exception_spsr_constraints te te_def fixed_cpsr_thm fixed_cpsr_thm2
                                          wp_thm const_comp_rp_thm sl_elm2 spec_lists
                                          ltype
    end);



val preserve_priv_bisimilarity_def =
Define `preserve_priv_bisimilarity f m =
           ! s1 s1' a1 s2 s2' a2 g.
             (f s1 = ValueState a1 s1') ==>
             (f s2 = ValueState a2 s2') ==>
             (~access_violation s1') ==>
             (~access_violation s2') ==>
             (s1.registers(0,RName_PC) = s2.registers(0,RName_PC)) ==>
             ((s1.psrs(0,CPSR)) = (s2.psrs(0,CPSR))) ==>
             ((s1'.psrs(0,CPSR)) = (s2'.psrs(0,CPSR))) ==>
             ((s1'.psrs(0,CPSR)).M = m) ==>
             ((s2'.psrs(0,CPSR)).M = m) ==>
             (priv_mode_similar  (g:bool[32]) s2' s1')`;


(*
val LR_SPSR_equality_implies_priv_bisimilarity_thm =
    new_axiom ("LR_SPSR_equality_implies_priv_bisimilarity_thm",
 ``! f m v.
              satisfy_SPSR_constraints f m
              ==>
              satisfy_LR_constraints f m v
              ==>
             preserve_priv_bisimilarity f m
           ``);
*)
val LR_SPSR_equality_implies_priv_bisimilarity_thm =
    store_thm ("LR_SPSR_equality_implies_priv_bisimilarity_thm",
 ``! f m v.
              satisfy_SPSR_constraints f m
              ==>
              satisfy_LR_constraints f m v
              ==>
             preserve_priv_bisimilarity f m
           ``,
               RW_TAC (srw_ss()) [satisfy_SPSR_constraints_def,
                                  satisfy_LR_constraints_def,
                                  preserve_priv_bisimilarity_def,
                                  ARM_MODE_def,priv_mode_similar_def,
                                  ARM_READ_CPSR_def]
                    THEN UNABBREV_ALL_TAC
                    THEN NTAC 2 ( RES_TAC
                   THEN FULL_SIMP_TAC (srw_ss()) [get_pc_value_def]
                   THEN RW_TAC (srw_ss()) []));

val take_undef_instr_exception_priv_mode_similar_thm =
    store_thm ("take_undef_instr_exception_priv_mode_similar_thm",
``preserve_priv_bisimilarity (take_undef_instr_exception <|proc:=0|>) 27w``
             ,
             MP_TAC (SPEC ``27w:bool[5]`` take_undef_instr_exception_LR_thm)
                    THEN MP_TAC take_undef_instr_exception_spsr_thm
                    THEN METIS_TAC [LR_SPSR_equality_implies_priv_bisimilarity_thm] );


val take_data_abort_exception_priv_mode_similar_thm =
    store_thm ("take_data_abort_exception_priv_mode_similar_thm",
``preserve_priv_bisimilarity (take_data_abort_exception <|proc:=0|>) 23w``
             ,
             MP_TAC (SPEC ``23w:bool[5]`` take_data_abort_exception_LR_thm)
                    THEN MP_TAC take_data_abort_exception_spsr_thm
                    THEN METIS_TAC [LR_SPSR_equality_implies_priv_bisimilarity_thm] );

val take_prefetch_abort_exception_priv_mode_similar_thm =
    store_thm ("take_prefetch_abort_exception_priv_mode_similar_thm",
``preserve_priv_bisimilarity (take_prefetch_abort_exception <|proc:=0|>) 23w``
             ,
             MP_TAC (SPEC ``23w:bool[5]`` take_prefetch_abort_exception_LR_thm)
                    THEN MP_TAC take_prefetch_abort_exception_spsr_thm
                    THEN METIS_TAC [LR_SPSR_equality_implies_priv_bisimilarity_thm] );

val take_irq_exception_priv_mode_similar_thm =
    store_thm ("take_irq_exception_priv_mode_similar_thm",
``preserve_priv_bisimilarity (take_irq_exception <|proc:=0|>) 18w``
             ,
             MP_TAC (SPEC ``18w:bool[5]`` take_irq_exception_LR_thm)
                    THEN MP_TAC take_irq_exception_spsr_thm
                    THEN METIS_TAC [LR_SPSR_equality_implies_priv_bisimilarity_thm] );

val take_svc_exception_priv_mode_similar_thm =
    store_thm ("take_svc_exception_priv_mode_similar_thm",
               let
                   val athm = SIMP_CONV (bool_ss) [take_svc_exception_def]
                                        ``take_svc_exception <|proc:=0|> ``
                   val (_, a) =  (dest_eq (concl athm))
                   val (_,_,rb)= decompose_term a
               in
                   ``preserve_priv_bisimilarity ^rb 19w``
               end
             ,
             MP_TAC (SPEC ``19w:bool[5]`` take_svc_exception_LR_thm)
                    THEN MP_TAC take_svc_exception_spsr_thm
                    THEN METIS_TAC [LR_SPSR_equality_implies_priv_bisimilarity_thm] );


val _ = export_theory();
