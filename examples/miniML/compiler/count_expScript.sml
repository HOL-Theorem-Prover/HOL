open HolKernel bossLib boolLib countableLib countableTheory MiniMLTheory CompileTheory compileTerminationTheory lcsymtacs

val _ = new_theory"count_exp"

val [count_error_aux_inj_rwt]        = mk_count_aux_inj_rwt [``:error``]
val [count_lit_aux_inj_rwt]          = mk_count_aux_inj_rwt [``:lit``]
val [count_error_result_aux_inj_rwt] = mk_count_aux_inj_rwt [``:error_result``]
val [count_result_aux_inj_rwt]       = mk_count_aux_inj_rwt [``:α result``]
val [count_opn_aux_inj_rwt]          = mk_count_aux_inj_rwt [``:opn``]
val [count_opb_aux_inj_rwt]          = mk_count_aux_inj_rwt [``:opb``]
val [count_op_aux_inj_rwt]           = mk_count_aux_inj_rwt [``:op``]
val [count_log_aux_inj_rwt]          = mk_count_aux_inj_rwt [``:log``]
val [count_pat_aux_inj_rwt] = let
  val tys  = [``:pat``]
  val ttac = SOME (
    WF_REL_TAC `measure pat_size` >>
    gen_tac >> Induct >>
    rw[pat_size_def] >>
    res_tac >> DECIDE_TAC )
in mk_count_aux_inj_rwt_ttac tys ttac end
val [count_exp_aux_inj_rwt,count_v_aux_inj_rwt] = let
  val tys  = [``:exp``,``:v``]
  val ttac = SOME (
    WF_REL_TAC `inv_image $< (λx. case x of INL v => v_size v | INR e => exp_size e)` >>
    srw_tac[ARITH_ss][] >>
    qmatch_assum_rename_tac `MEM X l` ["X"] >>
    Induct_on `l` >>
    srw_tac[ARITH_ss][exp_size_def] >>
    fs[]>>
    srw_tac[ARITH_ss][exp_size_def] )
in mk_count_aux_inj_rwt_ttac tys ttac end

val [count_Cpat_aux_inj_rwt] = let
  val tys = [``:Cpat``]
  val ttac = SOME (
    WF_REL_TAC `measure Cpat_size` >>
    gen_tac >> Induct >>
    rw[Cpat_size_def] >>
    res_tac >> DECIDE_TAC )
in mk_count_aux_inj_rwt_ttac tys ttac end
val [count_Cprim2_aux_inj_rwt] = mk_count_aux_inj_rwt [``:Cprim2``]
val [count_Clprim_aux_inj_rwt] = mk_count_aux_inj_rwt [``:Clprim``]
val [count_Cexp_aux_inj_rwt, count_Cv_aux_inj_rwt] = let
  val tys = [``:Cexp``,``:Cv``]
  val ttac = SOME (
    WF_REL_TAC `inv_image $< (λx. case x of INL v => Cv_size v | INR e => Cexp_size e)` >>
    srw_tac[ARITH_ss][Cexp1_size_thm,Cexp3_size_thm,Cexp5_size_thm,Cexp7_size_thm,Cexp8_size_thm] >>
    map_every (fn q => TRY (Q.ISPEC_THEN q IMP_RES_TAC listTheory.SUM_MAP_MEM_bound)) [`Cexp2_size`,`Cexp_size`,`Cexp4_size`,`Cv_size`,`Cexp6_size`] >>
    fsrw_tac[ARITH_ss][Cexp_size_def] )
in mk_count_aux_inj_rwt_ttac tys ttac end

val countable_v = save_thm("countable_v",inj_rwt_to_countable count_v_aux_inj_rwt)
val countable_Cv = save_thm("countable_Cv",inj_rwt_to_countable count_Cv_aux_inj_rwt)

val _ = export_theory()
