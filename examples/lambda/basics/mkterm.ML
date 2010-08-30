val vp = ``(λn u:unit. n = 0)``
val lp = ``(λn (d:unit + unit) tns uns.
               (n = 0) ∧ ISL d ∧ (tns = [0]) ∧ (uns = []) ∨
               (n = 0) ∧ ISR d ∧ (tns = []) ∧ (uns = [0;0]))``

val termP = ``genind  ^vp ^lp 0``

val LIST_REL_NIL1 = prove(
  ``LIST_REL R [] x ⇔ (x = [])``,
  Cases_on `x` >> srw_tac [][]);
val LIST_REL_CONS1 = prove(
  ``LIST_REL R (h::t) xs ⇔ ∃h' t'. (xs = h'::t') ∧ R h h' ∧ LIST_REL R t t'``,
  Cases_on `xs` >> srw_tac [][]);

val FORALL_ONE = prove(
  ``(∀x:unit. P x) ⇔ P ()``,
  srw_tac [][EQ_IMP_THM, oneTheory.one_induction]);


val term_exists = prove(
  ``∃x. ^termP x``,
  Q.EXISTS_TAC `GVAR s ()` >> srw_tac [][genind_rules]);

val term_bij_ax = new_type_definition("term", term_exists)
val term_ABSREP =
    define_new_type_bijections { ABS = "term_ABS", REP = "term_REP",
                                 name = "term_ABSREP", tyax = term_bij_ax}

val term_ABS_pseudo11 = prove(
  ``^termP x ∧ ^termP y ⇒ ((term_ABS x = term_ABS y) ⇔ (x = y))``,
  srw_tac [][EQ_IMP_THM] >> pop_assum (MP_TAC o Q.AP_TERM `term_REP`) >>
  metis_tac [term_ABSREP]);

val genind_exists = prove(
  ``^termP g ⇔ ∃t. (g = term_REP t)``,
  metis_tac [term_ABSREP]);

val genind_term_REP = prove(
  ``^termP (term_REP t)``,
  metis_tac [term_ABSREP]);


val LAM_def = new_definition(
  "LAM_def",
  ``LAM v t = term_ABS (GLAM v (INL ()) [term_REP t] [])``)

val LAM_termP = prove(
  ``^termP (GLAM v (INL ()) [term_REP t] [])``,
  match_mp_tac (hd (tl grules')) >> srw_tac [][genind_term_REP]);

val APP_def = new_definition(
  "APP_def",
  ``APP t1 t2 = term_ABS (GLAM ARB (INR ()) [] [term_REP t1; term_REP t2])``);

val APP_termP = prove(
  ``^termP (GLAM x (INR ()) [] [term_REP t1; term_REP t2])``,
  match_mp_tac (hd (tl grules')) >> srw_tac [][genind_term_REP])

val APP_def' = prove(
  ``term_ABS (GLAM v (INR ()) [] [term_REP t1; term_REP t2]) = APP t1 t2``,
  srw_tac [][APP_def, GLAM_NIL_EQ, term_ABS_pseudo11, APP_termP]);

val VAR_def = new_definition(
  "VAR_def",
  ``VAR s = term_ABS (GVAR s ())``);

val VAR_termP = prove(
  ``^termP (GVAR s ())``,
  srw_tac [][genind_rules]);

val tpm_def = new_definition(
  "tpm_def",
  ``tpm pi t = term_ABS (gtpm pi (term_REP t))``);

val repabs_id = term_ABSREP |> CONJUNCT2 |> SPEC_ALL |> (#1 o EQ_IMP_RULE)
                            |> GEN_ALL

(* not sure if defining this is a good idea; perhaps just show the necessary
   properties of supp tpm *)
val FV_def = new_definition(
  "FV_def",
  ``FV t = supp gtpm (term_REP t)``);

val FV_var =
    FV_def |> Q.SPEC `VAR s`
           |> CONV_RULE
               (RAND_CONV (SIMP_CONV (srw_ss()) [VAR_def, repabs_id,
                                                 VAR_termP, GFV_thm,
                                                 GFV_supp]))
val FV_app =
    FV_def |> Q.SPEC `APP t1 t2`
           |> CONV_RULE
               (RAND_CONV (SIMP_CONV (srw_ss()) [APP_def, repabs_id,
                                                 APP_termP, GFV_thm,
                                                 GFV_supp]))
           |> SIMP_RULE (srw_ss()) [GSYM GFV_supp, GSYM FV_def]

val FV_lam =
    FV_def |> Q.SPEC `LAM v t`
           |> CONV_RULE
               (RAND_CONV (SIMP_CONV (srw_ss()) [LAM_def, repabs_id,
                                                 LAM_termP, GFV_thm,
                                                 GFV_supp]))
           |> SIMP_RULE (srw_ss()) [GSYM GFV_supp, GSYM FV_def]

val term_ind =
    bvc_genind |> INST_TYPE [alpha |-> ``:unit+unit``, beta |-> ``:unit``]
               |> Q.INST [`vp` |-> `^vp`, `lp` |-> `^lp`]
               |> SIMP_RULE (std_ss ++ DNF_ss) [LIST_REL_NIL1, LIST_REL_CONS1]
               |> Q.SPEC `λn t x. Q t x`
               |> Q.SPEC `fv` |> Q.SPEC `0`
               |> SIMP_RULE (std_ss ++ DNF_ss)
                            [sumTheory.FORALL_SUM, supp_listpm,
                             IN_UNION, NOT_IN_EMPTY, FORALL_ONE,
                             genind_exists]
               |> Q.INST [`Q` |-> `λt. P (term_ABS t)`]
               |> SIMP_RULE std_ss [GSYM LAM_def, APP_def', GSYM VAR_def,
                                    CONJUNCT1 term_ABSREP]

val term_ind
