structure pflLib =
struct

val ERR = mk_HOL_ERR "pflLib";

val MAX_LE_THM = Q.prove
(`!m n. m <= MAX m n /\ n <= MAX m n`,
 RW_TAC arith_ss [MAX_DEF]);

val IS_SOME_EXISTS = Q.prove
(`!x. IS_SOME x = ?y. x = SOME y`,
 Cases THEN METIS_TAC [optionTheory.IS_SOME_DEF]);

fun GOAL_REWRITE_TAC rws =
  RULE_ASSUM_TAC (REWRITE_RULE rws) THEN REWRITE_TAC rws;

(*---------------------------------------------------------------------------*)
(* Prove lemma of the form                                                   *)
(*                                                                           *)
(*  IS_SOME (ifn d args) ==> (ifn d args = ifn (SUC d) args)                 *)
(*                                                                           *)
(*---------------------------------------------------------------------------*)

fun DLEM_TAC ifn_def ifn_some_thm =
(Ho_Rewrite.REWRITE_TAC [IS_SOME_EXISTS,GSYM LEFT_FORALL_IMP_THM] THEN
 Induct THEN REPEAT GEN_TAC THENL
 [STRIP_TAC THEN IMP_RES_TAC ifn_some_thm THEN
   POP_ASSUM MP_TAC THEN REWRITE_TAC [],
  ONCE_REWRITE_TAC [ifn_def] THEN BasicProvers.EVERY_CASE_TAC THEN
  GOAL_REWRITE_TAC [SUC_SUB1,NOT_SOME_NONE, NOT_NONE_SOME, IS_SOME_DEF] THEN
  STRIP_TAC THEN RES_THEN MP_TAC THEN RW_TAC (srw_ss()) []])
 handle e => raise ERR "DLEM_TAC" "unable to prove stability lemma";

fun dest_args [] = raise ERR "dest_args" "not enough args in function application"
  | dest_args (d::t) = (d,t);

fun basic_lemmas ifn_def rdepth_thm =
 let open optionSyntax numSyntax
     val ifn_app = lhs(snd(strip_forall(concl ifn_def)))
     val (ifn,args) = strip_comb ifn_app
     val (d,args') = dest_args args
     val argfrees = free_varsl args
     val is_some_ifn_goal =
       list_mk_forall(args, mk_imp(mk_is_some ifn_app,
                                   mk_neg(mk_eq(d,zero_tm))))
     val is_some_ifn_thm =
       prove(is_some_ifn_goal, Cases THEN RW_TAC std_ss [Once ifn_def])
          handle e => raise ERR "is_some_ifn_thm" "tactic failed"
     val ty = dest_option (type_of ifn_app)
     val a = variant argfrees (mk_var("a",ty))
     val ifn_some_goal = list_mk_forall(args@[a],
                          mk_imp(mk_eq(ifn_app,mk_some a),
                                 mk_neg(mk_eq(d,zero_tm))))
     val ifn_some_thm = prove(ifn_some_goal, ACCEPT_TAC
          (Ho_Rewrite.PURE_REWRITE_RULE [IS_SOME_EXISTS,GSYM LEFT_FORALL_IMP_THM]
                                   is_some_ifn_thm))
          handle e => raise ERR "is_ifn_some_thm" "tactic failed"
     val ifn_dlem_goal = list_mk_forall(args,
                           mk_imp(mk_is_some ifn_app,
                                  mk_eq (ifn_app,list_mk_comb(ifn,mk_suc d::args'))))
     val ifn_dlem = prove(ifn_dlem_goal,DLEM_TAC ifn_def ifn_some_thm)
          handle e => raise ERR "ifn_dlem" "tactic failed"
     val d1 = variant argfrees (mk_var("d1",num))
     val ifn_mono_goal = list_mk_forall(d::d1::args',
                           mk_imp(mk_conj(mk_is_some ifn_app,mk_leq(d,d1)),
                                  mk_eq(ifn_app,list_mk_comb(ifn,d1::args'))))
     val ifn_mono_thm = prove(ifn_mono_goal,
           REWRITE_TAC [LESS_EQ_EXISTS] THEN REPEAT STRIP_TAC
            THEN BasicProvers.VAR_EQ_TAC
            THEN Induct_on `p` THEN REWRITE_TAC [ADD_CLAUSES]
            THEN POP_ASSUM SUBST_ALL_TAC
            THEN MATCH_MP_TAC ifn_dlem THEN ASM_REWRITE_TAC[])
          handle e => raise ERR "ifn_mono_thm" "tactic failed"
     val rdepth_tm = fst(strip_comb(fst(dest_leq(snd(dest_imp
                      (snd(dest_forall (snd(dest_conj(snd(dest_imp
                        (snd(strip_forall (concl rdepth_thm))))))))))))))
     val rdepth_app = list_mk_comb(rdepth_tm,args')
     val ifn_norm_goal = list_mk_forall(args,
                             mk_imp(mk_is_some ifn_app,
                                    mk_eq(ifn_app, list_mk_comb(ifn,rdepth_app::args'))))
     val ifn_norm_thm = prove(ifn_norm_goal,
                         REPEAT STRIP_TAC THEN IMP_RES_TAC rdepth_thm
                          THEN MATCH_MP_TAC (GSYM ifn_mono_thm)
                          THEN ASM_REWRITE_TAC [])
                handle e => raise ERR "ifn_norm_thm" "tactic failed"
     val ifn_determ_goal = list_mk_forall(d::d1::args',
                             mk_imp(mk_conj(mk_is_some(ifn_app),
                                            mk_is_some(list_mk_comb(ifn,d1::args'))),
                                    mk_eq(ifn_app,list_mk_comb(ifn,d1::args'))))
     val ifn_determ_thm = prove(ifn_determ_goal,
                           REPEAT STRIP_TAC THEN IMP_RES_TAC ifn_norm_thm
                             THEN ASM_REWRITE_TAC[])
                handle e => raise ERR "ifn_determ_thm" "tactic failed"
 in
   (is_some_ifn_thm, ifn_some_thm,ifn_dlem,ifn_mono_thm,ifn_norm_thm, ifn_determ_thm)
 end
 handle e => raise wrap_exn "basic_lemmas" "proof failed" e;


(*
val (is_some_ifn_thm, _, ifn_mono_thm,
     ifn_norm_thm, ifn_determ_thm) = basic_lemmas ifn_def rdepth_thm;
*)

end;
