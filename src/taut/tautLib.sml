(*****************************************************************************)
(* FILE          : tautLib.sml                                               *)
(* DESCRIPTION   : Tautology checking by Boolean case analysis.              *)
(*                                                                           *)
(*                 Method suggested by Tom Melham.                           *)
(*                                                                           *)
(*                 Simplification done after each variable instantiation.    *)
(*                                                                           *)
(*                 Optimised for terms with more than two variables by       *)
(*                 eliminating some duplicated sub-calls.                    *)
(*                                                                           *)
(*                 Optimised for cases when the body simplifies to true or   *)
(*                 false before all the variables have been analysed.        *)
(*                                                                           *)
(*                 Simplification optimised to avoid rebuilding subterms that*)
(*                 are not changed.                                          *)
(*                                                                           *)
(*                 Experiments have been performed with special code for     *)
(*                 cases when the first argument of AND, OR, IMP and COND    *)
(*                 simplifies to a value that makes simplification of certain*)
(*                 other arguments unnecessary. The results suggested that in*)
(*                 general slightly fewer intermediate theorems are          *)
(*                 generated, but that due to the overhead of testing, the   *)
(*                 execution times are slightly longer.                      *)
(*                                                                           *)
(* READS FILES   : <none>                                                    *)
(* WRITES FILES  : <none>                                                    *)
(*                                                                           *)
(* AUTHOR        : R.J.Boulton, University of Cambridge                      *)
(* DATE          : 9th July 1991                                             *)
(*                                                                           *)
(* LAST MODIFIED : R.J.Boulton                                               *)
(* DATE          : 24th September 1991                                       *)
(* TRANSLATOR    : Konrad Slind, University of Calgary                       *)
(*****************************************************************************)

structure tautLib :> tautLib =
struct

open HolKernel Parse boolLib Abbrev QConv Rsyntax;

infix THEN THENL THENC ## |->;

val ERR = mk_HOL_ERR "tautLib"

val BOOL_CASES_AX = boolTheory.BOOL_CASES_AX;


(*===========================================================================*)
(* Discriminator functions for T (true) and F (false)                        *)
(*===========================================================================*)

fun is_T tm = (tm = T)
and is_F tm = (tm = F);


(*===========================================================================*)
(* Theorems used for Boolean case analysis                                   *)
(*===========================================================================*)

local open Tactical Rewrite
in 
val CASES_THM = prove
(Term`!(b:bool) f. (f b = F) ==> ((!x. f x) = F)`,
 GEN_TAC THEN BOOL_CASES_TAC (Term`b:bool`)
   THEN REPEAT STRIP_TAC
   THEN REWRITE_TAC [] 
   THEN CONV_TAC NOT_FORALL_CONV
   THENL [EXISTS_TAC T, EXISTS_TAC F]
   THEN ASM_REWRITE_TAC[])
end;

(*---------------------------------------------------------------------------*)
(* BOOL_CASES_T_F = |- !f. (f T = F) ==> ((!x. f x) = F)                     *)
(* BOOL_CASES_F_F = |- !f. (f F = F) ==> ((!x. f x) = F)                     *)
(*---------------------------------------------------------------------------*)

val BOOL_CASES_T_F = SPEC T CASES_THM
val BOOL_CASES_F_F = SPEC F CASES_THM

(*===========================================================================*)
(* Conversions for doing Boolean case analysis                               *)
(*===========================================================================*)

(*---------------------------------------------------------------------------*)
(* BOOL_CASES_BOTH_T_RULE : (thm # thm) -> conv                              *)
(*                                                                           *)
(* BOOL_CASES_BOTH_T_RULE (|- f[T] = T, |- f[F] = T) `!x. f[x]` returns the  *)
(* theorem |- (!x. f[x]) = T.                                                *)
(*---------------------------------------------------------------------------*)

fun BOOL_CASES_BOTH_T_RULE (thT,thF) tm =
  let val {Bvar,Body} = dest_forall tm
      val cases_thm = SPEC Bvar BOOL_CASES_AX
      val thT' = TRANS(SUBST_CONV
                        [Bvar |-> ASSUME(mk_eq{lhs=Bvar,rhs=T})] Body Body) thT
      and thF' = TRANS(SUBST_CONV
                        [Bvar |-> ASSUME(mk_eq{lhs=Bvar,rhs=F})] Body Body) thF
      val th = DISJ_CASES cases_thm thT' thF'
  in (EQT_INTRO o GEN Bvar o EQT_ELIM) th
  end 
  handle HOL_ERR _ => raise ERR "BOOL_CASES_BOTH_T_RULE" "";

(*---------------------------------------------------------------------------*)
(* BOOL_CASES_T_F_RULE : thm -> conv                                         *)
(*                                                                           *)
(* BOOL_CASES_T_F_RULE (|- f[T] = F) `!x. f[x]` returns the theorem          *)
(* |- (!x. f[x]) = F.                                                        *)
(*---------------------------------------------------------------------------*)

val ball = inst [alpha |-> bool] universal;

fun BOOL_CASES_T_F_RULE thT tm =
  let val (t as {Bvar,Body}) = dest_forall tm
      val f = mk_abs t
      val thT' = TRANS (BETA_CONV (mk_comb{Rator=f,Rand=T})) thT
      and th = AP_TERM ball (ABS Bvar(BETA_CONV(mk_comb{Rator=f,Rand=Bvar})))
      val th1 = SPEC f BOOL_CASES_T_F
      val th2 = MP th1 thT'
  in TRANS (SYM th) th2
  end 
  handle HOL_ERR _ => raise ERR "BOOL_CASES_T_F_RULE" "";

(*---------------------------------------------------------------------------*)
(* BOOL_CASES_F_F_RULE : thm -> conv                                         *)
(*                                                                           *)
(* BOOL_CASES_F_F_RULE (|- f[F] = F) `!x. f[x]` returns the theorem          *)
(* |- (!x. f[x]) = F.                                                        *)
(*---------------------------------------------------------------------------*)

fun BOOL_CASES_F_F_RULE thF tm =
   let val (t as {Bvar,Body}) = dest_forall tm
       val f = mk_abs t
       val thF' = TRANS (BETA_CONV (mk_comb{Rator=f,Rand=F})) thF
       and th = AP_TERM ball (ABS Bvar(BETA_CONV(mk_comb{Rator=f,Rand=Bvar})))
       and th1 = SPEC f BOOL_CASES_F_F
       val th2 = MP th1 thF'
   in TRANS (SYM th) th2
   end 
   handle HOL_ERR _ => raise ERR "BOOL_CASES_F_F_RULE" ""


(*---------------------------------------------------------------------------*)
(* RAND_QCONV : conv -> conv                                                 *)
(* RATOR_QCONV : conv -> conv                                                *)
(* ABS_QCONV : conv -> conv                                                  *)
(*                                                                           *)
(* Sleeker versions of Conv.{RAND,RATOR,ABS}_CONV. All failures propagate.   *)
(*---------------------------------------------------------------------------*)

fun RAND_QCONV conv tm =
 let val {Rator,Rand} = dest_comb tm in AP_TERM Rator (conv Rand) end;

fun RATOR_QCONV conv tm =
 let val {Rator,Rand} = dest_comb tm in AP_THM (conv Rator) Rand end;

fun ABS_QCONV conv tm =
 let val {Bvar,Body} = dest_abs tm in ABS Bvar (conv Body) end;

(*===========================================================================*)
(* Theorems used for simplifying Boolean terms                               *)
(*===========================================================================*)

(*---------------------------------------------------------------------------*)
(* T_REFL = |- T = T                                                         *)
(* F_REFL = |- F = F                                                         *)
(*---------------------------------------------------------------------------*)

val T_REFL = REFL T
and F_REFL = REFL F;

(*===========================================================================*)
(* Conversions used for simplifying Boolean terms                            *)
(*===========================================================================*)

(*---------------------------------------------------------------------------*)
(* NOT_CONV : conv                                                           *)
(*                                                                           *)
(*    |- !t. ~~t = t                                                         *)
(*    |- ~T = F                                                              *)
(*    |- ~F = T                                                              *)
(*---------------------------------------------------------------------------*)

local val [th1,th2,th3] = CONJUNCTS NOT_CLAUSES
in
fun NOT_CONV tm =
   let val arg = dest_neg tm
   in if is_T arg then th2 else 
      if is_F arg then th3
      else SPEC (dest_neg arg) th1
   end handle HOL_ERR _ => raise ERR "NOT_CONV" ""
end;

(*---------------------------------------------------------------------------*)
(* EQ_CONV : conv                                                            *)
(*                                                                           *)
(*    |- (t = t) = T                                                         *)
(*    |- (T = t) = t                                                         *)
(*    |- (t = T) = t                                                         *)
(*    |- (F = t) = ~t                                                        *)
(*    |- (t = F) = ~t                                                        *)
(*---------------------------------------------------------------------------*)

local val th1 = INST_TYPE [alpha |-> bool] REFL_CLAUSE
      val [th2,th3,th4,th5] = map GEN_ALL (CONJUNCTS (SPEC_ALL EQ_CLAUSES))
in
fun EQ_CONV tm =
  let val {lhs,rhs} = dest_eq tm
  in if is_T lhs then SPEC rhs th2 else 
     if is_T rhs then SPEC lhs th3 else 
     if is_F lhs then SPEC rhs th4 else 
     if is_F rhs then SPEC lhs th5 else 
     if lhs=rhs then SPEC lhs th1 
     else raise ERR "EQ_CONV" ""
  end 
end;

(*---------------------------------------------------------------------------*)
(* EQ_THEN_NOT_CONV : conv                                                   *)
(*                                                                           *)
(* Behaves as for EQ_CONV, then if EQ_CONV generated a top level negation, it*)
(* tries to apply NOT_CONV.                                                  *)
(*---------------------------------------------------------------------------*)

fun EQ_THEN_NOT_CONV tm =
   if is_F (rand (rator tm)) orelse is_F (rand tm)
   then (EQ_CONV THENC (TRY_CONV NOT_CONV)) tm
   else EQ_CONV tm;

(*---------------------------------------------------------------------------*)
(* AND_CONV : conv                                                           *)
(*                                                                           *)
(*    |- T /\ t = t                                                          *)
(*    |- t /\ T = t                                                          *)
(*    |- F /\ t = F                                                          *)
(*    |- t /\ F = F                                                          *)
(*    |- t /\ t = t                                                          *)
(*---------------------------------------------------------------------------*)

local val [th1,th2,th3,th4,th5] = map GEN_ALL (CONJUNCTS (SPEC_ALL AND_CLAUSES))
in
fun AND_CONV tm =
  let val {conj1,conj2} = dest_conj tm
  in if is_T conj1 then SPEC conj2 th1 else 
     if is_T conj2 then SPEC conj1 th2 else 
     if is_F conj1 then SPEC conj2 th3 else 
     if is_F conj2 then SPEC conj1 th4 else 
     if conj1=conj2 then SPEC conj1 th5
     else raise ERR "AND_CONV" ""
  end
end;

(*---------------------------------------------------------------------------*)
(* OR_CONV : conv                                                            *)
(*                                                                           *)
(*    |- T \/ t = T                                                          *)
(*    |- t \/ T = T                                                          *)
(*    |- F \/ t = t                                                          *)
(*    |- t \/ F = t                                                          *)
(*    |- t \/ t = t                                                          *)
(*---------------------------------------------------------------------------*)

local val [th1,th2,th3,th4,th5] = map GEN_ALL (CONJUNCTS (SPEC_ALL OR_CLAUSES))
in 
fun OR_CONV tm =
  let val {disj1,disj2} = dest_disj tm
  in if is_T disj1 then SPEC disj2 th1 else 
     if is_T disj2 then SPEC disj1 th2 else 
     if is_F disj1 then SPEC disj2 th3 else 
     if is_F disj2 then SPEC disj1 th4 else 
     if disj1=disj2 then SPEC disj1 th5
     else raise ERR "OR_CONV" ""
  end
end;

(*---------------------------------------------------------------------------*)
(* IMP_CONV : conv                                                           *)
(*                                                                           *)
(*    |- T ==> t = t                                                         *)
(*    |- t ==> T = T                                                         *)
(*    |- F ==> t = T                                                         *)
(*    |- t ==> t = T                                                         *)
(*    |- t ==> F = ~t                                                        *)
(*---------------------------------------------------------------------------*)

local val [th1,th2,th3,th4,th5] = map GEN_ALL(CONJUNCTS(SPEC_ALL IMP_CLAUSES))
in 
fun IMP_CONV tm =
  let val {ant,conseq} = dest_imp tm
  in if is_neg tm   then raise ERR "IMP_CONV" "" else 
     if is_T ant    then SPEC conseq th1 else 
     if is_T conseq then SPEC ant th2 else 
     if is_F ant    then SPEC conseq th3 else 
     if is_F conseq then SPEC ant th5 else 
     if ant=conseq  then SPEC ant th4 else 
     raise ERR "IMP_CONV" ""
   end
end;

(*---------------------------------------------------------------------------*)
(* IMP_THEN_NOT_CONV : conv                                                  *)
(*                                                                           *)
(* Behaves as for IMP_CONV, then if IMP_CONV generated a top level negation, *)
(* it tries to apply NOT_CONV.                                               *)
(*---------------------------------------------------------------------------*)

fun IMP_THEN_NOT_CONV tm =
   if is_F (rand tm)
   then (IMP_CONV THENC (TRY_CONV NOT_CONV)) tm
   else IMP_CONV tm;

(*---------------------------------------------------------------------------*)
(* IF_CONV : conv                                                            *)
(*                                                                           *)
(*    |- (T => t1 | t2) = t1                                                 *)
(*    |- (F => t1 | t2) = t2                                                 *)
(*---------------------------------------------------------------------------*)

local val theta = [alpha |-> bool]
      val t1 = mk_var{Name="t1",Ty=bool}
      val t2 = mk_var{Name="t2",Ty=bool}
      val [th1,th2] = map (GENL [t1, t2])
                          (CONJUNCTS (SPEC_ALL (INST_TYPE theta COND_CLAUSES)))
in
fun IF_CONV tm =
  let val {cond,larm,rarm} = dest_cond tm
  in if is_T cond then SPECL [larm,rarm] th1 else 
     if is_F cond then SPECL [larm,rarm] th2 else 
     raise ERR "IF_CONV" ""
  end
end;

(*---------------------------------------------------------------------------*)
(* SIMP_PROP_QCONV : conv                                                    *)
(*                                                                           *)
(* Conversion for simplifying propositional terms containing constants,      *)
(* variables, equality, implication, AND, OR, NOT and conditionals.          *)
(* Uses failure to avoid rebuilding unchanged subterms.                      *)
(*---------------------------------------------------------------------------*)

fun SIMP_PROP_QCONV tm =
 let fun ARGS_QCONV tm =
      let val (opp,[arg1,arg2]) = strip_comb tm
      in let val th1 = SIMP_PROP_QCONV arg1
             val th = AP_TERM opp th1
         in MK_COMB (th,SIMP_PROP_QCONV arg2)
            handle UNCHANGED => AP_THM th arg2
         end handle UNCHANGED 
         => let val th2 = SIMP_PROP_QCONV arg2
            in AP_TERM (rator tm) th2
            end
      end
 in
 if is_const tm orelse is_var tm then ALL_QCONV tm else 
 if is_neg tm  then THENQC (RAND_QCONV SIMP_PROP_QCONV) 
                           (TRY_QCONV NOT_CONV) tm else 
 if is_eq tm   then THENQC ARGS_QCONV (TRY_QCONV EQ_THEN_NOT_CONV) tm else 
 if is_conj tm then THENQC ARGS_QCONV (TRY_QCONV AND_CONV) tm else 
 if is_disj tm then THENQC ARGS_QCONV (TRY_QCONV OR_CONV) tm else 
 if is_imp tm  then THENQC ARGS_QCONV (TRY_QCONV IMP_THEN_NOT_CONV) tm else
 if is_cond tm
    then THENQC (THENQC (RATOR_QCONV (THENQC 
            (RATOR_QCONV (RAND_QCONV SIMP_PROP_QCONV))
            (RAND_QCONV SIMP_PROP_QCONV))) (RAND_QCONV SIMP_PROP_QCONV))
          (TRY_QCONV IF_CONV) tm 
 else raise ERR "SIMP_PROP_QCONV" ""
 end;

(*===========================================================================*)
(* Tautology checking                                                        *)
(*===========================================================================*)

(*---------------------------------------------------------------------------*)
(* DEPTH_FORALL_QCONV : conv -> conv                                         *)
(*                                                                           *)
(* Auxiliary function for applying a conversion inside universal             *)
(* quantifications.                                                          *)
(* Uses failure to avoid rebuilding unchanged subterms.                      *)
(*---------------------------------------------------------------------------*)

fun DEPTH_FORALL_QCONV conv tm =
  if is_forall tm
   then RAND_QCONV (ABS_QCONV (DEPTH_FORALL_QCONV conv)) tm
   else conv tm;

(*---------------------------------------------------------------------------*)
(* FORALL_T : term list -> thm                                               *)
(*                                                                           *)
(* Given a list of variables [`x1`;...;`xn`] (allowed to be empty), this     *)
(* function returns the theorem |- (!x1 ... xn. T) = T.                      *)
(*---------------------------------------------------------------------------*)

fun FORALL_T [] = T_REFL
  | FORALL_T vars = 
     EQT_INTRO (GENL vars TRUTH) handle HOL_ERR _ => raise ERR "FORALL_T" ""

(*---------------------------------------------------------------------------*)
(* FORALL_F : term list -> thm                                               *)
(*                                                                           *)
(* Given a list of variables [`x1`;...;`xn`] (allowed to be empty), this     *)
(* function returns the theorem |- (!x1 ... xn. F) = F.                      *)
(*---------------------------------------------------------------------------*)

local val forall_simp = SPEC F (INST_TYPE [alpha |-> bool] FORALL_SIMP)
in
fun FORALL_F [] = F_REFL
  | FORALL_F (h::t) = 
     TRANS (FORALL_EQ h (FORALL_F t)) forall_simp 
     handle HOL_ERR _ => raise ERR "FORALL_F" ""
end;

(*---------------------------------------------------------------------------*)
(* TAUT_CHECK_CONV : conv                                                    *)
(*                                                                           *)
(* Given a propositional term with all variables universally quantified,     *)
(* e.g. `!x1 ... xn. f[x1,...,xn]`, this conversion proves the term to be    *)
(* either true or false, i.e. it returns one of:                             *)
(*                                                                           *)
(*    |- (!x1 ... xn. f[x1,...,xn]) = T                                      *)
(*    |- (!x1 ... xn. f[x1,...,xn]) = F                                      *)
(*---------------------------------------------------------------------------*)

fun TAUT_CHECK_CONV tm =
 let val (vars,tm') = strip_forall tm
 in if (is_T tm') then FORALL_T vars else 
    if (is_F tm') then FORALL_F vars 
    else 
    let val {Bvar,Body} = dest_forall tm
        val tmT = subst [Bvar |-> T] Body
        val thT1 = QCONV (DEPTH_FORALL_QCONV SIMP_PROP_QCONV) tmT
        val tmT' = rhs (concl thT1)
        val thT2 = TAUT_CHECK_CONV tmT'
        val thT3 = TRANS thT1 thT2
    in if is_F (rhs (concl thT3))
       then BOOL_CASES_T_F_RULE thT3 tm
       else let val tmF = subst [Bvar |-> F] Body
                val thF1 = QCONV (DEPTH_FORALL_QCONV SIMP_PROP_QCONV) tmF
                val tmF' = rhs (concl thF1)
                val thF2 = if tmF' = tmT' then thT2 else TAUT_CHECK_CONV tmF'
                val thF3 = TRANS thF1 thF2
            in if is_F (rhs (concl thF3))
               then BOOL_CASES_F_F_RULE thF3 tm
               else BOOL_CASES_BOTH_T_RULE (thT3,thF3) tm
            end
    end
 end 
 handle HOL_ERR _ => raise ERR "TAUT_CHECK_CONV" "";

(*---------------------------------------------------------------------------*)
(* PTAUT_CONV :conv                                                          *)
(*                                                                           *)
(* Given a propositional term with all variables universally quantified,     *)
(* e.g. `!x1 ... xn. f[x1,...,xn]`, this conversion proves the term to be    *)
(* either true or false, i.e. it returns one of:                             *)
(*                                                                           *)
(*    |- (!x1 ... xn. f[x1,...,xn]) = T                                      *)
(*    |- (!x1 ... xn. f[x1,...,xn]) = F                                      *)
(*                                                                           *)
(* This conversion tries to simplify before calling TAUT_CHECK_CONV. It also *)
(* accepts propositional terms that are not fully universally quantified.    *)
(* However, for such a term, the conversion will fail if it is not true.     *)
(* Consider the term `!x2 ... xn. f[x1,...,xn]`. TAUT_CHECK_CONV proves      *)
(* one of:                                                                   *)
(*                                                                           *)
(*    |- (!x1 ... xn. f[x1,...,xn]) = T                                      *)
(*    |- (!x1 ... xn. f[x1,...,xn]) = F                                      *)
(*                                                                           *)
(* The former can be manipulated as follows:                                 *)
(*                                                                           *)
(*    |- (!x1 ... xn. f[x1,...,xn]) = T                                      *)
(*    |- !x1 ... xn. f[x1,...,xn]                                            *)
(*    |- !x2 ... xn. f[x1,...,xn]                                            *)
(*    |- (!x2 ... xn. f[x1,...,xn]) = T                                      *)
(*                                                                           *)
(* However when the fully quantified term is false, we have:                 *)
(*                                                                           *)
(*    |- (!x1 ... xn. f[x1,...,xn]) = F                                      *)
(*    |- ~(!x1 ... xn. f[x1,...,xn])                                         *)
(*    |- ?x1. ~(!x2 ... xn. f[x1,...,xn])                                    *)
(*    |- ?x1. ((!x2 ... xn. f[x1,...,xn]) = F)                               *)
(*                                                                           *)
(* whereas we want:                                                          *)
(*                                                                           *)
(*    |- !x1. ((!x2 ... xn. f[x1,...,xn]) = F)                               *)
(*                                                                           *)
(* i.e.                                                                      *)
(*                                                                           *)
(*    |- (!x2 ... xn. f[x1,...,xn]) = F                                      *)
(*                                                                           *)
(* The conversions given here are not capable of proving the latter theorem  *)
(* since it is not purely propositional.                                     *)
(*---------------------------------------------------------------------------*)

fun PTAUT_CONV tm =
 let val vars = free_vars tm
     val th = 
       (QCONV (DEPTH_FORALL_QCONV SIMP_PROP_QCONV) THENC TAUT_CHECK_CONV) 
       (list_mk_forall (vars,tm))
 in if null vars then th else 
    if is_F (rhs (concl th))
    then raise ERR "PTAUT_CONV" "false for at least one interpretation"
    else (EQT_INTRO o (SPECL vars) o EQT_ELIM) th
 end

(*---------------------------------------------------------------------------*)
(* PTAUT_TAC : tactic                                                        *)
(*                                                                           *)
(* Tactic for solving propositional terms.                                   *)
(*---------------------------------------------------------------------------*)

val PTAUT_TAC = CONV_TAC PTAUT_CONV;

(*---------------------------------------------------------------------------*)
(* PTAUT_PROVE : conv                                                        *)
(*                                                                           *)
(* Given a propositional term `t`, this conversion returns the theorem |- t  *)
(* if `t` is a tautology. Otherwise it fails.                                *)
(*---------------------------------------------------------------------------*)

fun PTAUT_PROVE tm = 
   EQT_ELIM (PTAUT_CONV tm) 
   handle e => raise (wrap_exn "tautLib" "PTAUT_PROVE" e);

(*===========================================================================*)
(* Tautology checking including instances of propositional tautologies       *)
(*===========================================================================*)

(*---------------------------------------------------------------------------*)
(* non_prop_terms : term -> term list                                        *)
(*                                                                           *)
(* Computes a list of subterms of a term that are either variables or Boolean*)
(* valued non-propositional terms. The result list may contain duplicates.   *)
(*---------------------------------------------------------------------------*)

fun non_prop_terms tm =
 let fun non_prop_args tm =
      let val (opp,args) = ((#Name o dest_const) ## I) (strip_comb tm)
      in if (mem opp ["T","F","~","=","/\\","\\/","==>","COND"])
         then flatten (map non_prop_terms args)
         else raise ERR "" ""
      end
 in non_prop_args tm handle HOL_ERR _ 
     => if type_of tm = bool then [tm]
        else raise ERR "non_prop_terms" ""
 end;

(*---------------------------------------------------------------------------*)
(* TAUT_CONV : conv                                                          *)
(*                                                                           *)
(* Given a term, `t`, that is a valid propositional formula or valid instance*)
(* of a propositional formula, this conversion returns the theorem |- t = T. *)
(* The variables in `t` do not have to be universally quantified.            *)
(*                                                                           *)
(* Example:                                                                  *)
(*                                                                           *)
(*    TAUT_CONV `!x n y z. x \/ ~(n < 0) \/ y \/ z \/ (n < 0)`  --->         *)
(*    |- (!x n y z. x \/ ~n < 0 \/ y \/ z \/ n < 0) = T                      *)
(*---------------------------------------------------------------------------*)

fun TAUT_CONV tm =
  let val (univs,tm') = strip_forall tm
      val insts = mk_set (non_prop_terms tm')
      val vars = map (genvar o type_of) insts
      val theta = map2 (curry (op |->)) insts vars
      val tm'' = list_mk_forall (vars,subst theta tm')
  in EQT_INTRO (GENL univs (SPECL insts (PTAUT_PROVE tm'')))
  end
  handle e => raise (wrap_exn "tautLib" "TAUT_CONV" e);

(*---------------------------------------------------------------------------*)
(* TAUT_TAC : tactic                                                         *)
(*                                                                           *)
(* Tactic for solving propositional formulae and instances of propositional  *)
(* formulae.                                                                 *)
(*---------------------------------------------------------------------------*)

val TAUT_TAC = CONV_TAC TAUT_CONV;

(*---------------------------------------------------------------------------*)
(* ASM_TAUT_TAC : tacti                                                      *)
(*                                                                           *)
(* Same as TAUT_TAC, except that it takes account of the assumptions of the  *)
(* goal.                                                                     *)
(*---------------------------------------------------------------------------*)

val ASM_TAUT_TAC = REPEAT (POP_ASSUM MP_TAC) THEN TAUT_TAC

(*---------------------------------------------------------------------------*)
(* TAUT_PROVE : conv                                                         *)
(*                                                                           *)
(* Given a valid propositional formula, or a valid instance of a             *)
(* propositional formula, `t`, this conversion returns the theorem |- t.     *)
(*---------------------------------------------------------------------------*)

fun TAUT_PROVE tm = 
 EQT_ELIM (TAUT_CONV tm) handle HOL_ERR _ => raise ERR "TAUT_PROVE" "";

fun TAUT q = TAUT_PROVE (Parse.Term q);

end; (* tautLib *)
