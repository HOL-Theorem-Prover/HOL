(****************************************************************************)
(* FILE          : taut.sml                                                 *)
(* DESCRIPTION   : Tautology checking by Boolean case analysis.             *)
(*                                                                          *)
(*                 Method suggested by Tom Melham.                          *)
(*                                                                          *)
(*                 Simplification done after each variable instantiation.   *)
(*                                                                          *)
(*                 Optimised for terms with more than two variables by      *)
(*                 eliminating some duplicated sub-calls.                   *)
(*                                                                          *)
(*                 Optimised for cases when the body simplifies to true or  *)
(*                 false before all the variables have been analysed.       *)
(*                                                                          *)
(*                 Simplification optimised to avoid rebuilding subterms    *)
(*                 that are not changed.                                    *)
(*                                                                          *)
(*                 Experiments have been performed with special code for    *)
(*                 cases when the first argument of AND, OR, IMP and COND   *)
(*                 simplifies to a value that makes simplification of       *)
(*                 certain other arguments unnecessary. The results         *)
(*                 suggested that in general slightly fewer intermediate    *)
(*                 theorems are generated, but that due to the overhead of  *)
(*                 testing, the execution times are slightly longer.        *)
(*                                                                          *)
(* AUTHOR (HOL88): R.J.Boulton, University of Cambridge                     *)
(* DATE          : 9th July 1991                                            *)
(*                                                                          *)
(* TRANSLATOR    : Konrad Slind, University of Calgary                      *)
(*                                                                          *)
(* LAST MODIFIED : R.J.Boulton                                              *)
(* DATE          : 12th June 1995                                           *)
(****************************************************************************)

structure Taut :> Taut =
struct

open Exception;

fun TAUT_ERR{function,message} = HOL_ERR{origin_structure = "Taut",
                                         origin_function = function,
                                         message = message};

local
   open HolKernel Parse basicHol90Lib Psyntax DecisionConv DecisionSupport
infix THEN THENC |->
in

(*==========================================================================*)
(* HOL constants                                                            *)
(*==========================================================================*)

val all =  (--`$! :(bool -> bool) -> bool`--);

(*==========================================================================*)
(* Theorems used for Boolean case analysis                                  *)
(*==========================================================================*)

(*--------------------------------------------------------------------------*)
(* BOOL_CASES_T_F = |- !f. (f T = F) ==> ((!x. f x) = F)                    *)
(*--------------------------------------------------------------------------*)

val BOOL_CASES_T_F = prove
  (--`!f. (f T = F) ==> ((!x. f x) = F)`--,
   REPEAT STRIP_TAC THEN
   REWRITE_TAC [] THEN
   CONV_TAC NOT_FORALL_CONV THEN
   EXISTS_TAC T THEN
   ASM_REWRITE_TAC []);

(*--------------------------------------------------------------------------*)
(* BOOL_CASES_F_F = |- !f. (f F = F) ==> ((!x. f x) = F)                    *)
(*--------------------------------------------------------------------------*)

val BOOL_CASES_F_F = prove
  (--`!f. (f F = F) ==> ((!x. f x) = F)`--,
   REPEAT STRIP_TAC THEN
   REWRITE_TAC [] THEN
   CONV_TAC NOT_FORALL_CONV THEN
   EXISTS_TAC F THEN
   ASM_REWRITE_TAC []);

(*==========================================================================*)
(* Conversions for doing Boolean case analysis                              *)
(*==========================================================================*)

(*--------------------------------------------------------------------------*)
(* BOOL_CASES_BOTH_T_RULE : (thm * thm) -> conv                             *)
(*                                                                          *)
(* BOOL_CASES_BOTH_T_RULE (|- f[T] = T, |- f[F] = T) `!x. f[x]` returns the *)
(* theorem |- (!x. f[x]) = T.                                               *)
(*--------------------------------------------------------------------------*)

fun BOOL_CASES_BOTH_T_RULE (thT,thF) tm =
   let val (x,body) = dest_forall tm
       val cases_thm = SPEC x boolTheory.BOOL_CASES_AX
       val thT' = TRANS (SUBST_CONV [(ASSUME (mk_eq (x,T)),x)] body body) thT
       and thF' = TRANS (SUBST_CONV [(ASSUME (mk_eq (x,F)),x)] body body) thF
       val th = DISJ_CASES cases_thm thT' thF'
   in  (EQT_INTRO o GEN x o EQT_ELIM) th
   end
   handle HOL_ERR _ => raise TAUT_ERR{function = "BOOL_CASES_BOTH_T_RULE",
                              message = ""};

(*--------------------------------------------------------------------------*)
(* BOOL_CASES_T_F_RULE : thm -> conv                                        *)
(*                                                                          *)
(* BOOL_CASES_T_F_RULE (|- f[T] = F) `!x. f[x]` returns the theorem         *)
(* |- (!x. f[x]) = F.                                                       *)
(*--------------------------------------------------------------------------*)

fun BOOL_CASES_T_F_RULE thT tm =
   let val (x,body) = dest_forall tm
       val f = mk_abs (x,body)
       val thT' = TRANS (BETA_CONV (mk_comb (f,T))) thT
       and th = AP_TERM all (ABS x (BETA_CONV (mk_comb (f,x))))
       val th1 = SPEC f BOOL_CASES_T_F
       val th2 = MP th1 thT'
   in  TRANS (SYM th) th2
   end
   handle HOL_ERR _ => raise TAUT_ERR{function = "BOOL_CASES_T_F_RULE",message = ""};

(*--------------------------------------------------------------------------*)
(* BOOL_CASES_F_F_RULE : thm -> conv                                        *)
(*                                                                          *)
(* BOOL_CASES_F_F_RULE (|- f[F] = F) `!x. f[x]` returns the theorem         *)
(* |- (!x. f[x]) = F.                                                       *)
(*--------------------------------------------------------------------------*)

fun BOOL_CASES_F_F_RULE thF tm =
   let val (x,body) = dest_forall tm
       val f = mk_abs (x,body)
       val thF' = TRANS (BETA_CONV (mk_comb (f,F))) thF
       and th = AP_TERM all (ABS x (BETA_CONV (mk_comb (f,x))))
       and th1 = SPEC f BOOL_CASES_F_F
       val th2 = MP th1 thF'
   in  TRANS (SYM th) th2
   end
   handle HOL_ERR _ => raise TAUT_ERR{function = "BOOL_CASES_F_F_RULE",message = ""};

(*==========================================================================*)
(* Theorems used for simplifying Boolean terms                              *)
(*==========================================================================*)

(*--------------------------------------------------------------------------*)
(* T_REFL = |- T = T                                                        *)
(* F_REFL = |- F = F                                                        *)
(*--------------------------------------------------------------------------*)

val T_REFL = REFL T
and F_REFL = REFL F;

(*==========================================================================*)
(* Conversions used for simplifying Boolean terms                           *)
(*==========================================================================*)

(*--------------------------------------------------------------------------*)
(* NOT_CONV : conv                                                          *)
(*                                                                          *)
(*    |- !t. ~~t = t                                                        *)
(*    |- ~T = F                                                             *)
(*    |- ~F = T                                                             *)
(*--------------------------------------------------------------------------*)

local

val ths = CONJUNCTS NOT_CLAUSES;

in

fun NOT_CONV tm =
   let val arg = dest_neg tm
   in  if (is_T arg) 
       then el 2 ths
       else if (is_F arg) 
            then el 3 ths
            else SPEC (dest_neg arg) (el 1 ths)
   end
   handle HOL_ERR _ => raise TAUT_ERR{function = "NOT_CONV",message = ""};

end;

(*--------------------------------------------------------------------------*)
(* EQ_CONV : conv                                                           *)
(*                                                                          *)
(*    |- (t = t) = T                                                        *)
(*    |- (T = t) = t                                                        *)
(*    |- (t = T) = t                                                        *)
(*    |- (F = t) = ~t                                                       *)
(*    |- (t = F) = ~t                                                       *)
(*--------------------------------------------------------------------------*)

local

val th = Rsyntax.INST_TYPE [Type.alpha |-> Type.bool] REFL_CLAUSE
and ths = map GEN_ALL (CONJUNCTS (SPEC_ALL EQ_CLAUSES));

in

fun EQ_CONV tm =
   let val (lhs,rhs) = dest_eq tm
   in  if (is_T lhs) then SPEC rhs (el 1 ths)
       else if (is_T rhs) then SPEC lhs (el 2 ths)
       else if (is_F lhs) then SPEC rhs (el 3 ths)
       else if (is_F rhs) then SPEC lhs (el 4 ths)
       else if (lhs = rhs) then SPEC lhs th
       else raise TAUT_ERR{function = "EQ_CONV",message = ""}
   end
   handle HOL_ERR _ => raise TAUT_ERR{function = "EQ_CONV",message = ""};

end;

(*--------------------------------------------------------------------------*)
(* EQ_THEN_NOT_CONV : conv                                                  *)
(*                                                                          *)
(* Behaves as for EQ_CONV, then if EQ_CONV generated a top level negation,  *)
(* it tries to apply NOT_CONV.                                              *)
(*--------------------------------------------------------------------------*)

fun EQ_THEN_NOT_CONV tm =
   if (is_F (arg1 tm)) orelse (is_F (arg2 tm))
   then (EQ_CONV THENC (TRY_CONV NOT_CONV)) tm
   else EQ_CONV tm;

(*--------------------------------------------------------------------------*)
(* AND_CONV : conv                                                          *)
(*                                                                          *)
(*    |- T /\ t = t                                                         *)
(*    |- t /\ T = t                                                         *)
(*    |- F /\ t = F                                                         *)
(*    |- t /\ F = F                                                         *)
(*    |- t /\ t = t                                                         *)
(*--------------------------------------------------------------------------*)

local

val ths = map GEN_ALL (CONJUNCTS (SPEC_ALL AND_CLAUSES));

in

fun AND_CONV tm =
   let val (conj1,conj2) = dest_conj tm
   in  if (is_T conj1) then SPEC conj2 (el 1 ths)
       else if (is_T conj2) then SPEC conj1 (el 2 ths)
       else if (is_F conj1) then SPEC conj2 (el 3 ths)
       else if (is_F conj2) then SPEC conj1 (el 4 ths)
       else if (conj1 = conj2) then SPEC conj1 (el 5 ths)
       else raise TAUT_ERR{function = "AND_CONV",message = ""}
   end
   handle HOL_ERR _ => raise TAUT_ERR{function = "AND_CONV",message = ""};

end;

(*--------------------------------------------------------------------------*)
(* OR_CONV : conv                                                           *)
(*                                                                          *)
(*    |- T \/ t = T                                                         *)
(*    |- t \/ T = T                                                         *)
(*    |- F \/ t = t                                                         *)
(*    |- t \/ F = t                                                         *)
(*    |- t \/ t = t                                                         *)
(*--------------------------------------------------------------------------*)

local

val ths = map GEN_ALL (CONJUNCTS (SPEC_ALL OR_CLAUSES));

in 

fun OR_CONV tm =
   let val (disj1,disj2) = dest_disj tm
   in  if (is_T disj1) then SPEC disj2 (el 1 ths)
       else if (is_T disj2) then SPEC disj1 (el 2 ths)
       else if (is_F disj1) then SPEC disj2 (el 3 ths)
       else if (is_F disj2) then SPEC disj1 (el 4 ths)
       else if (disj1 = disj2) then SPEC disj1 (el 5 ths)
       else raise TAUT_ERR{function = "OR_CONV",message = ""}
   end
   handle HOL_ERR _ => raise TAUT_ERR{function = "OR_CONV",message = ""};

end;

(*--------------------------------------------------------------------------*)
(* IMP_CONV : conv                                                          *)
(*                                                                          *)
(*    |- T ==> t = t                                                        *)
(*    |- t ==> T = T                                                        *)
(*    |- F ==> t = T                                                        *)
(*    |- t ==> t = T                                                        *)
(*    |- t ==> F = ~t                                                       *)
(*--------------------------------------------------------------------------*)

local

val ths = map GEN_ALL (CONJUNCTS (SPEC_ALL IMP_CLAUSES));

in

fun IMP_CONV tm =
   let val (ant,conseq) = dest_imp tm
   in  if (is_neg tm) then raise TAUT_ERR{function = "IMP_CONV",message = ""}
       else if (is_T ant) then SPEC conseq (el 1 ths)
       else if (is_T conseq) then SPEC ant (el 2 ths)
       else if (is_F ant) then SPEC conseq (el 3 ths)
       else if (is_F conseq) then SPEC ant (el 5 ths)
       else if (ant = conseq) then SPEC ant (el 4 ths)
       else raise TAUT_ERR{function = "IMP_CONV",message = ""}
   end
   handle HOL_ERR _ => raise TAUT_ERR{function = "IMP_CONV",message = ""};

end;

(*--------------------------------------------------------------------------*)
(* IMP_THEN_NOT_CONV : conv                                                 *)
(*                                                                          *)
(* Behaves as for IMP_CONV, then if IMP_CONV generated a top level          *)
(* negation, it tries to apply NOT_CONV.                                    *)
(*--------------------------------------------------------------------------*)

fun IMP_THEN_NOT_CONV tm =
   if (is_F (arg2 tm))
   then (IMP_CONV THENC (TRY_CONV NOT_CONV)) tm
   else IMP_CONV tm;

(*--------------------------------------------------------------------------*)
(* IF_CONV : conv                                                           *)
(*                                                                          *)
(*    |- (T => t1 | t2) = t1                                                *)
(*    |- (F => t1 | t2) = t2                                                *)
(*--------------------------------------------------------------------------*)

local

val ths =
   map GEN_ALL
      (CONJUNCTS (SPEC_ALL 
         (Rsyntax.INST_TYPE [Type.alpha |-> Type.bool] COND_CLAUSES)));

in

fun IF_CONV tm =
   let val (cond,larm,rarm) = dest_cond tm
   in  if (is_T cond) then SPECL [larm,rarm] (el 1 ths)
       else if (is_F cond) then SPECL [larm,rarm] (el 2 ths)
       else raise TAUT_ERR{function = "IF_CONV",message = ""}
   end
   handle HOL_ERR _ => raise TAUT_ERR{function = "IF_CONV",message = ""};

end;

(*--------------------------------------------------------------------------*)
(* SIMP_PROP_CONV : conv                                                    *)
(*                                                                          *)
(* Conversion for simplifying propositional terms containing constants,     *)
(* variables, equality, implication, AND, OR, NOT and conditionals.         *)
(* Uses failure to avoid rebuilding unchanged subterms.                     *)
(*--------------------------------------------------------------------------*)

fun SIMP_PROP_CONV tm =
   if ((is_const tm) orelse (is_var tm)) then ALL_CONV tm
   else if (is_neg tm) then
      (RAND_CONV SIMP_PROP_CONV THENC TRY_CONV NOT_CONV) tm
   else if (is_eq tm) then
      (BINOP_CONV SIMP_PROP_CONV THENC TRY_CONV EQ_THEN_NOT_CONV) tm
   else if (is_conj tm) then
      (BINOP_CONV SIMP_PROP_CONV THENC TRY_CONV AND_CONV) tm
   else if (is_disj tm) then
      (BINOP_CONV SIMP_PROP_CONV THENC TRY_CONV OR_CONV) tm
   else if (is_imp tm) then
      (BINOP_CONV SIMP_PROP_CONV THENC TRY_CONV IMP_THEN_NOT_CONV) tm
   else if (is_cond tm) then
      (ARGS_CONV [SIMP_PROP_CONV,SIMP_PROP_CONV,SIMP_PROP_CONV] THENC
       TRY_CONV IF_CONV)
      tm
   else raise TAUT_ERR{function="SIMP_PROP_CONV",message = ""};

(*==========================================================================*)
(* Tautology checking                                                       *)
(*==========================================================================*)

(*--------------------------------------------------------------------------*)
(* FORALL_T : term list -> thm                                              *)
(*                                                                          *)
(* Given a list of variables [`x1`;...;`xn`] (allowed to be empty), this    *)
(* function returns the theorem |- (!x1 ... xn. T) = T.                     *)
(*--------------------------------------------------------------------------*)

fun FORALL_T [] = T_REFL
  | FORALL_T vars = EQT_INTRO (GENL vars TRUTH)
  handle HOL_ERR _ => raise TAUT_ERR{function = "FORALL_T", message = ""};

(*--------------------------------------------------------------------------*)
(* FORALL_F : term list -> thm                                              *)
(*                                                                          *)
(* Given a list of variables [`x1`;...;`xn`] (allowed to be empty), this    *)
(* function returns the theorem |- (!x1 ... xn. F) = F.                     *)
(*--------------------------------------------------------------------------*)

local

val forall_simp =
   SPEC F (Rsyntax.INST_TYPE [Type.alpha |-> Type.bool] FORALL_SIMP);

in

fun FORALL_F [] = F_REFL
  | FORALL_F (h::t) = TRANS (FORALL_EQ h (FORALL_F t)) forall_simp
     handle HOL_ERR _ => raise TAUT_ERR{function = "FORALL_F", message = ""};

end;

(*--------------------------------------------------------------------------*)
(* TAUT_CHECK_CONV : conv                                                   *)
(*                                                                          *)
(* Given a propositional term with all variables universally quantified,    *)
(* e.g. `!x1 ... xn. f[x1,...,xn]`, this conversion proves the term to be   *)
(* either true or false, i.e. it returns one of:                            *)
(*                                                                          *)
(*    |- (!x1 ... xn. f[x1,...,xn]) = T                                     *)
(*    |- (!x1 ... xn. f[x1,...,xn]) = F                                     *)
(*--------------------------------------------------------------------------*)

fun TAUT_CHECK_CONV tm =
   let val (vars,tm') = strip_forall tm
   in  if (is_T tm') then FORALL_T vars
       else if (is_F tm') then FORALL_F vars
       else let val (var,body) = dest_forall tm
                val tmT = Rsyntax.subst [{residue = T,redex = var}] body
                val thT1 = RULE_OF_CONV (DEPTH_FORALL_CONV SIMP_PROP_CONV) tmT
                val tmT' = rhs (concl thT1)
                val thT2 = TAUT_CHECK_CONV tmT'
                val thT3 = TRANS thT1 thT2
            in  if (is_F (rhs (concl thT3)))
                then BOOL_CASES_T_F_RULE thT3 tm
                else let val tmF =
                            Rsyntax.subst [{residue = F,redex = var}] body
                         val thF1 =
                            RULE_OF_CONV (DEPTH_FORALL_CONV SIMP_PROP_CONV) tmF
                         val tmF' = rhs (concl thF1)
                         val thF2 = if (tmF' = tmT')
                                    then thT2
                                    else TAUT_CHECK_CONV tmF'
                         val thF3 = TRANS thF1 thF2
                     in  if (is_F (rhs (concl thF3)))
                         then BOOL_CASES_F_F_RULE thF3 tm
                         else BOOL_CASES_BOTH_T_RULE (thT3,thF3) tm
                     end
            end
   end
   handle HOL_ERR _ => raise TAUT_ERR{function = "TAUT_CHECK_CONV",
                              message = ""};

(*--------------------------------------------------------------------------*)
(* TAUT_CONV :conv                                                          *)
(*                                                                          *)
(* Given a propositional term with all variables universally quantified,    *)
(* e.g. `!x1 ... xn. f[x1,...,xn]`, this conversion proves the term to be   *)
(* either true or false, i.e. it returns one of:                            *)
(*                                                                          *)
(*    |- (!x1 ... xn. f[x1,...,xn]) = T                                     *)
(*    |- (!x1 ... xn. f[x1,...,xn]) = F                                     *)
(*                                                                          *)
(* This conversion tries to simplify before calling TAUT_CHECK_CONV. It     *)
(* also accepts propositional terms that are not fully universally          *)
(* quantified. However, for such a term, the conversion will fail if it is  *)
(* not true. Consider the term `!x2 ... xn. f[x1,...,xn]`. TAUT_CHECK_CONV  *)
(* proves one of:                                                           *)
(*                                                                          *)
(*    |- (!x1 ... xn. f[x1,...,xn]) = T                                     *)
(*    |- (!x1 ... xn. f[x1,...,xn]) = F                                     *)
(*                                                                          *)
(* The former can be manipulated as follows:                                *)
(*                                                                          *)
(*    |- (!x1 ... xn. f[x1,...,xn]) = T                                     *)
(*    |- !x1 ... xn. f[x1,...,xn]                                           *)
(*    |- !x2 ... xn. f[x1,...,xn]                                           *)
(*    |- (!x2 ... xn. f[x1,...,xn]) = T                                     *)
(*                                                                          *)
(* However when the fully quantified term is false, we have:                *)
(*                                                                          *)
(*    |- (!x1 ... xn. f[x1,...,xn]) = F                                     *)
(*    |- ~(!x1 ... xn. f[x1,...,xn])                                        *)
(*    |- ?x1. ~(!x2 ... xn. f[x1,...,xn])                                   *)
(*    |- ?x1. ((!x2 ... xn. f[x1,...,xn]) = F)                              *)
(*                                                                          *)
(* whereas we want:                                                         *)
(*                                                                          *)
(*    |- !x1. ((!x2 ... xn. f[x1,...,xn]) = F)                              *)
(*                                                                          *)
(* i.e.                                                                     *)
(*                                                                          *)
(*    |- (!x2 ... xn. f[x1,...,xn]) = F                                     *)
(*                                                                          *)
(* The conversions given here are not capable of proving the latter theorem *)
(* since it is not purely propositional.                                    *)
(*--------------------------------------------------------------------------*)

fun TAUT_CONV tm =
   let val vars = free_vars tm
       val tm' = list_mk_forall (vars,tm)
       val th = (RULE_OF_CONV (DEPTH_FORALL_CONV SIMP_PROP_CONV) THENC
                 TAUT_CHECK_CONV) tm'
   in  if (null vars)
       then th
       else if (is_F (rhs (concl th)))
            then raise TAUT_ERR{function = "PTAUT_CONV",
                          message = "false for at least one interpretation"}
            else (EQT_INTRO o SPECL vars o EQT_ELIM) th
   end
   handle e as HOL_ERR{origin_function = "TAUT_CONV",...} => raise e
        | HOL_ERR _ => raise TAUT_ERR{function = "TAUT_CONV",message = ""};

end;

end; (* Taut *)
