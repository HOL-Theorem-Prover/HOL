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

open HolKernel Parse basicHol90Lib;
infix THEN THENC ## |->;

type conv = Abbrev.conv;
type tactic = Abbrev.tactic;

fun TAUT_ERR{function,message} = HOL_ERR{origin_structure = "Taut",
                                         origin_function = function,
                                         message = message};

val BOOL_CASES_AX = boolTheory.BOOL_CASES_AX;


(*===========================================================================*)
(* Discriminator functions for T (true) and F (false)                        *)
(*===========================================================================*)

val T = --`T`--
and F = --`F`--;

fun is_T tm = (tm = T)
and is_F tm = (tm = F);


(*===========================================================================*)
(* Theorems used for Boolean case analysis                                   *)
(*===========================================================================*)

(*---------------------------------------------------------------------------*)
(* BOOL_CASES_T_F = |- !f. (f T = F) ==> ((!x. f x) = F)                     *)
(*---------------------------------------------------------------------------*)

val BOOL_CASES_T_F = prove
  (--`!f. (f T = F) ==> ((!x. f x) = F)`--,
   REPEAT STRIP_TAC THEN
   REWRITE_TAC [] THEN
   CONV_TAC NOT_FORALL_CONV THEN
   EXISTS_TAC T THEN
   ASM_REWRITE_TAC []);

(*---------------------------------------------------------------------------*)
(* BOOL_CASES_F_F = |- !f. (f F = F) ==> ((!x. f x) = F)                     *)
(*---------------------------------------------------------------------------*)

val BOOL_CASES_F_F = prove
  (--`!f. (f F = F) ==> ((!x. f x) = F)`--,
   REPEAT STRIP_TAC THEN
   REWRITE_TAC [] THEN
   CONV_TAC NOT_FORALL_CONV THEN
   EXISTS_TAC F THEN
   ASM_REWRITE_TAC []);

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
      val thT' = TRANS(SUBST_CONV[Bvar |-> ASSUME(mk_eq{lhs=Bvar,rhs=T})]
                                 Body Body) thT
      and thF' = TRANS(SUBST_CONV[Bvar |-> ASSUME(mk_eq{lhs=Bvar,rhs=F})]
                                 Body Body) thF
      val th = DISJ_CASES cases_thm thT' thF'
   in (EQT_INTRO o (GEN Bvar) o EQT_ELIM) th
  end handle _ => raise TAUT_ERR{function="BOOL_CASES_BOTH_T_RULE",message=""};

(*---------------------------------------------------------------------------*)
(* BOOL_CASES_T_F_RULE : thm -> conv                                         *)
(*                                                                           *)
(* BOOL_CASES_T_F_RULE (|- f[T] = F) `!x. f[x]` returns the theorem          *)
(* |- (!x. f[x]) = F.                                                        *)
(*---------------------------------------------------------------------------*)

local val frawl = --`$! :(bool -> bool) -> bool`--
in
fun BOOL_CASES_T_F_RULE thT tm =
   let val (t as {Bvar,Body}) = dest_forall tm
       val f = mk_abs t
       val thT' = TRANS (BETA_CONV (mk_comb{Rator=f,Rand=T})) thT
       and th = AP_TERM frawl(ABS Bvar(BETA_CONV(mk_comb{Rator=f,Rand=Bvar})))
       val th1 = SPEC f BOOL_CASES_T_F
       val th2 = MP th1 thT'
   in TRANS (SYM th) th2
   end handle _ => raise TAUT_ERR{function="BOOL_CASES_T_F_RULE",message = ""}
end;

(*---------------------------------------------------------------------------*)
(* BOOL_CASES_F_F_RULE : thm -> conv                                         *)
(*                                                                           *)
(* BOOL_CASES_F_F_RULE (|- f[F] = F) `!x. f[x]` returns the theorem          *)
(* |- (!x. f[x]) = F.                                                        *)
(*---------------------------------------------------------------------------*)

local val frawl =  (--`$! :(bool -> bool) -> bool`--)
in
fun BOOL_CASES_F_F_RULE thF tm =
   let val (t as {Bvar,Body}) = dest_forall tm
       val f = mk_abs t
       val thF' = TRANS (BETA_CONV (mk_comb{Rator=f,Rand=F})) thF
       and th = AP_TERM frawl(ABS Bvar(BETA_CONV(mk_comb{Rator=f,Rand=Bvar})))
       and th1 = SPEC f BOOL_CASES_F_F
       val th2 = MP th1 thF'
   in TRANS (SYM th) th2
   end handle _ => raise TAUT_ERR{function="BOOL_CASES_F_F_RULE",message = ""}
end;

(*===========================================================================*)
(* Conversions that use failure to indicate that they have not changed their *)
(* input term, and hence save the term from being rebuilt unnecessarily.     *)
(*===========================================================================*)

(*---------------------------------------------------------------------------*)
(* Failure string indicating that a term has not been changed by the         *)
(* conversion applied to it.                                                 *)
(*---------------------------------------------------------------------------*)

exception UNCHANGED;

(*---------------------------------------------------------------------------*)
(* QCONV : conv -> conv                                                      *)
(*                                                                           *)
(* Takes a conversion that uses failure to indicate that it has not changed  *)
(* its argument term, and produces an ordinary conversion.                   *)
(*---------------------------------------------------------------------------*)

fun QCONV conv tm = conv tm
                    handle UNCHANGED => REFL tm

(*---------------------------------------------------------------------------*)
(* ALL_QCONV : conv                                                          *)
(*                                                                           *)
(* Identity conversion for conversions using failure.                        *)
(*---------------------------------------------------------------------------*)

val ALL_QCONV:conv = fn _ => raise UNCHANGED


(*---------------------------------------------------------------------------*)
(* THENQC : conv -> conv -> conv                                             *)
(*                                                                           *)
(* Takes two conversions that use failure and produces a conversion that     *)
(* applies them in succession. The new conversion also uses failure. It fails*)
(* if neither of the two argument conversions cause a change.                *)
(*---------------------------------------------------------------------------*)

fun THENQC conv1 conv2 tm =
   let val th1 = conv1 tm
   in  TRANS th1 (conv2 (rhs (concl th1))) handle UNCHANGED => th1
   end handle UNCHANGED => conv2 tm;

(*---------------------------------------------------------------------------*)
(* ORELSEQC : conv -> conv -> conv                                           *)
(*                                                                           *)
(* Takes two conversions that use failure and produces a conversion that     *)
(* tries the first one, and if this fails for a reason other than that the   *)
(* term is unchanged, it tries the second one.                               *)
(*---------------------------------------------------------------------------*)

fun ORELSEQC (conv1:conv) conv2 tm =
   conv1 tm
   handle UNCHANGED => raise UNCHANGED
        | _ => conv2 tm;

(*---------------------------------------------------------------------------*)
(* TRY_QCONV : conv -> conv                                                  *)
(*                                                                           *)
(* Applies a conversion, and if it fails, raises an UNCHANGED exception.     *)
(*---------------------------------------------------------------------------*)

fun TRY_QCONV conv = ORELSEQC conv ALL_QCONV;

(*---------------------------------------------------------------------------*)
(* RAND_QCONV : conv -> conv                                                 *)
(*                                                                           *)
(* Applies a conversion to the rand of a term, propagating any failure that  *)
(* indicates that the subterm is unchanged.                                  *)
(*---------------------------------------------------------------------------*)

fun RAND_QCONV conv tm =
   let val {Rator,Rand} = 
         dest_comb tm handle _ => raise TAUT_ERR{function = "RAND_QCONV",
                                                 message = ""}
   in AP_TERM Rator (conv Rand)
   end;

(*---------------------------------------------------------------------------*)
(* RATOR_QCONV : conv -> conv                                                *)
(*                                                                           *)
(* Applies a conversion to the rator of a term, propagating any failure that *)
(* indicates that the subterm is unchanged.                                  *)
(*---------------------------------------------------------------------------*)

fun RATOR_QCONV conv tm =
   let val {Rator,Rand} = 
         dest_comb tm handle _ => raise TAUT_ERR{function = "RATOR_QCONV",
                                                 message = ""}
   in AP_THM (conv Rator) Rand
   end;

(*---------------------------------------------------------------------------*)
(* ABS_QCONV : conv -> conv                                                  *)
(*                                                                           *)
(* Applies a conversion to the body of an abstraction, propagating any       *)
(* failure that indicates that the subterm is unchanged.                     *)
(*---------------------------------------------------------------------------*)

fun ABS_QCONV conv tm =
   let val {Bvar,Body} = 
          dest_abs tm handle _ => raise TAUT_ERR{function = "ABS_QCONV",
                                                 message = "in dest_abs"}
       val bodyth = conv Body
   in ABS Bvar bodyth 
   handle (e as HOL_ERR _) => raise e
        | _ => raise TAUT_ERR{function = "ABS_QCONV",message = ""}
   end;

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

local
val [th1,th2,th3] = CONJUNCTS NOT_CLAUSES
in
fun NOT_CONV tm =
   let val arg = dest_neg tm
   in if (is_T arg) 
      then th2
      else if (is_F arg) 
           then th3
           else SPEC (dest_neg arg) th1
   end handle _ => raise TAUT_ERR{function = "NOT_CONV",message = ""}
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

local val th1 = INST_TYPE [Type.alpha |-> Type.bool] REFL_CLAUSE
      and [th2,th3,th4,th5] = map GEN_ALL (CONJUNCTS (SPEC_ALL EQ_CLAUSES))
in
fun EQ_CONV tm =
   let val {lhs,rhs} = dest_eq tm
   in
   if (is_T lhs) 
   then SPEC rhs th2
   else if (is_T rhs) 
        then SPEC lhs th3
        else if (is_F lhs) 
             then SPEC rhs th4
             else if (is_F rhs) 
                  then SPEC lhs th5
                  else if (lhs = rhs) 
                       then SPEC lhs th1
                       else raise TAUT_ERR{function = "EQ_CONV",message = ""}
   end handle (e as HOL_ERR _) => raise e
            | _ => raise TAUT_ERR{function = "EQ_CONV",message = ""}
end;

(*---------------------------------------------------------------------------*)
(* EQ_THEN_NOT_CONV : conv                                                   *)
(*                                                                           *)
(* Behaves as for EQ_CONV, then if EQ_CONV generated a top level negation, it*)
(* tries to apply NOT_CONV.                                                  *)
(*---------------------------------------------------------------------------*)

fun EQ_THEN_NOT_CONV tm =
   if ((is_F (rand (rator tm))) orelse (is_F (rand tm)))
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

local
val [th1,th2,th3,th4,th5] = map GEN_ALL (CONJUNCTS (SPEC_ALL AND_CLAUSES))
in
fun AND_CONV tm =
   let val {conj1,conj2} = dest_conj tm
   in
   if (is_T conj1) 
   then SPEC conj2 th1
   else if (is_T conj2) 
        then SPEC conj1 th2
        else if (is_F conj1) 
             then SPEC conj2 th3
             else if (is_F conj2) 
                  then SPEC conj1 th4
                  else if (conj1 = conj2) 
                       then SPEC conj1 th5
                       else raise TAUT_ERR{function = "AND_CONV",message = ""}
   end
   handle (e as HOL_ERR _) => raise e
        | _ => raise TAUT_ERR{function = "AND_CONV",message = ""}
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

local
val [th1,th2,th3,th4,th5] = map GEN_ALL (CONJUNCTS (SPEC_ALL OR_CLAUSES))
in 
fun OR_CONV tm =
   let val {disj1,disj2} = dest_disj tm
   in
   if (is_T disj1) 
   then SPEC disj2 th1
   else if (is_T disj2) 
        then SPEC disj1 th2
        else if (is_F disj1) 
             then SPEC disj2 th3
             else if (is_F disj2) 
                  then SPEC disj1 th4
                  else if (disj1 = disj2) 
                       then SPEC disj1 th5
                       else raise TAUT_ERR{function = "OR_CONV",message = ""}
   end
   handle (e as HOL_ERR _) => raise e
        | _ => raise TAUT_ERR{function = "OR_CONV",message = ""}
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

local
val [th1,th2,th3,th4,th5] = map GEN_ALL (CONJUNCTS (SPEC_ALL IMP_CLAUSES))
in 
fun IMP_CONV tm =
   let val {ant,conseq} = dest_imp tm
   in  
   if (is_neg tm) 
   then raise TAUT_ERR{function = "IMP_CONV",message = ""}
   else if (is_T ant) 
        then SPEC conseq th1
        else if (is_T conseq) 
             then SPEC ant th2
             else if (is_F ant) 
                  then SPEC conseq th3
                  else if (is_F conseq) 
                       then SPEC ant th5
                       else if (ant = conseq) 
                            then SPEC ant th4
                            else raise TAUT_ERR{function = "IMP_CONV",
                                                message = ""}
   end
   handle (e as HOL_ERR _) => raise e 
        | _ => raise TAUT_ERR{function = "IMP_CONV",message = ""}
end;

(*---------------------------------------------------------------------------*)
(* IMP_THEN_NOT_CONV : conv                                                  *)
(*                                                                           *)
(* Behaves as for IMP_CONV, then if IMP_CONV generated a top level negation, *)
(* it tries to apply NOT_CONV.                                               *)
(*---------------------------------------------------------------------------*)

fun IMP_THEN_NOT_CONV tm =
   if (is_F (rand tm))
   then (IMP_CONV THENC (TRY_CONV NOT_CONV)) tm
   else IMP_CONV tm;

(*---------------------------------------------------------------------------*)
(* IF_CONV : conv                                                            *)
(*                                                                           *)
(*    |- (T => t1 | t2) = t1                                                 *)
(*    |- (F => t1 | t2) = t2                                                 *)
(*---------------------------------------------------------------------------*)

local val theta = [Type.alpha |-> Type.bool]
      val [th1,th2] = map (GENL [--`t1:bool`--, --`t2:bool`--])
                    (CONJUNCTS (SPEC_ALL (INST_TYPE theta COND_CLAUSES)))
in
fun IF_CONV tm =
   let val {cond,larm,rarm} = dest_cond tm
   in if (is_T cond) 
      then SPECL [larm,rarm] th1
      else if (is_F cond) 
           then SPECL [larm,rarm] th2
           else raise TAUT_ERR{function = "IF_CONV",message = ""}
   end handle (e as HOL_ERR _) => raise e
            | _ => raise TAUT_ERR{function = "IF_CONV",message = ""}
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
          in
          let val th1 = SIMP_PROP_QCONV arg1
              val th = AP_TERM opp th1
          in
          MK_COMB (th,SIMP_PROP_QCONV arg2)
          handle UNCHANGED => AP_THM th arg2
          end handle UNCHANGED => let val th2 = SIMP_PROP_QCONV arg2
                                  in AP_TERM (rator tm) th2
                                  end
          end
   in
   if ((is_const tm) orelse (is_var tm)) 
   then ALL_QCONV tm
   else if (is_neg tm) 
        then THENQC (RAND_QCONV SIMP_PROP_QCONV) 
                    (TRY_QCONV NOT_CONV) 
                    tm
        else if (is_eq tm)
             then THENQC ARGS_QCONV (TRY_QCONV EQ_THEN_NOT_CONV) tm
             else if (is_conj tm)
                  then THENQC ARGS_QCONV (TRY_QCONV AND_CONV) tm
                  else if (is_disj tm)
                       then THENQC ARGS_QCONV (TRY_QCONV OR_CONV) tm
                       else if (is_imp tm)
                            then THENQC ARGS_QCONV 
                                        (TRY_QCONV IMP_THEN_NOT_CONV)
                                        tm
                            else if (is_cond tm) 
                                 then THENQC
                                       (THENQC
                                         (RATOR_QCONV
                                            (THENQC 
                                              (RATOR_QCONV 
                                                  (RAND_QCONV SIMP_PROP_QCONV))
                                              (RAND_QCONV SIMP_PROP_QCONV)))
                                         (RAND_QCONV SIMP_PROP_QCONV))
                                       (TRY_QCONV IF_CONV)
                                       tm
                                else raise TAUT_ERR{function="SIMP_PROP_QCONV",
                                                    message = ""}
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
   if (is_forall tm)
   then RAND_QCONV (ABS_QCONV (DEPTH_FORALL_QCONV conv)) tm
   else conv tm;

(*---------------------------------------------------------------------------*)
(* FORALL_T : term list -> thm                                               *)
(*                                                                           *)
(* Given a list of variables [`x1`;...;`xn`] (allowed to be empty), this     *)
(* function returns the theorem |- (!x1 ... xn. T) = T.                      *)
(*---------------------------------------------------------------------------*)

fun FORALL_T [] = T_REFL
  | FORALL_T vars = EQT_INTRO (GENL vars TRUTH)
                    handle _ => raise TAUT_ERR{function = "FORALL_T",
                                               message = ""}

(*---------------------------------------------------------------------------*)
(* FORALL_F : term list -> thm                                               *)
(*                                                                           *)
(* Given a list of variables [`x1`;...;`xn`] (allowed to be empty), this     *)
(* function returns the theorem |- (!x1 ... xn. F) = F.                      *)
(*---------------------------------------------------------------------------*)

local
val forall_simp = SPEC F (INST_TYPE [Type.alpha |-> Type.bool] FORALL_SIMP)
in
fun FORALL_F [] = F_REFL
  | FORALL_F (h::t) = TRANS (FORALL_EQ h (FORALL_F t)) forall_simp
      handle _ => raise TAUT_ERR{function = "FORALL_F", message = ""}
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
   in
   if (is_T tm') 
   then FORALL_T vars
   else if (is_F tm') 
        then FORALL_F vars
        else let val {Bvar,Body} = dest_forall tm
                 val tmT = subst [{redex = Bvar, residue = T}] Body
                 val thT1 = QCONV (DEPTH_FORALL_QCONV SIMP_PROP_QCONV) tmT
                 val tmT' = rhs (concl thT1)
                 val thT2 = TAUT_CHECK_CONV tmT'
                 val thT3 = TRANS thT1 thT2
             in
             if (is_F (rhs (concl thT3)))
             then BOOL_CASES_T_F_RULE thT3 tm
             else let val tmF = subst [{redex=Bvar,residue=F}] Body
                      val thF1 = QCONV (DEPTH_FORALL_QCONV SIMP_PROP_QCONV) tmF
                      val tmF' = rhs (concl thF1)
                      val thF2 = if (tmF' = tmT')
                                 then thT2
                                 else TAUT_CHECK_CONV tmF'
                      val thF3 = TRANS thF1 thF2
                  in if (is_F (rhs (concl thF3)))
                     then BOOL_CASES_F_F_RULE thF3 tm
                     else BOOL_CASES_BOTH_T_RULE (thT3,thF3) tm
                  end
             end
   end handle _ => raise TAUT_ERR{function = "TAUT_CHECK_CONV",message = ""};

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
       val tm' = list_mk_forall (vars,tm)
       val th = ((QCONV (DEPTH_FORALL_QCONV SIMP_PROP_QCONV)) THENC
                 TAUT_CHECK_CONV) tm'
   in
   if (null vars)
   then th
   else if (is_F (rhs (concl th)))
        then raise TAUT_ERR{function = "PTAUT_CONV",
                            message = "false for at least one interpretation"}
        else (EQT_INTRO o (SPECL vars) o EQT_ELIM) th
   end
   handle (e as HOL_ERR{origin_structure = "Taut",
                        origin_function = "PTAUT_CONV",...}) => raise e
        | _ => raise TAUT_ERR{function = "PTAUT_CONV",message = ""};

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
   handle (HOL_ERR{origin_structure,origin_function,message})
          => raise TAUT_ERR{function = "PTAUT_PROVE",
                   message = origin_structure^"."^origin_function^": "^message}
        | e => raise TAUT_ERR{function = "PTAUT_PROVE",message = ""};

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
             else raise TAUT_ERR{function = "",message = ""}
          end
   in  non_prop_args tm
       handle _ => case (dest_type (type_of tm))
                   of {Tyop="bool",...} => [tm]
                    | _ => raise TAUT_ERR{function="non_prop_terms",message=""}
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
fun mk_subst tm1 tm2 = {redex=tm1, residue = tm2}

fun TAUT_CONV tm =
   let val (univs,tm') = strip_forall tm
       val insts = mk_set (non_prop_terms tm')
       val vars = map (genvar o type_of) insts
       val theta = map2 mk_subst insts vars
       val tm'' = list_mk_forall (vars,subst theta tm')
   in EQT_INTRO (GENL univs (SPECL insts (PTAUT_PROVE tm'')))
   end handle HOL_ERR{origin_structure,origin_function,message}
              => raise TAUT_ERR{function = "TAUT_CONV", 
                   message = origin_structure^"."^origin_function^": "^message}
            | e => raise TAUT_ERR{function = "TAUT_CONV",message = ""};

(*---------------------------------------------------------------------------*)
(* TAUT_TAC : tactic                                                         *)
(*                                                                           *)
(* Tactic for solving propositional formulae and instances of propositional  *)
(* formulae.                                                                 *)
(*---------------------------------------------------------------------------*)

val TAUT_TAC = CONV_TAC TAUT_CONV;

(*---------------------------------------------------------------------------*)
(* TAUT_PROVE : conv                                                         *)
(*                                                                           *)
(* Given a valid propositional formula, or a valid instance of a             *)
(* propositional formula, `t`, this conversion returns the theorem |- t.     *)
(*---------------------------------------------------------------------------*)

fun TAUT_PROVE tm = EQT_ELIM (TAUT_CONV tm) 
                    handle _ => raise TAUT_ERR{function = "TAUT_PROVE",
                                               message = ""};


end; (* tautLib *)
