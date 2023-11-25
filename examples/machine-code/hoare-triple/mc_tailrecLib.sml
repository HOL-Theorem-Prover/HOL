structure mc_tailrecLib :> mc_tailrecLib =
struct

open HolKernel boolLib bossLib Parse;
open tailrecTheory helperLib sumSyntax pairSyntax;

structure Parse =
struct
   open Parse
   val (Type, Term) = parse_from_grammars tailrecTheory.tailrec_grammars
end

val tailrec_definitions = ref ([]:thm list);
fun allow_rebinds f x = Feedback.trace ("Theory.allow_rebinds", 1) f x
val new_definition = allow_rebinds new_definition
val save_thm = allow_rebinds save_thm

(* tactic, move to helperLib? *)

fun dest_tuple tm =
  let val (x,y) = dest_pair tm in x :: dest_tuple y end handle HOL_ERR e => [tm];

fun EXPAND_BASIC_LET_CONV tm = let
  val (xs,x) = dest_anylet tm
  val (lhs,rhs) = hd xs
  val ys = dest_tuple lhs
  val zs = dest_tuple rhs
  val _ = if length zs = length ys then () else fail()
  fun every p [] = true
    | every p (x::xs) = if p x then every p xs else fail()
  val _ = every (fn x => every is_var (list_dest dest_conj x)) zs
  in (((RATOR_CONV o RATOR_CONV) (REWRITE_CONV [LET_DEF]))
      THENC DEPTH_CONV PairRules.PBETA_CONV) tm end
  handle HOL_ERR _ => NO_CONV tm;

fun STRIP_FORALL_TAC (hs,tm) =
  if is_forall tm then STRIP_TAC (hs,tm) else NO_TAC (hs,tm)

fun SPEC_AND_CASES_TAC x =
  SPEC_TAC (x,genvar(type_of x)) THEN Cases THEN REWRITE_TAC []

fun GENSPEC_TAC [] = SIMP_TAC pure_ss [pairTheory.FORALL_PROD]
  | GENSPEC_TAC (x::xs) = SPEC_TAC (x,genvar(type_of x)) THEN GENSPEC_TAC xs;

val EXPAND_BASIC_LET_TAC =
  CONV_TAC (DEPTH_CONV EXPAND_BASIC_LET_CONV)
  THEN REPEAT STRIP_FORALL_TAC

fun AUTO_DECONSTRUCT_TAC finder (hs,goal) = let
  val tm = finder goal
  in if is_cond tm then let
       val (b,_,_) = dest_cond tm
       in SPEC_AND_CASES_TAC b (hs,goal) end
     else if is_let tm then let
       val (v,c) = (hd o fst o dest_anylet) tm
       val c = if not (type_of c = ``:bool``) then c else
         (find_term (can (match_term ``address$GUARD x b``)) c
          handle HOL_ERR _ => c)
       val cs = dest_tuple c
       in (GENSPEC_TAC cs THEN EXPAND_BASIC_LET_TAC) (hs,goal) end
     else (REWRITE_TAC [] THEN NO_TAC) (hs,goal) end

(* /move to helper *)


fun merge_side t NONE = t
  | merge_side t (SOME (FUN_VAL tm)) =
      if tm ~~ mk_var("cond",``:bool``) then t else
      if Teq tm then t else FUN_COND (tm,t)
  | merge_side t (SOME (FUN_COND (tm,t2))) = FUN_COND (tm,merge_side t (SOME t2))
  | merge_side (FUN_IF (b,x,y)) (SOME (FUN_IF (b2,x2,y2))) =
      if b ~~ b2 then FUN_IF (b, merge_side x (SOME x2), merge_side y (SOME y2))
      else fail()
  | merge_side (FUN_LET (x,y,t)) (SOME (FUN_LET (x2,y2,t2))) =
      if x ~~ x2 andalso y ~~ y2 then FUN_LET (x,y,merge_side t (SOME t2))
      else fail()
  | merge_side _ _ = fail ()

fun leaves (FUN_VAL tm)      f = FUN_VAL (f tm)
  | leaves (FUN_COND (c,t))  f = FUN_COND (c, leaves t f)
  | leaves (FUN_IF (a,b,c))  f = FUN_IF (a, leaves b f, leaves c f)
  | leaves (FUN_LET (v,y,t)) f = FUN_LET (v, y, leaves t f)

fun rm_conds (FUN_VAL tm)      = FUN_VAL tm
  | rm_conds (FUN_COND (c,t))  = rm_conds t
  | rm_conds (FUN_IF (a,b,c))  = FUN_IF (a, rm_conds b, rm_conds c)
  | rm_conds (FUN_LET (v,y,t)) = FUN_LET (v, y, rm_conds t)

fun tailrec_define_from_step func_name step_fun tm_option = let
  (* definitions *)
  val thm = ISPEC step_fun SHORT_TAILREC_def
  val def_rhs = (fst o dest_eq o concl) thm
  val def_tm = mk_eq (mk_var(func_name,type_of def_rhs),def_rhs)
  val def_thm = new_definition(func_name,def_tm)
  val new_def_tm = (fst o dest_eq o concl) def_thm
  val side = ISPEC step_fun SHORT_TAILREC_PRE_def
  val side_rhs = (fst o dest_eq o concl) side
  val side_tm = mk_eq (mk_var(func_name ^ "_pre",type_of side_rhs),side_rhs)
  val side_thm = new_definition(func_name ^ "_pre",side_tm)
  val new_side_tm = (fst o dest_eq o concl) side_thm
  val _ = tailrec_definitions := def_thm::side_thm::(!tailrec_definitions)
  (* goals *)
  fun is_inl tm = can (match_term ``(INL x):'a + 'b``) tm
  fun leaves_inl body f1 f2 = ftree2tm (leaves (tm2ftree body) (fn tm =>
          if is_inl (fst (dest_pair tm))
          then f1 (cdr (fst (dest_pair tm)),snd (dest_pair tm))
          else f2 (cdr (fst (dest_pair tm)),snd (dest_pair tm))))
  val inst_cond_var = snd o dest_eq o concl o QCONV (REWRITE_CONV [GSYM CONJ_ASSOC]) o
                      subst [mk_var("cond",``:bool``) |-> T]
  val (def_goal,side_goal) = case tm_option of
      SOME (tm,pre_option) => let
        val (lhs,rhs) = dest_eq tm
        val func_tm = repeat car lhs
        val (old_side_tm,tm2) = (case pre_option of
              NONE => (new_side_tm,T)
            | SOME x => (repeat car (fst (dest_eq x)),x))
        in (subst [func_tm |-> new_def_tm] tm,
            subst [old_side_tm |-> new_side_tm] tm2) end
    | NONE => let
        val (args,body) = dest_pabs step_fun
        val def_body = (ftree2tm o rm_conds o tm2ftree) body
        val def_body = leaves_inl def_body (fn (tm,_) => mk_comb(new_def_tm,tm)) fst
        val def_goal = mk_eq(mk_comb(new_def_tm,args),def_body)
        val side_body = leaves_inl body (fn (tm,c) => mk_conj(mk_comb(new_side_tm,tm),c)) snd
        val side_goal = mk_eq(mk_comb(new_side_tm,args),side_body)
        val side_goal = if Teq side_body then side_goal
                        else inst_cond_var (side_goal)
        in (def_goal,side_goal) end
  (* prove exported theorems *)
  fun tac finder =
    PURE_REWRITE_TAC [def_thm,side_thm]
    THEN CONV_TAC (RATOR_CONV (PURE_ONCE_REWRITE_CONV [SHORT_TAILREC_THM]))
    THEN PURE_REWRITE_TAC [GSYM def_thm,GSYM side_thm]
    THEN CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV)
    THEN PURE_REWRITE_TAC [AND_CLAUSES]
    THEN REPEAT (AUTO_DECONSTRUCT_TAC finder)
    THEN ASM_SIMP_TAC std_ss [sumTheory.ISL,sumTheory.ISR,sumTheory.OUTL,
           sumTheory.OUTR,LET_DEF, AC CONJ_COMM CONJ_ASSOC]
    THEN EQ_TAC THEN SIMP_TAC std_ss []
  val finder = (rand o rand o rand o fst o dest_eq)
  val def_result = auto_prove "tailrec_define" (def_goal,tac finder)
  val finder = rand
  val side_result = RW [] (auto_prove "tailrec_define_with_pre" (side_goal,tac finder))
  in (def_result,def_thm,side_result,side_thm) end

fun prepare_pre pre_tm = let
  val (x,y) = dest_eq pre_tm
  val pre_tm = ftree2tm (leaves (tm2ftree y) (fn tm =>
     list_mk_conj (
       (filter (fn c => not (is_comb c andalso (car c ~~ car x)))
              (list_dest dest_conj tm)))))
  val cond_var = mk_var("cond",``:bool``)
  val pre_tm = subst [cond_var|->T] pre_tm
  val pre_tm = (snd o dest_eq o concl o SPEC_ALL o QCONV
                (REWRITE_CONV [])) pre_tm
  in pre_tm end

fun tailrec_define_full tm pre_option = let
  val (lhs,rhs) = dest_eq tm
  val func_tm = repeat car lhs
  val func_name = fst (dest_var func_tm) handle HOL_ERR e => fst (dest_const func_tm)
  (* construct step function *)
  fun option_apply f NONE = NONE | option_apply f (SOME x) = SOME (f x)
  val t = merge_side (tm2ftree rhs) (option_apply (tm2ftree o prepare_pre) pre_option)
  val ty = (snd o dest_type o type_of) func_tm
  val input_type = el 1 ty
  val output_type = el 2 ty
  val cond_var = mk_var("cond",``:bool``)
  fun step (FUN_IF (b,t1,t2)) = FUN_IF (b,step t1,step t2)
    | step (FUN_LET (x,y,t)) = FUN_LET (x,y,step t)
    | step (FUN_COND (c,t)) = FUN_COND (c,step t)
    | step (FUN_VAL tm) =
        if ((car tm ~~ func_tm) handle HOL_ERR _ => false)
        then FUN_VAL (mk_pair(mk_inl(cdr tm,output_type),cond_var))
        else FUN_VAL (mk_pair(mk_inr(tm,input_type),cond_var))
  val tm2 = subst [cond_var|->T] (ftree2tm (step t))
  val step_fun = mk_pabs(cdr lhs,tm2)
  val tm_option = SOME (tm,pre_option)
  val (def_result,def_thm,side_result,side_thm) =
        tailrec_define_from_step func_name step_fun tm_option
  val _ = save_thm(func_name ^ "_def", def_result)
  val _ = save_thm(func_name ^ "_pre_def", side_result)
  in (def_result,def_thm,side_result,side_thm) end;

fun tailrec_define tm =
  let val (th,_,_,_) = tailrec_define_full tm NONE in th end;

fun tailrec_define_with_pre tm pre =
  let val (th,_,pre,_) = tailrec_define_full tm (SOME pre) in (th,pre) end;

fun TAILREC_TAC (hs,g) =
  (REWRITE_TAC [] THEN ONCE_REWRITE_TAC (!tailrec_definitions)) (hs,g);


end;
