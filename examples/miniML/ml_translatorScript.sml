open HolKernel Parse boolLib bossLib; val _ = new_theory "ml_translator";

open MiniMLTheory miniMLProofsTheory determTheory;
open arithmeticTheory listTheory combinTheory pairTheory;

infix \\ val op \\ = op THEN;


(* Definitions *)

val Eval_def = Define `
  Eval env exp P =
    ?res. evaluate' env exp (Rval res) /\ P res`;

val evaluate_closure_def = Define `
  evaluate_closure input cl output =
    ?env exp. (do_app ARB Opapp cl input = SOME (env,exp)) /\
              evaluate' env exp (Rval output)`;

val AppReturns_def = Define ` (* think of this as a Hoare triple {P} cl {Q} *)
  AppReturns P Q cl =
    !a x.
      P a x ==>
      ?y. evaluate_closure x cl y /\ Q a y`;

val Arrow_def = Define `
  Arrow abs1 abs2 f closure =
    AppReturns (\x. abs1 x) (\x. abs2 (f x)) closure`;

val _ = add_infix("-->",400,HOLgrammars.RIGHT)
val _ = overload_on ("-->",``Arrow``)

val Fix_def = Define `
  Fix (abs:'a->v->bool) x =
    (\y v. (x = y) /\ abs y v)`;

val NUM_def = Define `
  NUM n = \v. (v = Lit (Num n))`;

val BOOL_def = Define `
  BOOL b = \v. (v = Lit (Bool b))`;

val CONTAINER_def = Define `CONTAINER x = x`;

val TAG_def = Define `TAG n x = x`;


(* Theorems *)

val evaluate_cases = evaluate'_cases;

val evaluate_11_Rval = prove(
  ``evaluate' env exp (Rval res1) ==>
    evaluate' env exp (Rval res2) ==> (res1 = res2)``,
  REPEAT STRIP_TAC \\ IMP_RES_TAC big_exp_determ'
  \\ FULL_SIMP_TAC (srw_ss()) []);

val Eval_Arrow = store_thm("Eval_Arrow",
  ``Eval env x1 ((a --> b) f) ==>
    Eval env x2 (a x) ==>
    Eval env (App Opapp x1 x2) (b (f x))``,
  SIMP_TAC std_ss [Eval_def,Arrow_def] \\ REPEAT STRIP_TAC
  \\ ONCE_REWRITE_TAC [evaluate_cases] \\ SIMP_TAC (srw_ss()) []
  \\ FULL_SIMP_TAC std_ss [AppReturns_def] \\ RES_TAC
  \\ FULL_SIMP_TAC std_ss [evaluate_closure_def]
  \\ Q.EXISTS_TAC `y` \\ FULL_SIMP_TAC std_ss []
  \\ Q.LIST_EXISTS_TAC [`res`,`res'`,`env'`]
  \\ FULL_SIMP_TAC (srw_ss()) [do_app_def]);

val Eval_Fun = store_thm("Eval_Fun",
  ``(!v x. a x v ==> Eval ((name,v)::env) body (b (f x))) ==>
    Eval env (Fun name body) ((a --> b) f)``,
  SIMP_TAC std_ss [Eval_def,Arrow_def] \\ REPEAT STRIP_TAC
  \\ ONCE_REWRITE_TAC [evaluate_cases] \\ SIMP_TAC (srw_ss()) []
  \\ ASM_SIMP_TAC (srw_ss()) [AppReturns_def,Eval_def,do_app_def,
       bind_def,evaluate_closure_def]);

val Eval_Let = store_thm("Eval_Let",
  ``Eval env exp (a res) /\
    (!v. a res v ==> Eval ((name,v)::env) body (b (f res))) ==>
    Eval env (Let name exp body) (b (LET f res))``,
  SIMP_TAC std_ss [Eval_def,Arrow_def] \\ REPEAT STRIP_TAC
  \\ ONCE_REWRITE_TAC [evaluate_cases] \\ SIMP_TAC (srw_ss()) []
  \\ RES_TAC \\ Q.EXISTS_TAC `res''` \\ FULL_SIMP_TAC std_ss [LET_DEF,bind_def]
  \\ Q.EXISTS_TAC `res'` \\ FULL_SIMP_TAC std_ss []);

val Eval_Val = store_thm("Eval_Val",
  ``!x. Eval env (Val x) (\v. v = x)``,
  SIMP_TAC (srw_ss()) [Once evaluate_cases,Eval_def]);

val Eval_Var = store_thm("Eval_Var",
  ``!name x. Eval env (Var name) (\v. v = x) = (lookup name env = SOME x)``,
  SIMP_TAC (srw_ss()) [Once evaluate_cases,Eval_def]);

val Eval_Val_NUM = store_thm("Eval_Val_NUM",
  ``!n. Eval env (Val (Lit (Num n))) (NUM n)``,
  SIMP_TAC (srw_ss()) [Once evaluate_cases,NUM_def,Eval_def]);

val Eval_Val_BOOL = store_thm("Eval_Val_BOOL",
  ``!n. Eval env (Val (Lit (Bool n))) (BOOL n)``,
  SIMP_TAC (srw_ss()) [Once evaluate_cases,BOOL_def,Eval_def]);

val Eval_Var_NUM = store_thm("Eval_Var_NUM",
  ``!name x.
       (lookup name env = SOME (Lit (Num x))) ==> Eval env (Var name) (NUM x)``,
  SIMP_TAC (srw_ss()) [Once evaluate_cases,NUM_def,Eval_def]);

val Eval_Var_BOOL = store_thm("Eval_Var_BOOL",
  ``!name x.
       (lookup name env = SOME (Lit (Bool x))) ==> Eval env (Var name) (BOOL x)``,
  SIMP_TAC (srw_ss()) [Once evaluate_cases,BOOL_def,Eval_def]);

val Eval_Opn = store_thm("Eval_Opn",
  ``!f. Eval env x1 (NUM n1) ==>
        Eval env x2 (NUM n2) ==>
        Eval env (App (Opn f) x1 x2) (NUM (f n1 n2))``,
  SIMP_TAC std_ss [Eval_def,NUM_def] \\ SIMP_TAC std_ss []
  \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss []
  \\ ONCE_REWRITE_TAC [evaluate_cases] \\ SIMP_TAC (srw_ss()) []
  \\ Q.LIST_EXISTS_TAC [`Lit (Num n1)`,`Lit (Num n2)`]
  \\ FULL_SIMP_TAC (srw_ss()) [do_app_def]
  \\ ONCE_REWRITE_TAC [evaluate_cases] \\ SIMP_TAC (srw_ss()) []);

val Eval_Opb = store_thm("Eval_Opb",
  ``!f. Eval env x1 (NUM n1) ==>
        Eval env x2 (NUM n2) ==>
        Eval env (App (Opb f) x1 x2) (BOOL (f n1 n2))``,
  SIMP_TAC std_ss [Eval_def,NUM_def,BOOL_def] \\ SIMP_TAC std_ss []
  \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss []
  \\ ONCE_REWRITE_TAC [evaluate_cases] \\ SIMP_TAC (srw_ss()) []
  \\ Q.LIST_EXISTS_TAC [`Lit (Num n1)`,`Lit (Num n2)`]
  \\ FULL_SIMP_TAC (srw_ss()) [do_app_def]
  \\ ONCE_REWRITE_TAC [evaluate_cases] \\ SIMP_TAC (srw_ss()) []);

val Eval_Or = store_thm("Eval_Or",
  ``Eval env x1 (BOOL b1) ==>
    Eval env x2 (BOOL b2) ==>
    Eval env (Log Or x1 x2) (BOOL (b1 \/ b2))``,
  SIMP_TAC std_ss [Eval_def,NUM_def,BOOL_def] \\ SIMP_TAC std_ss []
  \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss []
  \\ ONCE_REWRITE_TAC [evaluate_cases] \\ SIMP_TAC (srw_ss()) []
  \\ Q.EXISTS_TAC `(Lit (Bool b1))` \\ Cases_on `b1`
  \\ FULL_SIMP_TAC (srw_ss()) [do_log_def]
  \\ ONCE_REWRITE_TAC [evaluate_cases] \\ SIMP_TAC (srw_ss()) []);

val Eval_And = store_thm("Eval_And",
  ``Eval env x1 (BOOL b1) ==>
    Eval env x2 (BOOL b2) ==>
    Eval env (Log And x1 x2) (BOOL (b1 /\ b2))``,
  SIMP_TAC std_ss [Eval_def,NUM_def,BOOL_def] \\ SIMP_TAC std_ss []
  \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss []
  \\ ONCE_REWRITE_TAC [evaluate_cases] \\ SIMP_TAC (srw_ss()) []
  \\ Q.EXISTS_TAC `(Lit (Bool b1))` \\ Cases_on `b1`
  \\ FULL_SIMP_TAC (srw_ss()) [do_log_def]
  \\ ONCE_REWRITE_TAC [evaluate_cases] \\ SIMP_TAC (srw_ss()) []);

val Eval_If = store_thm("Eval_If",
  ``(a1 ==> Eval env x1 (BOOL b1)) /\
    (a2 ==> Eval env x2 (a b2)) /\
    (a3 ==> Eval env x3 (a b3)) ==>
    (a1 /\ (CONTAINER b1 ==> a2) /\ (~CONTAINER b1 ==> a3) ==>
     Eval env (If x1 x2 x3) (a (if b1 then b2 else b3)))``,
  SIMP_TAC std_ss [Eval_def,NUM_def,BOOL_def] \\ SIMP_TAC std_ss [CONTAINER_def]
  \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss []
  \\ ONCE_REWRITE_TAC [evaluate_cases] \\ SIMP_TAC (srw_ss()) []
  \\ Cases_on `b1` \\ FULL_SIMP_TAC std_ss []
  THEN1 (Q.EXISTS_TAC `res` \\ ASM_SIMP_TAC std_ss []
    \\ Q.EXISTS_TAC `Lit (Bool T)` \\ ASM_SIMP_TAC (srw_ss()) [do_if_def])
  THEN1 (Q.EXISTS_TAC `res` \\ ASM_SIMP_TAC std_ss []
    \\ Q.EXISTS_TAC `Lit (Bool F)` \\ ASM_SIMP_TAC (srw_ss()) [do_if_def]));

val Eval_Bool_Not = store_thm("Eval_Bool_Not",
  ``Eval env x1 (BOOL b1) ==>
    Eval env (App Equality x1 (Val (Lit (Bool F)))) (BOOL (~b1))``,
  SIMP_TAC std_ss [Eval_def,NUM_def,BOOL_def] \\ SIMP_TAC std_ss []
  \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss []
  \\ ONCE_REWRITE_TAC [evaluate_cases] \\ SIMP_TAC (srw_ss()) []
  \\ Q.EXISTS_TAC `(Lit (Bool b1))`
  \\ Q.EXISTS_TAC `(Lit (Bool F))`
  \\ FULL_SIMP_TAC (srw_ss()) [do_app_def]
  \\ ONCE_REWRITE_TAC [evaluate_cases] \\ SIMP_TAC (srw_ss()) []);

val Eval_Implies = store_thm("Eval_Implies",
  ``Eval env x1 (BOOL b1) ==>
    Eval env x2 (BOOL b2) ==>
    Eval env (If x1 x2 (Val (Lit (Bool T)))) (BOOL (b1 ==> b2))``,
  SIMP_TAC std_ss [Eval_def,NUM_def,BOOL_def] \\ SIMP_TAC std_ss []
  \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss []
  \\ ONCE_REWRITE_TAC [evaluate_cases] \\ SIMP_TAC (srw_ss()) []
  \\ Q.EXISTS_TAC `(Lit (Bool b1))` \\ Cases_on `b1`
  \\ FULL_SIMP_TAC (srw_ss()) [do_if_def]
  \\ ONCE_REWRITE_TAC [evaluate_cases] \\ SIMP_TAC (srw_ss()) []);

val Eval_Var_SIMP = store_thm("Eval_Var_SIMP",
  ``Eval ((x,v)::env) (Var y) p =
      if x = y then p v else Eval env (Var y) p``,
  SIMP_TAC (srw_ss()) [Eval_def,Once evaluate_cases,lookup_def]
  \\ SRW_TAC [] [] \\ SIMP_TAC (srw_ss()) [Eval_def,Once evaluate_cases,lookup_def]);

val Eval_Fun_Fix = store_thm("Eval_Fun_Fix",
  ``(!v. a x v ==> Eval ((name,v)::env) body (b (f x))) ==>
    Eval env (Fun name body) ((Fix a x --> b) f)``,
  SIMP_TAC std_ss [Eval_def,Arrow_def] \\ REPEAT STRIP_TAC
  \\ ONCE_REWRITE_TAC [evaluate_cases] \\ SIMP_TAC (srw_ss()) []
  \\ ASM_SIMP_TAC (srw_ss()) [AppReturns_def,evaluate_closure_def,
       do_app_def,bind_def,Fix_def]);

val Eval_Fix = store_thm("Eval_Fix",
  ``Eval env exp (a x) ==> Eval env exp ((Fix a x) x)``,
  SIMP_TAC std_ss [Eval_def,Fix_def]);

val FUN_FORALL = new_binder_definition("FUN_FORALL",
  ``($FUN_FORALL) = \(abs:'a->'b->v->bool) a v. !y. abs y a v``);

val FUN_EXISTS = new_binder_definition("FUN_EXISTS",
  ``($FUN_EXISTS) = \(abs:'a->'b->v->bool) a v. ?y. abs y a v``);

val Eval_FUN_FORALL = store_thm("Eval_FUN_FORALL",
  ``(!x. Eval env exp ((p x) f)) ==>
    Eval env exp ((FUN_FORALL x. p x) f)``,
  SIMP_TAC std_ss [Eval_def,Arrow_def,Fix_def] \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [AppReturns_def,FUN_FORALL]
  \\ `?res. evaluate' env exp (Rval res)` by METIS_TAC []
  \\ Q.EXISTS_TAC `res` \\ FULL_SIMP_TAC std_ss []
  \\ REPEAT STRIP_TAC \\ Q.PAT_ASSUM `!x.bbb` (STRIP_ASSUME_TAC o Q.SPEC `y`)
  \\ IMP_RES_TAC evaluate_11_Rval \\ FULL_SIMP_TAC (srw_ss()) []);

val PULL_FORALL = METIS_PROVE [] ``((p ==> !x. q x) = (!x. p ==> q x)) /\
                                   ((p /\ !x. q x) = (!x. p /\ q x))``

val FUN_FORALL_PUSH1 = prove(
  ``(FUN_FORALL x. a --> (b x)) = (a --> FUN_FORALL x. b x)``,
  FULL_SIMP_TAC std_ss [Arrow_def,FUN_EQ_THM,AppReturns_def,FUN_FORALL,
    Eval_def,evaluate_closure_def] \\ REPEAT STRIP_TAC \\ REVERSE EQ_TAC
  THEN1 METIS_TAC [evaluate_11_Rval]
  \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [PULL_FORALL] \\ RES_TAC
  \\ POP_ASSUM (fn th => STRIP_ASSUME_TAC (Q.SPEC `ARB` th) THEN ASSUME_TAC th)
  \\ FULL_SIMP_TAC std_ss []
  \\ Q.EXISTS_TAC `y'` \\ FULL_SIMP_TAC std_ss []
  \\ REPEAT STRIP_TAC
  \\ POP_ASSUM (MP_TAC o Q.SPEC `y''`) \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [] \\ METIS_TAC [evaluate_11_Rval]) |> GEN_ALL;

val FUN_FORALL_PUSH2 = prove(
  ``(FUN_FORALL x. (a x) --> b) = ((FUN_EXISTS x. a x) --> b)``,
  FULL_SIMP_TAC std_ss [Arrow_def,FUN_EQ_THM,AppReturns_def,FUN_FORALL,FUN_EXISTS,
    Eval_def] \\ METIS_TAC []) |> GEN_ALL;

val FUN_EXISTS_Fix = prove(
  ``(FUN_EXISTS x. Fix a x) = a``,
  SIMP_TAC std_ss [FUN_EQ_THM,FUN_EXISTS,Fix_def]) |> GEN_ALL;

val FUN_QUANT_SIMP = save_thm("FUN_QUANT_SIMP",
  LIST_CONJ [FUN_EXISTS_Fix,FUN_FORALL_PUSH1,FUN_FORALL_PUSH2]);

val Eval_Recclosure = store_thm("Eval_Recclosure",
  ``(!v. a n v ==>
  Eval ((name,v)::(fname,Recclosure env2 [(fname,name,body)] fname)::env2) body (b (f n))) ==>
    Eval env (Var fname) ($= (Recclosure env2 [(fname,name,body)] fname)) ==>
    Eval env (Var fname) ((Fix a n --> b) f)``,
  FULL_SIMP_TAC std_ss [Eval_def,Arrow_def] \\ REPEAT STRIP_TAC
  \\ POP_ASSUM MP_TAC \\ ONCE_REWRITE_TAC [evaluate_cases]
  \\ FULL_SIMP_TAC (srw_ss()) [AppReturns_def,Fix_def,
       do_app_def,evaluate_closure_def]
  \\ SIMP_TAC (srw_ss()) [Once find_recfun_def,Eval_def]
  \\ FULL_SIMP_TAC std_ss [bind_def,build_rec_env_def,FOLDR]);

val SafeVar_def = Define `SafeVar = Var`;

val Eval_Eq_Recclosure = store_thm("Eval_Eq_Recclosure",
  ``Eval env (Var name) ($= (Recclosure x1 x2 x3)) ==>
    (P f (Recclosure x1 x2 x3) =
     Eval env (Var name) (P f))``,
  SIMP_TAC std_ss [Eval_Var_SIMP,Eval_def]
  \\ SIMP_TAC (srw_ss()) [Once evaluate_cases]
  \\ SIMP_TAC (srw_ss()) [Once evaluate_cases]);

val Eval_Eq_Fun = store_thm("Eval_Eq_Fun",
  ``Eval env (Fun v x) p ==>
    !env2. Eval env2 (Var name) ($= (Closure env v x)) ==>
           Eval env2 (Var name) p``,
  SIMP_TAC std_ss [Eval_Var_SIMP,Eval_def]
  \\ SIMP_TAC (srw_ss()) [Once evaluate_cases]
  \\ SIMP_TAC (srw_ss()) [Once evaluate_cases]
  \\ SIMP_TAC (srw_ss()) [Once evaluate_cases]);

val Eval_WEAKEN = store_thm("Eval_WEAKEN",
  ``Eval env exp P ==> (!v. P v ==> Q v) ==> Eval env exp Q``,
  SIMP_TAC std_ss [Eval_def] \\ METIS_TAC []);


(* Equality *)

val no_closures_def = tDefine "no_closures" `
  (no_closures (Lit l) = T) /\
  (no_closures (Conv name vs) = EVERY no_closures vs) /\
  (no_closures _ = F)`
 (WF_REL_TAC `measure v_size` \\ REPEAT STRIP_TAC
  \\ Induct_on `vs` \\ FULL_SIMP_TAC (srw_ss()) [MEM]
  \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC (srw_ss()) [MEM,exp_size_def]
  \\ DECIDE_TAC)    

val EqualityType_def = Define `
  EqualityType (abs:'a->v->bool) =
    (!x1 v1. abs x1 v1 ==> no_closures v1) /\
    !x1 v1 x2 v2. 
      abs x1 v1 /\ abs x2 v2 ==> ((v1 = v2) = (x1 = x2))`;

val Eq_def = Define `
  ((Eq abs):'a->v->bool) = \a v. EqualityType abs /\ abs a v`; 

val EqualityType_Eq = store_thm("EqualityType_Eq",
  ``!a. EqualityType (Eq a)``,
  SIMP_TAC std_ss [Eq_def,EqualityType_def] \\ METIS_TAC []);

val EqualityType_NUM_BOOL = store_thm("EqualityType_NUM_BOOL",
  ``EqualityType NUM /\ EqualityType BOOL``,
  EVAL_TAC \\ FULL_SIMP_TAC (srw_ss()) [no_closures_def]);

val Eval_Equality = store_thm("Eval_Equality",
  ``Eval env x1 (a y1) /\ Eval env x2 (a y2) ==>
    EqualityType a ==>
    Eval env (App Equality x1 x2) (BOOL (y1 = y2))``,
  SIMP_TAC std_ss [Eval_def,BOOL_def] \\ SIMP_TAC std_ss []
  \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss []
  \\ ONCE_REWRITE_TAC [evaluate_cases] \\ SIMP_TAC (srw_ss()) []
  \\ Q.LIST_EXISTS_TAC [`res`,`res'`]
  \\ FULL_SIMP_TAC (srw_ss()) [do_app_def]
  \\ ONCE_REWRITE_TAC [evaluate_cases] 
  \\ FULL_SIMP_TAC (srw_ss()) [EqualityType_def]);


(* a few misc. lemmas that help the automation *)

val PULL_EXISTS = save_thm("PULL_EXISTS",
  METIS_PROVE [] ``(((?x. P x) ==> Q) = !x. P x ==> Q) /\
                   (((?x. P x) /\ Q) = ?x. P x /\ Q) /\
                   ((Q /\ (?x. P x)) = ?x. Q /\ P x)``);

val evaluate_list_SIMP = store_thm("evaluate_list_SIMP",
  ``(evaluate_list' env [] (Rval []) = T) /\
    (evaluate_list' env (x::xs) (Rval (y::ys)) =
     evaluate' env x (Rval y) /\ evaluate_list' env xs (Rval ys))``,
  REPEAT STRIP_TAC \\ SIMP_TAC std_ss [Once evaluate_cases]
  \\ FULL_SIMP_TAC (srw_ss()) []);

val UNCURRY1 = prove(
  ``!f. UNCURRY f = \x. case x of (x,y) => f x y``,
  STRIP_TAC \\ FULL_SIMP_TAC std_ss [FUN_EQ_THM,pair_case_def]
  \\ Cases \\ FULL_SIMP_TAC std_ss [FUN_EQ_THM,pair_case_def]);

val UNCURRY2 = prove(
  ``!x y f. pair_case f x y = pair_case (\z1 z2. f z1 z2 y) x``,
  Cases \\ EVAL_TAC \\ SIMP_TAC std_ss []);

val UNCURRY3 = prove(
  ``pair_case f (x,y) = f x y``,
  EVAL_TAC) |> GEN_ALL;

val UNCURRY_SIMP = save_thm("UNCURRY_SIMP",
  LIST_CONJ [UNCURRY1,UNCURRY2,UNCURRY3]);

val num_case_thm = store_thm("num_case_thm",
  ``num_case = \b f n. if n = 0 then b else f (n-1)``,
  SIMP_TAC std_ss [FUN_EQ_THM,num_case_def] \\ Cases_on `n`
  \\ EVAL_TAC \\ SIMP_TAC std_ss []);

val _ = export_theory();

