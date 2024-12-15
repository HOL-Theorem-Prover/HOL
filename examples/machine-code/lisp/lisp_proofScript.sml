open HolKernel boolLib bossLib Parse; val _ = new_theory "lisp_proof";

open stringTheory finite_mapTheory pred_setTheory listTheory sumTheory;
open lisp_typeTheory lisp_semanticsTheory lisp_evalTheory;

val _ = numLib.temp_prefer_num();

(* translating the semantics' s-expressions into implementation s-expressions *)

val atom2sexp_def = Define `
  (atom2sexp Nil = Sym "nil") /\
  (atom2sexp (Number n) = Val n) /\
  (atom2sexp (String s) = Sym s)`;

val sexpression2sexp_def = Define `
  (sexpression2sexp (A a) = atom2sexp a) /\
  (sexpression2sexp (Cons x y) = Dot (sexpression2sexp x) (sexpression2sexp y))`;

val list2sexp_def = Define `
  (list2sexp [] = Sym "nil") /\
  (list2sexp (x::xs) = Dot x (list2sexp xs))`;

val x2sexp_def = tDefine "x2sexp" `
  (x2sexp (F,xx,FunCon s) = Sym s) /\
  (x2sexp (F,xx,FunVar s) = Sym s) /\
  (x2sexp (F,xx,Lambda vs x) =
     list2sexp [Sym "lambda"; list2sexp (MAP Sym vs); x2sexp (T,x,FunVar "nil")]) /\
  (x2sexp (F,xx,Label l f) = list2sexp [Sym "label"; Sym l; x2sexp (F,Var "nil",f)]) /\
  (x2sexp (T,Con y,yy) = list2sexp [Sym "quote"; sexpression2sexp y]) /\
  (x2sexp (T,Var v,yy) = Sym v) /\
  (x2sexp (T,App f xs,yy) = list2sexp (x2sexp (F,Var "nil",f) :: MAP (\x. x2sexp (T,x,FunVar "nil")) xs)) /\
  (x2sexp (T,Ite cs,yy) = list2sexp (Sym "cond" :: MAP (\ (t1,t2).
       list2sexp [x2sexp (T,t1,FunVar "nil"); x2sexp (T,t2,FunVar "nil")]) cs))`
 (WF_REL_TAC `measure (\(x,y,z). if x then term_size y else func_size z)`);

val x2sexp = x2sexp_def |> CONJUNCTS |> map SPEC_ALL |> LIST_CONJ

val term2sexp_def = save_thm(
  "func2sexp_def[allow_rebind]",
  save_thm(
    "term2sexp_def[allow_rebind]",
    let
      val term2sexp_deff = Define `term2sexp x = x2sexp (T,x,FunVar "nil")`;
      val func2sexp_deff = Define `func2sexp y = x2sexp (F,Var "nil",y)`;
      val th = Q.INST [`xx`|->`Var "nil"`,`yy`|->`FunVar "nil"`] x2sexp
      val th = REWRITE_RULE [GSYM term2sexp_deff,GSYM func2sexp_deff] th
    in th end));

val zip_yz_lemma = prove(
  ``!xs ys zs x (stack:SExp) alist (l:num).
      (LENGTH xs = LENGTH ys) ==>
      ?x' alist'. zip_yz (list2sexp zs,x,list2sexp xs,list2sexp ys,stack,alist,l) =
                  (list2sexp (REVERSE (MAP (\ (x,y). Dot x y) (ZIP (xs,ys))) ++ zs),x',list2sexp [],list2sexp [],stack,alist',l)``,
  Induct
  THEN Cases_on `ys` THEN SIMP_TAC std_ss [LENGTH,DECIDE ``~(SUC n = 0)``]
  THEN REWRITE_TAC [ZIP,MAP,APPEND,list2sexp_def,REVERSE_DEF]
  THEN ONCE_REWRITE_TAC [zip_yz_def]
  THEN REWRITE_TAC [isDot_def] THEN1 METIS_TAC []
  THEN SIMP_TAC std_ss [ZIP,MAP,list2sexp_def,APPEND,CAR_def,CDR_def,LET_DEF]
  THEN REWRITE_TAC [GSYM list2sexp_def]
  THEN REPEAT STRIP_TAC
  THEN RES_TAC
  THEN POP_ASSUM (STRIP_ASSUME_TAC o Q.SPECL [`Dot h' h::zs`,`list2sexp zs`,
        `stack`,`l`,`list2sexp zs`])
  THEN ASM_SIMP_TAC std_ss [GSYM APPEND_ASSOC,APPEND])

val LISP_LENGTH_def = Define `
  (LISP_LENGTH (Dot x y) = 1 + LISP_LENGTH y) /\
  (LISP_LENGTH (Val n) = 0) /\
  (LISP_LENGTH (Sym s) = 0)`;

val lisp_length_EQ = (REWRITE_RULE [DECIDE ``n + 0 = n``] o Q.SPEC `0` o prove) (
  ``!n x. ?x2. !y z stack alist l.
                 lisp_length (Val n,x,y,z,stack,alist,l:num) =
                   (Val (LISP_LENGTH x + n),x2,y,z,stack,alist,l)``,
  REVERSE (Induct_on `x`)
  THEN ONCE_REWRITE_TAC [lisp_length_def,LISP_LENGTH_def]
  THEN REWRITE_TAC [isDot_def,DECIDE ``(0 + n) = n``]
  THEN1 (METIS_TAC []) THEN1 (METIS_TAC [])
  THEN SIMP_TAC std_ss [CDR_def,LISP_ADD_def,LET_DEF]
  THEN REWRITE_TAC [DECIDE ``1 + m + n = m + (n + 1)``]
  THEN METIS_TAC []);

val lisp_ops_thm = prove(
  ``!exp x y zstack alist l.
      (lisp_numberp (exp,x,y,z,stack,alist,l) =
       (LISP_NUMBERP exp,x,y,z,stack,alist,l)) /\
      (lisp_symbolp (exp,x,y,z,stack,alist,l) =
       (LISP_SYMBOLP exp,x,y,z,stack,alist,l)) /\
      (lisp_consp (exp,x,y,z,stack,alist,l) =
       (LISP_CONSP exp,x,y,z,stack,alist,l)) /\
      (lisp_atomp (exp,x,y,z,stack,alist,l) =
       (LISP_ATOMP exp,x,y,z,stack,alist,l)) /\
      (lisp_less (Val m,Val n,y,z,stack,alist,l) =
       (LISP_LESS (Val m) (Val n),Val n,y,z,stack,alist,l))``,
  Cases
  THEN SIMP_TAC std_ss [LISP_SYMBOLP_def,LISP_NUMBERP_def,LISP_ATOMP_def,
    LISP_CONSP_def,LISP_TEST_def,isSym_def,isDot_def,isVal_def,LET_DEF,
    lisp_numberp_def,lisp_symbolp_def,lisp_atomp_def,lisp_consp_def,
    LISP_LESS_def,getVal_def,lisp_less_def] THEN METIS_TAC []);

val rev_exp_thm = prove(
  ``!ys xs x y stack alist l.
      rev_exp(list2sexp xs,x,y,list2sexp ys,stack,alist,l) =
        (list2sexp (REVERSE ys ++ xs),y,y,list2sexp [],stack,alist,l)``,
  Induct
  THEN REWRITE_TAC [list2sexp_def]
  THEN ONCE_REWRITE_TAC [rev_exp_def]
  THEN SIMP_TAC std_ss [isDot_def,LET_DEF,REVERSE_DEF,APPEND]
  THEN SIMP_TAC std_ss [CAR_def,CDR_def,GSYM APPEND_ASSOC,APPEND]
  THEN ASM_REWRITE_TAC [GSYM list2sexp_def]);

val reverse_exp_thm = prove(
  ``!xs x y stack alist l.
      reverse_exp(list2sexp xs,x,y,z,stack,alist,l) =
        (list2sexp (REVERSE xs),y,y,TASK_FUNC,stack,alist,l)``,
  SIMP_TAC std_ss [reverse_exp_def,LET_DEF,GSYM list2sexp_def,
    rev_exp_thm,APPEND_NIL]);

val LIST_LOOKUP_def = Define `
  (LIST_LOOKUP (x:string) [] = (FEMPTY ' x:(sexpression + func))) /\
  (LIST_LOOKUP x (y::ys) = if x = FST y then SND y else LIST_LOOKUP x ys)`;

val iFunBind_def =
 Define
  `iFunBind (a:(string # (sexpression + func)) list) f fn = (f, INR fn) :: a`;

val iVarBind_def =
 Define
  `(iVarBind a [] sl = (a : (string # (sexpression + func)) list)) /\
   (iVarBind a (x::xl) [] = iVarBind ((x,INL (A Nil)) :: a) xl []) /\
   (iVarBind a (x::xl) (s::sl) = iVarBind ((x, INL s) :: a) xl sl)`;

val (iR_ev_rules,iR_ev_ind,iR_ev_cases) =
 Hol_reln
 `(!s a.
    iR_ev (Con s, a) s)
  /\
  (!x a.
    MEM x (MAP FST a) /\ ISL (LIST_LOOKUP x a) ==>
    iR_ev (Var x, a) (OUTL(LIST_LOOKUP x a)))
  /\
  (!fc args a.
    FunConSemOK fc args ==>
    iR_ap (FunCon fc,args,a) (FunConSem fc args))
  /\
  (!fn el args s a.
    ~(MEM (func2sexp fn) [Sym "quote"; Sym "cond"]) /\
    iR_evl (el,a) args /\ iR_ap (fn,args,a) s /\ (LENGTH args = LENGTH el)
    ==> iR_ev (App fn el,a) s)
  /\
  (!a.
    iR_ev (Ite [], a) False)
  /\
  (!e1 e2 el s a.
    iR_ev (e1,a) False /\ iR_ev (Ite el,a) s
    ==> iR_ev (Ite ((e1,e2)::el),a) s)
  /\
  (!e1 e2 el s1 s a.
    iR_ev (e1,a) s1 /\ isTrue s1 /\ iR_ev (e2,a) s
    ==>
    iR_ev (Ite ((e1,e2)::el),a) s)
  /\
  (!x fn args s a.
    ~(MEM (func2sexp fn) [Sym "quote"; Sym "cond"]) /\
    iR_ap (fn,args,iFunBind a x fn) s ==> iR_ap(Label x fn,args,a) s)
  /\
  (!fv args s a.
    fv NOTIN {"quote";"cond";"car";"cdr";"cons";"+";"-";"*";"div";"mod";"<";
              "equal";"atomp";"consp";"symbolp";"numberp"} /\
    MEM fv (MAP FST a) /\ ISR (LIST_LOOKUP fv a) /\
    iR_ap (OUTR(LIST_LOOKUP fv a),args,a) s ==> iR_ap (FunVar fv,args,a) s)
  /\
  (!xl e args s a.
    (LENGTH args = LENGTH xl) /\
    (!a2. (FILTER (\x. ~(MEM (FST x) xl)) a = FILTER (\x. ~(MEM (FST x) xl)) a2) ==>
          iR_ev (e,iVarBind a2 xl args) s)
    ==> iR_ap (Lambda xl e,args,a) s)
  /\
  (!a.
    iR_evl ([],a) [])
  /\
  (!e el s sl a.
    iR_ev (e,a) s /\ iR_evl (el,a) sl
    ==> iR_evl (e::el,a) (s::sl))`;

val IF_LEMMA = prove(
  ``!b x y. (if b then x else y) <=> (b /\ x) \/ (~b /\ y)``,
  Cases THEN SIMP_TAC std_ss []);

val iR_ap_LEMMA = prove(
  ``iR_ap (fn,args,a) s ==> ~(MEM (func2sexp fn) [Sym "quote"; Sym "cond"])``,
  ONCE_REWRITE_TAC [iR_ev_cases]
  THEN SRW_TAC [] [term2sexp_def]
  THEN FULL_SIMP_TAC std_ss [FunConSemOK_def,IF_LEMMA]
  THEN EVAL_TAC THEN ASM_SIMP_TAC std_ss []);

val pair2sexp_def = Define `
  (pair2sexp (s, INL x) = Dot (Sym s) (sexpression2sexp x)) /\
  (pair2sexp (s, INR y) = Dot (Sym s) (func2sexp y))`;

val alist2sexp_def = Define `
  (alist2sexp al = list2sexp (MAP pair2sexp al))`;

val lisp_eval_ok_def = Define `
  lisp_eval_ok (exp_in,alist) exp_out =
    !x:SExp y:SExp stack:SExp l:num. ?x':SExp y':SExp.
      lisp_eval (term2sexp exp_in,x,y,TASK_EVAL,stack,alist2sexp alist,l) =
      lisp_eval (sexpression2sexp exp_out,x',y',TASK_CONT,stack,alist2sexp alist,l)`;

val lisp_func_ok_def = Define `
  lisp_func_ok (fn,args,alist) result =
    !y:SExp stack:SExp l:num. ?x':SExp y':SExp.
      lisp_eval (list2sexp (MAP sexpression2sexp args),func2sexp fn,y,TASK_FUNC,stack,alist2sexp alist,l) =
      lisp_eval (sexpression2sexp result,x',y',TASK_CONT,stack,alist2sexp alist,l)`;

val lookup_aux_lemma = prove(
  ``!x a t:SExp z:SExp q:SExp.
      MEM x (MAP FST a) ==>
      ?q' y'.
      (lookup_aux (Sym x,q,alist2sexp a,z,stack:SExp,t,l:num) =
        (if ISL (LIST_LOOKUP x a)
         then sexpression2sexp (OUTL (LIST_LOOKUP x a))
         else func2sexp (OUTR (LIST_LOOKUP x a)),
         q',y',z,stack,t,l))``,
  STRIP_TAC THEN Induct
  THEN SIMP_TAC std_ss [MAP,MEM]
  THEN NTAC 4 STRIP_TAC
  THEN Cases_on `x = FST h`
  THEN ASM_SIMP_TAC std_ss [LIST_LOOKUP_def,alist2sexp_def,MAP]
  THEN Cases_on `h` THEN Cases_on `r`
  THEN ONCE_REWRITE_TAC [lookup_aux_def]
  THEN SIMP_TAC std_ss [LET_DEF,pair2sexp_def,list2sexp_def,CAR_def,CDR_def]
  THEN FULL_SIMP_TAC std_ss [SExp_11]
  THEN POP_ASSUM MP_TAC
  THEN POP_ASSUM (ASSUME_TAC o Q.SPECL [`t`,`z`,`Sym q'`])
  THEN REPEAT STRIP_TAC
  THEN RES_TAC
  THEN ASM_REWRITE_TAC [GSYM alist2sexp_def]
  THEN METIS_TAC []);

val lisp_eval_hide_def = Define `lisp_eval_hide = lisp_eval`;

val sexpression2sexp_11 = prove(
  ``!u v. (sexpression2sexp u = sexpression2sexp v) =
          (delete_Nil u = delete_Nil v)``,
  Induct
  THEN Cases_on `v`
  THEN REPEAT (Cases_on `a`)
  THEN REPEAT (Cases_on `a'`)
  THEN REWRITE_TAC [sexpression2sexp_def,atom2sexp_def,
                    delete_Nil_def,delete_Nil_aux_def]
  THEN SRW_TAC [] []);

val LISP_EQUAL_THM = prove(
  ``!u v. (LISP_EQUAL (sexpression2sexp u) (sexpression2sexp v) =
           sexpression2sexp (Equal (u,v))) /\
          (LISP_CONSP (sexpression2sexp u) = sexpression2sexp (Consp u)) /\
          (LISP_ATOMP (sexpression2sexp u) = sexpression2sexp (Atomp u)) /\
          (LISP_SYMBOLP (sexpression2sexp u) = sexpression2sexp (Symbolp u)) /\
          (LISP_NUMBERP (sexpression2sexp u) = sexpression2sexp (Numberp u))``,
  REWRITE_TAC [LISP_EQUAL_def,Equal_def,sexpression2sexp_11,True_def,
    False_def,LISP_TEST_def,LISP_ATOMP_def,LISP_SYMBOLP_def,LISP_CONSP_def,
    LISP_NUMBERP_def,isDot_def,isSym_def,isVal_def]
  THEN REPEAT STRIP_TAC
  THEN1 SRW_TAC [] [delete_Nil_def,delete_Nil_aux_def,True_def,
          sexpression2sexp_def,atom2sexp_def,False_def]
  THEN Cases_on `u` THEN (Cases_on `a` ORELSE ALL_TAC)
  THEN REWRITE_TAC [isDot_def,isSym_def,isVal_def,sexpression2sexp_def,
         atom2sexp_def,Consp_def,False_def,True_def,Atomp_def,
         Symbolp_def,Numberp_def]);

val EVAL_ARGS_LEMMA = prove(
  ``!t h args fn a s x y xs.
      EVERY I (MAP (\(x,y). lisp_eval_ok (x,a) y) (ZIP (h::t,args))) /\
      (LENGTH args = LENGTH (h::t)) /\ ~(fn = Sym "cond") ==>
      ?x' y'.
        lisp_eval
          (term2sexp h,x,y,TASK_EVAL,
           Dot (Dot (list2sexp (MAP (\x. term2sexp x) t)) (list2sexp xs))
            (Dot fn stack),alist2sexp a,l) =
        lisp_eval_hide
          (list2sexp (REVERSE xs ++ MAP sexpression2sexp args),fn,fn,TASK_FUNC,stack,
           alist2sexp a,l)``,
  Induct
  THEN Cases_on `args`
  THEN SIMP_TAC std_ss [LENGTH,ZIP,MAP,EVERY_DEF]
  THEN REWRITE_TAC [DECIDE ``~(0 = SUC n)``]
  THEN REPEAT STRIP_TAC
  THENL [
    FULL_SIMP_TAC std_ss [lisp_eval_ok_def]
    THEN Q.PAT_X_ASSUM `!x y stack l. ?x'. bbb` (STRIP_ASSUME_TAC o Q.SPECL [`x`,`y`,`
      Dot (Dot (list2sexp []) (list2sexp xs)) (Dot fn stack)`,`l`])
    THEN ASM_SIMP_TAC std_ss []
    THEN ONCE_REWRITE_TAC [lisp_eval_def]
    THEN REWRITE_TAC [EVAL ``TASK_CONT = TASK_EVAL``]
    THEN REWRITE_TAC [EVAL ``TASK_CONT = TASK_FUNC``]
    THEN SIMP_TAC std_ss [SExp_distinct,lisp_cont_def]
    THEN ASM_SIMP_TAC std_ss [LET_DEF,isDot_def,CDR_def,CAR_def,list2sexp_def]
    THEN ASM_SIMP_TAC std_ss [LET_DEF,isDot_def,CDR_def,CAR_def,GSYM list2sexp_def]
    THEN SIMP_TAC std_ss [reverse_exp_thm,HD,lisp_eval_hide_def]
    THEN FULL_SIMP_TAC std_ss [LENGTH_NIL,MAP,REVERSE_DEF],
    FULL_SIMP_TAC std_ss [lisp_eval_ok_def]
    THEN Q.PAT_X_ASSUM `!x y stack l. ?x'. bbb` (STRIP_ASSUME_TAC o Q.SPECL [`x`,`y`,`
      Dot (Dot (list2sexp (term2sexp h'::MAP (\x. term2sexp x) t)) (list2sexp xs)) (Dot fn stack)`,`l`])
    THEN ASM_SIMP_TAC std_ss []
    THEN ONCE_REWRITE_TAC [lisp_eval_def]
    THEN REWRITE_TAC [EVAL ``TASK_CONT = TASK_EVAL``]
    THEN REWRITE_TAC [EVAL ``TASK_CONT = TASK_FUNC``]
    THEN SIMP_TAC std_ss [SExp_distinct,lisp_cont_def]
    THEN ASM_SIMP_TAC std_ss [LET_DEF,isDot_def,CDR_def,CAR_def,list2sexp_def]
    THEN ASM_SIMP_TAC std_ss [LET_DEF,isDot_def,CDR_def,CAR_def,GSYM list2sexp_def]
    THEN POP_ASSUM (K ALL_TAC)
    THEN `(LENGTH t' = LENGTH (h'::t))` by ASM_SIMP_TAC std_ss [LENGTH]
    THEN RES_TAC THEN ONCE_REWRITE_TAC [list2sexp_def]
    THEN ASM_REWRITE_TAC [REVERSE_DEF,GSYM APPEND_ASSOC,APPEND]]);

val LISP_LENGTH_THM = prove(
  ``!xs. LISP_LENGTH (list2sexp xs) = LENGTH xs``,
  Induct THEN ASM_SIMP_TAC std_ss [LISP_LENGTH_def,list2sexp_def,LENGTH]
  THEN DECIDE_TAC);

val repeat_cdr_1 = prove(
  ``repeat_cdr(exp,Val 1,y,z,stack,alist,l) =
      (exp,Val 0,y,z,stack,CDR alist,l)``,
  NTAC 2 (ONCE_REWRITE_TAC [repeat_cdr_def])
  THEN SIMP_TAC std_ss [LET_DEF,LISP_SUB_def,SExp_11]);

val iVarBind_EXISTS = prove(
  ``!a xl args. ?xs. (iVarBind a xl args = xs ++ a) /\ (LENGTH xs = LENGTH xl)``,
  Induct_on `xl` THEN Cases_on `args` THEN REWRITE_TAC [iVarBind_def]
  THEN1 (STRIP_TAC THEN Q.EXISTS_TAC `[]` THEN SIMP_TAC std_ss [APPEND,LENGTH])
  THEN1 (STRIP_TAC THEN Q.EXISTS_TAC `[]` THEN SIMP_TAC std_ss [APPEND,LENGTH])
  THEN REPEAT STRIP_TAC THEN1
    (POP_ASSUM (STRIP_ASSUME_TAC o Q.SPECL [`(h,INL (A Nil))::a`,`[]`])
     THEN Q.EXISTS_TAC `SNOC (h,INL (A Nil)) xs`
     THEN ASM_SIMP_TAC std_ss [LENGTH_SNOC,LENGTH]
     THEN ASM_SIMP_TAC std_ss [SNOC_APPEND,GSYM APPEND_ASSOC,APPEND])
  THEN POP_ASSUM (STRIP_ASSUME_TAC o Q.SPECL [`(h',INL h)::a`,`t`])
     THEN Q.EXISTS_TAC `SNOC (h',INL h) xs`
     THEN ASM_SIMP_TAC std_ss [LENGTH_SNOC,LENGTH]
     THEN ASM_SIMP_TAC std_ss [SNOC_APPEND,GSYM APPEND_ASSOC,APPEND]);

val sexpression_IF = prove(
  ``!b. sexpression2sexp (if b then True else False) = LISP_TEST b``,
  Cases THEN EVAL_TAC);

val lisp_add_lemma = prove(
  ``!args x m.
      (!x. MEM x args ==> ?n. x = A (Number n)) ==>
      ?q1 q2.
      lisp_add (Val m,x,list2sexp (MAP sexpression2sexp args),
        TASK_CONT,stack,alist2sexp a,l) =
      (sexpression2sexp (FOLDL Add (A (Number m)) args),q1,q2,TASK_CONT,
       stack,alist2sexp a,l)``,
  Induct
  THEN SIMP_TAC std_ss [MAP,list2sexp_def,FOLDL]
  THEN ONCE_REWRITE_TAC [lisp_add_def]
  THEN SIMP_TAC std_ss [LET_DEF,isDot_def,sexpression2sexp_def,atom2sexp_def]
  THEN SIMP_TAC std_ss [CAR_def,CDR_def,MEM]
  THEN REPEAT STRIP_TAC
  THEN `?n. h = A (Number n)` by METIS_TAC []
  THEN ASM_SIMP_TAC std_ss [LISP_ADD_def,FOLDL]
  THEN SIMP_TAC std_ss [LET_DEF,isDot_def,sexpression2sexp_def,atom2sexp_def]
  THEN ASM_SIMP_TAC std_ss [LISP_ADD_def,FOLDL,Add_def]
  THEN `!x. MEM x args ==> ?n. x = A (Number n)` by METIS_TAC []
  THEN RES_TAC THEN METIS_TAC []);

val lisp_mult_lemma = prove(
  ``!args x y m.
      (!x. MEM x args ==> ?n. x = A (Number n)) ==>
      ?q1 q2 q3.
      lisp_mult (Val m,x,y,list2sexp (MAP sexpression2sexp args),
        stack,alist2sexp a,l) =
      (sexpression2sexp (FOLDL Mult (A (Number m)) args),q1,q2,q3,
       stack,alist2sexp a,l)``,
  Induct
  THEN SIMP_TAC std_ss [MAP,list2sexp_def,FOLDL]
  THEN ONCE_REWRITE_TAC [lisp_mult_def]
  THEN SIMP_TAC std_ss [LET_DEF,isDot_def,sexpression2sexp_def,atom2sexp_def]
  THEN SIMP_TAC std_ss [CAR_def,CDR_def,MEM]
  THEN REPEAT STRIP_TAC
  THEN `?n. h = A (Number n)` by METIS_TAC []
  THEN ASM_SIMP_TAC std_ss [LISP_MULT_def,FOLDL]
  THEN SIMP_TAC std_ss [LET_DEF,isDot_def,sexpression2sexp_def,atom2sexp_def]
  THEN ASM_SIMP_TAC std_ss [LISP_MULT_def,FOLDL,Mult_def]
  THEN `!x. MEM x args ==> ?n. x = A (Number n)` by METIS_TAC []
  THEN RES_TAC THEN METIS_TAC []);

val LISP_REDUCE_AUX_def = Define `
  (LISP_REDUCE_AUX 0 xs alist = ((alist:(string # (sexpression + func)) list),Val 0)) /\
  (LISP_REDUCE_AUX n xs [] = ([],Val n)) /\
  (LISP_REDUCE_AUX (SUC n) xs ((y,z)::ys) =
    if MEM (Sym y) xs then LISP_REDUCE_AUX n xs ys
                else ((y,z)::ys,Val (SUC n)))`;

val LISP_REDUCE_A_def = Define `
  LISP_REDUCE_A (stack,xs,alist) =
    if isDot stack /\ isVal (CAR stack)
    then FST (LISP_REDUCE_AUX (getVal (CAR stack)) xs alist) else alist`;

val LISP_REDUCE_S_def = Define `
  LISP_REDUCE_S (stack,xs,alist) =
    if isDot stack /\ isVal (CAR stack)
    then let s = (SND (LISP_REDUCE_AUX (getVal (CAR stack)) xs alist)) in
      if s = Val 0 then CDR stack else Dot s (CDR stack)
    else stack`;

val lisp_find_in_list_thm = prove(
  ``!xs x.
      ?exp2 x2 y2.
      (lisp_find_in_list (CAR (pair2sexp (q,r)),x,list2sexp xs,z,stack,alist,l) =
         (exp2,x2,y2,z,stack,alist,l)) /\
      ((exp2 = Sym "nil") = ~MEM (Sym q) xs)``,
  Induct THEN ONCE_REWRITE_TAC [lisp_find_in_list_def]
  THEN ASM_SIMP_TAC std_ss [MEM,list2sexp_def,isDot_def,CAR_def,CDR_def,LET_DEF]
  THEN Cases_on `r` THEN FULL_SIMP_TAC std_ss [pair2sexp_def,CAR_def]
  THEN REPEAT STRIP_TAC THEN Cases_on `Sym q = h`
  THEN ASM_SIMP_TAC std_ss [EVAL ``Sym "t" = Sym "nil"``]);

val lisp_reduce_alist_aux_EQ = prove(
  ``!xs alist exp x y.
      ?exp2 x2 y2.
        lisp_reduce_alist_aux (exp,x,y,Val n,Dot (list2sexp xs) stack,alist2sexp alist,l) =
          let (alist,z) = LISP_REDUCE_AUX n xs alist in
            (exp2,x2,y2,z,Dot (list2sexp xs) stack,alist2sexp alist,l)``,
  Induct_on `n` THEN Cases_on `alist`
  THEN SIMP_TAC std_ss [alist2sexp_def,list2sexp_def,MAP,LISP_REDUCE_AUX_def,LET_DEF]
  THEN ONCE_REWRITE_TAC [lisp_reduce_alist_aux_def]
  THEN SIMP_TAC std_ss [SExp_11,isDot_def,DECIDE ``~(SUC n = 0)``,CAR_def,CDR_def,LET_DEF]
  THEN ASSUME_TAC (GEN_ALL lisp_find_in_list_thm) THEN REPEAT STRIP_TAC
  THEN Cases_on `h` THEN helperLib.SEP_I_TAC "lisp_find_in_list"
  THEN ASM_SIMP_TAC std_ss [LISP_REDUCE_AUX_def,LISP_SUB_def] THEN REPEAT STRIP_TAC
  THEN Cases_on `MEM (Sym q) xs` THEN ASM_SIMP_TAC std_ss [GSYM alist2sexp_def,LET_DEF]
  THEN FULL_SIMP_TAC std_ss [alist2sexp_def,MAP,list2sexp_def,CDR_def]
  THEN helperLib.SEP_I_TAC "lisp_reduce_alist_aux"
  THEN ASM_SIMP_TAC std_ss [LET_DEF] THEN METIS_TAC []);

val lisp_reduce_alist_EQ = prove(
  ``!stack exp xs x y z l alist.
      ?x2 z2.
        lisp_reduce_alist (exp,x,Dot (list2sexp xs) y,z,stack,alist2sexp alist,l) =
         (exp,x2,Dot (list2sexp xs) y,z2, LISP_REDUCE_S (stack,xs,alist),
          alist2sexp (LISP_REDUCE_A (stack,xs,alist)),l)``,
  STRIP_TAC
  THEN `?n s x1 x2. (stack = Sym s) \/ (stack = Dot x1 x2) \/ (stack = Val n)` by
         (Cases_on `stack` THEN ASM_SIMP_TAC std_ss [SExp_11,SExp_distinct] THEN METIS_TAC [])
  THEN ASM_SIMP_TAC std_ss [lisp_reduce_alist_def,
         LISP_REDUCE_A_def,LISP_REDUCE_S_def,isDot_def,LET_DEF,CAR_def,CDR_def]
  THEN `?n1 s1 x3 x4. (x1 = Sym s1) \/ (x1 = Dot x3 x4) \/ (x1 = Val n1)` by
         (Cases_on `x1` THEN ASM_SIMP_TAC std_ss [SExp_11,SExp_distinct] THEN METIS_TAC [])
  THEN FULL_SIMP_TAC std_ss [isDot_def,isSym_def,isVal_def]
  THEN REPEAT STRIP_TAC
  THEN STRIP_ASSUME_TAC (helperLib.MATCH_INST (SPEC_ALL lisp_reduce_alist_aux_EQ)
         ``lisp_reduce_alist_aux
       (Dot (list2sexp xs) (Dot (Dot exp x2) (Dot (list2sexp xs) y)),
        Dot (Dot exp x2) (Dot (list2sexp xs) y),list2sexp xs,Val n1,
        Dot (list2sexp xs) (Dot (Dot exp x2) (Dot (list2sexp xs) y)),
        alist2sexp alist,l)``)
  THEN ASM_SIMP_TAC std_ss [getVal_def,CDR_def,LET_DEF]
  THEN Cases_on `LISP_REDUCE_AUX n1 xs alist` THEN ASM_SIMP_TAC std_ss []
  THEN REPEAT STRIP_TAC THEN Cases_on `r = Val 0`
  THEN ASM_SIMP_TAC std_ss [CAR_def,CDR_def]);

val FILTER_LISP_REDUCE_A = prove(
  ``!a stack xl.
      FILTER (\x. ~MEM (FST x) xl) (LISP_REDUCE_A (stack,MAP Sym xl,a)) =
      FILTER (\x. ~MEM (FST x) xl) a``,
  SIMP_TAC std_ss [LISP_REDUCE_A_def]
  THEN Cases_on `stack` THEN ASM_SIMP_TAC std_ss [isDot_def,CAR_def]
  THEN Cases_on `S'` THEN ASM_SIMP_TAC std_ss [isVal_def,CAR_def,getVal_def]
  THEN Q.SPEC_TAC (`n`,`n`) THEN Induct_on `a`
  THEN Cases_on `n` THEN ASM_SIMP_TAC std_ss [FILTER,LISP_REDUCE_AUX_def]
  THEN Cases THEN ASM_SIMP_TAC std_ss [FILTER,LISP_REDUCE_AUX_def,MEM_MAP,SExp_11]
  THEN REPEAT STRIP_TAC THEN Cases_on `MEM q xl` THEN ASM_SIMP_TAC std_ss [FILTER]);

val repeat_cdr_thm = prove(
  ``!n exp y z stack a l.
      (repeat_cdr (exp,Val n,y,z,stack,a,l) =
                  (exp,Val 0,y,z,stack,FUNPOW CDR n a,l))``,
  Induct THEN ONCE_REWRITE_TAC [repeat_cdr_def]
  THEN REWRITE_TAC [iVarBind_def,APPEND]
  THEN SIMP_TAC std_ss [SExp_11,DECIDE ``~(SUC n = 0)``,LET_DEF,arithmeticTheory.FUNPOW]
  THEN ASM_SIMP_TAC std_ss [LISP_SUB_def]);

val FUNPOW_CDR_iVarBind = prove(
  ``!a xs ys. FUNPOW CDR (LENGTH xs) (alist2sexp (iVarBind a xs ys)) = alist2sexp a``,
  REPEAT STRIP_TAC THEN STRIP_ASSUME_TAC (Q.SPECL [`a`,`xs`,`ys`] iVarBind_EXISTS)
  THEN POP_ASSUM (ASSUME_TAC o GSYM) THEN ASM_SIMP_TAC std_ss []
  THEN Q.SPEC_TAC (`xs'`,`ts`) THEN REPEAT (POP_ASSUM (K ALL_TAC))
  THEN Induct THEN SIMP_TAC std_ss [arithmeticTheory.FUNPOW,LENGTH,APPEND]
  THEN Cases_on `h` THEN Cases_on `r`
  THEN FULL_SIMP_TAC std_ss [MAP,pair2sexp_def,list2sexp_def,CDR_def,alist2sexp_def]);

val LISP_REDUCE_AUX_IMP = prove(
  ``!n a x alist m.
      (LISP_REDUCE_AUX n x a = (alist,m)) ==>
      getVal m <= n /\ isVal m /\
      (alist2sexp alist = FUNPOW CDR (n - getVal m) (alist2sexp a))``,
  Induct THEN Cases_on `a`
  THEN SIMP_TAC std_ss [LISP_REDUCE_AUX_def,getVal_def,arithmeticTheory.FUNPOW,isVal_def]
  THEN Cases_on `h`
  THEN SIMP_TAC std_ss [LISP_REDUCE_AUX_def,getVal_def,arithmeticTheory.FUNPOW]
  THEN REVERSE (Cases_on `MEM (Sym q) x`)
  THEN ASM_SIMP_TAC std_ss [getVal_def,arithmeticTheory.FUNPOW,isVal_def]
  THEN REPEAT STRIP_TAC THEN RES_TAC THEN1 DECIDE_TAC
  THEN `SUC n - getVal m = SUC (n - getVal m)` by DECIDE_TAC
  THEN ASM_SIMP_TAC std_ss [arithmeticTheory.FUNPOW]
  THEN ASM_SIMP_TAC std_ss [alist2sexp_def,MAP,list2sexp_def,CDR_def]);

val iR_ev_LEMMA = let
  val th = iR_ev_ind
  val th = Q.SPECL [`lisp_eval_ok`,`lisp_func_ok`,
            `\(xl,a) yl. EVERY I (MAP (\(x,y). lisp_eval_ok (x,a) y) (ZIP (xl,yl)))`] th
  val th = SIMP_RULE std_ss [ZIP,MAP,EVERY_DEF] th
  val goal = (fst o dest_imp o concl) th
  val INIT_TAC = SIMP_TAC std_ss [lisp_func_ok_def,lisp_eval_ok_def,term2sexp_def,list2sexp_def]
    THEN REPEAT STRIP_TAC
    THEN CONV_TAC ((QUANT_CONV o QUANT_CONV) (RAND_CONV
           (REWRITE_CONV [GSYM lisp_eval_hide_def])))
    THEN ONCE_REWRITE_TAC [lisp_eval_def]
  val th = (hd o CONJUNCTS o MP th o prove) (goal,
  STRIP_TAC THEN1
   (INIT_TAC
    THEN REWRITE_TAC [isSym_def,isDot_def]
    THEN SIMP_TAC std_ss [CAR_def,CDR_def,LET_DEF]
    THEN SIMP_TAC std_ss [lisp_app_def,LET_DEF,CAR_def]
    THEN REWRITE_TAC [lisp_eval_hide_def] THEN METIS_TAC [])
  THEN STRIP_TAC THEN1
   (INIT_TAC
    THEN REWRITE_TAC [isSym_def,lisp_lookup_def]
    THEN SIMP_TAC std_ss [LET_DEF]
    THEN STRIP_ASSUME_TAC (UNDISCH (Q.SPECL [`x`,`a`,`alist2sexp a`,`TASK_CONT`,`x'`] lookup_aux_lemma))
    THEN ASM_REWRITE_TAC []
    THEN SIMP_TAC std_ss []
    THEN REWRITE_TAC [lisp_eval_hide_def] THEN METIS_TAC [])
  THEN STRIP_TAC THEN1
   (INIT_TAC
    THEN REWRITE_TAC [EVAL ``TASK_FUNC = TASK_EVAL``]
    THEN FULL_SIMP_TAC std_ss [IF_LEMMA,FunConSemOK_def]
    THEN REWRITE_TAC [list2sexp_def,sexpression2sexp_def,MAP,FunConSem_def]
    THEN REWRITE_TAC [EVAL ``EL 0 (x::xs)``,EVAL ``EL 1 (x::y::zs)``,Cdr_def,Car_def]
    THEN ONCE_REWRITE_TAC [lisp_func_def]
    THEN SIMP_TAC std_ss [isDot_def,CDR_def,CAR_def,LET_DEF,SExp_11,lisp_ops_thm]
    THEN CONV_TAC (DEPTH_CONV stringLib.string_EQ_CONV)
    THEN SIMP_TAC std_ss [LISP_EQUAL_THM,Add_def,Sub_def,Mult_def,Div_def,Mod_def,
           sexpression2sexp_def,atom2sexp_def,LISP_ADD_def,LISP_SUB_def,LISP_MULT_def,LISP_DIV_def,LISP_MOD_def,
           lisp_ops_thm,Less_def,LISP_LESS_def,getVal_def,sexpression_IF]
    THEN IMP_RES_TAC ((Q.SPECL [`args`,`Sym "+"`,`0`] lisp_add_lemma))
    THEN POP_ASSUM (STRIP_ASSUME_TAC o SPEC_ALL)
    THEN IMP_RES_TAC ((Q.SPECL [`args`,`Sym "*"`,`y`,`1`] lisp_mult_lemma))
    THEN POP_ASSUM (STRIP_ASSUME_TAC o SPEC_ALL)
    THEN ASM_SIMP_TAC std_ss []
    THEN ASM_REWRITE_TAC [lisp_eval_hide_def] THEN METIS_TAC [])
  THEN STRIP_TAC THEN1
   (INIT_TAC
    THEN SIMP_TAC std_ss [LET_DEF,isSym_def,isDot_def,CDR_def,CAR_def]
    THEN ONCE_REWRITE_TAC [lisp_app_def]
(*    THEN IMP_RES_TAC iR_ap_LEMMA  *)
    THEN FULL_SIMP_TAC std_ss [MEM]
    THEN Cases_on `el = []` THEN1
     (FULL_SIMP_TAC std_ss [list2sexp_def,MAP,isDot_def,LET_DEF]
      THEN FULL_SIMP_TAC std_ss [LENGTH,LENGTH_NIL,list2sexp_def,MAP]
      THEN Q.PAT_X_ASSUM `!x.bbb` (STRIP_ASSUME_TAC o Q.SPECL [`y`,`stack`,`l`])
      THEN FULL_SIMP_TAC std_ss [LENGTH,LENGTH_NIL,list2sexp_def,MAP]
      THEN (REWRITE_TAC [lisp_eval_hide_def] THEN METIS_TAC []))
    THEN Cases_on `el` THEN FULL_SIMP_TAC std_ss []
    THEN SIMP_TAC std_ss [MAP,list2sexp_def,isDot_def,CAR_def,CDR_def,LET_DEF]
    THEN FULL_SIMP_TAC std_ss [GSYM lisp_eval_ok_def, GSYM lisp_func_ok_def]
    THEN IMP_RES_TAC (REWRITE_RULE [REVERSE_DEF,APPEND,list2sexp_def] (Q.INST [`xs`|->`[]`] (SPEC_ALL EVAL_ARGS_LEMMA)))
    THEN ASM_SIMP_TAC std_ss []
    THEN FULL_SIMP_TAC std_ss [lisp_func_ok_def]
    THEN METIS_TAC [lisp_eval_hide_def])
  THEN STRIP_TAC THEN1
   (INIT_TAC
    THEN SIMP_TAC std_ss [isDot_def,isSym_def,CAR_def,CDR_def,LET_DEF,MAP,list2sexp_def]
    THEN ONCE_REWRITE_TAC [lisp_app_def]
    THEN SIMP_TAC std_ss [SExp_11,EVAL ``"cond" = "quote"``,isDot_def]
    THEN SIMP_TAC std_ss [False_def,sexpression2sexp_def,atom2sexp_def,lisp_eval_hide_def]
    THEN METIS_TAC [])
  THEN STRIP_TAC THEN1
   (INIT_TAC
    THEN SIMP_TAC std_ss [isDot_def,isSym_def,CAR_def,CDR_def,LET_DEF,MAP,list2sexp_def]
    THEN ONCE_REWRITE_TAC [lisp_app_def]
    THEN SIMP_TAC std_ss [SExp_11,EVAL ``"cond" = "quote"``,isDot_def]
    THEN SIMP_TAC std_ss [False_def,sexpression2sexp_def,atom2sexp_def,
           lisp_eval_hide_def,LET_DEF,CAR_def]
    THEN POP_ASSUM MP_TAC
  (*  THEN POP_ASSUM (K ALL_TAC) *)
    THEN POP_ASSUM (STRIP_ASSUME_TAC o Q.SPECL [`Dot (Sym "cond") stack`,`y`,`Dot
       (Dot (Dot (term2sexp e1) (Dot (term2sexp e2) (Sym "nil")))
          (list2sexp (MAP
             (\(t1,t2). Dot (term2sexp t1) (Dot (term2sexp t2) (Sym "nil")))
                el))) (Dot (Sym "cond") stack)`,`l`])
    THEN ASM_SIMP_TAC std_ss [] THEN POP_ASSUM (K ALL_TAC)
    THEN STRIP_TAC
    THEN SIMP_TAC std_ss [sexpression2sexp_def,False_def,atom2sexp_def]
    THEN CONV_TAC ((QUANT_CONV o QUANT_CONV o RATOR_CONV) (ONCE_REWRITE_CONV [lisp_eval_def]))
    THEN REWRITE_TAC [EVAL ``TASK_CONT = TASK_FUNC``]
    THEN REWRITE_TAC [EVAL ``TASK_CONT = TASK_EVAL``]
    THEN SIMP_TAC std_ss [LET_DEF,SExp_distinct]
    THEN SIMP_TAC std_ss [lisp_cont_def,LET_DEF,CDR_def,CAR_def,isDot_def]
    THEN METIS_TAC [])
  THEN STRIP_TAC THEN1
   (INIT_TAC
    THEN SIMP_TAC std_ss [isDot_def,isSym_def,CAR_def,CDR_def,LET_DEF,MAP,list2sexp_def]
    THEN ONCE_REWRITE_TAC [lisp_app_def]
    THEN SIMP_TAC std_ss [SExp_11,EVAL ``"cond" = "quote"``,isDot_def]
    THEN SIMP_TAC std_ss [False_def,sexpression2sexp_def,atom2sexp_def,
           lisp_eval_hide_def,LET_DEF,CAR_def]
    THEN POP_ASSUM MP_TAC
 (*   THEN POP_ASSUM (K ALL_TAC) *)
    THEN POP_ASSUM MP_TAC
    THEN POP_ASSUM (STRIP_ASSUME_TAC o Q.SPECL [`Dot (Sym "cond") stack`,`y`,`Dot
       (Dot (Dot (term2sexp e1) (Dot (term2sexp e2) (Sym "nil")))
          (list2sexp (MAP
             (\(t1,t2). Dot (term2sexp t1) (Dot (term2sexp t2) (Sym "nil")))
                el))) (Dot (Sym "cond") stack)`,`l`])
    THEN ASM_SIMP_TAC std_ss [] THEN POP_ASSUM (K ALL_TAC)
    THEN SIMP_TAC std_ss [isTrue_def,False_def]
    THEN STRIP_TAC THEN STRIP_TAC
    THEN SIMP_TAC std_ss [sexpression2sexp_def,False_def,atom2sexp_def]
    THEN CONV_TAC ((QUANT_CONV o QUANT_CONV o RATOR_CONV) (ONCE_REWRITE_CONV [lisp_eval_def]))
    THEN REWRITE_TAC [EVAL ``TASK_CONT = TASK_FUNC``]
    THEN REWRITE_TAC [EVAL ``TASK_CONT = TASK_EVAL``]
    THEN SIMP_TAC std_ss [LET_DEF,SExp_distinct]
    THEN SIMP_TAC std_ss [lisp_cont_def,LET_DEF,CDR_def,CAR_def,isDot_def]
    THEN `sexpression2sexp s1 <> Sym "nil"` by
      (Cases_on `s1` THEN (Cases_on `a'` ORELSE ALL_TAC)
       THEN SRW_TAC [] [sexpression2sexp_def,atom2sexp_def])
    THEN ASM_SIMP_TAC std_ss [] THEN METIS_TAC [])
  THEN STRIP_TAC THEN1
   (INIT_TAC
    THEN REWRITE_TAC [EVAL ``TASK_FUNC = TASK_EVAL``]
    THEN ONCE_REWRITE_TAC [lisp_func_def]
    THEN SIMP_TAC std_ss [LET_DEF,isDot_def,CAR_def,CDR_def]
    THEN REWRITE_TAC [EVAL ``Sym "label" = Sym "lambda"``]
    THEN POP_ASSUM (STRIP_ASSUME_TAC o Q.SPECL
      [`Dot (Sym x) (Dot (func2sexp fn) (Sym "nil"))`,`Dot (Val 1) stack`,`l`])
    THEN POP_ASSUM (ASSUME_TAC o CONV_RULE (RAND_CONV
           (ONCE_REWRITE_CONV [GSYM lisp_eval_hide_def]) THENC
           ONCE_REWRITE_CONV [lisp_eval_def] THENC
           REWRITE_CONV [EVAL ``TASK_FUNC = TASK_EVAL``] THENC
           SIMP_CONV std_ss [LET_DEF,iFunBind_def,alist2sexp_def,MAP,
              pair2sexp_def,list2sexp_def] THENC
           REWRITE_CONV [GSYM alist2sexp_def,lisp_eval_hide_def]))
    THEN ASM_SIMP_TAC std_ss []
    THEN ONCE_REWRITE_TAC [lisp_eval_def]
    THEN REWRITE_TAC [EVAL ``TASK_CONT = TASK_FUNC``]
    THEN REWRITE_TAC [EVAL ``TASK_CONT = TASK_EVAL``]
    THEN SIMP_TAC std_ss [LET_DEF,SExp_distinct]
    THEN SIMP_TAC std_ss [lisp_cont_def,LET_DEF,CDR_def,CAR_def,isDot_def,repeat_cdr_1]
    THEN REWRITE_TAC [lisp_eval_hide_def] THEN METIS_TAC [])
  THEN STRIP_TAC THEN1
   (INIT_TAC
    THEN REWRITE_TAC [EVAL ``TASK_FUNC = TASK_EVAL``]
    THEN ONCE_REWRITE_TAC [lisp_func_def]
    THEN SIMP_TAC std_ss [CAR_def,CDR_def,isDot_def,isSym_def,list2sexp_def,SExp_11]
    THEN FULL_SIMP_TAC std_ss [IN_INSERT,LET_DEF,lisp_lookup_def]
    THEN IMP_RES_TAC lookup_aux_lemma
    THEN POP_ASSUM (STRIP_ASSUME_TAC o Q.SPECL [`list2sexp (MAP sexpression2sexp args)`,`alist2sexp a`,`stack`,`Sym fv`,`l`])
    THEN ASM_REWRITE_TAC []
    THEN POP_ASSUM (K ALL_TAC)
    THEN Cases_on `LIST_LOOKUP fv a`
    THEN FULL_SIMP_TAC std_ss [ISR,ISL]
    THEN POP_ASSUM (K ALL_TAC)
    THEN POP_ASSUM (STRIP_ASSUME_TAC o Q.SPECL [`y'`,`stack`,`l`])
    THEN POP_ASSUM (ASSUME_TAC o CONV_RULE (RAND_CONV
           (ONCE_REWRITE_CONV [GSYM lisp_eval_hide_def]) THENC
           ONCE_REWRITE_CONV [lisp_eval_def] THENC
           REWRITE_CONV [EVAL ``TASK_FUNC = TASK_EVAL``] THENC
           SIMP_CONV std_ss [LET_DEF,iFunBind_def,alist2sexp_def,MAP,
              pair2sexp_def,list2sexp_def] THENC
           REWRITE_CONV [GSYM alist2sexp_def,lisp_eval_hide_def]))
    THEN ASM_SIMP_TAC std_ss []
    THEN REWRITE_TAC [lisp_eval_hide_def] THEN METIS_TAC [])
  THEN
   (INIT_TAC
    THEN REWRITE_TAC [EVAL ``TASK_FUNC = TASK_EVAL``]
    THEN ONCE_REWRITE_TAC [lisp_func_def]
    THEN SIMP_TAC std_ss [CAR_def,CDR_def,isDot_def,isSym_def,list2sexp_def,SExp_11]
    THEN FULL_SIMP_TAC std_ss [IN_INSERT,LET_DEF,CAR_def,CDR_def]
    THEN ASSUME_TAC (GEN_ALL lisp_reduce_alist_EQ)
    THEN helperLib.SEP_I_TAC "lisp_reduce_alist"
    THEN ASM_SIMP_TAC std_ss []
    THEN STRIP_ASSUME_TAC (Q.SPEC `list2sexp (MAP sexpression2sexp args)` lisp_length_EQ)
    THEN ASM_SIMP_TAC std_ss []
    THEN SIMP_TAC std_ss [CAR_def,CDR_def,isDot_def,isSym_def,list2sexp_def,SExp_11]
    THEN FULL_SIMP_TAC std_ss [IN_INSERT,LET_DEF,CAR_def,CDR_def]
    THEN REWRITE_TAC [alist2sexp_def,LISP_LENGTH_THM,LENGTH_MAP]
    THEN Q.PAT_X_ASSUM `LENGTH args = LENGTH xl` (ASSUME_TAC o GSYM)
    THEN SIMP_TAC std_ss [CAR_def,CDR_def,isDot_def,isSym_def,list2sexp_def,SExp_11]
    THEN ASSUME_TAC (GEN_ALL zip_yz_lemma) THEN helperLib.SEP_I_TAC "zip_yz"
    THEN POP_ASSUM MP_TAC THEN ASM_SIMP_TAC std_ss [LENGTH_MAP]
    THEN REPEAT STRIP_TAC THEN ASM_SIMP_TAC std_ss [CAR_def,CDR_def]
    THEN POP_ASSUM (K ALL_TAC)
    THEN `!zs. list2sexp (REVERSE
          (MAP (\(x,y). Dot x y)
             (ZIP (MAP Sym xl,MAP sexpression2sexp args))) ++
           MAP pair2sexp zs) =
          alist2sexp (iVarBind zs xl args)` by
     (Q.PAT_X_ASSUM `LENGTH xl = LENGTH args` MP_TAC
      THEN Q.SPEC_TAC (`xl`,`xs`)
      THEN Q.SPEC_TAC (`args`,`ys`)
      THEN REPEAT (POP_ASSUM (K ALL_TAC))
      THEN Induct
      THEN Cases_on `xs` THEN SIMP_TAC std_ss [LENGTH,DECIDE ``~(SUC n = 0)``]
      THEN SIMP_TAC std_ss [ZIP,MAP,REVERSE_DEF,APPEND,iVarBind_def,alist2sexp_def,GSYM APPEND_ASSOC,GSYM pair2sexp_def]
      THEN REWRITE_TAC [GSYM MAP]
      THEN REPEAT STRIP_TAC THEN RES_TAC
      THEN ASM_SIMP_TAC std_ss [alist2sexp_def])
    THEN ASM_SIMP_TAC std_ss [] THEN POP_ASSUM (K ALL_TAC)
    THEN POP_ASSUM MP_TAC
    THEN POP_ASSUM (K ALL_TAC)
    THEN STRIP_TAC
    THEN Q.PAT_X_ASSUM `!a2.bbb` (ASSUME_TAC o
            Q.SPEC `LISP_REDUCE_A (stack,MAP Sym xl,a)`)
    THEN FULL_SIMP_TAC std_ss [FILTER_LISP_REDUCE_A]
    THEN Q.PAT_X_ASSUM `!x.bbb` (STRIP_ASSUME_TAC o Q.SPECL
          [`x'`,`list2sexp []`,`Dot (Val (LENGTH (args:sexpression list)))
                                    (LISP_REDUCE_S (stack,MAP Sym xl,a))`,`l`])
    THEN ASM_REWRITE_TAC [] THEN POP_ASSUM (K ALL_TAC)
    THEN ONCE_REWRITE_TAC [lisp_eval_def]
    THEN REWRITE_TAC [EVAL ``TASK_CONT = TASK_EVAL``]
    THEN REWRITE_TAC [EVAL ``TASK_CONT = TASK_FUNC``]
    THEN SIMP_TAC std_ss [SExp_distinct,lisp_cont_def,LET_DEF,isDot_def,CDR_def,CAR_def]
    THEN SIMP_TAC std_ss [repeat_cdr_thm]
    THEN POP_ASSUM (ASSUME_TAC o GSYM) THEN ASM_SIMP_TAC std_ss []
    THEN ASM_SIMP_TAC std_ss [FUNPOW_CDR_iVarBind,GSYM alist2sexp_def]
    THEN SIMP_TAC std_ss [LISP_REDUCE_S_def,LISP_REDUCE_A_def]
    THEN REVERSE (Cases_on `isDot stack /\ isVal (CAR stack)`)
    THEN1 (FULL_SIMP_TAC std_ss [lisp_eval_hide_def] THEN METIS_TAC [])
    THEN FULL_SIMP_TAC std_ss []
    THEN `?n s2. stack = Dot (Val n) s2` by METIS_TAC [isVal_thm,isDot_thm,CAR_def]
    THEN FULL_SIMP_TAC std_ss [CAR_def,CDR_def,getVal_def]
    THEN ONCE_REWRITE_TAC [ONCE_REWRITE_RULE [GSYM lisp_eval_hide_def] lisp_eval_def]
    THEN REWRITE_TAC [EVAL ``TASK_CONT = TASK_EVAL``]
    THEN REWRITE_TAC [EVAL ``TASK_CONT = TASK_FUNC``,isDot_def]
    THEN SIMP_TAC std_ss [lisp_cont_def,LET_DEF,CAR_def,CDR_def,isDot_def,repeat_cdr_thm]
    THEN `?alist m. LISP_REDUCE_AUX n (MAP Sym xl) a = (alist,m)` by METIS_TAC [pairTheory.PAIR]
    THEN ASM_SIMP_TAC std_ss []
    THEN IMP_RES_TAC LISP_REDUCE_AUX_IMP
    THEN Cases_on `m = Val 0` THEN ASM_SIMP_TAC std_ss [getVal_def]
    THEN1 METIS_TAC [lisp_eval_hide_def]
    THEN ONCE_REWRITE_TAC [lisp_eval_def]
    THEN REWRITE_TAC [EVAL ``TASK_CONT = TASK_EVAL``]
    THEN REWRITE_TAC [EVAL ``TASK_CONT = TASK_FUNC``,isDot_def]
    THEN SIMP_TAC std_ss [lisp_cont_def,LET_DEF,CAR_def,CDR_def,isDot_def,repeat_cdr_thm]
    THEN `?i. m = Val i` by METIS_TAC [isVal_thm]
    THEN FULL_SIMP_TAC std_ss [SExp_11,isDot_def,repeat_cdr_thm,getVal_def]
    THEN `i + (n - i) = n` by DECIDE_TAC
    THEN FULL_SIMP_TAC std_ss [GSYM arithmeticTheory.FUNPOW_ADD,lisp_eval_hide_def]
    THEN METIS_TAC []))
  in th end;

val fmap2list_def = Define `
  fmap2list f = MAP (\x. (x,f ' x)) (SET_TO_LIST (FDOM f))`;

val list2fmap_def = Define `
  (list2fmap [] = FEMPTY) /\
  (list2fmap ((a,x)::xs) = (list2fmap xs) |+ (a,x))`;

val FDOM_list2sexp = prove(
  ``!xs x. x IN (FDOM (list2fmap xs)) <=> MEM x (MAP FST xs)``,
  Induct THEN (Cases_on `h` ORELSE ALL_TAC)
  THEN REWRITE_TAC [list2fmap_def,FDOM_FEMPTY,NOT_IN_EMPTY,MAP,MEM]
  THEN ASM_SIMP_TAC std_ss [FDOM_FUPDATE,IN_INSERT]);

val FDOM_fmap2list_list2fmap = prove(
  ``!f. FDOM (list2fmap (fmap2list f)) = FDOM f``,
  REWRITE_TAC [FDOM_list2sexp,EXTENSION]
  THEN SIMP_TAC std_ss [fmap2list_def]
  THEN SIMP_TAC std_ss [MEM_MAP,fmap2list_def,MEM_SET_TO_LIST,FDOM_FINITE]
  THEN METIS_TAC [pairTheory.FST]);

val list2fmap_fmap2list = prove(
  ``!f:('a |-> 'b). list2fmap (fmap2list f) = f``,
  REWRITE_TAC [fmap_EXT]
  THEN REWRITE_TAC [FDOM_fmap2list_list2fmap,EXTENSION]
  THEN REWRITE_TAC [fmap2list_def]
  THEN STRIP_TAC
  THEN `FINITE (FDOM f)` by REWRITE_TAC [FDOM_FINITE]
  THEN POP_ASSUM MP_TAC
  THEN Q.SPEC_TAC (`FDOM f`,`d`)
  THEN Induct_on `CARD d` THEN STRIP_TAC
  THEN1 METIS_TAC [CARD_EQ_0,NOT_IN_EMPTY]
  THEN Cases_on `d = {}` THEN ASM_SIMP_TAC std_ss [CARD_EMPTY,numTheory.NOT_SUC]
  THEN IMP_RES_TAC CHOICE_INSERT_REST
  THEN REPEAT STRIP_TAC
  THEN IMP_RES_TAC SET_TO_LIST_THM
  THEN ASM_SIMP_TAC std_ss [MAP,list2fmap_def,FAPPLY_FUPDATE_THM]
  THEN Cases_on `x = CHOICE d` THEN ASM_SIMP_TAC std_ss []
  THEN `FINITE (REST d)` by METIS_TAC [FINITE_INSERT]
  THEN `v = CARD (REST d)` by (
    `SUC v = SUC (CARD (REST d))` by METIS_TAC [CARD_INSERT,CHOICE_NOT_IN_REST]
    THEN FULL_SIMP_TAC std_ss [])
  THEN RES_TAC THEN METIS_TAC [IN_INSERT]);

val list2fmap_APPLY = prove(
  ``!xs x. list2fmap xs ' x = LIST_LOOKUP x xs``,
  Induct THEN (Cases_on `h` ORELSE ALL_TAC)
  THEN REWRITE_TAC [list2fmap_def,LIST_LOOKUP_def]
  THEN ASM_SIMP_TAC std_ss [FAPPLY_FUPDATE_THM]);

val LIST_LOOKUP_INTRO = prove(
  ``!x a. a ' x = LIST_LOOKUP x (fmap2list a)``,
  METIS_TAC [list2fmap_fmap2list,list2fmap_APPLY]);

val iR_PERM_def = Define `
  iR_PERM x y = (list2fmap x = list2fmap y)`;

val iR_PERM_EQ = prove(
  ``!xs a. iR_PERM xs (fmap2list a) = (a = list2fmap xs)``,
  METIS_TAC [iR_PERM_def,list2fmap_fmap2list]);

val LIST_LOOKUP_fmap2list_list2fmap = prove(
  ``!xs x. LIST_LOOKUP x (fmap2list (list2fmap xs)) =
           LIST_LOOKUP x xs``,
  REWRITE_TAC [GSYM LIST_LOOKUP_INTRO]
  THEN Induct THEN (Cases_on `h` ORELSE ALL_TAC)
  THEN REWRITE_TAC [list2fmap_def,LIST_LOOKUP_def]
  THEN ASM_SIMP_TAC std_ss [FAPPLY_FUPDATE_THM]);

val FILTER_T = prove(
  ``!xs. FILTER (\x. T) xs = xs``,
  Induct THEN SRW_TAC [] []);

val list2fmap_iVarBind = prove(
  ``!xs ys zs. list2fmap (iVarBind xs ys zs) = VarBind (list2fmap xs) ys zs``,
  Induct_on `ys` THEN SIMP_TAC std_ss [iVarBind_def,VarBind_def]
  THEN Cases_on `zs` THEN ASM_SIMP_TAC std_ss [iVarBind_def,VarBind_def,list2fmap_def]);

val VarBind_EQ = prove(
  ``!xs ys f1 f2.
      (DRESTRICT f1 (COMPL (LIST_TO_SET xs)) =
       DRESTRICT f2 (COMPL (LIST_TO_SET xs))) ==>
      (VarBind f1 xs ys = VarBind f2 xs ys)``,
  Induct THEN SIMP_TAC std_ss [VarBind_def,MEM,LIST_TO_SET_THM]
  THEN1 SRW_TAC [] [DRESTRICT_UNIV] THEN Cases_on `ys`
  THEN SIMP_TAC std_ss [VarBind_def,MEM,LIST_TO_SET_THM]
  THEN REPEAT STRIP_TAC THEN Q.PAT_X_ASSUM `!ys. bbb` MATCH_MP_TAC
  THEN FULL_SIMP_TAC std_ss [GSYM fmap_EQ_THM,DRESTRICT_DEF,IN_INTER,IN_COMPL,IN_INSERT,EXTENSION,FDOM_FUPDATE,FAPPLY_FUPDATE_THM]
  THEN METIS_TAC []);

val DRESTRICT_list2fmap = prove(
  ``!xs ys. DRESTRICT (list2fmap xs) (COMPL (set ys)) =
            list2fmap (FILTER (\x. ~MEM (FST x) ys) xs)``,
  Induct THEN SIMP_TAC std_ss [list2fmap_def,FILTER,DRESTRICT_FEMPTY]
  THEN Cases THEN SIMP_TAC std_ss [list2fmap_def,DRESTRICT_FUPDATE]
  THEN ASM_SIMP_TAC std_ss [IN_COMPL]
  THEN Cases_on `MEM q ys` THEN ASM_SIMP_TAC std_ss [list2fmap_def]);

val R_ev_LEMMA = let
  val th = Q.SPECL [`\(e,a) s. !xs. iR_PERM xs (fmap2list a) ==> iR_ev (e,xs) s`,
                    `\(fn,args,a) s. !xs. iR_PERM xs (fmap2list a) ==> iR_ap (fn,args,xs) s`,
                    `\(xl,a) yl. !xs. iR_PERM xs (fmap2list a) ==> iR_evl (xl,xs) yl`] R_ev_ind
  val th = SIMP_RULE std_ss [ZIP,MAP,EVERY_DEF] th
  val goal = (fst o dest_imp o concl) th
  val th = (hd o CONJUNCTS o MP th o prove) (goal,
  REPEAT STRIP_TAC THEN REWRITE_TAC [iR_ev_rules]
  THEN IMP_RES_TAC iR_ev_rules THEN ASM_SIMP_TAC std_ss []
  THEN FULL_SIMP_TAC std_ss [MEM,IN_INSERT,NOT_IN_EMPTY]
  THEN REPEAT (Q.PAT_X_ASSUM `T` (K ALL_TAC))
  THEN RES_TAC
  THEN1
   (FULL_SIMP_TAC std_ss [LIST_LOOKUP_INTRO,iR_PERM_EQ]
    THEN FULL_SIMP_TAC bool_ss [LIST_LOOKUP_fmap2list_list2fmap]
    THEN MATCH_MP_TAC (el 2 (CONJUNCTS iR_ev_rules))
    THEN ASM_SIMP_TAC std_ss [GSYM FDOM_list2sexp])
  THEN1 (METIS_TAC [iR_ev_rules,iR_ap_LEMMA])
  THEN1
   (MATCH_MP_TAC (el 6 (CONJUNCTS iR_ev_rules)) THEN ASM_SIMP_TAC std_ss [])
  THEN1
   (MATCH_MP_TAC (el 8 (CONJUNCTS iR_ev_rules)) THEN ASM_SIMP_TAC std_ss []
    THEN MATCH_MP_TAC (METIS_PROVE [] ``((c ==> b) /\ c) ==> (b /\ c)``)
    THEN STRIP_TAC THEN1 METIS_TAC [iR_ap_LEMMA]
    THEN Q.PAT_X_ASSUM `!xs.bbb` MATCH_MP_TAC
    THEN FULL_SIMP_TAC std_ss [iR_PERM_def,list2fmap_fmap2list]
    THEN ASM_SIMP_TAC std_ss [FunBind_def,iFunBind_def,list2fmap_def])
  THEN1
   (MATCH_MP_TAC (el 9 (CONJUNCTS iR_ev_rules))
    THEN FULL_SIMP_TAC std_ss [IN_INSERT,NOT_IN_EMPTY]
    THEN FULL_SIMP_TAC std_ss [LIST_LOOKUP_INTRO,iR_PERM_EQ]
    THEN FULL_SIMP_TAC bool_ss [LIST_LOOKUP_fmap2list_list2fmap]
    THEN FULL_SIMP_TAC std_ss [FDOM_list2sexp])
  THEN1
   (MATCH_MP_TAC (el 10 (CONJUNCTS iR_ev_rules)) THEN ASM_SIMP_TAC std_ss []
    THEN REPEAT STRIP_TAC THEN Q.PAT_X_ASSUM `!xs. bbb ==> bbbb` MATCH_MP_TAC
    THEN FULL_SIMP_TAC std_ss [iR_PERM_EQ,list2fmap_iVarBind]
    THEN MATCH_MP_TAC VarBind_EQ THEN POP_ASSUM MP_TAC
    THEN ASM_SIMP_TAC std_ss [DRESTRICT_list2fmap])
  THEN METIS_TAC [iR_ev_rules])
  in th end;

val R_lisp_eval_ok = prove(
  ``!e a s. R_ev (e,a) s ==> lisp_eval_ok (e,fmap2list a) s``,
  REPEAT STRIP_TAC
  THEN IMP_RES_TAC R_ev_LEMMA
  THEN FULL_SIMP_TAC std_ss []
  THEN `iR_PERM (fmap2list a) (fmap2list a)` by
         REWRITE_TAC [iR_PERM_def]
  THEN RES_TAC THEN METIS_TAC [iR_ev_LEMMA]);

val LISP_EVAL_def = Define `
  LISP_EVAL (exp,alist,limit) =
    FST (lisp_eval (exp,Sym "nil",Sym "nil",Sym "nil",Sym "nil",alist,limit))`;

val LISP_EVAL_CORRECT = store_thm("LISP_EVAL_CORRECT",
  ``!exp alist result l.
      R_ev (exp,alist) result ==>
      (LISP_EVAL (term2sexp exp, alist2sexp (fmap2list alist),l) =
       sexpression2sexp result)``,
  REPEAT STRIP_TAC
  THEN IMP_RES_TAC R_lisp_eval_ok
  THEN FULL_SIMP_TAC std_ss [lisp_eval_ok_def,LISP_EVAL_def]
  THEN REWRITE_TAC [GSYM TASK_EVAL_def]
  THEN POP_ASSUM (STRIP_ASSUME_TAC o Q.SPECL [`TASK_EVAL`,`TASK_EVAL`,`TASK_EVAL`,`l`])
  THEN ASM_SIMP_TAC std_ss []
  THEN ONCE_REWRITE_TAC [lisp_eval_def]
  THEN REWRITE_TAC [EVAL ``TASK_CONT = TASK_FUNC``]
  THEN REWRITE_TAC [EVAL ``TASK_CONT = TASK_EVAL``]
  THEN REWRITE_TAC [TASK_EVAL_def,isDot_def]);

val LISP_EVAL_LIMIT_CORRECT = store_thm("LISP_EVAL_LIMIT_CORRECT",
  ``!exp alist result l.
      R_ev (exp,alist) result ==>
      ((SND o SND o SND o SND o SND o SND)
         (lisp_eval (term2sexp exp, Sym "nil", Sym "nil", Sym "nil",
                     Sym "nil", alist2sexp (fmap2list alist),l)) = l)``,
  REPEAT STRIP_TAC
  THEN IMP_RES_TAC R_lisp_eval_ok
  THEN FULL_SIMP_TAC std_ss [lisp_eval_ok_def,LISP_EVAL_def]
  THEN REWRITE_TAC [GSYM TASK_EVAL_def]
  THEN POP_ASSUM (STRIP_ASSUME_TAC o Q.SPECL [`TASK_EVAL`,`TASK_EVAL`,`TASK_EVAL`,`l`])
  THEN ASM_SIMP_TAC std_ss []
  THEN ONCE_REWRITE_TAC [lisp_eval_def]
  THEN REWRITE_TAC [EVAL ``TASK_CONT = TASK_FUNC``]
  THEN REWRITE_TAC [EVAL ``TASK_CONT = TASK_EVAL``]
  THEN REWRITE_TAC [TASK_EVAL_def,isDot_def]);

val _ = export_theory();
