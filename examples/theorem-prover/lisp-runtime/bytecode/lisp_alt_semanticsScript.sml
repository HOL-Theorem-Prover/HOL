open HolKernel boolLib bossLib Parse; val _ = new_theory "lisp_alt_semantics";

open stringTheory finite_mapTheory pred_setTheory listTheory sumTheory;
open optionTheory arithmeticTheory relationTheory;

open lisp_sexpTheory lisp_parseTheory lisp_semanticsTheory;

val RW = REWRITE_RULE;
val RW1 = ONCE_REWRITE_RULE;


(* We define an alternative formulation of the semantics that is
   better suited for compiler verification. At the bottom of this
   script we prove that the two fomrmulations are equivalent. *)

val isFun_def = Define `(isFun (Fun x) = T) /\ (isFun _ = F)`;

val (RR_ev_rules,RR_ev_ind,RR_ev_cases) = Hol_reln `
 (!s a fns.
    RR_ev (Const s, a,fns,io,ok) (s,fns,io,ok))
  /\
  (!x (a: string |-> SExp) fns.
    x IN FDOM a ==>
    RR_ev (Var x,a,fns,io,ok) (a ' x,fns,io,ok))
  /\
  (!a fns io s fns1 io1.
    RR_ev (Const (Sym "NIL"),a,fns,io,ok) (s,fns1,io1,ok1) ==>
    RR_ev (Or [],a,fns,io,ok) (s,fns1,io1,ok1))
  /\
  (!a fns io s1 fns1 io1 t ts.
    RR_ev (t,a,fns,io,ok) (s1,fns1,io1,ok1) /\ isTrue s1 ==>
    RR_ev (Or (t::ts),a,fns,io,ok) (s1,fns1,io1,ok1))
  /\
  (!a fns io s1 fns1 io1 s2 fns2 io2 t ts.
    RR_ev (t,a,fns,io,ok) (s1,fns1,io1,ok1) /\ ~(isTrue s1) /\
    RR_ev (Or ts,a,fns1,io1,ok1) (s2,fns2,io2,ok2) ==>
    RR_ev (Or (t::ts),a,fns,io,ok) (s2,fns2,io2,ok2))
  /\
  (!e1 e2 e3 s1 s a.
    RR_ev (e1,a,fns,io,ok) (s1,fns1,io1,ok1) /\ ~isTrue s1 /\
    RR_ev (e3,a,fns1,io1,ok1) (s,fns2,io2,ok2)
    ==>
    RR_ev (If e1 e2 e3,a,fns,io,ok) (s,fns2,io2,ok2))
  /\
  (!e1 e2 e3 s1 s a.
    RR_ev (e1,a,fns,io,ok) (s1,fns1,io1,ok1) /\ isTrue s1 /\
    RR_ev (e2,a,fns1,io1,ok1) (s,fns2,io2,ok2)
    ==>
    RR_ev (If e1 e2 e3,a,fns,io,ok) (s,fns2,io2,ok2))
  /\
  (!e xs ys fns a.
    RR_evl (ys,a,fns,io,ok) (sl,fns1,io1,ok1) /\ (LENGTH xs = LENGTH ys) /\
    RR_ev (e,FUNION (VarBind xs sl) a,fns1,io1,ok1) (x,fns2,io2,ok2)
    ==>
    RR_ev (LamApp xs e ys,a,fns,io,ok) (x,fns2,io2,ok2))
  /\
  (!el args a fc fns x.
    RR_evl (el,a,fns,io,ok) (args,fns1,io1,ok1) /\ RR_ap (fc,args,a,fns1,io1,ok1) (x,fns2,io2,ok2) /\
    ~(isFun fc)
    ==>
    RR_ev (App fc el,a,fns,io,ok) (x,fns2,io2,ok2))
  /\
  (!fc args a fns f.
    (EVAL_DATA_OP fc = (f,LENGTH args))
    ==>
    RR_ap (PrimitiveFun fc,args,a,fns,io,ok) (f args,fns,io,ok))
  /\
  (!el args a fc fns params exp x.
    fc IN FDOM fns1 /\
    (fns1 ' fc = (params,exp)) /\ (LENGTH params = LENGTH args) /\
    RR_evl (el,a,fns,io,ok) (args,fns1,io1,ok1) /\
    RR_ev (exp,VarBind params args,fns1,io1,ok1) (x,fns2,io2,ok2)
    ==>
    RR_ev (App (Fun fc) el,a,fns,io,ok) (x,fns2,io2,ok2))
  /\
  (!args a fns.
    RR_ap (Print,args,a,fns,io,ok) (Sym "NIL",fns,
          io ++ sexp2string (list2sexp (Sym "PRINT"::args)) ++ "\n",ok))
  /\
  (!args a fns.
    RR_ap (Error,args,a,fns,io,ok) (anything,fns,
          io ++ sexp2string (list2sexp (Sym "ERROR"::args)) ++ "\n",F))
  /\
  (!a fns fc formals body.
    RR_ap (Define,[fc; formals; body],a,fns,io,ok)
         (Sym "NIL",add_def fns (getSym fc,MAP getSym (sexp2list formals),sexp2term body),
          io,ok /\ ~(getSym fc IN FDOM fns)))
  /\
  (!args params a fname fns x.
    fname IN FDOM fns /\
    (fns ' fname = (params,exp)) /\ (LENGTH params = LENGTH args) /\
    RR_ev (exp,VarBind params args,fns,io,ok) (x,fns2,io2,ok2)
    ==>
    RR_ap (Funcall,Sym fname::args,a,fns,io,ok) (x,fns2,io2,ok2))
  /\ (* give short-cut semantics for failure states *)
  (!f args a fns io res.
    RR_ap (Fun f,args,a,fns,io,F) (res,fns,io,F))
  /\ (* give short-cut semantics for failure states *)
  (!args a fns io res.
    RR_ap (Funcall,args,a,fns,io,F) (res,fns,io,F))
  /\ (* give short-cut semantics for failure states *)
  (!exp a fns io res.
    RR_ev (exp,a,fns,io,F) (res,fns,io,F))
  /\
  (!a.
    RR_evl ([],a,fns,io,ok) ([],fns,io,ok))
  /\
  (!e el s sl a.
    RR_ev (e,a,fns,io,ok) (s,fns1,io1,ok1) /\ RR_evl (el,a,fns1,io1,ok1) (sl,fns2,io2,ok2)
    ==>
    RR_evl (e::el,a,fns,io,ok) (s::sl,fns2,io2,ok2:bool))
  /\

  (* semantics of macros below *)

  (!e a fns io s fns1 io1.
    RR_ev (App (PrimitiveFun opCAR) [e],a,fns,io,ok) (s,fns1,io1,ok1) ==>
    RR_ev (First e,a,fns,io,ok) (s,fns1,io1,ok1))
  /\
  (!e a fns io s fns1 io1.
    RR_ev (First (App (PrimitiveFun opCDR) [e]),a,fns,io,ok) (s,fns1,io1,ok1) ==>
    RR_ev (Second e,a,fns,io,ok) (s,fns1,io1,ok1))
  /\
  (!e a fns io s fns1 io1.
    RR_ev (Second (App (PrimitiveFun opCDR) [e]),a,fns,io,ok) (s,fns1,io1,ok1) ==>
    RR_ev (Third e,a,fns,io,ok) (s,fns1,io1,ok1))
  /\
  (!e a fns io s fns1 io1.
    RR_ev (Third (App (PrimitiveFun opCDR) [e]),a,fns,io,ok) (s,fns1,io1,ok1) ==>
    RR_ev (Fourth e,a,fns,io,ok) (s,fns1,io1,ok1))
  /\
  (!e a fns io s fns1 io1.
    RR_ev (Fourth (App (PrimitiveFun opCDR) [e]),a,fns,io,ok) (s,fns1,io1,ok1) ==>
    RR_ev (Fifth e,a,fns,io,ok) (s,fns1,io1,ok1))
  /\
  (!zs x a fns io s fns1 io1.
    RR_ev (LamApp (MAP FST zs) x (MAP SND zs),a,fns,io,ok) (s,fns1,io1,ok1) ==>
    RR_ev (Let zs x,a,fns,io,ok) (s,fns1,io1,ok1))
  /\
  (!x a fns io s fns1 io1.
    RR_ev (x,a,fns,io,ok) (s,fns1,io1,ok1) ==>
    RR_ev (LetStar [] x,a,fns,io,ok) (s,fns1,io1,ok1))
  /\
  (!z zs x a fns io s fns1 io1.
    RR_ev (Let [z] (LetStar zs x),a,fns,io,ok) (s,fns1,io1,ok1) ==>
    RR_ev (LetStar (z::zs) x,a,fns,io,ok) (s,fns1,io1,ok1))
  /\
  (!a fns io s fns1 io1.
    RR_ev (Const (Sym "NIL"),a,fns,io,ok) (s,fns1,io1,ok1) ==>
    RR_ev (Cond [],a,fns,io,ok) (s,fns1,io1,ok1))
  /\
  (!x1 x2 qs a fns io s fns1 io1.
    RR_ev (If x1 x2 (Cond qs),a,fns,io,ok) (s,fns1,io1,ok1) ==>
    RR_ev (Cond ((x1,x2)::qs),a,fns,io,ok) (s,fns1,io1,ok1))
  /\
  (!a fns io s fns1 io1.
    RR_ev (Const (Sym "T"),a,fns,io,ok) (s,fns1,io1,ok1) ==>
    RR_ev (And [],a,fns,io,ok) (s,fns1,io1,ok1))
  /\
  (!a fns io s fns1 io1.
    RR_ev (Const (Sym "NIL"),a,fns,io,ok) (s,fns1,io1,ok1) ==>
    RR_ev (List [],a,fns,io,ok) (s,fns1,io1,ok1))
  /\
  (!a fns io s fns1 io1.
    RR_ev (t,a,fns,io,ok) (s,fns1,io1,ok1) ==>
    RR_ev (And [t],a,fns,io,ok) (s,fns1,io1,ok1))
  /\
  (!a fns io s fns1 io1.
    RR_ev (If t1 (And (t2::ts)) (Const (Sym "NIL")),a,fns,io,ok) (s,fns1,io1,ok1) ==>
    RR_ev (And (t1::t2::ts),a,fns,io,ok) (s,fns1,io1,ok1))
  /\
  (!a fns io s fns1 io1.
    RR_ev (App (PrimitiveFun opCONS) [t;List ts],a,fns,io,ok) (s,fns1,io1,ok1) ==>
    RR_ev (List (t::ts),a,fns,io,ok) (s,fns1,io1,ok1))
  /\
  (!fname ps body a fns io s fns1 io1.
    RR_ev (App Define [Const (Sym fname); Const (list2sexp (MAP Sym ps)); Const body],a,fns,io,ok) (s,fns1,io1,ok1) ==>
    RR_ev (Defun fname ps body,a,fns,io,ok) (s,fns1,io1,ok1))`;

val RR_evl_LENGTH = save_thm("RR_evl_LENGTH",
  RR_ev_ind
  |> Q.SPECL [`\x y. T`,`\x y. (LENGTH (FST x) = LENGTH (FST y))`,`\x y. T`]
  |> SIMP_RULE std_ss [LENGTH]);


(* R_ev implies RR_ev *)

val lemma = R_ev_ind
  |> Q.SPECL [`\x y. if isFun (FST x) then
                       ?fc args a fns1 io1 ok1 fc' params exp.
                         ((fc,args,a,fns1,io1,ok1) = x) /\
                         (fc = Fun fc') /\ fc' IN FDOM fns1 /\
                         (fns1 ' fc' = (params,exp)) /\
                         (LENGTH params = LENGTH args) /\
                         RR_ev (exp,VarBind params args,fns1,io1,ok1) y
                     else RR_ap x y`,
              `\x y. RR_evl x y`,
              `\x y. RR_ev x y`]

val goal = lemma |> concl |> rand;

(*
  set_goal([],goal)
*)

val R_ev_IMP_RR_ev = prove(goal,
  MATCH_MP_TAC lemma
  \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC (srw_ss()) []
  THEN1 (ONCE_REWRITE_TAC [RR_ev_cases] \\ FULL_SIMP_TAC (srw_ss()) [isFun_def] \\ METIS_TAC [])
  THEN1 (ONCE_REWRITE_TAC [RR_ev_cases] \\ FULL_SIMP_TAC (srw_ss()) [isFun_def] \\ METIS_TAC [])
  THEN1 (ONCE_REWRITE_TAC [RR_ev_cases] \\ FULL_SIMP_TAC (srw_ss()) [isFun_def] \\ METIS_TAC [])
  THEN1 (ONCE_REWRITE_TAC [RR_ev_cases] \\ FULL_SIMP_TAC (srw_ss()) [isFun_def] \\ METIS_TAC [])
  THEN1 (ONCE_REWRITE_TAC [RR_ev_cases] \\ FULL_SIMP_TAC (srw_ss()) [isFun_def] \\ METIS_TAC [])
  THEN1 (ONCE_REWRITE_TAC [RR_ev_cases] \\ FULL_SIMP_TAC (srw_ss()) [isFun_def] \\ METIS_TAC [])
  THEN1 (ONCE_REWRITE_TAC [RR_ev_cases] \\ FULL_SIMP_TAC (srw_ss()) [isFun_def] \\ METIS_TAC [])
  THEN1 (ONCE_REWRITE_TAC [RR_ev_cases] \\ FULL_SIMP_TAC (srw_ss()) [isFun_def] \\ METIS_TAC [])
  THEN1 (ONCE_REWRITE_TAC [RR_ev_cases] \\ FULL_SIMP_TAC (srw_ss()) [isFun_def] \\ METIS_TAC [])
  THEN1 (ONCE_REWRITE_TAC [RR_ev_cases] \\ FULL_SIMP_TAC (srw_ss()) [isFun_def] \\ METIS_TAC [])
  THEN1 (ONCE_REWRITE_TAC [RR_ev_cases] \\ FULL_SIMP_TAC (srw_ss()) [isFun_def] \\ METIS_TAC [])
  THEN1 (ONCE_REWRITE_TAC [RR_ev_cases] \\ FULL_SIMP_TAC (srw_ss()) [isFun_def] \\ METIS_TAC [])
  THEN1 (ONCE_REWRITE_TAC [RR_ev_cases] \\ FULL_SIMP_TAC (srw_ss()) [isFun_def] \\ METIS_TAC [])
  THEN1 (ONCE_REWRITE_TAC [RR_ev_cases] \\ FULL_SIMP_TAC (srw_ss()) [isFun_def] \\ METIS_TAC [])
  THEN1 (ONCE_REWRITE_TAC [RR_ev_cases] \\ FULL_SIMP_TAC (srw_ss()) [isFun_def] \\ METIS_TAC [])
  THEN1 (ONCE_REWRITE_TAC [RR_ev_cases] \\ FULL_SIMP_TAC (srw_ss()) [isFun_def] \\ METIS_TAC [])
  THEN1 (ONCE_REWRITE_TAC [RR_ev_cases] \\ FULL_SIMP_TAC (srw_ss()) [isFun_def] \\ METIS_TAC [])
  \\ ONCE_REWRITE_TAC [RR_ev_cases] \\ FULL_SIMP_TAC (srw_ss()) [isFun_def]
  \\ METIS_TAC []) |> SIMP_RULE std_ss [] |> CONJUNCTS |> last;

val _ = save_thm("R_ev_IMP_RR_ev",R_ev_IMP_RR_ev);

val _ = export_theory();
