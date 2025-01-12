open HolKernel boolLib bossLib Parse; val _ = new_theory "milawa_exec";

open stringTheory finite_mapTheory pred_setTheory listTheory sumTheory;
open optionTheory arithmeticTheory relationTheory combinTheory;

open lisp_sexpTheory lisp_semanticsTheory;
open milawa_logicTheory milawa_defsTheory;

(* We define an intermediate language MR_ev -- a language which is
   very much like the runtime's specification R_ev. The difference is
   that MR_ev is deterministic, functions that are simply just Error
   are given a semantics from the logic's context ctxt.

   We prove three important properties in this file:
     - any evlaution in MR is also valid in the runtime
         MR_ev ==> R_ev
     - macro expansion does not change the evalaution result
         MR_ev (term2term x,...) ==> MR_ev (x,...)
     - any evaluation inside the logic can also be done in MR
         M_ev ==> MR_ev

*)

val (MR_ev_rules,MR_ev_ind,MR_ev_cases) = Hol_reln `
  (!s a fns ok.
    MR_ev (Const s,a,ctxt:context_type,fns,ok) (s,ok))
  /\
  (!x (a: string |-> SExp) fns ok.
    x IN FDOM a ==>
    MR_ev (Var x,a,ctxt,fns,ok) (FAPPLY a x,ok))
  /\
  (!a fns ok s ok1.
    MR_ev (Const (Sym "NIL"),a,ctxt,fns,ok) (s,ok1) ==>
    MR_ev (Or [],a,ctxt,fns,ok) (s,ok1))
  /\
  (!a fns s1 t ts ok.
    MR_ev (t,a,ctxt,fns,ok) (s1,ok1) /\ isTrue s1 ==>
    MR_ev (Or (t::ts),a,ctxt,fns,ok) (s1,ok1))
  /\
  (!a fns s1 s2 t ts ok ok2.
    MR_ev (t,a,ctxt,fns,ok) (s1,ok1) /\ ~(isTrue s1) /\
    MR_ev (Or ts,a,ctxt,fns,ok1) (s2,ok2) ==>
    MR_ev (Or (t::ts),a,ctxt,fns,ok) (s2,ok2))
  /\
  (!e1 e2 e3 s1 s a ok1 ok2.
    MR_ev (e1,a,ctxt,fns,ok) (s1,ok1) /\ ~isTrue s1 /\
    MR_ev (e3,a,ctxt,fns,ok1) (s,ok2)
    ==>
    MR_ev (If e1 e2 e3,a,ctxt,fns,ok) (s,ok2))
  /\
  (!e1 e2 e3 s1 s a ok1 ok2.
    MR_ev (e1,a,ctxt,fns,ok) (s1,ok1) /\ isTrue s1 /\
    MR_ev (e2,a,ctxt,fns,ok1) (s,ok2)
    ==>
    MR_ev (If e1 e2 e3,a,ctxt,fns,ok) (s,ok2))
  /\
  (!e xs ys fns a ok1 ok2.
    MR_evl (ys,a,ctxt,fns,ok) (sl,ok1) /\ (LENGTH xs = LENGTH ys) /\
    MR_ev (e,FUNION (VarBind xs sl) a,ctxt,fns,ok1) (x,ok2)
    ==>
    MR_ev (LamApp xs e ys,a,ctxt,fns,ok) (x,ok2))
  /\
  (!el args a fc fns x ok1 ok2.
    MR_evl (el,a,ctxt,fns,ok) (args,ok1) /\
    MR_ap (fc,args,a,ctxt,fns,ok1) (x,ok2)
    ==>
    MR_ev (App fc el,a,ctxt,fns,ok) (x,ok2))
  /\
  (!fc args a fns f.
    (EVAL_DATA_OP fc = (f,LENGTH args))
    ==>
    MR_ap (PrimitiveFun fc,args,a,ctxt,fns,ok) (f args,ok))
  /\
  (!args a fc fns params exp x ok2.
    ~MEM fc ["NOT";"RANK";"ORDP";"ORD<"] /\
    fc IN FDOM fns /\ ~(?xs. exp = App Error xs) /\
    (fns ' fc = (params,exp)) /\ (LENGTH params = LENGTH args) /\
    MR_ev (exp,VarBind params args,ctxt,fns,ok) (x,ok2)
    ==>
    MR_ap (Fun fc,args,a,ctxt,fns,ok) (x,ok2))
  /\
  (!args a fc fns params x.
    ~MEM fc ["NOT";"RANK";"ORDP";"ORD<"] /\
    (LENGTH params = LENGTH args) /\
    fc IN FDOM fns /\ (fns ' fc = (params,App Error [Const x])) /\
    fc IN FDOM ctxt /\ (ctxt ' fc = (params,body,sem))
    ==>
    MR_ap (Fun fc,args,a,ctxt,fns,ok) (sem args,F))
  /\
  (!x a ctxt fns ok.
    MR_ap (Fun "NOT",[x],a,ctxt,fns,ok) (not x,ok))
  /\
  (!x a ctxt fns ok.
    MR_ap (Fun "RANK",[x],a,ctxt,fns,ok) (rank x,ok))
  /\
  (!x a ctxt fns ok.
    MR_ap (Fun "ORDP",[x],a,ctxt,fns,ok) (ordp x,ok))
  /\
  (!x y a ctxt fns ok.
    MR_ap (Fun "ORD<",[x;y],a,ctxt,fns,ok) (ord_ x y,ok))
  /\
  (!args params a fname fns x ok2.
    fname IN FDOM fns /\
    (fns ' fname = (params,exp)) /\ (LENGTH params = LENGTH args) /\
    MR_ev (exp,VarBind params args,ctxt,fns,ok) (x,ok2)
    ==>
    MR_ap (Funcall,Sym fname::args,a,ctxt,fns,ok) (x,ok2))
  /\
  (!a.
    MR_evl ([],a,ctxt,fns,ok) ([],ok))
  /\
  (!e el s sl a ok1 ok2.
    MR_ev (e,a,ctxt,fns,ok) (s,ok1) /\
    MR_evl (el,a,ctxt,fns,ok1) (sl,ok2)
    ==>
    MR_evl (e::el,a,ctxt,fns,ok) (s::sl,ok2))

  /\ (* semantics of macros below *)

  (!e a fns s ok1.
    MR_ev (App (PrimitiveFun opCAR) [e],a,ctxt,fns,ok) (s,ok1) ==>
    MR_ev (First e,a,ctxt,fns,ok) (s,ok1))
  /\
  (!e a fns s ok1.
    MR_ev (First (App (PrimitiveFun opCDR) [e]),a,ctxt,fns,ok) (s,ok1) ==>
    MR_ev (Second e,a,ctxt,fns,ok) (s,ok1))
  /\
  (!e a fns s ok1.
    MR_ev (Second (App (PrimitiveFun opCDR) [e]),a,ctxt,fns,ok) (s,ok1) ==>
    MR_ev (Third e,a,ctxt,fns,ok) (s,ok1))
  /\
  (!e a fns s ok1.
    MR_ev (Third (App (PrimitiveFun opCDR) [e]),a,ctxt,fns,ok) (s,ok1) ==>
    MR_ev (Fourth e,a,ctxt,fns,ok) (s,ok1))
  /\
  (!e a fns s ok1.
    MR_ev (Fourth (App (PrimitiveFun opCDR) [e]),a,ctxt,fns,ok) (s,ok1) ==>
    MR_ev (Fifth e,a,ctxt,fns,ok) (s,ok1))
  /\
  (!zs x a fns s ok1.
    MR_ev (LamApp (MAP FST zs) x (MAP SND zs),a,ctxt,fns,ok) (s,ok1) ==>
    MR_ev (Let zs x,a,ctxt,fns,ok) (s,ok1))
  /\
  (!x a fns s ok1.
    MR_ev (x,a,ctxt,fns,ok) (s,ok1) ==>
    MR_ev (LetStar [] x,a,ctxt,fns,ok) (s,ok1))
  /\
  (!z zs x a fns s ok1.
    MR_ev (Let [z] (LetStar zs x),a,ctxt,fns,ok) (s,ok1) ==>
    MR_ev (LetStar (z::zs) x,a,ctxt,fns,ok) (s,ok1))
  /\
  (!a fns s ok1.
    MR_ev (Const (Sym "NIL"),a,ctxt,fns,ok) (s,ok1) ==>
    MR_ev (Cond [],a,ctxt,fns,ok) (s,ok1))
  /\
  (!x1 x2 qs a fns s ok1.
    MR_ev (If x1 x2 (Cond qs),a,ctxt,fns,ok) (s,ok1) ==>
    MR_ev (Cond ((x1,x2)::qs),a,ctxt,fns,ok) (s,ok1))
  /\
  (!a fns s ok1.
    MR_ev (Const (Sym "T"),a,ctxt,fns,ok) (s,ok1) ==>
    MR_ev (And [],a,ctxt,fns,ok) (s,ok1))
  /\
  (!a fns s ok1.
    MR_ev (Const (Sym "NIL"),a,ctxt,fns,ok) (s,ok1) ==>
    MR_ev (List [],a,ctxt,fns,ok) (s,ok1))
  /\
  (!a fns s ok1.
    MR_ev (t,a,ctxt,fns,ok) (s,ok1) ==>
    MR_ev (And [t],a,ctxt,fns,ok) (s,ok1))
  /\
  (!a fns s ok1.
    MR_ev (If t1 (And (t2::ts)) (Const (Sym "NIL")),a,ctxt,fns,ok) (s,ok1) ==>
    MR_ev (And (t1::t2::ts),a,ctxt,fns,ok) (s,ok1))
  /\
  (!a fns s ok1.
    MR_ev (App (PrimitiveFun opCONS) [t;List ts],a,ctxt,fns,ok) (s,ok1) ==>
    MR_ev (List (t::ts),a,ctxt,fns,ok) (s,ok1))
  /\
  (!fname ps body a fns s ok1.
    MR_ev (App Define [Const (Sym fname); Const (list2sexp (MAP Sym ps)); Const body],a,ctxt,fns,ok) (s,ok1) ==>
    MR_ev (Defun fname ps body,a,ctxt,fns,ok) (s,ok1))`;

(* deterministic *)

val PULL_IMP = save_thm("PULL_IMP",METIS_PROVE []
  ``!P Q. ((P ==> !x. Q x) = !x. P ==> Q x) /\
          (((?x. Q x) ==> P) = !x. Q x ==> P)``)

val PULL_CONJ = METIS_PROVE []
  ``!P Q. ((P /\ !x. Q x) = !x. P /\ Q x) /\
          (((!x. Q x) /\ P) = !x. Q x /\ P) /\
          ((P /\ ?x. Q x) = ?x. P /\ Q x) /\
          (((?x. Q x) /\ P) = ?x. Q x /\ P)``

local

val lemma = MR_ev_ind
  |> Q.SPEC `\x y.
        !f args a ctxt fns ok res ok1 res2 ok2 ok3.
           (x = (f,args,a,ctxt,fns,ok)) /\ (y = (res,ok1)) /\
           MR_ap (f,args,a,ctxt,fns,ok2) (res2,ok3) ==> (res = res2)`
  |> Q.SPEC `\x y.
        !xs a ctxt fns ok res ok1 res2 ok2 ok3.
           (x = (xs,a,ctxt,fns,ok)) /\ (y = (res,ok1)) /\
           MR_evl (xs,a,ctxt,fns,ok2) (res2,ok3) ==> (res = res2)`
  |> Q.SPEC `\x y.
        !x1 a ctxt fns ok res ok1 res2 ok2 ok3.
           (x = (x1,a,ctxt,fns,ok)) /\ (y = (res,ok1)) /\
           MR_ev (x1,a,ctxt,fns,ok2) (res2,ok3) ==> (res = res2)`
  |> CONV_RULE (RAND_CONV (SIMP_CONV std_ss [PULL_IMP]))

in

val MR_ev_11 = store_thm("MR_ev_11",
  lemma |> concl |> dest_comb |> snd,
  MATCH_MP_TAC lemma \\ REPEAT STRIP_TAC
  \\ SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss []
  \\ POP_ASSUM MP_TAC \\ ONCE_REWRITE_TAC [MR_ev_cases]
  \\ ASM_SIMP_TAC (srw_ss()) []
  \\ REPEAT STRIP_TAC \\ RES_TAC \\ FULL_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC std_ss [] \\ RES_TAC \\ FULL_SIMP_TAC std_ss [MEM]);

end

local

val lemma = MR_ev_ind
  |> Q.SPEC `\x y.
        !f args a ctxt fns ok res ok1 res2 ok2 ok3.
           (x = (f,args,a,ctxt,fns,ok)) /\ (y = (res,ok1)) /\
           MR_ap (f,args,a,ctxt,fns,ok) (res2,ok2) ==> (res = res2) /\ (ok1 = ok2)`
  |> Q.SPEC `\x y.
        !xs a ctxt fns ok res ok1 res2 ok2 ok3.
           (x = (xs,a,ctxt,fns,ok)) /\ (y = (res,ok1)) /\
           MR_evl (xs,a,ctxt,fns,ok) (res2,ok2) ==> (res = res2) /\ (ok1 = ok2)`
  |> Q.SPEC `\x y.
        !x1 a ctxt fns ok res ok1 res2 ok2 ok3.
           (x = (x1,a,ctxt,fns,ok)) /\ (y = (res,ok1)) /\
           MR_ev (x1,a,ctxt,fns,ok) (res2,ok2) ==> (res = res2) /\ (ok1 = ok2)`
  |> CONV_RULE (RAND_CONV (SIMP_CONV std_ss [PULL_IMP]))

in

val MR_ev_11_ALL = store_thm("MR_ev_11_ALL",
  lemma |> concl |> dest_comb |> snd,
  MATCH_MP_TAC lemma \\ REPEAT STRIP_TAC
  \\ SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss []
  \\ POP_ASSUM MP_TAC \\ ONCE_REWRITE_TAC [MR_ev_cases]
  \\ ASM_SIMP_TAC (srw_ss()) []
  \\ REPEAT STRIP_TAC \\ RES_TAC \\ FULL_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC std_ss [] \\ RES_TAC \\ FULL_SIMP_TAC std_ss [MEM]
  \\ NTAC 2 (POP_ASSUM MP_TAC)
  \\ ONCE_REWRITE_TAC [MR_ev_cases]
  \\ ASM_SIMP_TAC (srw_ss()) []);

end

local

val lemma = MR_ev_ind
  |> Q.SPEC `\x y.
        !f args a ctxt fns ok res ok1.
           (x = (f,args,a,ctxt \\ name,fns,ok)) /\ (y = (res,ok1)) ==>
           MR_ap (f,args,a,ctxt,fns,ok) (res,ok1)`
  |> Q.SPEC `\x y.
        !xs a ctxt fns ok res ok1 res2 ok2 ok3.
           (x = (xs,a,ctxt \\ name,fns,ok)) /\ (y = (res,ok1)) ==>
           MR_evl (xs,a,ctxt,fns,ok) (res,ok1)`
  |> Q.SPEC `\x y.
        !x1 a ctxt fns ok res ok1 res2 ok2 ok3.
           (x = (x1,a,ctxt \\ name,fns,ok)) /\ (y = (res,ok1)) ==>
           MR_ev (x1,a,ctxt,fns,ok) (res,ok1)`
  |> CONV_RULE (RAND_CONV (SIMP_CONV std_ss [PULL_IMP]))

in

val MR_ev_CTXT = store_thm("MR_ev_CTXT",
  lemma |> concl |> dest_comb |> snd,
  MATCH_MP_TAC lemma \\ REPEAT STRIP_TAC
  \\ SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC
  \\ ONCE_REWRITE_TAC [MR_ev_cases]
  \\ FULL_SIMP_TAC (srw_ss()) []
  \\ METIS_TAC [DOMSUB_FAPPLY_NEQ]);

end

val add_def_lemma = store_thm("add_def_lemma",
  ``(FDOM (add_def k x) = FDOM k UNION {FST x}) /\
    (add_def k x ' n = if n IN FDOM k then k ' n else
                       if n = FST x then SND x else FEMPTY ' n)``,
  Cases_on `x`
  \\ ASM_SIMP_TAC std_ss [SUBMAP_DEF,add_def_def,
    FUNION_DEF,FAPPLY_FUPDATE_THM,
    FDOM_FUPDATE,IN_UNION,FDOM_FUPDATE,
    FDOM_FEMPTY]);

local

val lemma = MR_ev_ind
  |> Q.SPEC `\x y.
        !f args a ctxt fns ok res ok1.
           (x = (f,args,a,ctxt,fns,ok)) /\ (y = (res,ok1)) ==>
           MR_ap (f,args,a,ctxt,add_def fns d,ok) (res,ok1)`
  |> Q.SPEC `\x y.
        !xs a ctxt fns ok res ok1 res2 ok2 ok3.
           (x = (xs,a,ctxt,fns,ok)) /\ (y = (res,ok1)) ==>
           MR_evl (xs,a,ctxt,add_def fns d,ok) (res,ok1)`
  |> Q.SPEC `\x y.
        !x1 a ctxt fns ok res ok1 res2 ok2 ok3.
           (x = (x1,a,ctxt,fns,ok)) /\ (y = (res,ok1)) ==>
           MR_ev (x1,a,ctxt,add_def fns d,ok) (res,ok1)`
  |> CONV_RULE (RAND_CONV (SIMP_CONV std_ss [PULL_IMP]))

in

val MR_ev_add_def = store_thm("MR_ev_add_def",
  lemma |> concl |> dest_comb |> snd,
  MATCH_MP_TAC lemma \\ REPEAT STRIP_TAC
  \\ SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC
  \\ ONCE_REWRITE_TAC [MR_ev_cases]
  \\ FULL_SIMP_TAC (srw_ss()) [add_def_lemma]
  \\ METIS_TAC []);

end

local

val lemma = MR_ev_ind
  |> Q.SPEC `\x y.
        !f args a ctxt fns ok res ok1 z.
           (x = (f,args,a,ctxt,fns,ok)) /\ (y = (res,ok1)) /\
           MR_ap (f,args,a,ctxt,fns,ok) z ==> (z = (res,ok1))`
  |> Q.SPEC `\x y.
        !xs a ctxt fns ok res ok1 z.
           (x = (xs,a,ctxt,fns,ok)) /\ (y = (res,ok1)) /\
           MR_evl (xs,a,ctxt,fns,ok) z ==> (z = (res,ok1))`
  |> Q.SPEC `\x y.
        !x1 a ctxt fns ok res ok1 z.
           (x = (x1,a,ctxt,fns,ok)) /\ (y = (res,ok1)) /\
           MR_ev (x1,a,ctxt,fns,ok) z ==> (z = (res,ok1))`
  |> CONV_RULE (RAND_CONV (SIMP_CONV std_ss [PULL_IMP]))

in

val MR_ev_11_FULL = store_thm("MR_ev_11_FULL",
  lemma |> concl |> dest_comb |> snd,
  MATCH_MP_TAC lemma \\ REPEAT STRIP_TAC
  \\ SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss []
  \\ POP_ASSUM MP_TAC \\ ONCE_REWRITE_TAC [MR_ev_cases]
  \\ ASM_SIMP_TAC (srw_ss()) []
  \\ REPEAT STRIP_TAC \\ RES_TAC \\ FULL_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC std_ss [] \\ RES_TAC \\ FULL_SIMP_TAC std_ss [MEM]);

end

local

val lemma = MR_ev_ind
  |> Q.SPEC `\x y.
        !f args a ctxt fns ok res ok1 z.
           (x = (f,args,a,ctxt,fns,ok)) /\ (y = (res,ok1)) /\ ok1 ==> ok`
  |> Q.SPEC `\x y.
        !xs a ctxt fns ok res ok1 z.
           (x = (xs,a,ctxt,fns,ok)) /\ (y = (res,ok1)) /\ ok1 ==> ok`
  |> Q.SPEC `\x y.
        !x1 a ctxt fns ok res ok1 z.
           (x = (x1,a,ctxt,fns,ok)) /\ (y = (res,ok1)) /\ ok1 ==> ok`
  |> CONV_RULE (RAND_CONV (SIMP_CONV std_ss [PULL_IMP]))

in

val MR_ev_OK = store_thm("MR_ev_OK",
  lemma |> concl |> dest_comb |> snd,
  MATCH_MP_TAC lemma \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss []);

end

val MR_ev_induct = IndDefLib.derive_strong_induction(MR_ev_rules,MR_ev_ind);

val MR_ap_ARB = prove(
  ``MR_ap (fc,args,b,ctxt,fns,ok1) (x,ok2) =
    MR_ap (fc,args,ARB,ctxt,fns,ok1) (x,ok2)``,
  ONCE_REWRITE_TAC [MR_ev_cases] \\ SIMP_TAC std_ss []);

val FDOM_VarBind = prove(
  ``!xs ys x. (LENGTH xs = LENGTH ys) ==>
              (x IN FDOM (VarBind xs ys) = MEM x xs)``,
  SIMP_TAC std_ss [VarBind_def]
  \\ ONCE_REWRITE_TAC [GSYM MEM_REVERSE,GSYM LENGTH_REVERSE]
  \\ NTAC 3 STRIP_TAC
  \\ Q.SPEC_TAC (`REVERSE xs`,`xs`) \\ Q.SPEC_TAC (`REVERSE ys`,`ys`)
  \\ Induct_on `xs` \\ Cases_on `ys` \\ FULL_SIMP_TAC std_ss [LENGTH,ADD1]
  \\ ASM_SIMP_TAC (srw_ss()) [VarBindAux_def]);

val MR_ap_cases = CONJUNCTS MR_ev_cases |> el 1
val MR_evl_cases = CONJUNCTS MR_ev_cases |> el 2

val MR_evl_LENGTH = prove(
  ``!xs ys ok ok1. MR_evl (xs,a,ctxt,fns,ok) (ys,ok1) ==> (LENGTH xs = LENGTH ys)``,
  Induct \\ Cases_on `ys` \\ SIMP_TAC (srw_ss()) [Once MR_evl_cases,LENGTH]
  \\ FULL_SIMP_TAC std_ss [] \\ METIS_TAC [])


(* MR_ev ==> R_ev *)

local

val lemma = R_ev_ind
  |> Q.SPEC `\x y.
        !f args a ctxt fns ok res ok1 io q1 q2.
           (x = (f,args,a,fns,io,ok)) /\ (y = (res,q1,q2,ok1)) /\ ok1 ==> ok`
  |> Q.SPEC `\x y.
        !xs a ctxt fns ok res ok1 io q1 q2.
           (x = (xs,a,fns,io,ok)) /\ (y = (res,q1,q2,ok1)) /\ ok1 ==> ok`
  |> Q.SPEC `\x y.
        !x1 a ctxt fns ok res ok1 io q1 q2.
           (x = (x1,a,fns,io,ok)) /\ (y = (res,q1,q2,ok1)) /\ ok1 ==> ok`
  |> CONV_RULE (RAND_CONV (SIMP_CONV std_ss [PULL_IMP,AND_IMP_INTRO]))

in

val R_ev_ok_LEMMA = prove(
  lemma |> concl |> dest_comb |> snd,
  MATCH_MP_TAC lemma \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [])
  |> SIMP_RULE std_ss []

end


local

val lemma = MR_ev_ind
  |> Q.SPEC `\x y.
        !f args a ctxt fns ok res ok1 io.
           (x = (f,args,a,ctxt,fns,ok)) /\ (y = (res,ok1)) /\ core_assum fns ==>
           ?io1. (ok1 ==> (io1 = "")) /\
                 R_ap (f,args,a,fns,io,ok) (res,fns,io ++ io1,ok1)`
  |> Q.SPEC `\x y.
        !xs a ctxt fns ok res ok1 io.
           (x = (xs,a,ctxt,fns,ok)) /\ (y = (res,ok1)) /\ core_assum fns ==>
           ?io1. (ok1 ==> (io1 = "")) /\
                 R_evl (xs,a,fns,io,ok) (res,fns,io ++ io1,ok1)`
  |> Q.SPEC `\x y.
        !x1 a ctxt fns ok res ok1 io.
           (x = (x1,a,ctxt,fns,ok)) /\ (y = (res,ok1)) /\ core_assum fns ==>
           ?io1. (ok1 ==> (io1 = "")) /\
                 R_ev (x1,a,fns,io,ok) (res,fns,io ++ io1,ok1)`
  |> CONV_RULE (RAND_CONV (SIMP_CONV std_ss [PULL_IMP,AND_IMP_INTRO]))

in

val MR_IMP_R = store_thm("MR_IMP_R",
  lemma |> concl |> dest_comb |> snd,
  MATCH_MP_TAC lemma \\ REPEAT STRIP_TAC
  \\ SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC
  \\ ASM_SIMP_TAC (srw_ss()) [Once R_ev_cases]
  \\ FULL_SIMP_TAC std_ss [R_ev_not,R_ev_rank,R_ev_ordp,R_ev_ord_]
  THEN1 METIS_TAC [APPEND_ASSOC,APPEND]
  \\ TRY (Q.PAT_X_ASSUM `!io.bbb` MP_TAC
    \\ Q.PAT_X_ASSUM `!io.bbb` (STRIP_ASSUME_TAC o SPEC_ALL)
    \\ REPEAT STRIP_TAC
    \\ Q.PAT_X_ASSUM `!io.bbb` (STRIP_ASSUME_TAC o Q.SPEC `STRCAT io io1`)
    \\ FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC]
    \\ Q.EXISTS_TAC `io1 ++ io1'`
    \\ FULL_SIMP_TAC std_ss [APPEND_eq_NIL]
    \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss []
    \\ IMP_RES_TAC R_ev_ok_LEMMA \\ FULL_SIMP_TAC std_ss [] \\ METIS_TAC [])
  \\ TRY (METIS_TAC [])
  THEN1
   (ONCE_REWRITE_TAC [R_ev_cases] \\ SIMP_TAC (srw_ss()) []
    \\ ONCE_REWRITE_TAC [R_ev_cases] \\ SIMP_TAC (srw_ss()) []
    \\ ONCE_REWRITE_TAC [R_ev_cases] \\ SIMP_TAC (srw_ss()) [] \\ METIS_TAC [])
  \\ Q.EXISTS_TAC `""` \\ FULL_SIMP_TAC std_ss [APPEND_NIL]
  THEN1 (IMP_RES_TAC R_ev_not \\ POP_ASSUM MP_TAC
         \\ SIMP_TAC (srw_ss()) [Once R_ev_cases])
  THEN1 (IMP_RES_TAC R_ev_rank \\ POP_ASSUM MP_TAC
         \\ SIMP_TAC (srw_ss()) [Once R_ev_cases])
  THEN1 (IMP_RES_TAC R_ev_ordp \\ POP_ASSUM MP_TAC
         \\ SIMP_TAC (srw_ss()) [Once R_ev_cases])
  THEN1 (IMP_RES_TAC R_ev_ord_ \\ POP_ASSUM MP_TAC
         \\ SIMP_TAC (srw_ss()) [Once R_ev_cases]));

end

(* definition of term2term *)

val ISORT_INSERT_def = Define `
  (ISORT_INSERT ord x [] = [x]) /\
  (ISORT_INSERT ord x (y::ys) =
     if ord y x then y::ISORT_INSERT ord x ys else x::y::ys)`;

val ISORT_def = Define `
  (ISORT ord [] = []) /\
  (ISORT ord (x::xs) = ISORT_INSERT ord x (ISORT ord xs))`;

val REMOVE_DUPLICATES_def = Define `
  (REMOVE_DUPLICATES [] = []) /\
  (REMOVE_DUPLICATES (x::xs) =
     if MEM x xs then REMOVE_DUPLICATES xs else x::REMOVE_DUPLICATES xs)`;

val logic_sym2prim_def = Define `
  logic_sym2prim s =
    if s = "CONS" then SOME logic_CONS else
    if s = "EQUAL" then SOME logic_EQUAL else
    if s = "<" then SOME logic_LESS else
    if s = "SYMBOL-<" then SOME logic_SYMBOL_LESS else
    if s = "+" then SOME logic_ADD else
    if s = "-" then SOME logic_SUB else
    if s = "CONSP" then SOME logic_CONSP else
    if s = "NATP" then SOME logic_NATP else
    if s = "SYMBOLP" then SOME logic_SYMBOLP else
    if s = "CAR" then SOME logic_CAR else
    if s = "CDR" then SOME logic_CDR else
    if s = "NOT" then SOME logic_NOT else
    if s = "RANK" then SOME logic_RANK else
    if s = "IF" then SOME logic_IF else
    if s = "ORDP" then SOME logic_ORDP else
    if s = "ORD<" then SOME logic_ORD_LESS else NONE`;

val prim2p_def = Define `
  (prim2p opCONS = logic_CONS) /\
  (prim2p opEQUAL = logic_EQUAL) /\
  (prim2p opLESS = logic_LESS) /\
  (prim2p opSYMBOL_LESS = logic_SYMBOL_LESS) /\
  (prim2p opADD = logic_ADD) /\
  (prim2p opSUB = logic_SUB) /\
  (prim2p opCONSP = logic_CONSP) /\
  (prim2p opNATP = logic_NATP) /\
  (prim2p opSYMBOLP = logic_SYMBOLP) /\
  (prim2p opCAR = logic_CAR) /\
  (prim2p opCDR = logic_CDR)`;

val func2f_def = Define `
  (func2f (PrimitiveFun opCONS) = mPrimitiveFun logic_CONS) /\
  (func2f (PrimitiveFun opEQUAL) = mPrimitiveFun logic_EQUAL) /\
  (func2f (PrimitiveFun opLESS) = mPrimitiveFun logic_LESS) /\
  (func2f (PrimitiveFun opSYMBOL_LESS) = mPrimitiveFun logic_SYMBOL_LESS) /\
  (func2f (PrimitiveFun opADD) = mPrimitiveFun logic_ADD) /\
  (func2f (PrimitiveFun opSUB) = mPrimitiveFun logic_SUB) /\
  (func2f (PrimitiveFun opCONSP) = mPrimitiveFun logic_CONSP) /\
  (func2f (PrimitiveFun opNATP) = mPrimitiveFun logic_NATP) /\
  (func2f (PrimitiveFun opSYMBOLP) = mPrimitiveFun logic_SYMBOLP) /\
  (func2f (PrimitiveFun opCAR) = mPrimitiveFun logic_CAR) /\
  (func2f (PrimitiveFun opCDR) = mPrimitiveFun logic_CDR) /\
  (func2f (Fun name) = if name = "NOT" then mPrimitiveFun logic_NOT else
                       if name = "RANK" then mPrimitiveFun logic_RANK else
                       if name = "ORDP" then mPrimitiveFun logic_ORDP else
                       if name = "ORD<" then mPrimitiveFun logic_ORD_LESS else
                       if name = "IF" then mPrimitiveFun logic_IF else
                                             mFun name) /\
  (func2f Define = mFun "DEFINE") /\
  (func2f Print = mFun "PRINT") /\
  (func2f Error = mFun "ERROR") /\
  (func2f Funcall = mFun "FUNCALL")`

val SUM_def = Define `
  (SUM [] = 0:num) /\
  (SUM (x::xs) = x + SUM xs)`;

val MEM_term5_size = prove(
  ``!xs a. MEM a xs ==> term_size a < term5_size xs``,
  Induct \\ FULL_SIMP_TAC std_ss [MEM,term_size_def] \\ REPEAT STRIP_TAC
  \\ RES_TAC \\ FULL_SIMP_TAC std_ss [] \\ DECIDE_TAC);

val MEM_term3_size = prove(
  ``!xs a. MEM a xs ==> term_size (FST a) < term3_size xs /\
                        term_size (SND a) < term3_size xs``,
  Induct \\ FULL_SIMP_TAC std_ss [MEM,term_size_def] \\ REPEAT STRIP_TAC
  \\ Cases_on `h` \\ RES_TAC \\ FULL_SIMP_TAC std_ss [term_size_def] \\ DECIDE_TAC);

val MEM_term1_size = prove(
  ``!xs a. MEM a xs ==> term_size (SND a) <= term1_size xs``,
  Induct \\ FULL_SIMP_TAC std_ss [MEM,term_size_def] \\ REPEAT STRIP_TAC
  \\ Cases_on `h` \\ RES_TAC \\ FULL_SIMP_TAC std_ss [term_size_def] \\ DECIDE_TAC);

val term_cost_def = tDefine "term_cost" `
  (term_cost (Const c) = 1) /\
  (term_cost (Var v) = 1) /\
  (term_cost (If x1 x2 x3) = 1 + term_cost x1 + term_cost x2 + term_cost x3) /\
  (term_cost (App f xs) = 10 + SUM (MAP term_cost xs)) /\
  (term_cost (LamApp vs x xs) = 1 + LENGTH xs + SUM (MAP term_cost xs) + term_cost x) /\
  (term_cost (First x) = 20 + term_cost x) /\
  (term_cost (Second x) = 30 + term_cost x) /\
  (term_cost (Third x) = 40 + term_cost x) /\
  (term_cost (Fourth x) = 50 + term_cost x) /\
  (term_cost (Fifth x) = 60 + term_cost x) /\
  (term_cost (Or xs) = 5 * SUM (MAP term_cost xs) + 5 * LENGTH xs + 5) /\
  (term_cost (And xs) = 5 * SUM (MAP term_cost xs) + 5 * LENGTH xs + 5) /\
  (term_cost (List xs) = 5 * SUM (MAP term_cost xs) + 5 * LENGTH xs + 5) /\
  (term_cost (Cond ys) = 5 * SUM (MAP term_cost (MAP FST ys)) +
                         5 * SUM (MAP term_cost (MAP SND ys)) + 5 * LENGTH ys + 5) /\
  (term_cost (Defun name vs body) = 100:num) /\
  (term_cost (Let zs x) = SUM (MAP term_cost (MAP SND zs)) +
                          LENGTH zs + term_cost x + 5) /\
  (term_cost (LetStar zs x) = 5 * SUM (MAP term_cost (MAP SND zs)) +
                              10 * LENGTH zs + term_cost x + 5)`
 (WF_REL_TAC `measure term_size` \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [PULL_IMP,MEM_MAP] \\ IMP_RES_TAC MEM_term1_size
  \\ IMP_RES_TAC MEM_term3_size \\ IMP_RES_TAC MEM_term5_size \\ DECIDE_TAC)

val MEM_term_cost = prove(
  ``!xs a. MEM a xs ==> term_cost a <= SUM (MAP (\a. term_cost a) xs)``,
  Induct \\ SIMP_TAC std_ss [MEM,SUM_def,MAP] \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [] \\ RES_TAC \\ DECIDE_TAC);

val FST_MEM_term_cost = prove(
  ``!xs a. MEM (a,b) xs ==>
           term_cost a <= SUM (MAP (\a. term_cost a) (MAP FST xs))``,
  Induct \\ SIMP_TAC std_ss [MEM,SUM_def,MAP] \\ REPEAT STRIP_TAC
  \\ Cases_on `h` \\ FULL_SIMP_TAC std_ss [] \\ RES_TAC \\ DECIDE_TAC);

val SND_MEM_term_cost = prove(
  ``!xs a. MEM (b,a) xs ==>
           term_cost a <= SUM (MAP (\a. term_cost a) (MAP SND xs))``,
  Induct \\ SIMP_TAC std_ss [MEM,SUM_def,MAP] \\ REPEAT STRIP_TAC
  \\ Cases_on `h` \\ FULL_SIMP_TAC std_ss [] \\ RES_TAC \\ DECIDE_TAC);

val car = ``mApp (mPrimitiveFun logic_CAR)``
val cdr = ``mApp (mPrimitiveFun logic_CDR)``
val iif = ``mApp (mPrimitiveFun logic_IF)``
val cos = ``mApp (mPrimitiveFun logic_CONS)``

val term_vars_def = tDefine "term_vars" `
  (term_vars (Const c) = []) /\
  (term_vars (Var v) = [v]) /\
  (term_vars (If x1 x2 x3) = term_vars x1 ++ term_vars x2 ++ term_vars x3) /\
  (term_vars (App f xs) = FLAT (MAP term_vars xs)) /\
  (term_vars (LamApp vs x xs) = FILTER (\v. ~(MEM v vs)) (term_vars x) ++ FLAT (MAP term_vars xs)) /\
  (term_vars (First x) = term_vars x) /\
  (term_vars (Second x) = term_vars x) /\
  (term_vars (Third x) = term_vars x) /\
  (term_vars (Fourth x) = term_vars x) /\
  (term_vars (Fifth x) = term_vars x) /\
  (term_vars (Or xs) = FLAT (MAP term_vars xs)) /\
  (term_vars (And xs) = FLAT (MAP term_vars xs)) /\
  (term_vars (List xs) = FLAT (MAP term_vars xs)) /\
  (term_vars (Let ts x) = FILTER (\v. ~(MEM v (MAP FST ts))) (term_vars x) ++
                          FLAT (MAP (\ (x,y). term_vars y) ts)) /\
  (term_vars (Cond ys) = FLAT (MAP (\ (x,y). term_vars x ++ term_vars y) ys)) /\
  (term_vars (LetStar [] x) = term_vars x) /\
  (term_vars (LetStar (t::ts) x) = FILTER (\v. ~(v = FST t)) (term_vars (LetStar ts x)) ++ term_vars (SND t)) /\
  (term_vars (Defun name vs body) = [])`
 (WF_REL_TAC `measure term_cost`
  \\ REPEAT STRIP_TAC \\ IMP_RES_TAC MEM_term_cost
  \\ IMP_RES_TAC SND_MEM_term_cost \\ IMP_RES_TAC FST_MEM_term_cost
  \\ FULL_SIMP_TAC std_ss [term_cost_def,LENGTH_MAP,LENGTH,MAP,SUM_def]
  \\ FULL_SIMP_TAC std_ss [LEFT_ADD_DISTRIB,MULT_CLAUSES] \\ REPEAT DECIDE_TAC);

local

val lemma = MR_ev_induct
  |> Q.SPEC `\x y.
        !f args a ctxt fns ok res ok1 z.
           (x = (f,args,a,ctxt,fns,ok)) /\ (y = (res,ok1)) ==>
           MR_ap (f,args,a,ctxt,fns,ok) (res,ok1)`
  |> Q.SPEC `\x y.
        !xs a b ctxt fns ok res ok1 z n v.
           (x = (xs,a,ctxt,fns,ok)) /\ (y = (res,ok1)) ==>
           (!y. MEM y (FLAT (MAP term_vars xs)) ==>
                (y IN FDOM a = y IN FDOM b) /\ (a ' y = b ' y)) ==>
           MR_evl (xs,b,ctxt,fns,ok) (res,ok1)`
  |> Q.SPEC `\x y.
        !x1 a b ctxt fns ok res ok1 z n v.
           (x = (x1,a,ctxt,fns,ok)) /\ (y = (res,ok1)) ==>
           (!y. MEM y (term_vars x1) ==>
                (y IN FDOM a = y IN FDOM b) /\ (a ' y = b ' y)) ==>
           MR_ev (x1,b,ctxt,fns,ok) (res,ok1)`
  |> CONV_RULE (RAND_CONV (SIMP_CONV std_ss [PULL_IMP]))

in

val MR_ev_VARS = prove(
  lemma |> concl |> dest_comb |> snd,
  MATCH_MP_TAC lemma \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss []
  \\ ASM_SIMP_TAC (srw_ss()) [Once MR_ev_cases,term_vars_def]
  \\ FULL_SIMP_TAC (srw_ss()) [term_vars_def,MR_ap_ARB]
  THEN1 (METIS_TAC []) THEN1 (METIS_TAC []) THEN1 (METIS_TAC [])
  THEN1
   (REPEAT STRIP_TAC
    \\ `MR_evl (ys,b,ctxt,fns,ok) (sl,ok1)` by METIS_TAC []
    \\ Q.LIST_EXISTS_TAC [`sl`,`ok1`] \\ FULL_SIMP_TAC std_ss []
    \\ Q.PAT_X_ASSUM `!b:string |-> SExp. bbb` MATCH_MP_TAC
    \\ FULL_SIMP_TAC std_ss [FUNION_DEF,IN_UNION]
    \\ FULL_SIMP_TAC std_ss [MEM_FILTER,MEM_FLAT,MEM_MAP,PULL_CONJ]
    \\ STRIP_TAC \\ STRIP_TAC
    \\ Cases_on `y IN FDOM (VarBind xs sl)` \\ FULL_SIMP_TAC std_ss []
    \\ IMP_RES_TAC MR_evl_LENGTH \\ METIS_TAC [FDOM_VarBind])
  THEN1 (METIS_TAC []) THEN1 (METIS_TAC [])
  THEN1
   (POP_ASSUM MP_TAC \\ SIMP_TAC std_ss [MAP_MAP_o,o_DEF]
    \\ `(\x. term_vars (SND x)) = (\(x':string,y). term_vars y)` by (FULL_SIMP_TAC std_ss [FUN_EQ_THM] \\ Cases \\ FULL_SIMP_TAC std_ss [])
    \\ FULL_SIMP_TAC std_ss [MEM_FILTER] \\ METIS_TAC [])
  \\ Cases_on `z` \\ FULL_SIMP_TAC std_ss []
  \\ METIS_TAC []) |> CONJUNCT2 |> SIMP_RULE std_ss [AND_IMP_INTRO];

end

val logic_prim2sym_def = Define `
  (logic_prim2sym logic_CONS = "CONS") /\
  (logic_prim2sym logic_EQUAL = "EQUAL") /\
  (logic_prim2sym logic_LESS = "<") /\
  (logic_prim2sym logic_SYMBOL_LESS = "SYMBOL-<") /\
  (logic_prim2sym logic_ADD = "+") /\
  (logic_prim2sym logic_SUB = "-") /\
  (logic_prim2sym logic_CONSP = "CONSP") /\
  (logic_prim2sym logic_NATP = "NATP") /\
  (logic_prim2sym logic_SYMBOLP = "SYMBOLP") /\
  (logic_prim2sym logic_CAR = "CAR") /\
  (logic_prim2sym logic_CDR = "CDR") /\
  (logic_prim2sym logic_NOT = "NOT") /\
  (logic_prim2sym logic_RANK = "RANK") /\
  (logic_prim2sym logic_IF = "IF") /\
  (logic_prim2sym logic_ORDP = "ORDP") /\
  (logic_prim2sym logic_ORD_LESS = "ORD<")`;

val bad_names_tm =
  ``["NIL"; "QUOTE"; "CONS"; "EQUAL"; "<"; "SYMBOL-<"; "+"; "-"; "CONSP";
     "NATP"; "SYMBOLP"; "CAR"; "CDR"; "NOT"; "RANK"; "IF"; "ORDP"; "ORD<"]``

val INDEX_OF_def = Define `
  (INDEX_OF n x [] = NONE) /\
  (INDEX_OF n x (y::xs) = if x = y then SOME n else INDEX_OF (n+1:num) x xs)`;

val logic_func2sexp_def = Define `
  (logic_func2sexp (mPrimitiveFun p) = Sym (logic_prim2sym p)) /\
  (logic_func2sexp (mFun f) =
     if MEM f ^bad_names_tm then Val (THE (INDEX_OF 0 f ^bad_names_tm)) else Sym f)`

val t2sexp_def = tDefine "t2sexp" `
  (t2sexp (mConst s) = list2sexp [Sym "QUOTE"; s]) /\
  (t2sexp (mVar v) = Sym v) /\
  (t2sexp (mApp fc vs) = list2sexp (logic_func2sexp fc :: MAP t2sexp vs)) /\
  (t2sexp (mLamApp xs z ys) = list2sexp (list2sexp [Sym "LAMBDA"; list2sexp (MAP Sym xs); t2sexp z]::MAP t2sexp ys))`
 (WF_REL_TAC `measure (logic_term_size)`);

val f2sexp_def = Define `
  (f2sexp (Or x y) = list2sexp [Sym "POR*"; f2sexp x; f2sexp y]) /\
  (f2sexp (Not x) = list2sexp [Sym "PNOT*"; f2sexp x]) /\
  (f2sexp (Equal t1 t2) = list2sexp [Sym "PEQUAL*"; t2sexp t1; t2sexp t2])`;

val let2t_def = Define `
  let2t ts body =
    let vars = MAP Sym (MAP FST ts) in
    let terms = MAP SND ts in
    let body_vars = (REMOVE_DUPLICATES (MAP Sym (free_vars body))) in
    let id_vars = ISORT (\x y. getSym x <= getSym y)
                    (FILTER (\x. ~MEM x vars) body_vars) in
    let formals = MAP getSym (id_vars ++ vars) in
    let actuals = MAP (mVar o getSym) id_vars ++ terms in
      mLamApp formals body actuals`;

val or2t_def = Define `
  (or2t [] = mConst (Sym "NIL")) /\
  (or2t [x] = x) /\
  (or2t (x::y::xs) =
     let else_term = or2t (y::xs) in
     let cheap = (isTrue (logic_variablep (t2sexp x)) \/
                  isTrue (logic_constantp (t2sexp x))) in
       if cheap \/ MEM "SPECIAL-VAR-FOR-OR" (free_vars else_term) then
         mApp (mPrimitiveFun logic_IF) [x;x;else_term]
       else
         let2t [("SPECIAL-VAR-FOR-OR",x)]
            (mApp (mPrimitiveFun logic_IF)
               [mVar "SPECIAL-VAR-FOR-OR"; mVar "SPECIAL-VAR-FOR-OR"; else_term]))`

val term2t_def = tDefine "term2t" `
  (term2t (Const c) = mConst c) /\
  (term2t (Var v) = mVar v) /\
  (term2t (If x1 x2 x3) = ^iif [term2t x1; term2t x2; term2t x3]) /\
  (term2t (App f xs) = mApp (func2f f) (MAP term2t xs)) /\
  (term2t (LamApp vs x xs) = mLamApp vs (term2t x) (MAP term2t xs)) /\
  (term2t (First x) = ^car [term2t x]) /\
  (term2t (Second x) = ^car [^cdr [term2t x]]) /\
  (term2t (Third x) = ^car [^cdr [^cdr [term2t x]]]) /\
  (term2t (Fourth x) = ^car [^cdr [^cdr [^cdr [term2t x]]]]) /\
  (term2t (Fifth x) = ^car [^cdr [^cdr [^cdr [^cdr [term2t x]]]]]) /\
  (term2t (Or xs) = or2t (MAP term2t xs)) /\
  (term2t (And []) = mConst (Sym "T")) /\
  (term2t (And [x]) = term2t x) /\
  (term2t (And (x1::x2::xs)) = ^iif [term2t x1; term2t (And (x2::xs)); mConst (Sym "NIL")]) /\
  (term2t (List []) = mConst (Sym "NIL")) /\
  (term2t (List (x::xs)) = ^cos [term2t x; term2t (List xs)]) /\
  (term2t (Let ts x) = let2t (MAP (\ (x,y). (x,term2t y)) ts) (term2t x)) /\
  (term2t (Cond []) = mConst (Sym "NIL")) /\
  (term2t (Cond ((x,y)::rs)) = ^iif [term2t x; term2t y; term2t (Cond rs)]) /\
  (term2t (LetStar [] x) = term2t x) /\
  (term2t (LetStar ((v,x)::ts) y) = term2t (Let [(v,x)] (LetStar ts y))) /\
  (term2t (Defun name vs body) =
     mApp (mFun "DEFINE") [mConst (Sym name);
                           mConst (list2sexp (MAP Sym vs));
                           mConst body])`
 (WF_REL_TAC `measure term_cost`
  \\ REPEAT STRIP_TAC \\ IMP_RES_TAC MEM_term_cost \\ IMP_RES_TAC SND_MEM_term_cost
  \\ FULL_SIMP_TAC std_ss [term_cost_def,LENGTH_MAP,LENGTH,MAP,SUM_def]
  \\ FULL_SIMP_TAC std_ss [LEFT_ADD_DISTRIB,MULT_CLAUSES] \\ REPEAT DECIDE_TAC);

val MEM_logic_term_size = prove(
  ``!xs x. MEM x xs ==> logic_term_size x < logic_term1_size xs``,
  Induct \\ SIMP_TAC std_ss [MEM] \\ REPEAT STRIP_TAC \\ RES_TAC
  \\ ASM_SIMP_TAC std_ss [] \\ EVAL_TAC \\ DECIDE_TAC)

val LENGTH_EQ_3 = prove(
  ``(LENGTH xs = 3) = ?x1 x2 x3. xs = [x1;x2;x3]``,
  Cases_on `xs` \\ SIMP_TAC (srw_ss()) []
  \\ Cases_on `t` \\ SIMP_TAC (srw_ss()) []
  \\ Cases_on `t'` \\ SIMP_TAC (srw_ss()) []
  \\ Cases_on `t` \\ SIMP_TAC (srw_ss()) []
  \\ DECIDE_TAC)

val f2func_def = Define `
  (f2func (mPrimitiveFun logic_CONS) = PrimitiveFun opCONS) /\
  (f2func (mPrimitiveFun logic_EQUAL) = PrimitiveFun opEQUAL) /\
  (f2func (mPrimitiveFun logic_LESS) = PrimitiveFun opLESS) /\
  (f2func (mPrimitiveFun logic_SYMBOL_LESS) = PrimitiveFun opSYMBOL_LESS) /\
  (f2func (mPrimitiveFun logic_ADD) = PrimitiveFun opADD) /\
  (f2func (mPrimitiveFun logic_SUB) = PrimitiveFun opSUB) /\
  (f2func (mPrimitiveFun logic_CONSP) = PrimitiveFun opCONSP) /\
  (f2func (mPrimitiveFun logic_NATP) = PrimitiveFun opNATP) /\
  (f2func (mPrimitiveFun logic_SYMBOLP) = PrimitiveFun opSYMBOLP) /\
  (f2func (mPrimitiveFun logic_CAR) = PrimitiveFun opCAR) /\
  (f2func (mPrimitiveFun logic_CDR) = PrimitiveFun opCDR) /\
  (f2func (mPrimitiveFun logic_NOT) = Fun "NOT") /\
  (f2func (mPrimitiveFun logic_RANK) = Fun "RANK") /\
  (f2func (mPrimitiveFun logic_ORDP) = Fun "ORDP") /\
  (f2func (mPrimitiveFun logic_ORD_LESS) = Fun "ORD<") /\
  (f2func (mPrimitiveFun logic_IF) = Fun "IF") /\
  (f2func (mFun name) = if name = "DEFINE" then Define else
                        if name = "PRINT" then Print else
                        if name = "ERROR" then Error else
                        if name = "FUNCALL" then Funcall else
                          Fun name)`

val t2term_def = tDefine "t2term" `
  (t2term (mConst c) = Const c) /\
  (t2term (mVar v) = Var v) /\
  (t2term (mApp f xs) =
     if (f = mPrimitiveFun logic_IF) /\ (LENGTH xs = 3) then
       If (t2term (EL 0 xs)) (t2term (EL 1 xs)) (t2term (EL 2 xs))
     else App (f2func f) (MAP t2term xs)) /\
  (t2term (mLamApp vs x xs) = LamApp vs (t2term x) (MAP t2term xs))`
 (WF_REL_TAC `measure logic_term_size` \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [LENGTH_EQ_3] \\ FULL_SIMP_TAC (srw_ss()) []
  \\ IMP_RES_TAC MEM_logic_term_size
  \\ EVAL_TAC \\ DECIDE_TAC);

val term2term_def = Define `term2term x = t2term (term2t x)`;


(* MR_ev (term2term x,...) ==> MR_ev (x,...) *)

val func_name_ok_def = Define `
  func_name_ok f =
    ~MEM f [Fun "IF"; Fun "DEFINE"; Fun "FUNCALL"; Fun "PRINT"; Fun "ERROR"]`;

val f2func_func2f = prove(
  ``!f. func_name_ok f ==> (f2func (func2f f) = f) /\
                           ~(func2f f = mPrimitiveFun logic_IF)``,
  Cases \\ TRY (Cases_on `l` \\ EVAL_TAC)
  \\ EVAL_TAC \\ SRW_TAC [] [] \\ EVAL_TAC \\ ASM_SIMP_TAC std_ss []);

val funcs_ok_def = tDefine "funcs_ok" `
  (funcs_ok (Const c) = T) /\
  (funcs_ok (Var v) = T) /\
  (funcs_ok (If x1 x2 x3) = funcs_ok x1 /\ funcs_ok x2 /\ funcs_ok x3) /\
  (funcs_ok (App f xs) = func_name_ok f /\ EVERY funcs_ok xs) /\
  (funcs_ok (LamApp vs x xs) = funcs_ok x /\ EVERY funcs_ok xs) /\
  (funcs_ok (First x) = funcs_ok x) /\
  (funcs_ok (Second x) = funcs_ok x) /\
  (funcs_ok (Third x) = funcs_ok x) /\
  (funcs_ok (Fourth x) = funcs_ok x) /\
  (funcs_ok (Fifth x) = funcs_ok x) /\
  (funcs_ok (Or xs) = EVERY funcs_ok xs) /\
  (funcs_ok (And xs) = EVERY funcs_ok xs) /\
  (funcs_ok (List xs) = EVERY funcs_ok xs) /\
  (funcs_ok (Let ts x) = EVERY (\ (x,y). funcs_ok y) ts /\ funcs_ok x) /\
  (funcs_ok (Cond ys) = EVERY (\ (x,y). funcs_ok x /\ funcs_ok y) ys) /\
  (funcs_ok (LetStar zs x) = funcs_ok x /\ EVERY (\ (x,y). funcs_ok y) zs) /\
  (funcs_ok (Defun name vs body) = T)`
 (WF_REL_TAC `measure term_cost`
  \\ REPEAT STRIP_TAC \\ IMP_RES_TAC MEM_term_cost
  \\ IMP_RES_TAC SND_MEM_term_cost \\ IMP_RES_TAC FST_MEM_term_cost
  \\ FULL_SIMP_TAC std_ss [term_cost_def,LENGTH_MAP,LENGTH,MAP,SUM_def]
  \\ FULL_SIMP_TAC std_ss [LEFT_ADD_DISTRIB,MULT_CLAUSES] \\ REPEAT DECIDE_TAC);

val funcs_ok_sexp2term = store_thm("funcs_ok_sexp2term",
  ``!x. funcs_ok (sexp2term x)``,
  HO_MATCH_MP_TAC sexp2term_ind \\ SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC
  \\ ONCE_REWRITE_TAC [sexp2term_def] \\ SIMP_TAC std_ss [LET_DEF]
  \\ SRW_TAC [] [] \\ SIMP_TAC std_ss [funcs_ok_def]
  \\ FULL_SIMP_TAC std_ss [EVERY_MEM,MEM_MAP,PULL_IMP]
  \\ ASM_SIMP_TAC (srw_ss()) [func_name_ok_def,MEM]
  \\ Cases_on `CAR x` \\ FULL_SIMP_TAC std_ss [getSym_def]
  \\ FULL_SIMP_TAC (srw_ss()) []);

val MR_ev_CAR = prove(
  ``MR_ev (App (PrimitiveFun opCAR) [x],a,ctxt,fns,ok) (s,ok2) =
    ?res. MR_ev (x,a,ctxt,fns,ok) (res,ok2) /\ (s = CAR res)``,
  SIMP_TAC (srw_ss()) [Once MR_ev_cases]
  \\ SIMP_TAC (srw_ss()) [Once MR_evl_cases, Once MR_ap_cases]
  \\ SIMP_TAC (srw_ss()) [Once MR_evl_cases,EVAL_DATA_OP_def,PULL_CONJ]);

val MR_ev_CDR = prove(
  ``MR_ev (App (PrimitiveFun opCDR) [x],a,ctxt,fns,ok) (s,ok2) =
    ?res. MR_ev (x,a,ctxt,fns,ok) (res,ok2) /\ (s = CDR res)``,
  SIMP_TAC (srw_ss()) [Once MR_ev_cases]
  \\ SIMP_TAC (srw_ss()) [Once MR_evl_cases, Once MR_ap_cases]
  \\ SIMP_TAC (srw_ss()) [Once MR_evl_cases,EVAL_DATA_OP_def,PULL_CONJ]);

val MR_ev_First =
  (SIMP_CONV (srw_ss()) [Once MR_ev_cases,MR_ev_CAR])
  ``MR_ev (First x,a,ctxt,fns,ok) (s,ok2)``

val MR_ev_Second =
  (SIMP_CONV (srw_ss()) [Once MR_ev_cases,MR_ev_CDR,MR_ev_First,PULL_CONJ])
  ``MR_ev (Second x,a,ctxt,fns,ok) (s,ok2)``

val MR_ev_Third =
  (SIMP_CONV (srw_ss()) [Once MR_ev_cases,MR_ev_CDR,MR_ev_Second,PULL_CONJ])
  ``MR_ev (Third x,a,ctxt,fns,ok) (s,ok2)``

val MR_ev_Fourth =
  (SIMP_CONV (srw_ss()) [Once MR_ev_cases,MR_ev_CDR,MR_ev_Third,PULL_CONJ])
  ``MR_ev (Fourth x,a,ctxt,fns,ok) (s,ok2)``

val MR_ev_Fifth =
  (SIMP_CONV (srw_ss()) [Once MR_ev_cases,MR_ev_CDR,MR_ev_Fourth,PULL_CONJ])
  ``MR_ev (Fifth x,a,ctxt,fns,ok) (s,ok2)``

val term2term_First = prove(
  ``(!res ok2 ok a.
        funcs_ok x /\
        MR_ev (term2term x,a,ctxt,fns,ok) (res,ok2) ==>
        MR_ev (x,a,ctxt,fns,ok) (res,ok2)) /\
    funcs_ok (First x) /\
    MR_ev (term2term (First x),a,ctxt,fns,ok) (res,ok2) ==>
    MR_ev (First x,a,ctxt,fns,ok) (res,ok2)``,
  REPEAT STRIP_TAC \\ FULL_SIMP_TAC (srw_ss()) [term2term_def,t2term_def,term2t_def,
        LENGTH,funcs_ok_def,EVERY_MEM,f2func_def] \\ POP_ASSUM MP_TAC
  \\ SIMP_TAC std_ss [MR_ev_First,MR_ev_CAR,MR_ev_First] \\ METIS_TAC []);

val term2term_Second = prove(
  ``(!res ok2 ok a.
        funcs_ok x /\
        MR_ev (term2term x,a,ctxt,fns,ok) (res,ok2) ==>
        MR_ev (x,a,ctxt,fns,ok) (res,ok2)) /\
    funcs_ok (Second x) /\
    MR_ev (term2term (Second x),a,ctxt,fns,ok) (res,ok2) ==>
    MR_ev (Second x,a,ctxt,fns,ok) (res,ok2)``,
  REPEAT STRIP_TAC \\ FULL_SIMP_TAC (srw_ss()) [term2term_def,t2term_def,term2t_def,
        LENGTH,funcs_ok_def,EVERY_MEM,f2func_def] \\ POP_ASSUM MP_TAC
  \\ SIMP_TAC std_ss [MR_ev_CDR,MR_ev_CAR,MR_ev_Second] \\ METIS_TAC []);

val term2term_Third = prove(
  ``(!res ok2 ok a.
        funcs_ok x /\
        MR_ev (term2term x,a,ctxt,fns,ok) (res,ok2) ==>
        MR_ev (x,a,ctxt,fns,ok) (res,ok2)) /\
    funcs_ok (Third x) /\
    MR_ev (term2term (Third x),a,ctxt,fns,ok) (res,ok2) ==>
    MR_ev (Third x,a,ctxt,fns,ok) (res,ok2)``,
  REPEAT STRIP_TAC \\ FULL_SIMP_TAC (srw_ss()) [term2term_def,t2term_def,term2t_def,
        LENGTH,funcs_ok_def,EVERY_MEM,f2func_def] \\ POP_ASSUM MP_TAC
  \\ SIMP_TAC std_ss [MR_ev_CDR,MR_ev_CAR,MR_ev_Third] \\ METIS_TAC []);

val term2term_Fourth = prove(
  ``(!res ok2 ok a.
        funcs_ok x /\
        MR_ev (term2term x,a,ctxt,fns,ok) (res,ok2) ==>
        MR_ev (x,a,ctxt,fns,ok) (res,ok2)) /\
    funcs_ok (Fourth x) /\
    MR_ev (term2term (Fourth x),a,ctxt,fns,ok) (res,ok2) ==>
    MR_ev (Fourth x,a,ctxt,fns,ok) (res,ok2)``,
  REPEAT STRIP_TAC \\ FULL_SIMP_TAC (srw_ss()) [term2term_def,t2term_def,term2t_def,
        LENGTH,funcs_ok_def,EVERY_MEM,f2func_def] \\ POP_ASSUM MP_TAC
  \\ SIMP_TAC std_ss [MR_ev_CDR,MR_ev_CAR,MR_ev_Fourth] \\ METIS_TAC []);

val term2term_Fifth = prove(
  ``(!res ok2 ok a.
        funcs_ok x /\
        MR_ev (term2term x,a,ctxt,fns,ok) (res,ok2) ==>
        MR_ev (x,a,ctxt,fns,ok) (res,ok2)) /\
    funcs_ok (Fifth x) /\
    MR_ev (term2term (Fifth x),a,ctxt,fns,ok) (res,ok2) ==>
    MR_ev (Fifth x,a,ctxt,fns,ok) (res,ok2)``,
  REPEAT STRIP_TAC \\ FULL_SIMP_TAC (srw_ss()) [term2term_def,t2term_def,term2t_def,
        LENGTH,funcs_ok_def,EVERY_MEM,f2func_def] \\ POP_ASSUM MP_TAC
  \\ SIMP_TAC std_ss [MR_ev_CDR,MR_ev_CAR,MR_ev_Fifth] \\ METIS_TAC []);

val MR_evl_MAP_Var = prove(
  ``!vs sl.
      MR_evl (MAP Var vs ++ ys,a,ctxt,fns,ok) (sl,ok1) ==>
      EVERY (\v. v IN FDOM a) vs /\
      ?sl2. (sl = MAP (\v. a ' v) vs ++ sl2) /\
            MR_evl (ys,a,ctxt,fns,ok) (sl2,ok1)``,
  Induct \\ SIMP_TAC std_ss [MAP,APPEND,EVERY_DEF]
  \\ SIMP_TAC (srw_ss()) [Once MR_ev_cases]
  \\ SIMP_TAC (srw_ss()) [Once MR_ev_cases]
  \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [APPEND,CONS_11]
  \\ Q.PAT_X_ASSUM `sl = xxx` ASSUME_TAC
  \\ FULL_SIMP_TAC std_ss [] \\ RES_TAC);

val VarBindAux_APPEND = prove(
  ``!xs xs2 ys ys2.
     (LENGTH xs = LENGTH ys) ==>
     (VarBindAux (xs ++ xs2) (ys ++ ys2) =
      FUNION (VarBindAux xs ys) (VarBindAux xs2 ys2))``,
  Induct \\ Cases_on `ys`
  \\ ASM_SIMP_TAC std_ss [APPEND,VarBindAux_def,FUNION_FEMPTY_1,
       LENGTH,ADD1,FUNION_FUPDATE_1]);

val VarBindAux_ELIM = prove(
  ``!vs a. EVERY (\v. v IN FDOM a) vs ==>
          ((FUNION (VarBindAux vs (MAP (\v. a ' v) vs)) a) = a)``,
  Induct \\ ASM_SIMP_TAC std_ss [VarBindAux_def,FUNION_FEMPTY_1,
    MAP,EVERY_DEF,FUNION_FUPDATE_1,SIMP_RULE std_ss [] FUPDATE_ELIM]);

val term2term_Let = prove(
  ``(!x' x.
        MEM (x',x) ts ==>
        !res ok2 ok a.
          funcs_ok x /\
          MR_ev (term2term x,a,ctxt,fns,ok) (res,ok2) ==>
          MR_ev (x,a,ctxt,fns,ok) (res,ok2)) /\
    (!res ok2 ok a.
        funcs_ok x /\
        MR_ev (term2term x,a,ctxt,fns,ok) (res,ok2) ==>
        MR_ev (x,a,ctxt,fns,ok) (res,ok2)) /\
    funcs_ok (Let ts x) /\
    MR_ev (term2term (Let ts x),a,ctxt,fns,ok) (res,ok2) ==>
    MR_ev (Let ts x,a,ctxt,fns,ok) (res,ok2)``,
  REPEAT STRIP_TAC
  \\ SIMP_TAC (srw_ss()) [Once MR_ev_cases]
  \\ SIMP_TAC (srw_ss()) [Once MR_ev_cases]
  \\ POP_ASSUM MP_TAC
  \\ SIMP_TAC std_ss [term2term_def,term2t_def,t2term_def,let2t_def,LET_DEF]
  \\ SIMP_TAC (srw_ss()) [Once MR_ev_cases]
  \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC std_ss [MAP_MAP_o]
  \\ Q.ABBREV_TAC `xs1 = (MAP (Sym o FST o (\(x',y). (x',term2t y)))) ts`
  \\ Q.ABBREV_TAC `xs2 = (MAP Sym (free_vars (term2t x)))`
  \\ Q.ABBREV_TAC `xs3 = (ISORT (\x y. getSym x <= getSym y) (FILTER
                 (\x. ~MEM x xs1) (REMOVE_DUPLICATES xs2)))`
  \\ `MAP ((\a. t2term a) o mVar o getSym) xs3 = MAP Var (MAP getSym xs3)` by (SIMP_TAC std_ss [MAP_MAP_o,o_DEF,t2term_def])
  \\ FULL_SIMP_TAC std_ss []
  \\ `MAP (getSym o Sym o FST o (\(x',y). (x',term2t y))) ts = MAP FST ts` by (SIMP_TAC std_ss [MAP_MAP_o,o_DEF,t2term_def,getSym_def]
         \\ CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV)
         \\ SIMP_TAC std_ss [] \\ CONV_TAC (DEPTH_CONV ETA_CONV)
         \\ SIMP_TAC std_ss [])
  \\ FULL_SIMP_TAC std_ss []
  \\ `MAP ((\a. t2term a) o SND o (\(x',y). (x',term2t y))) ts =
      MAP term2term (MAP SND ts)` by
        (SIMP_TAC std_ss [MAP_MAP_o,o_DEF,t2term_def,getSym_def]
         \\ CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV)
         \\ SIMP_TAC std_ss [term2term_def])
  \\ FULL_SIMP_TAC std_ss []
  \\ IMP_RES_TAC MR_evl_MAP_Var
  \\ FULL_SIMP_TAC std_ss [funcs_ok_def]
  \\ Q.LIST_EXISTS_TAC [`sl2`,`ok1`]
  \\ `FUNION (VarBind (MAP getSym xs3 ++ MAP FST ts)
               (MAP (\v. a ' v) (MAP getSym xs3) ++ sl2)) a =
      FUNION (VarBind (MAP FST ts) sl2) a` by
   (FULL_SIMP_TAC std_ss [VarBind_def,REVERSE_APPEND]
    \\ `LENGTH (REVERSE (MAP FST ts)) = LENGTH (REVERSE sl2)` by
       (IMP_RES_TAC MR_evl_LENGTH
        \\ FULL_SIMP_TAC std_ss [LENGTH_REVERSE,LENGTH_MAP])
    \\ IMP_RES_TAC VarBindAux_APPEND
    \\ FULL_SIMP_TAC std_ss [GSYM FUNION_ASSOC]
    \\ METIS_TAC [VarBindAux_ELIM,rich_listTheory.ALL_EL_REVERSE,rich_listTheory.MAP_REVERSE])
  \\ FULL_SIMP_TAC std_ss [GSYM term2term_def] \\ RES_TAC
  \\ Q.PAT_X_ASSUM `!x' x''. MEM (x',x'') ts ==> bbb` MP_TAC
  \\ Q.PAT_X_ASSUM `MR_evl (MAP term2term (MAP SND ts),a,xx) bb` MP_TAC
  \\ Q.PAT_X_ASSUM `EVERY (\(x',y). funcs_ok y) ts` MP_TAC
  \\ Q.SPEC_TAC (`ok`,`ok`) \\ Q.SPEC_TAC (`ok1`,`ok1`)
  \\ Q.SPEC_TAC (`sl2`,`sl2`) \\ Q.SPEC_TAC (`ts`,`ts`)
  \\ Induct \\ SIMP_TAC std_ss [MAP] \\ Cases
  \\ SIMP_TAC (srw_ss()) [Once MR_evl_cases] \\ REPEAT STRIP_TAC
  \\ ASM_SIMP_TAC (srw_ss()) [Once MR_evl_cases]
  \\ Q.LIST_EXISTS_TAC [`ok1''`]
  \\ STRIP_TAC THEN1 (FULL_SIMP_TAC std_ss [PULL_IMP,AND_IMP_INTRO])
  \\ Q.PAT_X_ASSUM `!sl:SExp list.bbb` ASSUME_TAC
  \\ FULL_SIMP_TAC std_ss [AND_IMP_INTRO]
  \\ POP_ASSUM MATCH_MP_TAC \\ METIS_TAC []);

val IMP_IMP = METIS_PROVE [] ``b1 /\ (b2 ==> b3) ==> ((b1 ==> b2) ==> b3)``;

val MEM_ISORT_INSERT = prove(
  ``!xs g x y. MEM x (ISORT_INSERT g y xs) = MEM x (y::xs)``,
  Induct \\ SRW_TAC [] [ISORT_INSERT_def,MEM] \\ METIS_TAC []);

val MEM_ISORT = prove(
  ``!xs x g. MEM x (ISORT g xs) = MEM x xs``,
  Induct \\ ASM_SIMP_TAC std_ss [ISORT_def,MEM,MEM_ISORT_INSERT]);

val FLAT_SNOC = prove(
  ``!xs x. FLAT (xs ++ [x]) = FLAT xs ++ x``,
  Induct \\ FULL_SIMP_TAC std_ss [FLAT,APPEND,APPEND_NIL,APPEND_ASSOC]);

val MEM_free_vars_or2t = prove(
  ``!xs.
      MEM "SPECIAL-VAR-FOR-OR" (free_vars (or2t xs)) =
      MEM "SPECIAL-VAR-FOR-OR" (FLAT (MAP free_vars xs))``,
  Cases THEN1 EVAL_TAC \\ Q.SPEC_TAC (`h`,`h`) \\ Induct_on `t`
  \\ ASM_SIMP_TAC std_ss [or2t_def,MAP,FLAT,APPEND_NIL,LET_DEF,MEM_APPEND]
  \\ STRIP_TAC \\ STRIP_TAC
  \\ Cases_on `MEM "SPECIAL-VAR-FOR-OR" (free_vars h)`
  \\ FULL_SIMP_TAC std_ss [free_vars_def,MAP,FLAT,MEM_APPEND]
  \\ Cases_on `MEM "SPECIAL-VAR-FOR-OR" (FLAT (MAP free_vars t))`
  \\ FULL_SIMP_TAC std_ss [free_vars_def,MAP,FLAT,MEM_APPEND]
  \\ Cases_on `isTrue (logic_variablep (t2sexp h'))`
  \\ FULL_SIMP_TAC std_ss [free_vars_def,MAP,FLAT,MEM_APPEND,MEM]
  \\ Cases_on `isTrue (logic_constantp (t2sexp h'))`
  \\ FULL_SIMP_TAC std_ss [free_vars_def,MAP,FLAT,MEM_APPEND,MEM]
  \\ SIMP_TAC std_ss [let2t_def,MAP,LET_DEF,free_vars_def,FLAT,APPEND,
       APPEND_NIL,REMOVE_DUPLICATES_def,MEM,MEM_APPEND,MAP_APPEND]
  \\ FULL_SIMP_TAC std_ss [FLAT_SNOC,MEM_APPEND]
  \\ MATCH_MP_TAC (METIS_PROVE [] ``~b ==> (b \/ c = c)``)
  \\ FULL_SIMP_TAC std_ss [MEM_FLAT]
  \\ FULL_SIMP_TAC std_ss [MEM_MAP,MEM_ISORT,MEM_FILTER]
  \\ SIMP_TAC std_ss [METIS_PROVE [] ``~b \/ c = b ==> c``]
  \\ SIMP_TAC std_ss [METIS_PROVE [] ``c \/ ~b = b ==> c``]
  \\ SIMP_TAC (srw_ss()) [PULL_IMP]
  \\ Cases \\ SIMP_TAC std_ss [free_vars_def,MEM,getSym_def,CONS_11,NOT_CONS_NIL]);

val term_ok_let2t = prove(
  ``term_ok ctxt (let2t xs y) ==>
    EVERY (\x. term_ok ctxt (SND x)) xs /\ term_ok ctxt y``,
  SIMP_TAC std_ss [let2t_def,LET_DEF,term_ok_def,EVERY_APPEND,EVERY_MEM,MEM_MAP]
  \\ SIMP_TAC std_ss [PULL_IMP]);

val term_ok_or2t = prove(
  ``!xs. term_ok ctxt (or2t xs) ==> EVERY (term_ok ctxt) xs``,
  Cases THEN1 (SIMP_TAC std_ss [EVERY_DEF])
  \\ Q.SPEC_TAC (`h`,`h`) \\ Q.SPEC_TAC (`t`,`t`) \\ Induct
  \\ SIMP_TAC std_ss [or2t_def,EVERY_DEF,LET_DEF]
  \\ SRW_TAC [] [] \\ FULL_SIMP_TAC std_ss [term_ok_def,EVERY_DEF]
  \\ RES_TAC \\ IMP_RES_TAC term_ok_let2t
  \\ FULL_SIMP_TAC std_ss [EVERY_DEF,term_ok_def] \\ RES_TAC);

val MEM_REMOVE_DUPLICATES = prove(
  ``!xs x. MEM x (REMOVE_DUPLICATES xs) = MEM x xs``,
  Induct \\ SRW_TAC [] [REMOVE_DUPLICATES_def,MEM] \\ METIS_TAC []);

val FLAT_APPEND = prove(
  ``!xs ys. FLAT (xs ++ ys) = FLAT xs ++ FLAT ys``,
  Induct \\ ASM_SIMP_TAC std_ss [APPEND,FLAT,APPEND_ASSOC]);

val MEM_free_vars_let2t = prove(
  ``MEM "SPECIAL-VAR-FOR-OR" (free_vars (let2t ts x)) =
    MEM "SPECIAL-VAR-FOR-OR"
      (FILTER (\v. ~MEM v (MAP FST ts)) (free_vars x) ++
       FLAT (MAP (\ (x,y). free_vars y) ts))``,
  SIMP_TAC std_ss [let2t_def,LET_DEF,free_vars_def,MAP_APPEND,FLAT_APPEND]
  \\ SIMP_TAC std_ss [MEM_APPEND]
  \\ FULL_SIMP_TAC std_ss [MAP_MAP_o,o_DEF]
  \\ `(\x. free_vars (SND x)) = (\(x:string,y). free_vars y)` by (FULL_SIMP_TAC std_ss [FUN_EQ_THM,pairTheory.FORALL_PROD])
  \\ FULL_SIMP_TAC std_ss []
  \\ Cases_on `MEM "SPECIAL-VAR-FOR-OR" (FLAT (MAP (\(x,y). free_vars y) ts))`
  \\ FULL_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC std_ss [MEM_FLAT]
  \\ FULL_SIMP_TAC std_ss [METIS_PROVE [] ``~b \/ c = b ==> c``]
  \\ FULL_SIMP_TAC std_ss [MEM_MAP,PULL_IMP,pairTheory.FORALL_PROD,PULL_CONJ]
  \\ FULL_SIMP_TAC std_ss [MEM_ISORT,MEM_FILTER,MEM_REMOVE_DUPLICATES]
  \\ FULL_SIMP_TAC std_ss [MEM_MAP]
  \\ FULL_SIMP_TAC std_ss [METIS_PROVE [] ``Q /\ (?x. P x) = ?x. Q /\ P x``]
  \\ FULL_SIMP_TAC std_ss [METIS_PROVE [] ``(?x. P x) /\ Q = ?x. Q /\ P x``]
  \\ FULL_SIMP_TAC (srw_ss()) [free_vars_def,getSym_def]);

val free_vars_term_vars = prove(
  ``!x. term_ok ctxt (term2t x) ==>
        (MEM "SPECIAL-VAR-FOR-OR" (free_vars (term2t x)) =
         MEM "SPECIAL-VAR-FOR-OR" (term_vars x))``,
  HO_MATCH_MP_TAC (fetch "-" "term2t_ind") \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [term2t_def,free_vars_def,term_vars_def,
       FLAT,MEM,MAP,APPEND_NIL,APPEND_ASSOC,MEM_APPEND,term_ok_def,EVERY_DEF]
  \\ IMP_RES_TAC term_ok_or2t
  \\ FULL_SIMP_TAC std_ss [MEM_FLAT,MEM_MAP,PULL_CONJ,MEM_free_vars_or2t,
       EVERY_MEM,PULL_CONJ,PULL_IMP,MEM_FILTER]
  THEN1 (METIS_TAC [])
  THEN1 (Cases_on `MEM "SPECIAL-VAR-FOR-OR" vs` \\ FULL_SIMP_TAC std_ss []
         \\ FULL_SIMP_TAC std_ss [SUBSET_DEF] \\ METIS_TAC [])
  THEN1 (METIS_TAC [])
  THEN1 (METIS_TAC [])
  THEN1 (FULL_SIMP_TAC std_ss [MEM_free_vars_let2t,MEM_FILTER,pairTheory.EXISTS_PROD,
           MEM_APPEND,MEM_FLAT,MEM_MAP,PULL_CONJ,pairTheory.FORALL_PROD]
         \\ IMP_RES_TAC term_ok_let2t
         \\ FULL_SIMP_TAC std_ss [EVERY_MEM,MEM_MAP,PULL_IMP,pairTheory.FORALL_PROD]
         \\ METIS_TAC []));

val term2term_Or = prove(
  ``!xs res ok ok2 a.
      (!x.
         MEM x xs ==>
          !res' ok2' ok' a'.
            MR_ev (term2term x,a',ctxt,fns,ok') (res',ok2') ==>
            MR_ev (x,a',ctxt,fns,ok') (res',ok2')) /\
      EVERY (term_ok ctxt5) (MAP term2t xs) /\ EVERY funcs_ok xs /\
      MR_ev (term2term (Or xs),a,ctxt,fns,ok) (res,ok2) ==>
      MR_ev (Or xs,a,ctxt,fns,ok) (res,ok2)``,
  Cases THEN1
   (SIMP_TAC std_ss [term2term_def,term2t_def,MAP,or2t_def,t2term_def,MEM]
    \\ REPEAT (ASM_SIMP_TAC (srw_ss()) [Once MR_ev_cases]))
  \\ SIMP_TAC std_ss [term2term_def,term2t_def]
  \\ Q.SPEC_TAC (`h`,`h`) \\ Q.SPEC_TAC (`t`,`t`) \\ Induct THEN1
   (SIMP_TAC std_ss [MAP,MEM,or2t_def,EVERY_DEF] \\ REPEAT STRIP_TAC
    \\ ASM_SIMP_TAC (srw_ss()) [Once MR_ev_cases] \\ RES_TAC
    \\ SIMP_TAC std_ss [isTrue_def]
    \\ Cases_on `res = Sym "NIL"` \\ FULL_SIMP_TAC std_ss []
    \\ ONCE_REWRITE_TAC [CONJ_COMM]
    \\ ASM_SIMP_TAC (srw_ss()) [Once MR_ev_cases]
    \\ ASM_SIMP_TAC (srw_ss()) [Once MR_ev_cases] \\ METIS_TAC [])
  \\ SIMP_TAC std_ss [or2t_def,MAP,LET_DEF]
  \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [METIS_PROVE [] ``b\/c = ~b ==> c``]
  \\ Cases_on `~isTrue (logic_variablep (t2sexp (term2t h'))) /\
               ~isTrue (logic_constantp (t2sexp (term2t h'))) ==>
               MEM "SPECIAL-VAR-FOR-OR" (free_vars (or2t (term2t h::MAP (\a. term2t a) t)))`
  \\ FULL_SIMP_TAC (srw_ss()) [t2term_def,LENGTH] THEN1
   (FULL_SIMP_TAC std_ss [LET_DEF]
    \\ POP_ASSUM (K ALL_TAC) \\ SIMP_TAC (srw_ss()) [Once MR_ev_cases]
    \\ POP_ASSUM MP_TAC \\ SIMP_TAC (srw_ss()) [Once MR_ev_cases]
    \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [] THEN1
     (DISJ2_TAC \\ Q.LIST_EXISTS_TAC [`ok1`,`s1`]
      \\ FULL_SIMP_TAC std_ss [PULL_IMP,AND_IMP_INTRO]
      \\ Q.PAT_X_ASSUM `!x1 x2 x3 x4 x5. bbb ==> MR_ev (Or xx,yyy) zz` MATCH_MP_TAC
      \\ FULL_SIMP_TAC std_ss [] \\ STRIP_TAC THEN1 (METIS_TAC [])
      \\ FULL_SIMP_TAC std_ss [GSYM lisp_extractTheory.R_ev_Or_SING_EQ])
    \\ IMP_RES_TAC MR_ev_11 \\ FULL_SIMP_TAC std_ss [] \\ DISJ1_TAC
    \\ `MR_ev (h',a,ctxt,fns,ok) (res,ok1)` by METIS_TAC []
    \\ `MR_ev (h',a,ctxt,fns,ok1) (res,ok2)` by METIS_TAC []
    \\ Cases_on `ok2` \\ IMP_RES_TAC MR_ev_OK \\ FULL_SIMP_TAC std_ss []
    \\ Cases_on `ok1` \\ IMP_RES_TAC MR_ev_OK \\ FULL_SIMP_TAC std_ss [])
  \\ SIMP_TAC (srw_ss()) [Once MR_ev_cases]
  \\ MP_TAC (term2term_Let
    |> Q.INST [`ts`|->`[("SPECIAL-VAR-FOR-OR",h')]`,
               `x`|->`If (Var "SPECIAL-VAR-FOR-OR") (Var "SPECIAL-VAR-FOR-OR") (Or (h::t))`]
    |> SIMP_RULE (srw_ss()) [term2term_def,t2term_def,term2t_def,funcs_ok_def,LET_DEF])
  \\ FULL_SIMP_TAC std_ss []
  \\ MATCH_MP_TAC IMP_IMP
  \\ STRIP_TAC THEN1
   (FULL_SIMP_TAC std_ss [EVERY_MEM]
    \\ REPEAT STRIP_TAC \\ POP_ASSUM MP_TAC
    \\ ONCE_REWRITE_TAC [MR_ev_cases] \\ SIMP_TAC (srw_ss()) []
    \\ SIMP_TAC std_ss [ONCE_REWRITE_CONV [MR_ev_cases] ``MR_ev (Var v,a,x) y``
         |> SIMP_RULE (srw_ss()) []] \\ METIS_TAC [MR_ev_OK])
  \\ SIMP_TAC (srw_ss()) [Once MR_ev_cases]
  \\ SIMP_TAC (srw_ss()) [Once MR_ev_cases]
  \\ SIMP_TAC (srw_ss()) [Once MR_ev_cases]
  \\ SIMP_TAC (srw_ss()) [Once MR_evl_cases,PULL_CONJ] \\ STRIP_TAC
  \\ Q.PAT_X_ASSUM `MR_ev xx yy` MP_TAC \\ SIMP_TAC (srw_ss()) [Once MR_ev_cases]
  \\ SIMP_TAC std_ss [ONCE_REWRITE_CONV [MR_ev_cases] ``MR_ev (Var v,a,x) y``
         |> SIMP_RULE (srw_ss()) [],FAPPLY_FUPDATE_THM,FDOM_FUPDATE,IN_INSERT]
  \\ FULL_SIMP_TAC std_ss [VarBind_def,VarBindAux_def,REVERSE_DEF,APPEND]
  \\ FULL_SIMP_TAC std_ss [FUNION_FUPDATE_1,FUNION_FEMPTY_1,
       FAPPLY_FUPDATE_THM,FDOM_FUPDATE,IN_INSERT]
  \\ REVERSE (REPEAT STRIP_TAC) THEN1 (FULL_SIMP_TAC std_ss [])
  \\ DISJ2_TAC \\ Q.LIST_EXISTS_TAC [`ok1`,`s`]
  \\ FULL_SIMP_TAC std_ss []
  \\ MATCH_MP_TAC MR_ev_VARS
  \\ Q.EXISTS_TAC `a |+ ("SPECIAL-VAR-FOR-OR",s)` \\ FULL_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC std_ss [FDOM_FUPDATE,FAPPLY_FUPDATE_THM,IN_INSERT]
  \\ STRIP_TAC \\ Cases_on `y = "SPECIAL-VAR-FOR-OR"` \\ FULL_SIMP_TAC std_ss []
  \\ STRIP_TAC \\ sg `F` \\ FULL_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC std_ss [term_vars_def,MEM_free_vars_or2t]
  \\ FULL_SIMP_TAC std_ss [MEM_FLAT,MEM_MAP]
  \\ `term2t h::MAP (\a. term2t a) t = MAP (\a. term2t a) (h::t)` by FULL_SIMP_TAC std_ss [MAP]
  \\ FULL_SIMP_TAC std_ss [] \\ POP_ASSUM (K ALL_TAC)
  \\ FULL_SIMP_TAC std_ss [MEM_MAP,EVERY_MEM,PULL_IMP]
  \\ METIS_TAC [free_vars_term_vars,MEM]);

val MR_ev_term2term = store_thm("MR_ev_term2term",
  ``!x res ok2 ok a.
      funcs_ok x /\ term_ok ctxt5 (term2t x) /\
      MR_ev (term2term x,a,ctxt,fns,ok) (res,ok2) ==>
      MR_ev (x,a,ctxt,fns,ok) (res,ok2)``,
  HO_MATCH_MP_TAC (fetch "-" "term2t_ind") \\ REPEAT STRIP_TAC
  THEN1 (FULL_SIMP_TAC (srw_ss()) [term2term_def,t2term_def,term2t_def,LENGTH])
  THEN1 (FULL_SIMP_TAC (srw_ss()) [term2term_def,t2term_def,term2t_def,LENGTH])
  THEN1 (FULL_SIMP_TAC (srw_ss()) [term2term_def,t2term_def,term2t_def,
           LENGTH,funcs_ok_def,LET_DEF,term_ok_def]
         \\ POP_ASSUM MP_TAC \\ ONCE_REWRITE_TAC [MR_ev_cases]
         \\ FULL_SIMP_TAC (srw_ss()) [] \\ METIS_TAC [])
  THEN1 (FULL_SIMP_TAC (srw_ss()) [term2term_def,t2term_def,term2t_def,
           LENGTH,funcs_ok_def,EVERY_MEM,term_ok_def]
         \\ IMP_RES_TAC f2func_func2f \\ FULL_SIMP_TAC std_ss []
         \\ Q.PAT_X_ASSUM `MR_ev xx yy` MP_TAC
         \\ ONCE_REWRITE_TAC [MR_ev_cases] \\ SIMP_TAC (srw_ss()) []
         \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss []
         \\ Q.LIST_EXISTS_TAC [`args`,`ok1`] \\ ASM_SIMP_TAC std_ss []
         \\ FULL_SIMP_TAC std_ss [] \\ RES_TAC \\ FULL_SIMP_TAC std_ss []
         \\ REPEAT (Q.PAT_X_ASSUM `!x.bbb` MP_TAC)
         \\ Q.PAT_X_ASSUM `MR_evl xx yy` MP_TAC
         \\ REPEAT (POP_ASSUM (K ALL_TAC))
         \\ Q.SPEC_TAC (`args`,`args`) \\ Q.SPEC_TAC (`ok`,`ok`)
         \\ Induct_on `xs` \\ FULL_SIMP_TAC std_ss [MAP,MEM]
         \\ SIMP_TAC (srw_ss()) [Once MR_ev_cases]
         \\ REPEAT STRIP_TAC \\ ASM_SIMP_TAC (srw_ss()) [Once MR_ev_cases]
         \\ FULL_SIMP_TAC (srw_ss()) [] \\ REPEAT STRIP_TAC \\ METIS_TAC [])
  THEN1 (FULL_SIMP_TAC (srw_ss()) [term2term_def,t2term_def,term2t_def,
           LENGTH,funcs_ok_def,EVERY_MEM,term_ok_def]
         \\ POP_ASSUM MP_TAC \\ ONCE_REWRITE_TAC [MR_ev_cases]
         \\ FULL_SIMP_TAC (srw_ss()) [] \\ REPEAT STRIP_TAC
         \\ FULL_SIMP_TAC std_ss [] \\ RES_TAC
         \\ Q.LIST_EXISTS_TAC [`sl`,`ok1`]
         \\ ASM_SIMP_TAC std_ss []
         \\ REPEAT (Q.PAT_X_ASSUM `!x.bbb` MP_TAC)
         \\ Q.PAT_X_ASSUM `MR_evl xx yy` MP_TAC
         \\ REPEAT (POP_ASSUM (K ALL_TAC))
         \\ Q.SPEC_TAC (`sl`,`sl`) \\ Q.SPEC_TAC (`ok`,`ok`)
         \\ Induct_on `xs` \\ FULL_SIMP_TAC std_ss [MAP,MEM]
         \\ SIMP_TAC (srw_ss()) [Once MR_ev_cases]
         \\ REPEAT STRIP_TAC \\ ASM_SIMP_TAC (srw_ss()) [Once MR_ev_cases]
         \\ FULL_SIMP_TAC (srw_ss()) [] \\ REPEAT STRIP_TAC \\ METIS_TAC [])
  THEN1 (FULL_SIMP_TAC std_ss [term_ok_def,term2t_def,EVERY_DEF]
         \\ METIS_TAC [term2term_First])
  THEN1 (FULL_SIMP_TAC std_ss [term_ok_def,term2t_def,EVERY_DEF]
         \\ METIS_TAC [term2term_Second])
  THEN1 (FULL_SIMP_TAC std_ss [term_ok_def,term2t_def,EVERY_DEF]
         \\ METIS_TAC [term2term_Third])
  THEN1 (FULL_SIMP_TAC std_ss [term_ok_def,term2t_def,EVERY_DEF]
         \\ METIS_TAC [term2term_Fourth])
  THEN1 (FULL_SIMP_TAC std_ss [term_ok_def,term2t_def,EVERY_DEF]
         \\ METIS_TAC [term2term_Fifth])
  THEN1 (MATCH_MP_TAC term2term_Or
         \\ FULL_SIMP_TAC std_ss [EVERY_MEM,funcs_ok_def,term_ok_def]
         \\ FULL_SIMP_TAC std_ss [term2t_def]
         \\ IMP_RES_TAC term_ok_or2t
         \\ FULL_SIMP_TAC std_ss [EVERY_MEM,MEM_MAP,PULL_IMP])
  THEN1 (SIMP_TAC (srw_ss()) [Once MR_ev_cases] \\ POP_ASSUM MP_TAC
         \\ SIMP_TAC (srw_ss()) [Once MR_ev_cases,term2term_def,term2t_def,t2term_def]
         \\ SIMP_TAC (srw_ss()) [Once MR_ev_cases,term2term_def,term2t_def,t2term_def])
  THEN1 (SIMP_TAC (srw_ss()) [Once MR_ev_cases] \\ POP_ASSUM MP_TAC
         \\ FULL_SIMP_TAC std_ss [term2term_def,term2t_def,t2term_def,funcs_ok_def,EVERY_DEF])
  THEN1 (SIMP_TAC (srw_ss()) [Once MR_ev_cases] \\ POP_ASSUM MP_TAC
         \\ SIMP_TAC std_ss [term2term_def,term2t_def,t2term_def,LENGTH]
         \\ SIMP_TAC (srw_ss()) [LET_DEF]
         \\ FULL_SIMP_TAC std_ss [funcs_ok_def,EVERY_DEF,term_ok_def,term2t_def]
         \\ ONCE_REWRITE_TAC [MR_ev_cases] \\ SIMP_TAC (srw_ss()) [t2term_def]
         \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [term2term_def]
         \\ RES_TAC \\ METIS_TAC [])
  THEN1 (SIMP_TAC (srw_ss()) [Once MR_ev_cases] \\ POP_ASSUM MP_TAC
         \\ SIMP_TAC (srw_ss()) [Once MR_ev_cases,term2term_def,term2t_def,t2term_def]
         \\ SIMP_TAC (srw_ss()) [Once MR_ev_cases,term2term_def,term2t_def,t2term_def])
  THEN1 (SIMP_TAC (srw_ss()) [Once MR_ev_cases]
         \\ SIMP_TAC (srw_ss()) [Once MR_ev_cases]
         \\ SIMP_TAC (srw_ss()) [Once MR_ap_cases,EVAL_DATA_OP_def]
         \\ SIMP_TAC (srw_ss()) [Once MR_evl_cases]
         \\ SIMP_TAC (srw_ss()) [Once MR_evl_cases]
         \\ SIMP_TAC (srw_ss()) [Once MR_evl_cases,PULL_CONJ]
         \\ SRW_TAC [] [] \\ POP_ASSUM MP_TAC
         \\ FULL_SIMP_TAC (srw_ss()) [term2term_def,t2term_def,term2t_def,f2func_def]
         \\ SIMP_TAC (srw_ss()) [Once MR_ev_cases]
         \\ SIMP_TAC (srw_ss()) [Once MR_ap_cases,EVAL_DATA_OP_def]
         \\ SIMP_TAC (srw_ss()) [Once MR_evl_cases]
         \\ SIMP_TAC (srw_ss()) [Once MR_evl_cases]
         \\ SIMP_TAC (srw_ss()) [Once MR_evl_cases,PULL_CONJ]
         \\ REPEAT STRIP_TAC
         \\ FULL_SIMP_TAC std_ss [funcs_ok_def,EVERY_DEF,term_ok_def]
         \\ METIS_TAC [])
  THEN1 (MATCH_MP_TAC term2term_Let
         \\ FULL_SIMP_TAC std_ss [EVERY_MEM,funcs_ok_def,term_ok_def]
         \\ FULL_SIMP_TAC std_ss [term2t_def]
         \\ IMP_RES_TAC term_ok_let2t
         \\ FULL_SIMP_TAC std_ss [EVERY_MEM,MEM_MAP,PULL_IMP]
         \\ FULL_SIMP_TAC std_ss [pairTheory.FORALL_PROD] \\ METIS_TAC [])
  THEN1 (SIMP_TAC (srw_ss()) [Once MR_ev_cases] \\ POP_ASSUM MP_TAC
         \\ SIMP_TAC (srw_ss()) [Once MR_ev_cases,term2term_def,term2t_def,t2term_def]
         \\ SIMP_TAC (srw_ss()) [Once MR_ev_cases,term2term_def,term2t_def,t2term_def])
  THEN1 (SIMP_TAC (srw_ss()) [Once MR_ev_cases] \\ POP_ASSUM MP_TAC
         \\ FULL_SIMP_TAC (srw_ss()) [term2term_def,t2term_def,term2t_def,f2func_def]
         \\ FULL_SIMP_TAC std_ss [LET_DEF]
         \\ SIMP_TAC (srw_ss()) [Once MR_ev_cases]
         \\ FULL_SIMP_TAC std_ss [funcs_ok_def,EVERY_DEF,term_ok_def]
         \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss []
         \\ SIMP_TAC (srw_ss()) [Once MR_ev_cases]
         \\ FULL_SIMP_TAC std_ss [] \\ RES_TAC \\ METIS_TAC [])
  THEN1 (SIMP_TAC (srw_ss()) [Once MR_ev_cases] \\ POP_ASSUM MP_TAC
         \\ FULL_SIMP_TAC std_ss [term2term_def,term2t_def,t2term_def,funcs_ok_def,EVERY_DEF])
  THEN1 (SIMP_TAC (srw_ss()) [Once MR_ev_cases]
         \\ Q.PAT_X_ASSUM `!x.bbb` MATCH_MP_TAC \\ POP_ASSUM MP_TAC
         \\ FULL_SIMP_TAC std_ss [term2term_def,term2t_def,funcs_ok_def,EVERY_DEF])
  THEN1 (SIMP_TAC (srw_ss()) [Once MR_ev_cases] \\ POP_ASSUM MP_TAC
         \\ FULL_SIMP_TAC (srw_ss()) [term2term_def,term2t_def,t2term_def,
               funcs_ok_def,EVERY_DEF,f2func_def]));

(* M_ev ==> MR_ev *)

val VarBindAux_lemma = prove(
  ``!params t.
      ~MEM p params /\ (LENGTH params = LENGTH t) ==>
      (VarBindAux (params ++ [p]) (t ++ [h]) =
       VarBindAux (params) t |+ (p,h))``,
  Induct \\ Cases_on `t` \\ FULL_SIMP_TAC std_ss [ADD1,LENGTH] THEN1 EVAL_TAC
  \\ ASM_SIMP_TAC std_ss [APPEND,MEM,VarBindAux_def]
  \\ METIS_TAC [FUPDATE_COMMUTES]);

val VarBind_CONS = prove(
  ``!params t.
      ~MEM p params /\ (LENGTH params = LENGTH t) ==>
      (VarBind (p::params) (h::t) = VarBind params t |+ (p,h))``,
  SIMP_TAC std_ss [VarBind_def,REVERSE_DEF] \\ Induct
  \\ Cases_on `t` \\ FULL_SIMP_TAC std_ss [ADD1,LENGTH] THEN1 EVAL_TAC
  \\ REPEAT STRIP_TAC \\ MATCH_MP_TAC VarBindAux_lemma
  \\ FULL_SIMP_TAC std_ss [LENGTH_REVERSE,LENGTH,MEM_REVERSE]);

val params_lemma = store_thm("params_lemma",
  ``!params args (v:string).
       MEM v params /\ (LENGTH args = LENGTH params) /\ ALL_DISTINCT params ==>
       v IN FDOM (VarBind params args) /\
       (VarBind params args ' v = FunVarBind params args v)``,
  Induct \\ SIMP_TAC std_ss [MEM]
  \\ Cases_on `args` \\ FULL_SIMP_TAC std_ss [LENGTH,ADD1]
  \\ FULL_SIMP_TAC std_ss [FunVarBind_def,APPLY_UPDATE_THM]
  \\ ASM_SIMP_TAC std_ss [VarBind_CONS,ALL_DISTINCT]
  \\ FULL_SIMP_TAC std_ss [FAPPLY_FUPDATE_THM,
        FDOM_FUPDATE,IN_INSERT]
  \\ METIS_TAC []);

val LENGTH_EQ_1 = prove(
  ``(1 = LENGTH xs) = ?x1. xs = [x1]``,
  Cases_on `xs` \\ SIMP_TAC (srw_ss()) []
  \\ Cases_on `t` \\ SIMP_TAC (srw_ss()) []
  \\ Cases_on `t'` \\ SIMP_TAC (srw_ss()) []
  \\ Cases_on `t` \\ SIMP_TAC (srw_ss()) []
  \\ DECIDE_TAC)

val LENGTH_EQ_2 = prove(
  ``(2 = LENGTH xs) = ?x1 x2. xs = [x1;x2]``,
  Cases_on `xs` \\ SIMP_TAC (srw_ss()) []
  \\ Cases_on `t` \\ SIMP_TAC (srw_ss()) []
  \\ Cases_on `t'` \\ SIMP_TAC (srw_ss()) []
  \\ Cases_on `t` \\ SIMP_TAC (srw_ss()) []
  \\ DECIDE_TAC)

val rank_lemma = prove(
  ``!x1. rank x1 = Val (LSIZE x1)``,
  REVERSE Induct \\ ONCE_REWRITE_TAC [rank_def]
  \\ FULL_SIMP_TAC (srw_ss()) [LSIZE_def,LISP_CONSP_def,isDot_def,
       LISP_TEST_def,isTrue_def,LISP_ADD_def,getVal_def,CDR_def,CAR_def]
 \\ DECIDE_TAC);

val LISP_TEST_THM = prove(
  ``!b. (isTrue (LISP_TEST b) = b) /\
        ((LISP_TEST b = Sym "NIL") = ~b) /\ ((LISP_TEST b = Sym "T") = b)``,
  Cases \\ FULL_SIMP_TAC std_ss [] \\ EVAL_TAC);

val isTrue_not = prove(
  ``!x. isTrue (not x) = ~isTrue x``,
  SIMP_TAC std_ss [isTrue_def,not_def] \\ SRW_TAC [] []);

val ord__lemma = prove(
  ``!x1 x2. LISP_TEST (ORD_LT x1 x2) = ord_ x1 x2``,
  HO_MATCH_MP_TAC milawa_ordinalTheory.ORD_LT_ind \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss []
  \\ ONCE_REWRITE_TAC [milawa_ordinalTheory.ORD_LT_def,ord__def]
  \\ SRW_TAC [] [LISP_TEST_def,LISP_LESS_def,isTrue_not,LISP_CONSP_def]
  \\ FULL_SIMP_TAC (srw_ss()) [lisp_extractTheory.isTrue_CLAUSES]
  \\ REPEAT (POP_ASSUM MP_TAC) \\ FULL_SIMP_TAC (srw_ss()) [isTrue_def]
  \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC std_ss [LISP_TEST_def]
  \\ Cases_on `isDot x2` \\ FULL_SIMP_TAC std_ss []);

val ordp_lemma = prove(
  ``!x1. LISP_TEST (ORDP x1) = ordp x1``,
  ONCE_REWRITE_TAC [EQ_SYM_EQ]
  \\ HO_MATCH_MP_TAC milawa_ordinalTheory.ORDP_ind \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss []
  \\ ONCE_REWRITE_TAC [milawa_ordinalTheory.ORDP_def,ordp_def]
  \\ SRW_TAC [] [LISP_TEST_def,LISP_LESS_def,isTrue_not,LISP_CONSP_def]
  \\ FULL_SIMP_TAC (srw_ss()) [lisp_extractTheory.isTrue_CLAUSES]
  \\ FULL_SIMP_TAC std_ss [LISP_NUMBERP_def,LISP_TEST_def]
  \\ REPEAT (POP_ASSUM MP_TAC)
  \\ SRW_TAC [] [] \\ FULL_SIMP_TAC std_ss [isTrue_def,getVal_def]
  \\ FULL_SIMP_TAC std_ss [GSYM ord__lemma,LISP_TEST_def]);

val fake_ftbl_entries_def = Define `
  fake_ftbl_entries =
    ["IF"; "EQUAL"; "SYMBOLP"; "SYMBOL-<"; "NATP"; "<"; "+"; "-";
     "CONSP"; "CONS"; "CAR"; "CDR"; "ERROR"; "PRINT"; "DEFINE";
     "DEFUN"; "FUNCALL"; "LOOKUP-SAFE"; "DEFINE-SAFE";
     "DEFINE-SAFE-LIST"; "MILAWA-INIT"; "MILAWA-MAIN"]`;

val MilawaTrueFun_def = Define `
  MilawaTrueFun ctxt f args result =
    MilawaTrue ctxt (Equal (mApp (mFun f) (MAP mConst args)) (mConst result))`;

val runtime_inv_def = Define `
  runtime_inv (ctxt:context_type) k =
    !name params body sem args ok.
      name IN FDOM ctxt /\ (ctxt ' name = (params,body,sem)) /\
      (LENGTH args = LENGTH params) ==>
      ?ok2. MR_ap (Fun name,args,ARB,ctxt,k,ok) (sem args,ok2) /\
            (ok2 ==> MilawaTrueFun ctxt name args (sem args))`;

val MR_ap_CTXT = prove(
  ``MR_ap (Fun fc,args,a,ctxt \\ name,k,ok) (sem args,ok2) ==>
    MR_ap (Fun fc,args,a,ctxt,k,ok) (sem args,ok2)``,
  METIS_TAC [MR_ev_CTXT]);


(* M_IMP_MilawaTrue *)

val MilawaTrue_MP = prove(
  ``context_ok ctxt /\
    MilawaTrue ctxt a /\ MilawaTrue ctxt (Or (Not a) b) ==>
    MilawaTrue ctxt b``,
  REPEAT STRIP_TAC \\ IMP_RES_TAC MilawaTrue_IMP_formula_ok
  \\ FULL_SIMP_TAC std_ss [formula_ok_def] \\ METIS_TAC [MilawaTrue_rules]);

val MilawaTrue_MP2 = prove(
  ``context_ok ctxt /\
    MilawaTrue ctxt (Not a) /\ MilawaTrue ctxt (Or a b) ==>
    MilawaTrue ctxt b``,
  REPEAT STRIP_TAC \\ IMP_RES_TAC MilawaTrue_IMP_formula_ok
  \\ FULL_SIMP_TAC std_ss [formula_ok_def]
  \\ METIS_TAC [MilawaTrue_rules,formula_ok_def]);

val MilawaTrue_REFL = prove(
  ``term_ok ctxt x ==> MilawaTrue ctxt (Equal x x)``,
  REPEAT STRIP_TAC
  \\ `MEM (HD MILAWA_AXIOMS) MILAWA_AXIOMS` by EVAL_TAC
  \\ FULL_SIMP_TAC std_ss [EVAL ``HD MILAWA_AXIOMS``]
  \\ `MilawaTrue ctxt (Equal (mVar "X") (mVar "X"))` by METIS_TAC [MilawaTrue_rules]
  \\ `Equal x x = formula_sub [("X",x)] (Equal (mVar "X") (mVar "X"))` by EVAL_TAC
  \\ FULL_SIMP_TAC std_ss []
  \\ MATCH_MP_TAC (MilawaTrue_rules |> CONJUNCTS |> el 7)
  \\ FULL_SIMP_TAC std_ss [] \\ EVAL_TAC \\ FULL_SIMP_TAC std_ss []);

val MilawaTrue_Sym = prove(
  ``context_ok ctxt /\
    MilawaTrue ctxt (Equal x y) ==> MilawaTrue ctxt (Equal y x)``,
  REPEAT STRIP_TAC \\ IMP_RES_TAC MilawaTrue_IMP_formula_ok
  \\ FULL_SIMP_TAC std_ss [formula_ok_def]
  \\ IMP_RES_TAC MilawaTrue_REFL
  \\ `MEM (EL 1 MILAWA_AXIOMS) MILAWA_AXIOMS` by EVAL_TAC
  \\ FULL_SIMP_TAC std_ss [EVAL ``EL 1 MILAWA_AXIOMS``]
  \\ IMP_RES_TAC (MilawaTrue_rules |> CONJUNCTS |> el 10)
  \\ POP_ASSUM (MP_TAC o SPEC_ALL)
  \\ Q.PAT_ABBREV_TAC `orrr = Or x1 x2` \\ STRIP_TAC
  \\ `formula_ok ctxt (formula_sub [("X1",x);("X2",x);("Y1",y);("Y2",x)] orrr)` by (Q.UNABBREV_TAC `orrr` \\ EVAL_TAC \\ FULL_SIMP_TAC std_ss [])
  \\ IMP_RES_TAC (MilawaTrue_rules |> CONJUNCTS |> el 7)
  \\ REPEAT (Q.PAT_X_ASSUM `!xx.bbb` (K ALL_TAC))
  \\ Q.UNABBREV_TAC `orrr` \\ POP_ASSUM MP_TAC
  \\ SIMP_TAC (srw_ss()) [formula_sub_def,term_sub_def,LOOKUP_def]
  \\ METIS_TAC [MilawaTrue_MP]);

val MilawaTrue_TRANS = store_thm("MilawaTrue_TRANS",
  ``context_ok ctxt /\
    MilawaTrue ctxt (Equal x y) /\ MilawaTrue ctxt (Equal y z) ==>
    MilawaTrue ctxt (Equal x z)``,
  REPEAT STRIP_TAC \\ IMP_RES_TAC MilawaTrue_IMP_formula_ok
  \\ FULL_SIMP_TAC std_ss [formula_ok_def]
  \\ IMP_RES_TAC MilawaTrue_REFL
  \\ `MEM (EL 1 MILAWA_AXIOMS) MILAWA_AXIOMS` by EVAL_TAC
  \\ FULL_SIMP_TAC std_ss [EVAL ``EL 1 MILAWA_AXIOMS``]
  \\ IMP_RES_TAC (MilawaTrue_rules |> CONJUNCTS |> el 10)
  \\ POP_ASSUM (MP_TAC o SPEC_ALL)
  \\ Q.PAT_ABBREV_TAC `orrr = Or x1 x2` \\ STRIP_TAC
  \\ `formula_ok ctxt (formula_sub [("X1",y);("X2",y);("Y1",x);("Y2",z)] orrr)` by (Q.UNABBREV_TAC `orrr` \\ EVAL_TAC \\ FULL_SIMP_TAC std_ss [])
  \\ IMP_RES_TAC (MilawaTrue_rules |> CONJUNCTS |> el 7)
  \\ REPEAT (Q.PAT_X_ASSUM `!xx.bbb` (K ALL_TAC))
  \\ Q.UNABBREV_TAC `orrr` \\ POP_ASSUM MP_TAC
  \\ SIMP_TAC (srw_ss()) [formula_sub_def,term_sub_def,LOOKUP_def]
  \\ METIS_TAC [MilawaTrue_MP,MilawaTrue_Sym]) |> GEN_ALL;

val MilawaTrue_IF1 = prove(
  ``context_ok ctxt /\
    MilawaTrue ctxt (Equal e1 (mConst s1)) /\ ~isTrue s1 /\
    MilawaTrue ctxt (Equal e3 (mConst s)) /\ term_ok ctxt e2 ==>
    MilawaTrue ctxt (Equal (mApp (mPrimitiveFun logic_IF) [e1;e2;e3]) (mConst s))``,
  REPEAT STRIP_TAC \\ IMP_RES_TAC MilawaTrue_IMP_formula_ok
  \\ FULL_SIMP_TAC std_ss [formula_ok_def]
  \\ IMP_RES_TAC MilawaTrue_Sym \\ MATCH_MP_TAC MilawaTrue_TRANS
  \\ Q.EXISTS_TAC `e3` \\ FULL_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC std_ss [isTrue_def]
  \\ `MEM (EL 5 MILAWA_AXIOMS) MILAWA_AXIOMS` by EVAL_TAC
  \\ FULL_SIMP_TAC std_ss [EVAL ``EL 5 MILAWA_AXIOMS``]
  \\ IMP_RES_TAC (MilawaTrue_rules |> CONJUNCTS |> el 10)
  \\ POP_ASSUM (MP_TAC o SPEC_ALL)
  \\ Q.PAT_ABBREV_TAC `orrr = Or x1 x2` \\ STRIP_TAC
  \\ `formula_ok ctxt (formula_sub [("X",e1);("Y",e2);("Z",e3)] orrr)` by (Q.UNABBREV_TAC `orrr` \\ EVAL_TAC \\ FULL_SIMP_TAC std_ss [])
  \\ IMP_RES_TAC (MilawaTrue_rules |> CONJUNCTS |> el 7)
  \\ REPEAT (Q.PAT_X_ASSUM `!xx.bbb` (K ALL_TAC))
  \\ Q.UNABBREV_TAC `orrr` \\ POP_ASSUM MP_TAC
  \\ SIMP_TAC (srw_ss()) [formula_sub_def,term_sub_def,LOOKUP_def]
  \\ METIS_TAC [MilawaTrue_MP]);

val MilawaTrue_Or_Sym = prove(
  ``context_ok ctxt /\
    MilawaTrue ctxt (Or x y) ==> MilawaTrue ctxt (Or y x)``,
  REPEAT STRIP_TAC \\ IMP_RES_TAC MilawaTrue_IMP_formula_ok
  \\ FULL_SIMP_TAC std_ss [formula_ok_def] \\ METIS_TAC [MilawaTrue_rules]);

val MilawaTrue_Or_Sym_RW = prove(
  ``context_ok ctxt ==>
    (MilawaTrue ctxt (Or x y) = MilawaTrue ctxt (Or y x))``,
  METIS_TAC [MilawaTrue_Or_Sym]);

val MilawaTrue_Or_ASSOC = prove(
  ``context_ok ctxt /\
    MilawaTrue ctxt (Or x (Or y z)) ==> MilawaTrue ctxt (Or (Or x y) z)``,
  REPEAT STRIP_TAC \\ IMP_RES_TAC MilawaTrue_IMP_formula_ok
  \\ FULL_SIMP_TAC std_ss [formula_ok_def] \\ METIS_TAC [MilawaTrue_rules]);

val MilawaTrue_Or_ASSOC_COMM = prove(
  ``context_ok ctxt /\
    MilawaTrue ctxt (Or x (Or y z)) ==> MilawaTrue ctxt (Or z (Or x y))``,
  METIS_TAC [MilawaTrue_Or_ASSOC,MilawaTrue_Or_Sym]);

val MilawaTrue_Not_Equal = prove(
  ``context_ok ctxt /\
    MilawaTrue ctxt (Equal x y) /\ MilawaTrue ctxt (Not (Equal y z)) ==>
    MilawaTrue ctxt (Not (Equal x z))``,
  REPEAT STRIP_TAC \\ IMP_RES_TAC MilawaTrue_IMP_formula_ok
  \\ FULL_SIMP_TAC std_ss [formula_ok_def]
  \\ IMP_RES_TAC MilawaTrue_REFL
  \\ `MEM (EL 1 MILAWA_AXIOMS) MILAWA_AXIOMS` by EVAL_TAC
  \\ FULL_SIMP_TAC std_ss [EVAL ``EL 1 MILAWA_AXIOMS``]
  \\ IMP_RES_TAC (MilawaTrue_rules |> CONJUNCTS |> el 10)
  \\ POP_ASSUM (MP_TAC o SPEC_ALL)
  \\ Q.PAT_ABBREV_TAC `orrr = Or x1 x2` \\ STRIP_TAC
  \\ `formula_ok ctxt (formula_sub [("X1",x);("X2",x);("Y1",y);("Y2",z)] orrr)` by (Q.UNABBREV_TAC `orrr` \\ EVAL_TAC \\ FULL_SIMP_TAC std_ss [])
  \\ IMP_RES_TAC (MilawaTrue_rules |> CONJUNCTS |> el 7)
  \\ REPEAT (Q.PAT_X_ASSUM `!xx.bbb` (K ALL_TAC))
  \\ Q.UNABBREV_TAC `orrr` \\ POP_ASSUM MP_TAC
  \\ SIMP_TAC (srw_ss()) [formula_sub_def,term_sub_def,LOOKUP_def]
  \\ REPEAT STRIP_TAC
  \\ `MilawaTrue ctxt (Or (Not (Equal x z)) (Or (Not (Equal x x)) (Equal y z)))` by
       IMP_RES_TAC MilawaTrue_MP
  \\ `MilawaTrue ctxt (Or (Or (Not (Equal x z)) (Not (Equal x x))) (Equal y z))` by
       IMP_RES_TAC MilawaTrue_Or_ASSOC
  \\ `MilawaTrue ctxt (Or (Not (Equal x z)) (Not (Equal x x)))` by
       METIS_TAC [MilawaTrue_MP2,MilawaTrue_Or_Sym]
  \\ METIS_TAC [MilawaTrue_MP,MilawaTrue_Or_Sym]) |> GEN_ALL;

val MilawaTrue_Not_Equal_COMM = prove(
  ``context_ok ctxt /\
    MilawaTrue ctxt (Not (Equal y x)) ==> MilawaTrue ctxt (Not (Equal x y))``,
  REPEAT STRIP_TAC \\ IMP_RES_TAC MilawaTrue_IMP_formula_ok
  \\ FULL_SIMP_TAC std_ss [formula_ok_def]
  \\ IMP_RES_TAC MilawaTrue_REFL
  \\ `MEM (EL 1 MILAWA_AXIOMS) MILAWA_AXIOMS` by EVAL_TAC
  \\ FULL_SIMP_TAC std_ss [EVAL ``EL 1 MILAWA_AXIOMS``]
  \\ IMP_RES_TAC (MilawaTrue_rules |> CONJUNCTS |> el 10)
  \\ POP_ASSUM (MP_TAC o SPEC_ALL)
  \\ Q.PAT_ABBREV_TAC `orrr = Or x1 x2` \\ STRIP_TAC
  \\ `formula_ok ctxt (formula_sub [("X1",x);("X2",x);("Y1",y);("Y2",x)] orrr)` by (Q.UNABBREV_TAC `orrr` \\ EVAL_TAC \\ FULL_SIMP_TAC std_ss [])
  \\ IMP_RES_TAC (MilawaTrue_rules |> CONJUNCTS |> el 7)
  \\ REPEAT (Q.PAT_X_ASSUM `!xx.bbb` (K ALL_TAC))
  \\ Q.UNABBREV_TAC `orrr` \\ POP_ASSUM MP_TAC
  \\ SIMP_TAC (srw_ss()) [formula_sub_def,term_sub_def,LOOKUP_def]
  \\ REPEAT STRIP_TAC
  \\ IMP_RES_TAC MilawaTrue_Or_ASSOC \\ POP_ASSUM (K ALL_TAC)
  \\ IMP_RES_TAC MilawaTrue_Or_ASSOC \\ POP_ASSUM (K ALL_TAC)
  \\ IMP_RES_TAC (ONCE_REWRITE_RULE [MilawaTrue_Or_Sym_RW] MilawaTrue_MP2)
  \\ METIS_TAC [MilawaTrue_MP,MilawaTrue_Or_Sym]) |> GEN_ALL;

val MilawaTrue_AX2 = prove(
  ``context_ok ctxt ==>
    MilawaTrue ctxt (Equal x1 y1) ==>
    MilawaTrue ctxt (Equal x2 y2) ==>
    MilawaTrue ctxt (Equal x1 x2) ==>
    MilawaTrue ctxt (Equal y1 y2)``,
  REPEAT STRIP_TAC \\ IMP_RES_TAC MilawaTrue_IMP_formula_ok
  \\ FULL_SIMP_TAC std_ss [formula_ok_def]
  \\ IMP_RES_TAC MilawaTrue_REFL
  \\ `MEM (EL 1 MILAWA_AXIOMS) MILAWA_AXIOMS` by EVAL_TAC
  \\ FULL_SIMP_TAC std_ss [EVAL ``EL 1 MILAWA_AXIOMS``]
  \\ IMP_RES_TAC (MilawaTrue_rules |> CONJUNCTS |> el 10)
  \\ POP_ASSUM (MP_TAC o SPEC_ALL)
  \\ Q.PAT_ABBREV_TAC `orrr = Or xx1 xx2` \\ STRIP_TAC
  \\ `formula_ok ctxt (formula_sub [("X1",x1);("X2",x2);("Y1",y1);("Y2",y2)] orrr)` by (Q.UNABBREV_TAC `orrr` \\ EVAL_TAC \\ FULL_SIMP_TAC std_ss [])
  \\ IMP_RES_TAC (MilawaTrue_rules |> CONJUNCTS |> el 7)
  \\ REPEAT (Q.PAT_X_ASSUM `!xx.bbb` (K ALL_TAC))
  \\ Q.UNABBREV_TAC `orrr` \\ POP_ASSUM MP_TAC
  \\ SIMP_TAC (srw_ss()) [formula_sub_def,term_sub_def,LOOKUP_def]
  \\ METIS_TAC [MilawaTrue_MP,MilawaTrue_Or_Sym]) |> GEN_ALL;

val MilawaTrue_AX4 = prove(
  ``context_ok ctxt /\
    term_ok ctxt x /\ term_ok ctxt y ==>
    MilawaTrue ctxt (Or (Not (Equal x y))
                        (Equal (mApp (mPrimitiveFun logic_EQUAL) [x; y])
                               (mConst (Sym "T"))))``,
  REPEAT STRIP_TAC \\ IMP_RES_TAC MilawaTrue_IMP_formula_ok
  \\ FULL_SIMP_TAC std_ss [formula_ok_def]
  \\ IMP_RES_TAC MilawaTrue_REFL
  \\ `MEM (EL 3 MILAWA_AXIOMS) MILAWA_AXIOMS` by EVAL_TAC
  \\ FULL_SIMP_TAC std_ss [EVAL ``EL 3 MILAWA_AXIOMS``]
  \\ IMP_RES_TAC (MilawaTrue_rules |> CONJUNCTS |> el 10)
  \\ POP_ASSUM (MP_TAC o SPEC_ALL)
  \\ Q.PAT_ABBREV_TAC `orrr = Or x1 x2` \\ STRIP_TAC
  \\ `formula_ok ctxt (formula_sub [("X",x);("Y",y)] orrr)` by (Q.UNABBREV_TAC `orrr` \\ EVAL_TAC \\ FULL_SIMP_TAC std_ss [])
  \\ IMP_RES_TAC (MilawaTrue_rules |> CONJUNCTS |> el 7)
  \\ REPEAT (Q.PAT_X_ASSUM `!xx.bbb` (K ALL_TAC))
  \\ Q.UNABBREV_TAC `orrr` \\ POP_ASSUM MP_TAC
  \\ SIMP_TAC (srw_ss()) [formula_sub_def,term_sub_def,LOOKUP_def]);

val MilawaTrue_AX5 = prove(
  ``context_ok ctxt /\
    term_ok ctxt x /\ term_ok ctxt y ==>
    MilawaTrue ctxt (Or (Equal x y)
                        (Equal (mApp (mPrimitiveFun logic_EQUAL) [x; y])
                               (mConst (Sym "NIL"))))``,
  REPEAT STRIP_TAC \\ IMP_RES_TAC MilawaTrue_IMP_formula_ok
  \\ FULL_SIMP_TAC std_ss [formula_ok_def]
  \\ IMP_RES_TAC MilawaTrue_REFL
  \\ `MEM (EL 4 MILAWA_AXIOMS) MILAWA_AXIOMS` by EVAL_TAC
  \\ FULL_SIMP_TAC std_ss [EVAL ``EL 4 MILAWA_AXIOMS``]
  \\ IMP_RES_TAC (MilawaTrue_rules |> CONJUNCTS |> el 10)
  \\ POP_ASSUM (MP_TAC o SPEC_ALL)
  \\ Q.PAT_ABBREV_TAC `orrr = Or x1 x2` \\ STRIP_TAC
  \\ `formula_ok ctxt (formula_sub [("X",x);("Y",y)] orrr)` by (Q.UNABBREV_TAC `orrr` \\ EVAL_TAC \\ FULL_SIMP_TAC std_ss [])
  \\ IMP_RES_TAC (MilawaTrue_rules |> CONJUNCTS |> el 7)
  \\ REPEAT (Q.PAT_X_ASSUM `!xx.bbb` (K ALL_TAC))
  \\ Q.UNABBREV_TAC `orrr` \\ POP_ASSUM MP_TAC
  \\ SIMP_TAC (srw_ss()) [formula_sub_def,term_sub_def,LOOKUP_def]);

val MilawaTrue_AX5 = prove(
  ``context_ok ctxt /\
    term_ok ctxt x /\ term_ok ctxt y ==>
    MilawaTrue ctxt (Or (Equal x y)
                        (Equal (mApp (mPrimitiveFun logic_EQUAL) [x; y])
                               (mConst (Sym "NIL"))))``,
  REPEAT STRIP_TAC \\ IMP_RES_TAC MilawaTrue_IMP_formula_ok
  \\ FULL_SIMP_TAC std_ss [formula_ok_def]
  \\ IMP_RES_TAC MilawaTrue_REFL
  \\ `MEM (EL 4 MILAWA_AXIOMS) MILAWA_AXIOMS` by EVAL_TAC
  \\ FULL_SIMP_TAC std_ss [EVAL ``EL 4 MILAWA_AXIOMS``]
  \\ IMP_RES_TAC (MilawaTrue_rules |> CONJUNCTS |> el 10)
  \\ POP_ASSUM (MP_TAC o SPEC_ALL)
  \\ Q.PAT_ABBREV_TAC `orrr = Or x1 x2` \\ STRIP_TAC
  \\ `formula_ok ctxt (formula_sub [("X",x);("Y",y)] orrr)` by (Q.UNABBREV_TAC `orrr` \\ EVAL_TAC \\ FULL_SIMP_TAC std_ss [])
  \\ IMP_RES_TAC (MilawaTrue_rules |> CONJUNCTS |> el 7)
  \\ REPEAT (Q.PAT_X_ASSUM `!xx.bbb` (K ALL_TAC))
  \\ Q.UNABBREV_TAC `orrr` \\ POP_ASSUM MP_TAC
  \\ SIMP_TAC (srw_ss()) [formula_sub_def,term_sub_def,LOOKUP_def]);

val NOT_NIL_EQ_T = prove(
  ``context_ok ctxt ==>
    MilawaTrue ctxt (Not (Equal (mConst (Sym "NIL")) (mConst (Sym "T"))))``,
  STRIP_TAC
  \\ MATCH_MP_TAC MilawaTrue_Not_Equal_COMM
  \\ `MEM (EL 2 MILAWA_AXIOMS) MILAWA_AXIOMS` by EVAL_TAC
  \\ FULL_SIMP_TAC std_ss [EVAL ``EL 2 MILAWA_AXIOMS``]
  \\ IMP_RES_TAC (MilawaTrue_rules |> CONJUNCTS |> el 10)
  \\ FULL_SIMP_TAC std_ss []);

val MilawaTrue_IF_LEMMA = prove(
  ``context_ok ctxt /\
    MilawaTrue ctxt (Equal e1 (mConst s1)) /\ s1 <> Sym "NIL" ==>
    MilawaTrue ctxt (Not (Equal e1 (mConst (Sym "NIL"))))``,
  REPEAT STRIP_TAC \\ MATCH_MP_TAC MilawaTrue_Not_Equal
  \\ Q.EXISTS_TAC `mConst s1` \\ ASM_SIMP_TAC std_ss []
  \\ IMP_RES_TAC MilawaTrue_IMP_formula_ok
  \\ FULL_SIMP_TAC std_ss [formula_ok_def]
  \\ `term_ok ctxt (mConst (Sym "NIL"))` by EVAL_TAC
  \\ `MilawaTrue ctxt
        (Or (Equal
              (mApp (mPrimitiveFun logic_EQUAL)
                 [mConst s1; mConst (Sym "NIL")]) (mConst (Sym "T")))
            (Not (Equal (mConst s1) (mConst (Sym "NIL")))))`
      by (IMP_RES_TAC MilawaTrue_AX4 THEN IMP_RES_TAC MilawaTrue_Or_Sym)
  \\ MATCH_MP_TAC (GEN_ALL MilawaTrue_MP2)
  \\ Q.EXISTS_TAC `(Equal
              (mApp (mPrimitiveFun logic_EQUAL)
                 [mConst s1; mConst (Sym "NIL")]) (mConst (Sym "T")))`
  \\ ASM_SIMP_TAC std_ss [] \\ POP_ASSUM (K ALL_TAC)
  \\ MATCH_MP_TAC MilawaTrue_Not_Equal
  \\ Q.EXISTS_TAC `mConst (Sym "NIL")`
  \\ ASM_SIMP_TAC std_ss [NOT_NIL_EQ_T]
  \\ MP_TAC (MilawaTrue_rules |> CONJUNCTS |> el 9
             |> Q.SPECL [`logic_EQUAL`,`[s1;Sym"NIL"]`,`ctxt`])
  \\ SIMP_TAC std_ss [primitive_arity_def,LENGTH,EVAL_PRIMITIVE_def]
  \\ EVAL_TAC \\ ASM_SIMP_TAC std_ss []);

val MilawaTrue_IF2 = prove(
  ``context_ok ctxt /\
    MilawaTrue ctxt (Equal e1 (mConst s1)) /\ isTrue s1 /\
    MilawaTrue ctxt (Equal e2 (mConst s)) /\ term_ok ctxt e3 ==>
    MilawaTrue ctxt (Equal (mApp (mPrimitiveFun logic_IF) [e1;e2;e3]) (mConst s))``,
  REPEAT STRIP_TAC \\ IMP_RES_TAC MilawaTrue_IMP_formula_ok
  \\ FULL_SIMP_TAC std_ss [formula_ok_def]
  \\ IMP_RES_TAC MilawaTrue_Sym \\ MATCH_MP_TAC MilawaTrue_TRANS
  \\ Q.EXISTS_TAC `e2` \\ FULL_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC std_ss [isTrue_def]
  \\ `MEM (EL 6 MILAWA_AXIOMS) MILAWA_AXIOMS` by EVAL_TAC
  \\ FULL_SIMP_TAC std_ss [EVAL ``EL 6 MILAWA_AXIOMS``]
  \\ IMP_RES_TAC (MilawaTrue_rules |> CONJUNCTS |> el 10)
  \\ POP_ASSUM (MP_TAC o SPEC_ALL)
  \\ Q.PAT_ABBREV_TAC `orrr = Or x1 x2` \\ STRIP_TAC
  \\ `formula_ok ctxt (formula_sub [("X",e1);("Y",e2);("Z",e3)] orrr)` by (Q.UNABBREV_TAC `orrr` \\ EVAL_TAC \\ FULL_SIMP_TAC std_ss [])
  \\ IMP_RES_TAC (MilawaTrue_rules |> CONJUNCTS |> el 7)
  \\ REPEAT (Q.PAT_X_ASSUM `!xx.bbb` (K ALL_TAC))
  \\ Q.UNABBREV_TAC `orrr` \\ POP_ASSUM MP_TAC
  \\ SIMP_TAC (srw_ss()) [formula_sub_def,term_sub_def,LOOKUP_def]
  \\ IMP_RES_TAC MilawaTrue_IF_LEMMA
  \\ METIS_TAC [MilawaTrue_MP2]);

val MilawaTrue_or_not_equal_list = prove(
  ``!ts_list x.
      context_ok ctxt /\
      (!x1 x2. MEM (x1,x2) ts_list ==> MilawaTrue ctxt (Equal x1 x2)) /\
      MilawaTrue ctxt (or_not_equal_list ts_list x) ==>
      MilawaTrue ctxt x``,
  Induct \\ SIMP_TAC std_ss [or_not_equal_list_def] \\ Cases
  \\ FULL_SIMP_TAC std_ss [MEM,or_not_equal_list_def] \\ REPEAT STRIP_TAC
  \\ `MilawaTrue ctxt (Equal q r)` by FULL_SIMP_TAC std_ss []
  \\ IMP_RES_TAC MilawaTrue_MP \\ METIS_TAC []);

val M_ev_induct = IndDefLib.derive_strong_induction(M_ev_rules,M_ev_ind);

val inst_term_def = Define `
  inst_term a exp = term_sub (MAP (\v. (v,mConst (a v))) (free_vars exp)) exp`;

val MAP_EQ = prove(
  ``!xs f g. (MAP f xs = MAP g xs) = EVERY (\x. f x = g x) xs``,
  Induct \\ SRW_TAC [] []);

val term_sub_EQ = store_thm("term_sub_EQ",
  ``!x xs. (set (free_vars x) SUBSET set xs) ==>
           (term_sub (MAP (\v. (v,f v)) xs) x =
            term_sub (MAP (\v. (v,f v)) (free_vars x)) x)``,
  STRIP_TAC \\ completeInduct_on `logic_term_size x`
  \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [PULL_IMP]
  \\ Cases_on `x` \\ FULL_SIMP_TAC std_ss [term_sub_def,free_vars_def] THEN1
   (FULL_SIMP_TAC std_ss [LOOKUP_def,SUBSET_DEF,MEM]
    \\ POP_ASSUM MP_TAC \\ REPEAT (POP_ASSUM (K ALL_TAC))
    \\ Induct_on `xs` \\ FULL_SIMP_TAC (srw_ss()) [LOOKUP_def] \\ METIS_TAC [])
  \\ FULL_SIMP_TAC (srw_ss()) [MAP_EQ,EVERY_MEM] \\ REPEAT STRIP_TAC
  THEN1
   (FULL_SIMP_TAC std_ss [AND_IMP_INTRO]
    \\ Q.PAT_X_ASSUM `!x.bbb` (fn th => MP_TAC (Q.SPECL [`a`,`xs`] th)
         THEN MP_TAC (Q.SPECL [`a`,`(FLAT (MAP (\a. free_vars a) l))`] th))
    \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
     (IMP_RES_TAC MEM_logic_term_size
      \\ FULL_SIMP_TAC std_ss [logic_term_size_def] \\ STRIP_TAC THEN1 DECIDE_TAC
      \\ POP_ASSUM (K ALL_TAC) \\ POP_ASSUM MP_TAC \\ REPEAT (POP_ASSUM (K ALL_TAC))
      \\ Induct_on `l` \\ FULL_SIMP_TAC (srw_ss()) [SUBSET_DEF] \\ METIS_TAC [])
    \\ STRIP_TAC \\ FULL_SIMP_TAC std_ss []
    \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
     (POP_ASSUM (K ALL_TAC) \\ IMP_RES_TAC MEM_logic_term_size
      \\ FULL_SIMP_TAC std_ss [logic_term_size_def] \\ STRIP_TAC THEN1 DECIDE_TAC
      \\ MATCH_MP_TAC SUBSET_TRANS
      \\ Q.EXISTS_TAC `set (FLAT (MAP (\a. free_vars a) l))`
      \\ ASM_SIMP_TAC std_ss []
      \\ POP_ASSUM (K ALL_TAC) \\ POP_ASSUM MP_TAC \\ REPEAT (POP_ASSUM (K ALL_TAC))
      \\ Induct_on `l` \\ FULL_SIMP_TAC (srw_ss()) [SUBSET_DEF] \\ METIS_TAC [])
    \\ FULL_SIMP_TAC std_ss [])
  THEN1
   (Q.ABBREV_TAC `vs = l` \\ POP_ASSUM (K ALL_TAC)
    \\ Q.ABBREV_TAC `l = l0` \\ POP_ASSUM (K ALL_TAC)
    \\ FULL_SIMP_TAC std_ss [AND_IMP_INTRO]
    \\ Q.PAT_X_ASSUM `!x.bbb` (fn th => MP_TAC (Q.SPECL [`a`,`xs`] th)
         THEN MP_TAC (Q.SPECL [`a`,`(FLAT (MAP (\a. free_vars a) l))`] th))
    \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
     (IMP_RES_TAC MEM_logic_term_size
      \\ FULL_SIMP_TAC std_ss [logic_term_size_def] \\ STRIP_TAC THEN1 DECIDE_TAC
      \\ POP_ASSUM (K ALL_TAC) \\ POP_ASSUM MP_TAC \\ REPEAT (POP_ASSUM (K ALL_TAC))
      \\ Induct_on `l` \\ FULL_SIMP_TAC (srw_ss()) [SUBSET_DEF] \\ METIS_TAC [])
    \\ STRIP_TAC \\ FULL_SIMP_TAC std_ss []
    \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
     (POP_ASSUM (K ALL_TAC) \\ IMP_RES_TAC MEM_logic_term_size
      \\ FULL_SIMP_TAC std_ss [logic_term_size_def] \\ STRIP_TAC THEN1 DECIDE_TAC
      \\ MATCH_MP_TAC SUBSET_TRANS
      \\ Q.EXISTS_TAC `set (FLAT (MAP (\a. free_vars a) l))`
      \\ ASM_SIMP_TAC std_ss []
      \\ POP_ASSUM (K ALL_TAC) \\ POP_ASSUM MP_TAC \\ REPEAT (POP_ASSUM (K ALL_TAC))
      \\ Induct_on `l` \\ FULL_SIMP_TAC (srw_ss()) [SUBSET_DEF] \\ METIS_TAC [])
    \\ FULL_SIMP_TAC std_ss []));

val inst_term_thm = prove(
  ``(inst_term a (mConst c) = mConst c) /\
    (inst_term a (mVar v) = mConst (a v)) /\
    (inst_term a (mApp f xs) = mApp f (MAP (inst_term a) xs)) /\
    (inst_term a (mLamApp vs x xs) = mLamApp vs x (MAP (inst_term a) xs))``,
  SIMP_TAC std_ss [inst_term_def,free_vars_def,MAP,term_sub_def,LOOKUP_def]
  \\ SIMP_TAC (srw_ss()) [MAP_EQ]
  \\ SIMP_TAC std_ss [EVERY_MEM,inst_term_def] \\ REPEAT STRIP_TAC
  \\ HO_MATCH_MP_TAC term_sub_EQ
  \\ Induct_on `xs` \\ FULL_SIMP_TAC (srw_ss()) [] \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [SUBSET_DEF,IN_UNION]);

val MAP_FST_ZIP = prove(
  ``!xs ys. (LENGTH xs = LENGTH ys) ==> (MAP FST (ZIP (xs,ys)) = xs)``,
  Induct \\ Cases_on `ys` \\ FULL_SIMP_TAC std_ss [LENGTH,ADD1,ZIP,MAP]);

val MAP_SND_ZIP = prove(
  ``!xs ys. (LENGTH xs = LENGTH ys) ==> (MAP SND (ZIP (xs,ys)) = ys)``,
  Induct \\ Cases_on `ys` \\ FULL_SIMP_TAC std_ss [LENGTH,ADD1,ZIP,MAP]);

val formula_ok_or_not_equal_list = prove(
  ``!xs x.
      formula_ok ctxt x /\ EVERY (\(x,y). term_ok ctxt y /\ term_ok ctxt x) xs ==>
      formula_ok ctxt (or_not_equal_list xs x)``,
  Induct \\ ASM_SIMP_TAC std_ss [or_not_equal_list_def,EVERY_DEF]
  \\ Cases \\ ASM_SIMP_TAC std_ss [or_not_equal_list_def,EVERY_DEF,formula_ok_def]);

val EVERY_ZIP = prove(
  ``!xs ys. (LENGTH xs = LENGTH ys) ==>
            (EVERY (\(x,y). g y /\ f x) (ZIP (xs,ys)) = EVERY f xs /\ EVERY g ys)``,
  Induct \\ Cases_on `ys` \\ FULL_SIMP_TAC std_ss [LENGTH,ADD1,ZIP,MAP,EVERY_DEF]
  \\ METIS_TAC []);

val MEM_ZIP = prove(
  ``!xs ys x. MEM x xs /\ (LENGTH xs = LENGTH ys) ==> ?y. MEM (x,y) (ZIP (xs,ys))``,
  Induct \\ Cases_on `ys` \\ FULL_SIMP_TAC std_ss [LENGTH,ADD1,ZIP,MAP,MEM]
  \\ METIS_TAC []);

val MEM_ZIP2 = prove(
  ``!xs ys x. MEM x xs /\ (LENGTH xs = LENGTH ys) ==> ?y. MEM (y,x) (ZIP (ys,xs))``,
  Induct \\ Cases_on `ys` \\ FULL_SIMP_TAC std_ss [LENGTH,ADD1,ZIP,MAP,MEM]
  \\ METIS_TAC []);

val ZIP_MAP = prove(
  ``!xs ys f g.
      (LENGTH xs = LENGTH ys) ==>
      (ZIP (MAP f xs, MAP g ys) = MAP (\(x,y). (f x, g y)) (ZIP (xs,ys)))``,
  Induct \\ Cases_on `ys` \\ FULL_SIMP_TAC std_ss [LENGTH,ADD1,ZIP,MAP,MEM]);

val term_ok_inst_term = prove(
  ``!exp. term_ok ctxt exp ==> term_ok ctxt (inst_term a exp)``,
  REPEAT STRIP_TAC \\ SIMP_TAC std_ss [inst_term_def]
  \\ MATCH_MP_TAC term_ok_sub \\ FULL_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC std_ss [EVERY_MEM,MEM_MAP,PULL_IMP,term_ok_def]);

val MEM_ZIP_IMP = prove(
  ``!xs ys.
      MEM (x,y) (ZIP (xs,ys)) /\ (LENGTH xs = LENGTH ys) ==> MEM x xs /\ MEM y ys``,
  Induct \\ Cases_on `ys` \\ FULL_SIMP_TAC std_ss [LENGTH,ADD1,ZIP,MAP,MEM]
  \\ METIS_TAC []);

val MAP_LOOKUP_LEMMA = store_thm("MAP_LOOKUP_LEMMA",
  ``!args params.
      (LENGTH args = LENGTH params) /\ ALL_DISTINCT params ==>
      (MAP mConst args =
       MAP (\x. LOOKUP x (ZIP (params,MAP mConst args)) (mVar x)) params)``,
  Induct \\ Cases_on `params` \\ SIMP_TAC (srw_ss()) [LENGTH,ADD1,LOOKUP_def]
  \\ REPEAT STRIP_TAC \\ RES_TAC
  \\ POP_ASSUM (fn th => CONV_TAC (RATOR_CONV (ONCE_REWRITE_CONV [th])))
  \\ SIMP_TAC std_ss [MAP_EQ,EVERY_MEM] \\ REPEAT STRIP_TAC
  \\ SRW_TAC [] [] \\ FULL_SIMP_TAC std_ss []);

val MAP_FunVarBind_LEMMA = store_thm("MAP_FunVarBind_LEMMA",
  ``!params args.
      (LENGTH params = LENGTH args) /\ ALL_DISTINCT params ==>
      (MAP (\v. (v,mConst (FunVarBind params args v))) params =
       ZIP (params,MAP mConst args))``,
  Induct \\ Cases_on `args` \\ SIMP_TAC (srw_ss()) [LENGTH,ADD1,FunVarBind_def]
  \\ SIMP_TAC std_ss [APPLY_UPDATE_THM] \\ REPEAT STRIP_TAC
  \\ sg `MAP (\v. (v,mConst (if h' = v then h else FunVarBind params t v)))
      params = MAP (\v. (v,mConst (FunVarBind params t v))) params`
  \\ SIMP_TAC std_ss [MAP_EQ,EVERY_MEM] \\ FULL_SIMP_TAC std_ss [] \\ METIS_TAC []);

val inst_term_EQ_term_sub = prove(
  ``!xs sl.
      set (free_vars e) SUBSET set xs /\ (LENGTH xs = LENGTH sl) ==>
      (inst_term (FunVarBind xs sl) e = term_sub (ZIP (xs,MAP mConst sl)) e)``,
  completeInduct_on `logic_term_size e` \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [PULL_IMP] \\ Cases_on `e`
  THEN1 (SIMP_TAC std_ss [inst_term_thm,term_sub_def,MilawaTrue_REFL,term_ok_def])
  THEN1
   (SIMP_TAC std_ss [inst_term_thm,term_sub_def]
    \\ POP_ASSUM MP_TAC \\ POP_ASSUM MP_TAC \\ REPEAT (POP_ASSUM (K ALL_TAC))
    \\ SIMP_TAC std_ss [free_vars_def,SUBSET_DEF,MEM]
    \\ Q.SPEC_TAC (`xs`,`xs`) \\ Q.SPEC_TAC (`sl`,`ys`)
    \\ Induct \\ Cases_on `xs` \\ FULL_SIMP_TAC std_ss [LENGTH,ADD1,MEM]
    \\ FULL_SIMP_TAC std_ss [FunVarBind_def,APPLY_UPDATE_THM,MAP,ZIP,LOOKUP_def]
    \\ METIS_TAC [])
  THEN
   (FULL_SIMP_TAC (srw_ss()) [inst_term_thm,term_sub_def,MAP_EQ,EVERY_MEM]
    \\ FULL_SIMP_TAC std_ss [free_vars_def] \\ REPEAT STRIP_TAC
    \\ FULL_SIMP_TAC std_ss [AND_IMP_INTRO]
    \\ Q.PAT_X_ASSUM `!x.bbb` MATCH_MP_TAC \\ FULL_SIMP_TAC std_ss []
    \\ IMP_RES_TAC MEM_logic_term_size
    \\ STRIP_TAC THEN1 (EVAL_TAC \\ DECIDE_TAC)
    \\ FULL_SIMP_TAC std_ss [SUBSET_DEF,MEM_FLAT,PULL_IMP,MEM_MAP]
    \\ METIS_TAC []));

val MEM_ZIP_ID = prove(
  ``!xs x y. MEM (x,y) (ZIP(xs,xs)) ==> (x = y)``,
  Induct \\ SIMP_TAC (srw_ss()) [ZIP] \\ METIS_TAC []);

val Equal_term_sub = prove(
  ``!vs xs ys.
      context_ok ctxt /\
      term_ok ctxt x /\ (LENGTH vs = LENGTH ys) /\ (LENGTH vs = LENGTH xs) /\
      (!x y. MEM (x,y) (ZIP(xs,ys)) ==> MilawaTrue ctxt (Equal x y)) ==>
      MilawaTrue ctxt (Equal (term_sub (ZIP (vs,xs)) x) (term_sub (ZIP(vs,ys)) x))``,
  completeInduct_on `logic_term_size x` \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [PULL_IMP] \\ Cases_on `x`
  THEN1 (SIMP_TAC std_ss [term_sub_def,MilawaTrue_REFL,term_ok_def])
  THEN1
   (POP_ASSUM MP_TAC \\ POP_ASSUM MP_TAC \\ POP_ASSUM MP_TAC
    \\ REPEAT (POP_ASSUM (K ALL_TAC))
    \\ Q.SPEC_TAC (`xs`,`xs`) \\ Q.SPEC_TAC (`ys`,`ys`) \\ Q.SPEC_TAC (`vs`,`vs`)
    \\ Induct \\ Cases_on `xs` \\ Cases_on `ys`
    \\ FULL_SIMP_TAC (srw_ss()) [LENGTH,ADD1,term_sub_def,LOOKUP_def]
    THEN1 (SIMP_TAC std_ss [term_sub_def,MilawaTrue_REFL,term_ok_def])
    \\ REPEAT STRIP_TAC \\ Cases_on `s = h''` \\ ASM_SIMP_TAC std_ss [])
  THEN1
   (SIMP_TAC std_ss [term_sub_def]
    \\ MATCH_MP_TAC MilawaTrue_or_not_equal_list
    \\ Q.LIST_EXISTS_TAC [`ZIP (MAP (\a. term_sub (ZIP (vs,xs)) a) l,
                                MAP (\a. term_sub (ZIP (vs,ys)) a) l)`]
    \\ ASM_SIMP_TAC std_ss []
    \\ STRIP_TAC THEN1
     (SIMP_TAC std_ss [ZIP_MAP,MEM_MAP,pairTheory.EXISTS_PROD,PULL_IMP]
      \\ REPEAT STRIP_TAC
      \\ IMP_RES_TAC MEM_ZIP_ID \\ FULL_SIMP_TAC std_ss [AND_IMP_INTRO]
      \\ Q.PAT_X_ASSUM `!x1 x2 x3. bbb` MATCH_MP_TAC \\ IMP_RES_TAC MEM_ZIP_IMP
      \\ FULL_SIMP_TAC std_ss [term_ok_def,EVERY_MEM]
      \\ IMP_RES_TAC MEM_logic_term_size \\ EVAL_TAC \\ DECIDE_TAC)
    \\ MATCH_MP_TAC (MilawaTrue_rules |> CONJUNCTS |> el 6)
    \\ Q.LIST_EXISTS_TAC [`l0`,`ZIP (MAP (\a. term_sub (ZIP (vs,xs)) a) l,
                                     MAP (\a. term_sub (ZIP (vs,ys)) a) l)`]
    \\ FULL_SIMP_TAC std_ss [MAP_FST_ZIP,MAP_SND_ZIP,LENGTH_MAP]
    \\ MATCH_MP_TAC formula_ok_or_not_equal_list
    \\ FULL_SIMP_TAC std_ss [formula_ok_def,term_ok_def,LENGTH_MAP,EVERY_ZIP]
    \\ FULL_SIMP_TAC std_ss [EVERY_MEM,MEM_MAP,PULL_IMP]
    \\ REPEAT STRIP_TAC \\ MATCH_MP_TAC term_ok_sub
    \\ ASM_SIMP_TAC std_ss [EVERY_MEM,MEM_MAP,pairTheory.EXISTS_PROD,PULL_IMP]
    \\ REPEAT STRIP_TAC
    \\ `LENGTH ys = LENGTH xs` by METIS_TAC []
    \\ `LENGTH vs = LENGTH ys` by METIS_TAC []
    \\ IMP_RES_TAC MEM_ZIP_IMP
    THENL [IMP_RES_TAC MEM_ZIP, IMP_RES_TAC MEM_ZIP2]
    \\ RES_TAC \\ IMP_RES_TAC MilawaTrue_IMP_formula_ok
    \\ FULL_SIMP_TAC std_ss [formula_ok_def,term_ok_def,LENGTH_MAP])
  THEN1
   (SIMP_TAC std_ss [term_sub_def]
    \\ MATCH_MP_TAC (MilawaTrue_AX2 |> SIMP_RULE std_ss [AND_IMP_INTRO])
    \\ Q.ABBREV_TAC `xs1 = MAP (\a. term_sub (ZIP (vs,xs)) a) l0`
    \\ Q.ABBREV_TAC `ys1 = MAP (\a. term_sub (ZIP (vs,ys)) a) l0`
    \\ Q.LIST_EXISTS_TAC [`term_sub (ZIP(l1,ys1)) l`,`term_sub (ZIP(l1,xs1)) l`]
    \\ ASM_SIMP_TAC std_ss []
    \\ REPEAT STRIP_TAC THEN1
     (MATCH_MP_TAC MilawaTrue_Sym \\ ASM_SIMP_TAC std_ss []
      \\ MATCH_MP_TAC (MilawaTrue_rules |> CONJUNCTS |> el 8)
      \\ FULL_SIMP_TAC std_ss [formula_ok_def,term_ok_def]
      \\ Q.UNABBREV_TAC `xs1` \\ Q.UNABBREV_TAC `ys1`
      \\ FULL_SIMP_TAC std_ss [EVERY_MEM,MEM_MAP,PULL_IMP,LENGTH_MAP]
      \\ REPEAT STRIP_TAC \\ MATCH_MP_TAC term_ok_sub
      \\ FULL_SIMP_TAC std_ss [EVERY_MEM,MEM_MAP,pairTheory.EXISTS_PROD,PULL_IMP]
      \\ REPEAT STRIP_TAC
      \\ `LENGTH ys = LENGTH xs` by METIS_TAC []
      \\ `LENGTH vs = LENGTH ys` by METIS_TAC []
      THEN1
       (IMP_RES_TAC MEM_ZIP_IMP \\ IMP_RES_TAC MEM_ZIP
        \\ RES_TAC \\ IMP_RES_TAC MilawaTrue_IMP_formula_ok
        \\ FULL_SIMP_TAC std_ss [formula_ok_def,term_ok_def,LENGTH_MAP])
      \\ Q.PAT_X_ASSUM `MEM (p_1,e) (ZIP (l1,MAP (\a. term_sub (ZIP (vs,xs)) a) l0))` MP_TAC
      \\ ASM_SIMP_TAC std_ss [MEM_MAP,pairTheory.EXISTS_PROD,
          ZIP_MAP |> Q.SPECL [`xs`,`ys`] |> Q.ISPEC `I` |> SIMP_RULE std_ss [MAP_ID]]
      \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss []
      \\ MATCH_MP_TAC term_ok_sub
      \\ IMP_RES_TAC MEM_ZIP_IMP \\ FULL_SIMP_TAC std_ss []
      \\ FULL_SIMP_TAC std_ss [EVERY_MEM,MEM_MAP,pairTheory.EXISTS_PROD,PULL_IMP]
      \\ REPEAT STRIP_TAC \\ `LENGTH vs = LENGTH xs` by METIS_TAC []
      \\ IMP_RES_TAC MEM_ZIP_IMP \\ FULL_SIMP_TAC std_ss []
      \\ IMP_RES_TAC MEM_ZIP_IMP \\ IMP_RES_TAC MEM_ZIP
      \\ RES_TAC \\ IMP_RES_TAC MilawaTrue_IMP_formula_ok
      \\ FULL_SIMP_TAC std_ss [formula_ok_def,term_ok_def,LENGTH_MAP])
    THEN1
     (MATCH_MP_TAC MilawaTrue_Sym \\ ASM_SIMP_TAC std_ss []
      \\ MATCH_MP_TAC (MilawaTrue_rules |> CONJUNCTS |> el 8)
      \\ FULL_SIMP_TAC std_ss [formula_ok_def,term_ok_def]
      \\ Q.UNABBREV_TAC `xs1` \\ Q.UNABBREV_TAC `ys1`
      \\ FULL_SIMP_TAC std_ss [EVERY_MEM,MEM_MAP,PULL_IMP,LENGTH_MAP]
      \\ REPEAT STRIP_TAC \\ MATCH_MP_TAC term_ok_sub
      \\ FULL_SIMP_TAC std_ss [EVERY_MEM,MEM_MAP,pairTheory.EXISTS_PROD,PULL_IMP]
      \\ REPEAT STRIP_TAC
      \\ `LENGTH ys = LENGTH xs` by METIS_TAC []
      \\ `LENGTH vs = LENGTH ys` by METIS_TAC []
      THEN1
       (IMP_RES_TAC MEM_ZIP_IMP \\ IMP_RES_TAC MEM_ZIP2
        \\ RES_TAC \\ IMP_RES_TAC MilawaTrue_IMP_formula_ok
        \\ FULL_SIMP_TAC std_ss [formula_ok_def,term_ok_def,LENGTH_MAP])
      \\ Q.PAT_X_ASSUM `MEM (p_1,e) (ZIP (l1,MAP (\a. term_sub (ZIP (vs,ys)) a) l0))` MP_TAC
      \\ ASM_SIMP_TAC std_ss [MEM_MAP,pairTheory.EXISTS_PROD,
          ZIP_MAP |> Q.SPECL [`xs`,`ys`] |> Q.ISPEC `I` |> SIMP_RULE std_ss [MAP_ID]]
      \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss []
      \\ MATCH_MP_TAC term_ok_sub
      \\ IMP_RES_TAC MEM_ZIP_IMP \\ FULL_SIMP_TAC std_ss []
      \\ FULL_SIMP_TAC std_ss [EVERY_MEM,MEM_MAP,pairTheory.EXISTS_PROD,PULL_IMP]
      \\ REPEAT STRIP_TAC \\ `LENGTH vs = LENGTH ys` by METIS_TAC []
      \\ IMP_RES_TAC MEM_ZIP_IMP \\ FULL_SIMP_TAC std_ss []
      \\ IMP_RES_TAC MEM_ZIP_IMP \\ IMP_RES_TAC MEM_ZIP2
      \\ RES_TAC \\ IMP_RES_TAC MilawaTrue_IMP_formula_ok
      \\ FULL_SIMP_TAC std_ss [formula_ok_def,term_ok_def,LENGTH_MAP])
    \\ FULL_SIMP_TAC std_ss [AND_IMP_INTRO]
    \\ Q.PAT_X_ASSUM `!x1 x2 x3. bbb` (fn th => ASSUME_TAC th THEN MATCH_MP_TAC th)
    \\ STRIP_TAC THEN1 (EVAL_TAC \\ DECIDE_TAC)
    \\ Q.UNABBREV_TAC `xs1` \\ Q.UNABBREV_TAC `ys1`
    \\ FULL_SIMP_TAC std_ss [term_ok_def,LENGTH_MAP,ZIP_MAP,MEM_MAP,
         PULL_IMP,pairTheory.FORALL_PROD] \\ REPEAT STRIP_TAC
    \\ IMP_RES_TAC MEM_ZIP_ID \\ FULL_SIMP_TAC std_ss []
    \\ Q.PAT_X_ASSUM `!x1 x2 x3. bbb` MATCH_MP_TAC
    \\ ASM_SIMP_TAC std_ss [] \\ IMP_RES_TAC MEM_ZIP_IMP
    \\ FULL_SIMP_TAC std_ss [EVERY_MEM]
    \\ IMP_RES_TAC MEM_logic_term_size
    \\ EVAL_TAC \\ DECIDE_TAC));

val MEM_ZIP_MAP_EQ = prove(
  ``!xs ys.
      (LENGTH xs = LENGTH ys) ==>
      (MEM (x,y) (ZIP (MAP f xs, MAP g ys)) =
       ?x1 y1. MEM (x1,y1) (ZIP(xs,ys)) /\ (x = f x1) /\ (y = g y1))``,
  Induct \\ Cases_on `ys`
  \\ FULL_SIMP_TAC (srw_ss()) [LENGTH,ADD1] \\ METIS_TAC []);

val term_funs_def = Define `
  term_funs ctxt =
    !name params body sem.
      name IN FDOM ctxt /\ (ctxt ' name = (params,BODY_FUN body,sem)) ==>
      MilawaTrue ctxt (Equal (mApp (mFun name) (MAP mVar params)) body)`;

val proof_in_full_ctxt_def = Define `
  proof_in_full_ctxt ctxt full_ctxt =
    !x. MilawaTrue ctxt x ==> MilawaTrue full_ctxt x`;

val ind =
  M_ev_induct
  |> Q.SPEC `name`
  |> Q.SPEC `\(exp,a,ctxt) result. !ok env.
      (!params exp sem.
         (ctxt ' name = (params,BODY_FUN exp,sem)) /\
         name IN FDOM ctxt ==>
         ?r. (k ' name = (params,r)) /\ name IN FDOM k /\
             term_ok ctxt exp /\ (term2t r = exp) /\ funcs_ok r) /\
       term_funs ctxt /\
       runtime_inv (ctxt \\ name) k /\ proof_in_full_ctxt (ctxt \\ name) ctxt /\
       EVERY (\x. ~(x IN FDOM ctxt)) ["NOT";"RANK";"ORDP";"ORD<"] /\
       EVERY (\x. ~(x IN FDOM ctxt)) fake_ftbl_entries /\
       context_ok ctxt /\ term_ok ctxt exp /\ core_assum k /\
       (!v. MEM v (free_vars exp) ==> v IN FDOM env /\ (env ' v = a v)) ==>
       ?ok2. MR_ev (t2term exp,env,ctxt,k,ok) (result,ok2) /\
             (ok2 ==> MilawaTrue ctxt (Equal (inst_term a exp) (mConst result)))`
  |> Q.SPEC `\(f,args,ctxt) result. !ok env.
      (!params exp sem.
         (ctxt ' name = (params,BODY_FUN exp,sem)) /\
         name IN FDOM ctxt ==>
         ?r. (k ' name = (params,r)) /\ name IN FDOM k /\
             term_ok ctxt exp /\ (term2t r = exp) /\ funcs_ok r) /\
       term_funs ctxt /\
       runtime_inv (ctxt \\ name) k /\ proof_in_full_ctxt (ctxt \\ name) ctxt /\
       EVERY (\x. ~(x IN FDOM ctxt)) ["NOT";"RANK";"ORDP";"ORD<"] /\
       EVERY (\x. ~(x IN FDOM ctxt)) fake_ftbl_entries /\
       context_ok ctxt /\ core_assum k /\
       ~(f = mPrimitiveFun logic_IF) ==>
       ?ok2. MR_ap (f2func f,args,ARB,ctxt,k,ok) (result,ok2) /\
             (ok2 ==> MilawaTrue ctxt (Equal (mApp f (MAP mConst args)) (mConst result)))`
  |> Q.SPEC `\(exp,a,ctxt) result. !ok env.
      (!params exp sem.
         (ctxt ' name = (params,BODY_FUN exp,sem)) /\
         name IN FDOM ctxt ==>
         ?r. (k ' name = (params,r)) /\ name IN FDOM k /\
             term_ok ctxt exp /\ (term2t r = exp) /\ funcs_ok r) /\
       term_funs ctxt /\
       runtime_inv (ctxt \\ name) k /\ proof_in_full_ctxt (ctxt \\ name) ctxt /\
       EVERY (\x. ~(x IN FDOM ctxt)) ["NOT";"RANK";"ORDP";"ORD<"] /\
       EVERY (\x. ~(x IN FDOM ctxt)) fake_ftbl_entries /\
       context_ok ctxt /\ EVERY (term_ok ctxt) exp /\ core_assum k /\
       (!v. MEM v (FLAT (MAP free_vars exp)) ==> v IN FDOM env /\ (env ' v = a v)) ==>
       ?ok2. MR_evl (MAP t2term exp,env,ctxt,k,ok) (result,ok2) /\
             (ok2 ==> !x1 x2. MEM (x1,x2) (ZIP (exp,result)) ==>
                              MilawaTrue ctxt (Equal (inst_term a x1) (mConst x2)))`

val goal = ind |> concl |> dest_comb |> snd

(*
  set_goal([],goal)
*)

val M_ev_IMP_R_ev_lemma = prove(goal,
  MATCH_MP_TAC ind \\ SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC
  THEN1 (SIMP_TAC std_ss [t2term_def] \\ ONCE_REWRITE_TAC [MR_ev_cases]
         \\ SIMP_TAC (srw_ss()) []
         \\ SIMP_TAC std_ss [inst_term_def,term_sub_def,MilawaTrue_REFL,term_ok_def])
  THEN1 (SIMP_TAC std_ss [t2term_def] \\ ONCE_REWRITE_TAC [MR_ev_cases]
         \\ FULL_SIMP_TAC (srw_ss()) [free_vars_def,MEM]
         \\ FULL_SIMP_TAC std_ss [inst_term_def,free_vars_def,MAP,
              term_sub_def,LOOKUP_def,MilawaTrue_REFL,term_ok_def])
  THEN1 (FULL_SIMP_TAC (srw_ss()) [term_ok_def,EVERY_DEF,free_vars_def,
           MAP,FLAT,MEM_APPEND,MEM,t2term_def,LENGTH,LET_DEF]
         \\ ONCE_REWRITE_TAC [MR_ev_cases] \\ SIMP_TAC (srw_ss()) []
         \\ `?ok2. MR_ev (t2term e1,env,ctxt,k,ok) (s1,ok2) /\
                (ok2 ==> MilawaTrue ctxt (Equal (inst_term a e1) (mConst s1)))`
                   by METIS_TAC []
         \\ `?ok3. MR_ev (t2term e3,env,ctxt,k,ok2) (s,ok3) /\
                (ok3 ==> MilawaTrue ctxt (Equal (inst_term a e3) (mConst s)))`
                   by METIS_TAC []
         \\ Q.EXISTS_TAC `ok3` \\ STRIP_TAC THEN1 (METIS_TAC [])
         \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss []
         \\ IMP_RES_TAC MR_ev_OK \\ FULL_SIMP_TAC std_ss [inst_term_thm,MAP]
         \\ MATCH_MP_TAC MilawaTrue_IF1 \\ ASM_SIMP_TAC std_ss [term_ok_inst_term])
  THEN1 (FULL_SIMP_TAC (srw_ss()) [term_ok_def,EVERY_DEF,free_vars_def,
           MAP,FLAT,MEM_APPEND,MEM,t2term_def,LENGTH,LET_DEF]
         \\ ONCE_REWRITE_TAC [MR_ev_cases] \\ SIMP_TAC (srw_ss()) []
         \\ `?ok2. MR_ev (t2term e1,env,ctxt,k,ok) (s1,ok2) /\
                (ok2 ==> MilawaTrue ctxt (Equal (inst_term a e1) (mConst s1)))`
                   by METIS_TAC []
         \\ `?ok3. MR_ev (t2term e2,env,ctxt,k,ok2) (s,ok3) /\
                (ok3 ==> MilawaTrue ctxt (Equal (inst_term a e2) (mConst s)))`
                   by METIS_TAC []
         \\ Q.EXISTS_TAC `ok3` \\ STRIP_TAC THEN1 (METIS_TAC [])
         \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss []
         \\ IMP_RES_TAC MR_ev_OK \\ FULL_SIMP_TAC std_ss [inst_term_thm,MAP]
         \\ MATCH_MP_TAC MilawaTrue_IF2 \\ ASM_SIMP_TAC std_ss [term_ok_inst_term])
  THEN1
   (SIMP_TAC std_ss [t2term_def]
    \\ ONCE_REWRITE_TAC [MR_ev_cases] \\ FULL_SIMP_TAC (srw_ss()) []
    \\ FULL_SIMP_TAC std_ss [free_vars_def,term_ok_def,EVERY_MEM]
    \\ POP_ASSUM MP_TAC \\ CONV_TAC (DEPTH_CONV ETA_CONV) \\ STRIP_TAC
    \\ FULL_SIMP_TAC std_ss []
    \\ Q.PAT_X_ASSUM `!ok:bool. bbb` MP_TAC
    \\ Q.PAT_X_ASSUM `!ok:bool. bbb` (MP_TAC o Q.SPECL [`ok`,`env`])
    \\ ASM_SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC
    \\ POP_ASSUM (MP_TAC o Q.SPECL [`ok2`,`FUNION (VarBind xs sl) env`])
    \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
     (NTAC 2 STRIP_TAC
      \\ IMP_RES_TAC MR_evl_LENGTH
      \\ FULL_SIMP_TAC std_ss [SUBSET_DEF] \\ RES_TAC
      \\ MP_TAC (Q.SPECL [`xs`,`sl`,`v`] params_lemma) \\ ASM_SIMP_TAC std_ss []
      \\ FULL_SIMP_TAC std_ss [FUNION_DEF,LENGTH_MAP,IN_UNION])
    \\ REPEAT STRIP_TAC
    \\ Q.EXISTS_TAC `ok2'` \\ STRIP_TAC THEN1 METIS_TAC []
    \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss []
    \\ IMP_RES_TAC MR_ev_OK \\ FULL_SIMP_TAC std_ss [inst_term_thm]
    \\ MATCH_MP_TAC MilawaTrue_TRANS \\ ASM_SIMP_TAC std_ss []
    \\ Q.EXISTS_TAC `(inst_term (FunVarBind xs sl) e)` \\ ASM_SIMP_TAC std_ss []
    \\ MATCH_MP_TAC MilawaTrue_TRANS \\ ASM_SIMP_TAC std_ss []
    \\ Q.EXISTS_TAC `term_sub (ZIP (xs,(MAP (inst_term a) ys))) e`
    \\ STRIP_TAC THEN1
     (FULL_SIMP_TAC std_ss []
      \\ MATCH_MP_TAC (MilawaTrue_rules |> CONJUNCTS |> el 8)
      \\ IMP_RES_TAC MilawaTrue_IMP_formula_ok
      \\ FULL_SIMP_TAC std_ss [formula_ok_def,term_ok_def,LENGTH_MAP,
           EVERY_MEM,MEM_MAP,PULL_IMP,term_ok_inst_term]
      \\ MATCH_MP_TAC term_ok_sub
      \\ FULL_SIMP_TAC std_ss [formula_ok_def,term_ok_def,LENGTH_MAP,
           EVERY_MEM,MEM_MAP,PULL_IMP,term_ok_inst_term] \\ Cases
      \\ ASM_SIMP_TAC std_ss [MEM_MAP,pairTheory.EXISTS_PROD,
          ZIP_MAP |> Q.SPECL [`xs`,`ys`] |> Q.ISPEC `I` |> SIMP_RULE std_ss [MAP_ID]]
      \\ REPEAT STRIP_TAC \\ RES_TAC \\ IMP_RES_TAC MEM_ZIP_IMP
      \\ FULL_SIMP_TAC std_ss [term_ok_inst_term])
    \\ IMP_RES_TAC MR_evl_LENGTH \\ FULL_SIMP_TAC std_ss [LENGTH_MAP]
    \\ FULL_SIMP_TAC std_ss [inst_term_EQ_term_sub]
    \\ MATCH_MP_TAC Equal_term_sub \\ FULL_SIMP_TAC std_ss [LENGTH_MAP]
    \\ IMP_RES_TAC MR_evl_LENGTH \\ FULL_SIMP_TAC std_ss [LENGTH_MAP]
    \\ FULL_SIMP_TAC std_ss [MEM_ZIP_MAP_EQ,PULL_IMP])
  THEN1
   (SIMP_TAC std_ss [t2term_def]
    \\ ONCE_REWRITE_TAC [MR_ev_cases] \\ FULL_SIMP_TAC (srw_ss()) []
    \\ FULL_SIMP_TAC std_ss [free_vars_def,term_ok_def]
    \\ NTAC 3 (POP_ASSUM MP_TAC) \\ CONV_TAC (DEPTH_CONV ETA_CONV)
    \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss []
    \\ Q.PAT_X_ASSUM `!ok env. bb ==> bbb` (MP_TAC o Q.SPECL [`ok`,`env`])
    \\ FULL_SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC
    \\ FULL_SIMP_TAC std_ss [MR_ap_ARB]
    \\ Q.PAT_X_ASSUM `!ok. ?ok2. bbb` (STRIP_ASSUME_TAC o Q.SPEC `ok2`)
    \\ Q.EXISTS_TAC `ok2'` \\ STRIP_TAC THEN1 METIS_TAC []
    \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss []
    \\ IMP_RES_TAC MR_ev_OK \\ FULL_SIMP_TAC std_ss [inst_term_thm]
    \\ MATCH_MP_TAC MilawaTrue_TRANS
    \\ Q.EXISTS_TAC `mApp fc (MAP mConst args)` \\ ASM_SIMP_TAC std_ss []
    \\ IMP_RES_TAC MilawaTrue_IMP_formula_ok
    \\ FULL_SIMP_TAC std_ss [formula_ok_def,term_ok_def,LENGTH_MAP]
    \\ MATCH_MP_TAC MilawaTrue_or_not_equal_list \\ ASM_SIMP_TAC std_ss []
    \\ Q.LIST_EXISTS_TAC [`ZIP (MAP (inst_term a) el,MAP mConst args)`]
    \\ STRIP_TAC THEN1
     (ASM_SIMP_TAC std_ss [ZIP_MAP,MEM_MAP,pairTheory.EXISTS_PROD,PULL_IMP])
    \\ MATCH_MP_TAC (MilawaTrue_rules |> CONJUNCTS |> el 6)
    \\ Q.LIST_EXISTS_TAC [`fc`,`ZIP (MAP (inst_term a) el,MAP mConst args)`]
    \\ FULL_SIMP_TAC std_ss [MAP_FST_ZIP,MAP_SND_ZIP,LENGTH_MAP]
    \\ MATCH_MP_TAC formula_ok_or_not_equal_list
    \\ FULL_SIMP_TAC std_ss [formula_ok_def,term_ok_def,LENGTH_MAP,EVERY_ZIP]
    \\ FULL_SIMP_TAC std_ss [EVERY_MEM,MEM_MAP,PULL_IMP]
    \\ REPEAT STRIP_TAC
    \\ `?x. MEM (y,x) (ZIP (el,args))` by METIS_TAC [MEM_ZIP]
    \\ RES_TAC \\ IMP_RES_TAC MilawaTrue_IMP_formula_ok
    \\ FULL_SIMP_TAC std_ss [formula_ok_def,term_ok_def,LENGTH_MAP])
  THEN1
   (Q.EXISTS_TAC `ok` \\ REVERSE STRIP_TAC THEN1
     (REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss []
      \\ METIS_TAC [MilawaTrue_cases])
    \\ Cases_on `p` \\ FULL_SIMP_TAC std_ss [f2func_def]
    \\ TRY (ONCE_REWRITE_TAC [MR_ev_cases]
            \\ SIMP_TAC (srw_ss()) [EVAL_DATA_OP_def,EVAL_PRIMITIVE_def]
            \\ FULL_SIMP_TAC std_ss [primitive_arity_def] \\ NO_TAC)
    \\ FULL_SIMP_TAC std_ss [primitive_arity_def]
    \\ FULL_SIMP_TAC std_ss [LENGTH_EQ_2,LENGTH_EQ_1]
    \\ `EVAL_PRIMITIVE logic_NOT [x1] = not x1` by
       (FULL_SIMP_TAC (srw_ss()) [EVAL_PRIMITIVE_def,LISP_TEST_def,
          not_def,isTrue_def] \\ METIS_TAC [])
    \\ `EVAL_PRIMITIVE logic_RANK [x1] = rank x1` by
       (FULL_SIMP_TAC (srw_ss()) [EVAL_PRIMITIVE_def,LISP_TEST_def,
          not_def,isTrue_def,rank_lemma])
    \\ `EVAL_PRIMITIVE logic_ORD_LESS [x1; x2] = ord_ x1 x2` by
       (FULL_SIMP_TAC (srw_ss()) [EVAL_PRIMITIVE_def,ord__lemma])
    \\ `EVAL_PRIMITIVE logic_ORDP [x1] = ordp x1` by
       (FULL_SIMP_TAC (srw_ss()) [EVAL_PRIMITIVE_def,ordp_lemma])
    \\ ONCE_REWRITE_TAC [MR_ev_cases] \\ FULL_SIMP_TAC (srw_ss()) [])
  THEN1
   (SIMP_TAC std_ss [f2func_def]
    \\ `~(fc = "DEFINE") /\ ~(fc = "PRINT") /\
        ~(fc = "ERROR") /\ ~(fc = "FUNCALL")` by
     (REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [EVERY_DEF,fake_ftbl_entries_def])
    \\ FULL_SIMP_TAC std_ss []
    \\ FULL_SIMP_TAC std_ss [runtime_inv_def,FDOM_DOMSUB,DOMSUB_FAPPLY_THM,IN_DELETE]
    \\ Q.PAT_X_ASSUM `!bb.nnn` (MP_TAC o Q.SPECL [`fc`])
    \\ FULL_SIMP_TAC std_ss []
    \\ STRIP_TAC \\ POP_ASSUM (MP_TAC o Q.SPECL [`args`,`ok`])
    \\ ASM_SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC
    \\ Q.EXISTS_TAC `ok2` \\ STRIP_TAC THEN1 METIS_TAC [MR_ev_CTXT]
    \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss []
    \\ FULL_SIMP_TAC std_ss [MilawaTrueFun_def]
    \\ FULL_SIMP_TAC std_ss [proof_in_full_ctxt_def])
  THEN1
   (SIMP_TAC std_ss [f2func_def]
    \\ `~(name = "DEFINE") /\ ~(name = "PRINT") /\
        ~(name = "ERROR") /\ ~(name = "FUNCALL")` by
     (REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [EVERY_DEF,fake_ftbl_entries_def])
    \\ FULL_SIMP_TAC std_ss []
    \\ FULL_SIMP_TAC std_ss [EVERY_DEF]
    \\ `~(name = "NOT") /\ ~(name = "ORDP") /\
        ~(name = "RANK") /\ ~(name = "ORD<")` by METIS_TAC []
    \\ ONCE_REWRITE_TAC [MR_ev_cases] \\ ASM_SIMP_TAC (srw_ss()) []
    \\ FULL_SIMP_TAC (srw_ss()) []
    \\ Q.PAT_X_ASSUM `term2t r = exp` (ASSUME_TAC o GSYM)
    \\ FULL_SIMP_TAC (srw_ss()) []
    \\ Q.PAT_X_ASSUM `!ok env. bbb` (MP_TAC o Q.SPECL [`ok`,`VarBind params args`])
    \\ FULL_SIMP_TAC (srw_ss()) []
    \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
     (FULL_SIMP_TAC std_ss [context_ok_def]
      \\ RES_TAC \\ FULL_SIMP_TAC std_ss [SUBSET_DEF]
      \\ METIS_TAC [params_lemma])
    \\ STRIP_TAC \\ FULL_SIMP_TAC std_ss [GSYM term2term_def]
    \\ IMP_RES_TAC (GEN_ALL MR_ev_term2term)
    \\ Q.EXISTS_TAC `ok2` \\ FULL_SIMP_TAC std_ss []
    \\ STRIP_TAC THEN1
     (CCONTR_TAC \\ FULL_SIMP_TAC std_ss [] \\ FULL_SIMP_TAC std_ss []
      \\ FULL_SIMP_TAC std_ss [term2t_def,term_ok_def,func_arity_def,func2f_def]
      \\ FULL_SIMP_TAC std_ss [fake_ftbl_entries_def,EVERY_DEF])
    \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss []
    \\ MATCH_MP_TAC MilawaTrue_TRANS
    \\ Q.EXISTS_TAC `(inst_term (FunVarBind params args) (term2t r))`
    \\ ASM_SIMP_TAC std_ss []
    \\ `ALL_DISTINCT params` by METIS_TAC [context_ok_def]
    \\ `(Equal (mApp (mFun name) (MAP mConst args))
          (inst_term (FunVarBind params args) (term2t r))) =
        formula_sub (ZIP(params,MAP mConst args))
          (Equal (mApp (mFun name) (MAP mVar params)) (term2t r))` by
     (FULL_SIMP_TAC (srw_ss()) [formula_sub_def,term_sub_def,MAP_MAP_o,o_DEF]
      \\ ASM_SIMP_TAC std_ss [MAP_LOOKUP_LEMMA,inst_term_def]
      \\ FULL_SIMP_TAC std_ss [context_ok_def]
      \\ RES_TAC \\ IMP_RES_TAC (GSYM term_sub_EQ)
      \\ POP_ASSUM (ASSUME_TAC o Q.SPEC `mConst o FunVarBind params args`)
      \\ FULL_SIMP_TAC std_ss [o_DEF,MAP_FunVarBind_LEMMA])
    \\ ASM_SIMP_TAC std_ss []
    \\ MATCH_MP_TAC (MilawaTrue_rules |> CONJUNCTS |> el 7)
    \\ STRIP_TAC THEN1
     (FULL_SIMP_TAC std_ss [formula_sub_def,formula_ok_def,
         term_sub_def,term_ok_def,func_arity_def,LENGTH_MAP]
      \\ FULL_SIMP_TAC std_ss [EVERY_MEM,MEM_MAP,PULL_IMP]
      \\ REPEAT STRIP_TAC \\ MATCH_MP_TAC term_ok_sub
      \\ FULL_SIMP_TAC std_ss [term_ok_def,EVERY_MEM,MEM_MAP,PULL_IMP]
      \\ Cases \\ ASM_SIMP_TAC std_ss [MEM_MAP,pairTheory.EXISTS_PROD,
          ZIP_MAP |> Q.SPECL [`xs`,`ys`] |> Q.ISPEC `I` |> SIMP_RULE std_ss [MAP_ID]]
      \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss [term_ok_def])
    \\ FULL_SIMP_TAC std_ss [term_funs_def])
  THEN1 (ONCE_REWRITE_TAC [MR_ev_cases] \\ SIMP_TAC (srw_ss()) [])
  THEN1 (ONCE_REWRITE_TAC [MR_ev_cases] \\ SIMP_TAC (srw_ss()) []
    \\ FULL_SIMP_TAC std_ss [EVERY_DEF,MAP,FLAT,MEM_APPEND]
    \\ Q.PAT_X_ASSUM `!xx yy. bbb ==> bbbb` MP_TAC
    \\ Q.PAT_X_ASSUM `!xx yy. bbb ==> bbbb` (MP_TAC o Q.SPECL [`ok`,`env`])
    \\ ASM_SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC
    \\ POP_ASSUM (MP_TAC o Q.SPECL [`ok2`,`env`])
    \\ ASM_SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC
    \\ Q.EXISTS_TAC `ok2'` \\ STRIP_TAC THEN1 METIS_TAC []
    \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss []
    \\ IMP_RES_TAC MR_ev_OK \\ FULL_SIMP_TAC std_ss []))

val MR_ev_thm = save_thm("MR_ev_thm",M_ev_IMP_R_ev_lemma
  |> CONJUNCTS |> el 1 |> Q.SPECL [`(exp,a,ctxt)`,`result`]
  |> SIMP_RULE std_ss [PULL_IMP,AND_IMP_INTRO] |> GEN_ALL);

val MR_ap_thm = save_thm("MR_ap_thm",M_ev_IMP_R_ev_lemma
  |> CONJUNCTS |> el 2 |> Q.SPECL [`(f,args,ctxt)`,`result`]
  |> SIMP_RULE std_ss [PULL_IMP,AND_IMP_INTRO] |> GEN_ALL);

val _ = export_theory();
