open HolKernel boolLib bossLib Parse; val _ = new_theory "lisp_semantics";

open stringTheory finite_mapTheory pred_setTheory listTheory sumTheory;
open optionTheory arithmeticTheory relationTheory;

open lisp_sexpTheory lisp_parseTheory;

infix \\
val op \\ = op THEN;


(* abstract syntax of well-formed Lisp prorams *)

val _ = Hol_datatype `
  func = PrimitiveFun of lisp_primitive_op
       | Define | Print | Error | Funcall | Fun of string`;

val _ = Hol_datatype `
  term = Const of SExp
       | Var of string
       | App of func => term list
       | If of term => term => term
       | LamApp of string list => term => term list
       (* only macros below *)
       | Let of (string # term) list => term
       | LetStar of (string # term) list => term
       | Cond of (term # term) list
       | Or of term list | And of term list
       | First of term | Second of term | Third of term
       | Fourth of term | Fifth of term | List of term list
       | Defun of string => string list => SExp`;

val term_11 = fetch "-" "term_11";
val term_distinct = fetch "-" "term_distinct";
val term_size_def = fetch "-" "term_size_def";
val func_11 = fetch "-" "func_11";


(* reading a program, i.e. term, from an s-expression -- sexp2term *)

val list2sexp_def = Define `
  (list2sexp [] = Sym "NIL") /\
  (list2sexp (x::xs) = Dot x (list2sexp xs))`;

val sym2prim_def = Define `
  sym2prim s =
    if s = "CONS" then SOME opCONS else
    if s = "EQUAL" then SOME opEQUAL else
    if s = "<" then SOME opLESS else
    if s = "SYMBOL-<" then SOME opSYMBOL_LESS else
    if s = "+" then SOME opADD else
    if s = "-" then SOME opSUB else
    if s = "CONSP" then SOME opCONSP else
    if s = "NATP" then SOME opNATP else
    if s = "SYMBOLP" then SOME opSYMBOLP else
    if s = "CAR" then SOME opCAR else
    if s = "CDR" then SOME opCDR else NONE`;

val sexp2list_def = Define `
  (sexp2list (Val n) = []) /\
  (sexp2list (Sym s) = []) /\
  (sexp2list (Dot x y) = x::sexp2list y)`;

val IMP_isDot = prove(
  ``!x. ~isVal x /\ ~isSym x ==> isDot x``,
  Cases \\ EVAL_TAC);

val MEM_sexp2list_LSIZE = prove(
  ``!b a. MEM a (sexp2list b) ==> LSIZE a < LSIZE b``,
  Induct \\ SIMP_TAC std_ss [sexp2list_def,MEM,LSIZE_def] \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [] \\ RES_TAC \\ DECIDE_TAC);

val LSIZE_CAR_LESS = prove(
  ``!x m. LSIZE x < m ==> LSIZE (CAR x) < m``,
  Cases \\ SIMP_TAC std_ss [CAR_def,LSIZE_def] \\ DECIDE_TAC);

val LSIZE_CDR_LESS = prove(
  ``!x m. LSIZE x < m ==> LSIZE (CDR x) < m``,
  Cases \\ SIMP_TAC std_ss [CDR_def,LSIZE_def] \\ DECIDE_TAC);

val sexp2term_def = tDefine "sexp2term" `
  sexp2term x = if x = Sym "T" then Const x else
                if x = Sym "NIL" then Const x else
                if isVal x then Const x else
                if isSym x then Var (getSym x) else
                let x1 = CAR x in
                let x2 = CAR (CDR x) in
                let x3 = CAR (CDR (CDR x)) in
                let x4 = CAR (CDR (CDR (CDR x))) in
                if x1 = Sym "QUOTE" then Const x2 else
                if x1 = Sym "IF" then
                  If (sexp2term x2) (sexp2term x3) (sexp2term x4) else
                if ~(sym2prim (getSym x1) = NONE) then
                  App (PrimitiveFun (THE (sym2prim (getSym x1))))
                    (MAP sexp2term (sexp2list (CDR x))) else
                if x1 = Sym "FIRST" then First (sexp2term x2) else
                if x1 = Sym "SECOND" then Second (sexp2term x2) else
                if x1 = Sym "THIRD" then Third (sexp2term x2) else
                if x1 = Sym "FOURTH" then Fourth (sexp2term x2) else
                if x1 = Sym "FIFTH" then Fifth (sexp2term x2) else
                if x1 = Sym "OR" then Or (MAP sexp2term (sexp2list (CDR x))) else
                if x1 = Sym "AND" then And (MAP sexp2term (sexp2list (CDR x))) else
                if x1 = Sym "LIST" then List (MAP sexp2term (sexp2list (CDR x))) else
                if x1 = Sym "DEFUN" then
                  Defun (getSym x2) (MAP getSym (sexp2list x3)) x4 else
                if x1 = Sym "COND" then
                  Cond (MAP (\y. (sexp2term (CAR y), sexp2term (CAR (CDR y))))
                            (sexp2list (CDR x))) else
                if x1 = Sym "LET" then
                  Let (MAP (\y. (getSym (CAR y), sexp2term (CAR (CDR y))))
                           (sexp2list x2)) (sexp2term x3) else
                if x1 = Sym "LET*" then
                  LetStar (MAP (\y. (getSym (CAR y), sexp2term (CAR (CDR y))))
                               (sexp2list x2)) (sexp2term x3) else
                if CAR x1 = Sym "LAMBDA" then
                  let y2 = CAR (CDR x1) in
                  let y3 = CAR (CDR (CDR x1)) in
                    LamApp (MAP getSym (sexp2list y2)) (sexp2term y3)
                           (MAP sexp2term (sexp2list (CDR x))) else
                if x1 = Sym "DEFINE" then
                  App Define (MAP sexp2term (sexp2list (CDR x))) else
                if x1 = Sym "ERROR" then
                  App Error (MAP sexp2term (sexp2list (CDR x))) else
                if x1 = Sym "FUNCALL" then
                  App Funcall (MAP sexp2term (sexp2list (CDR x))) else
                if x1 = Sym "PRINT" then
                  App Print (MAP sexp2term (sexp2list (CDR x)))
                else (* user-defined fun *)
                  App (Fun (getSym x1))
                    (MAP sexp2term (sexp2list (CDR x)))`
 (WF_REL_TAC `measure LSIZE`
  \\ REPEAT STRIP_TAC \\ IMP_RES_TAC IMP_isDot
  \\ FULL_SIMP_TAC std_ss [isDot_thm,LSIZE_def,CDR_def,CAR_def]
  \\ IMP_RES_TAC MEM_sexp2list_LSIZE
  \\ POP_ASSUM MP_TAC \\ FULL_SIMP_TAC std_ss [CDR_def]
  \\ REPEAT STRIP_TAC
  \\ REPEAT (MATCH_MP_TAC LSIZE_CAR_LESS)
  \\ REPEAT (MATCH_MP_TAC LSIZE_CDR_LESS) \\ REPEAT DECIDE_TAC
  \\ Cases_on `b` \\ FULL_SIMP_TAC std_ss [CAR_def,LSIZE_def] \\ DECIDE_TAC);


(* a structural operational semantics *)

val EVAL_DATA_OP_def = Define `
  (EVAL_DATA_OP opCONS = ((\xs. LISP_CONS (EL 0 xs) (EL 1 xs)), 2)) /\
  (EVAL_DATA_OP opEQUAL = ((\xs. LISP_EQUAL (EL 0 xs) (EL 1 xs)), 2)) /\
  (EVAL_DATA_OP opLESS = ((\xs. LISP_LESS (EL 0 xs) (EL 1 xs)), 2)) /\
  (EVAL_DATA_OP opSYMBOL_LESS = ((\xs. LISP_SYMBOL_LESS (EL 0 xs) (EL 1 xs)), 2)) /\
  (EVAL_DATA_OP opADD = ((\xs. LISP_ADD (EL 0 xs) (EL 1 xs)), 2)) /\
  (EVAL_DATA_OP opSUB = ((\xs. LISP_SUB (EL 0 xs) (EL 1 xs)), 2)) /\
  (EVAL_DATA_OP opCONSP = ((\xs. LISP_CONSP (EL 0 xs)), 1)) /\
  (EVAL_DATA_OP opNATP = ((\xs. LISP_NUMBERP (EL 0 xs)), 1)) /\
  (EVAL_DATA_OP opSYMBOLP = ((\xs. LISP_SYMBOLP (EL 0 xs)), 1)) /\
  (EVAL_DATA_OP opCAR = ((\xs. CAR (EL 0 xs)), 1)) /\
  (EVAL_DATA_OP opCDR = ((\xs. CDR (EL 0 xs)), (1:num)))`;

val VarBindAux_def = Define `
  (VarBindAux [] args = FEMPTY) /\
  (VarBindAux (p::ps) [] = FEMPTY) /\
  (VarBindAux (p::ps) (a::as) = (VarBindAux ps as) |+ (p,a))`;

val VarBind_def = Define `
  VarBind params args = VarBindAux (REVERSE params) (REVERSE args)`;

val add_def_def = Define `
  add_def fns x = FUNION fns (FEMPTY |+ x)`;

val (R_ev_rules,R_ev_ind,R_ev_cases) = Hol_reln `
 (!s a fns io ok.
    R_ev (Const s, a,fns,io,ok) (s,fns,io,ok))
  /\
  (!x (a: string |-> SExp) fns io ok.
    x IN FDOM a ==>
    R_ev (Var x,a,fns,io,ok) (a ' x,fns,io,ok))
  /\
  (!a fns io ok s fns1 io1 ok1.
    R_ev (Const (Sym "NIL"),a,fns,io,ok) (s,fns1,io1,ok1) ==>
    R_ev (Or [],a,fns,io,ok) (s,fns1,io1,ok1))
  /\
  (!a fns io s1 fns1 io1 t ts ok.
    R_ev (t,a,fns,io,ok) (s1,fns1,io1,ok1) /\ isTrue s1 ==>
    R_ev (Or (t::ts),a,fns,io,ok) (s1,fns1,io1,ok1))
  /\
  (!a fns io s1 fns1 io1 s2 fns2 io2 t ts ok ok2.
    R_ev (t,a,fns,io,ok) (s1,fns1,io1,ok1) /\ ~(isTrue s1) /\
    R_ev (Or ts,a,fns1,io1,ok1) (s2,fns2,io2,ok2) ==>
    R_ev (Or (t::ts),a,fns,io,ok) (s2,fns2,io2,ok2))
  /\
  (!e1 e2 e3 s1 s a ok1 ok2.
    R_ev (e1,a,fns,io,ok) (s1,fns1,io1,ok1) /\ ~isTrue s1 /\
    R_ev (e3,a,fns1,io1,ok1) (s,fns2,io2,ok2)
    ==>
    R_ev (If e1 e2 e3,a,fns,io,ok) (s,fns2,io2,ok2))
  /\
  (!e1 e2 e3 s1 s a ok1 ok2.
    R_ev (e1,a,fns,io,ok) (s1,fns1,io1,ok1) /\ isTrue s1 /\
    R_ev (e2,a,fns1,io1,ok1) (s,fns2,io2,ok2)
    ==>
    R_ev (If e1 e2 e3,a,fns,io,ok) (s,fns2,io2,ok2))
  /\
  (!e xs ys fns a ok1 ok2.
    R_evl (ys,a,fns,io,ok) (sl,fns1,io1,ok1) /\ (LENGTH xs = LENGTH ys) /\
    R_ev (e,FUNION (VarBind xs sl) a,fns1,io1,ok1) (x,fns2,io2,ok2)
    ==>
    R_ev (LamApp xs e ys,a,fns,io,ok) (x,fns2,io2,ok2))
  /\
  (!el args a fc fns x ok1 ok2.
    R_evl (el,a,fns,io,ok) (args,fns1,io1,ok1) /\
    R_ap (fc,args,a,fns1,io1,ok1) (x,fns2,io2,ok2)
    ==>
    R_ev (App fc el,a,fns,io,ok) (x,fns2,io2,ok2))
  /\
  (!fc args a fns f.
    (EVAL_DATA_OP fc = (f,LENGTH args))
    ==>
    R_ap (PrimitiveFun fc,args,a,fns,io,ok) (f args,fns,io,ok))
  /\
  (!args a fc fns params exp x ok2.
    fc IN FDOM fns /\
    (fns ' fc = (params,exp)) /\ (LENGTH params = LENGTH args) /\
    R_ev (exp,VarBind params args,fns,io,ok) (x,fns2,io2,ok2)
    ==>
    R_ap (Fun fc,args,a,fns,io:string,ok) (x,fns2,io2,ok2))
  /\
  (!args a fns io.
    R_ap (Print,args,a,fns,io,ok) (Sym "NIL",fns,
          io ++ sexp2string (list2sexp (Sym "PRINT"::args)) ++ "\n",ok))
  /\
  (!a fns fc formals body.
    R_ap (Define,[fc; formals; body],a,fns,io,ok)
         (Sym "NIL",add_def fns (getSym fc,MAP getSym (sexp2list formals),sexp2term body),
          io,ok /\ ~(getSym fc IN FDOM fns)))
  /\
  (!args a fns io anything.
    R_ap (Error,args,a,fns,io,ok) (anything,fns,
          io ++ sexp2string (list2sexp (Sym "ERROR"::args)) ++ "\n",F))
  /\
  (!args params a fname fns x ok2.
    fname IN FDOM fns /\
    (fns ' fname = (params,exp)) /\ (LENGTH params = LENGTH args) /\
    R_ev (exp,VarBind params args,fns,io,ok) (x,fns2,io2,ok2)
    ==>
    R_ap (Funcall,Sym fname::args,a,fns,io,ok) (x,fns2,io2,ok2))
  /\ (* give short-cut semantics for failure states *)
  (!f args a fns io res.
    f IN FDOM fns /\
    (fns ' f = (params,exp)) /\ (LENGTH params = LENGTH args) ==>
    R_ap (Fun f,args,a,fns,io,F) (res,fns,io,F))
  /\ (* give short-cut semantics for failure states *)
  (!args a fns io res.
    R_ap (Funcall,args,a,fns,io,F) (res,fns,io,F))
  /\
  (!a.
    R_evl ([],a,fns,io,ok) ([],fns,io,ok))
  /\
  (!e el s sl a ok1 ok2.
    R_ev (e,a,fns,io,ok) (s,fns1,io1,ok1) /\
    R_evl (el,a,fns1,io1,ok1) (sl,fns2,io2,ok2)
    ==>
    R_evl (e::el,a,fns,io,ok) (s::sl,fns2,io2,ok2))

  /\ (* semantics of macros below *)

  (!e a fns io s fns1 io1 ok1.
    R_ev (App (PrimitiveFun opCAR) [e],a,fns,io,ok) (s,fns1,io1,ok1) ==>
    R_ev (First e,a,fns,io,ok) (s,fns1,io1,ok1))
  /\
  (!e a fns io s fns1 io1 ok1.
    R_ev (First (App (PrimitiveFun opCDR) [e]),a,fns,io,ok) (s,fns1,io1,ok1) ==>
    R_ev (Second e,a,fns,io,ok) (s,fns1,io1,ok1))
  /\
  (!e a fns io s fns1 io1 ok1.
    R_ev (Second (App (PrimitiveFun opCDR) [e]),a,fns,io,ok) (s,fns1,io1,ok1) ==>
    R_ev (Third e,a,fns,io,ok) (s,fns1,io1,ok1))
  /\
  (!e a fns io s fns1 io1 ok1.
    R_ev (Third (App (PrimitiveFun opCDR) [e]),a,fns,io,ok) (s,fns1,io1,ok1) ==>
    R_ev (Fourth e,a,fns,io,ok) (s,fns1,io1,ok1))
  /\
  (!e a fns io s fns1 io1 ok1.
    R_ev (Fourth (App (PrimitiveFun opCDR) [e]),a,fns,io,ok) (s,fns1,io1,ok1) ==>
    R_ev (Fifth e,a,fns,io,ok) (s,fns1,io1,ok1))
  /\
  (!zs x a fns io s fns1 io1 ok1.
    R_ev (LamApp (MAP FST zs) x (MAP SND zs),a,fns,io,ok) (s,fns1,io1,ok1) ==>
    R_ev (Let zs x,a,fns,io,ok) (s,fns1,io1,ok1))
  /\
  (!x a fns io s fns1 io1 ok1.
    R_ev (x,a,fns,io,ok) (s,fns1,io1,ok1) ==>
    R_ev (LetStar [] x,a,fns,io,ok) (s,fns1,io1,ok1))
  /\
  (!z zs x a fns io s fns1 io1 ok1.
    R_ev (Let [z] (LetStar zs x),a,fns,io,ok) (s,fns1,io1,ok1) ==>
    R_ev (LetStar (z::zs) x,a,fns,io,ok) (s,fns1,io1,ok1))
  /\
  (!a fns io s fns1 io1 ok1.
    R_ev (Const (Sym "NIL"),a,fns,io,ok) (s,fns1,io1,ok1) ==>
    R_ev (Cond [],a,fns,io,ok) (s,fns1,io1,ok1))
  /\
  (!x1 x2 qs a fns io s fns1 io1 ok1.
    R_ev (If x1 x2 (Cond qs),a,fns,io,ok) (s,fns1,io1,ok1) ==>
    R_ev (Cond ((x1,x2)::qs),a,fns,io,ok) (s,fns1,io1,ok1))
  /\
  (!a fns io s fns1 io1 ok1.
    R_ev (Const (Sym "T"),a,fns,io,ok) (s,fns1,io1,ok1) ==>
    R_ev (And [],a,fns,io,ok) (s,fns1,io1,ok1))
  /\
  (!a fns io s fns1 io1 ok1.
    R_ev (Const (Sym "NIL"),a,fns,io,ok) (s,fns1,io1,ok1) ==>
    R_ev (List [],a,fns,io,ok) (s,fns1,io1,ok1))
  /\
  (!a fns io s fns1 io1 ok1.
    R_ev (t,a,fns,io,ok) (s,fns1,io1,ok1) ==>
    R_ev (And [t],a,fns,io,ok) (s,fns1,io1,ok1))
  /\
  (!a fns io s fns1 io1 ok1.
    R_ev (If t1 (And (t2::ts)) (Const (Sym "NIL")),a,fns,io,ok) (s,fns1,io1,ok1) ==>
    R_ev (And (t1::t2::ts),a,fns,io,ok) (s,fns1,io1,ok1))
  /\
  (!a fns io s fns1 io1 ok1.
    R_ev (App (PrimitiveFun opCONS) [t;List ts],a,fns,io,ok) (s,fns1,io1,ok1) ==>
    R_ev (List (t::ts),a,fns,io,ok) (s,fns1,io1,ok1))
  /\
  (!fname ps body a fns io s fns1 io1 ok1.
    R_ev (App Define [Const (Sym fname); Const (list2sexp (MAP Sym ps)); Const body],a,fns,io,ok) (s,fns1,io1,ok1) ==>
    R_ev (Defun fname ps body,a,fns,io,ok) (s,fns1,io1,ok1))`;

val R_evl_LENGTH = save_thm("R_evl_LENGTH",
  R_ev_ind
  |> Q.SPECL [`\x y. T`,`\x y. (LENGTH (FST x) = LENGTH (FST y))`,`\x y. T`]
  |> SIMP_RULE std_ss [LENGTH]);


(* semantics of the read-eval-print loop *)

val (R_exec_rules,R_exec_ind,R_exec_cases) = Hol_reln `
 (!input fns io rest.
    (is_eof input = (T,rest)) ==>
    R_exec (input,fns,io) (io,T))
  /\
 (!input fns io input2 exp rest s fns2 io2 ok2 io3 ok3.
    (is_eof input = (F,input2)) /\
    (sexp_parse_stream input2 = (exp,rest)) /\
    R_ev (sexp2term exp,FEMPTY,fns,io,T) (s,fns2,io2,ok2) /\
    R_exec (rest,fns2,io2 ++ sexp2string s ++ "\n") (io3,ok3) ==>
    R_exec (input,fns,io) (io3,ok2 /\ ok3))`;


(* theorems about the semantics *)

val R_ev_induct = IndDefLib.derive_strong_induction(R_ev_rules,R_ev_ind);

val PULL_FORALL_IMP = METIS_PROVE [] ``(p ==> !x. q x) = !x. p ==> q x``;

val R_ev_OK = prove(
  ``(!x y. R_ap x y ==> SND (SND (SND y)) ==> (SND (SND (SND (SND (SND x)))))) /\
    (!x y. R_evl x y ==> SND (SND (SND y)) ==> (SND (SND (SND (SND (x)))))) /\
    (!x y. R_ev x y ==> SND (SND (SND y)) ==> (SND (SND (SND (SND (x))))))``,
  HO_MATCH_MP_TAC R_ev_ind \\ SIMP_TAC std_ss [pairTheory.FORALL_PROD,LET_DEF]);

val R_ev_T_11_lemma = prove(
  ``(!x y. R_ap x y ==> !z. SND (SND (SND y)) /\ R_ap x z ==> (y = z)) /\
    (!x y. R_evl x y ==> !z. SND (SND (SND y)) /\ R_evl x z ==> (y = z)) /\
    (!x y. R_ev x y ==> !z. SND (SND (SND y)) /\ R_ev x z ==> (y = z))``,
  HO_MATCH_MP_TAC R_ev_induct \\ SIMP_TAC std_ss []
  \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss []
  \\ POP_ASSUM MP_TAC \\ ONCE_REWRITE_TAC [R_ev_cases] \\ SIMP_TAC (srw_ss()) []
  \\ ASM_SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC \\ RES_TAC
  \\ IMP_RES_TAC R_ev_OK \\ FULL_SIMP_TAC std_ss [listTheory.CONS_11]
  \\ RES_TAC \\ FULL_SIMP_TAC std_ss [])
  |> SIMP_RULE std_ss [pairTheory.FORALL_PROD,PULL_FORALL_IMP];

val R_ev_T_11 = store_thm("R_ev_T_11",
  ``!x y. R_ev x (res,k,io,T) /\ R_ev x y ==> (y = (res,k,io,T))``,
  FULL_SIMP_TAC std_ss [pairTheory.FORALL_PROD] \\ REPEAT STRIP_TAC
  \\ IMP_RES_TAC R_ev_T_11_lemma \\ FULL_SIMP_TAC std_ss []);

val R_ap_T_11 = store_thm("R_ap_T_11",
  ``!x y. R_ap x (res,k,io,T) /\ R_ap x y ==> (y = (res,k,io,T))``,
  FULL_SIMP_TAC std_ss [pairTheory.FORALL_PROD] \\ REPEAT STRIP_TAC
  \\ IMP_RES_TAC R_ev_T_11_lemma \\ FULL_SIMP_TAC std_ss []);

val R_ap_F_11 = store_thm("R_ap_F_11",
  ``R_ap x (res,k,io,F) /\ R_ap x (res2,k2,io2,b) ==> ~b``,
  REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss []
  \\ IMP_RES_TAC R_ap_T_11 \\ FULL_SIMP_TAC std_ss []);

val R_ev_T_cases = store_thm("R_ev_T_cases",
  ``(R_ev (x,env,k,io,ok) (r,k',io',T) =
     R_ev (x,env,k,io,T) (r,k',io',T) /\ ok) /\
    (R_evl (xs,env,k,io,ok) (rs,k',io',T) =
     R_evl (xs,env,k,io,T) (rs,k',io',T) /\ ok) /\
    (R_ap (f,args,env,k,io,ok) (r,k',io',T) =
     R_ap (f,args,env,k,io,T) (r,k',io',T) /\ ok)``,
  REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC
  \\ IMP_RES_TAC R_ev_OK \\ FULL_SIMP_TAC std_ss []);


val _ = export_theory();
