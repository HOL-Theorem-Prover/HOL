open HolKernel boolLib bossLib Parse; val _ = new_theory "lisp_extract";
val _ = ParseExtras.temp_loose_equality()

open stringTheory finite_mapTheory pred_setTheory listTheory sumTheory;
open optionTheory arithmeticTheory relationTheory;

open lisp_sexpTheory lisp_semanticsTheory lisp_parseTheory;

val RW = REWRITE_RULE;
val RW1 = ONCE_REWRITE_RULE;


(* mimicking the macro definitions in HOL4 *)

val OR_def = Define `
  (OR [] = Sym "NIL") /\
  (OR (x::xs) = if isTrue x then x else OR xs)`;

val AND_def = Define `
  (AND [] = Sym "T") /\
  (AND [x] = x) /\
  (AND (x::xs) = if isTrue x then AND xs else Sym "NIL")`;

val LIST_def = Define `
  (LIST [] = Sym "NIL") /\
  (LIST (x::xs) = LISP_CONS x (LIST xs))`;

val COND_LIST_def = Define `
  (COND_LIST [] = Sym "NIL") /\
  (COND_LIST ((x,y)::xs) = if isTrue x then y else COND_LIST xs)`;

val FIRST_def = Define `FIRST x = CAR x`;
val SECOND_def = Define `SECOND x = CAR (CDR x)`;
val THIRD_def = Define `THIRD x = CAR (CDR (CDR x))`;
val FOURTH_def = Define `FOURTH x = CAR (CDR (CDR (CDR x)))`;
val FIFTH_def = Define `FIFTH x = CAR (CDR (CDR (CDR (CDR x))))`;


(* help for evaluating R_ev and R_ap *)

val R_ev_Var = store_thm("R_ev_Var",
  ``!x. x IN FDOM e ==> R_ev (Var x,e,fns,io,ok) (e ' x,fns,io,ok)``,
  REPEAT STRIP_TAC \\ RES_TAC \\ IMP_RES_TAC R_ev_rules \\ ASM_SIMP_TAC std_ss []);

val R_ev_Const = store_thm("R_ev_Const",
  ``!x. T ==> R_ev (Const x,e,fns,io,ok) (x,fns,io,ok)``,
  REPEAT STRIP_TAC \\ RES_TAC \\ ASM_SIMP_TAC std_ss [R_ev_rules]);

val R_ev_If = store_thm("R_ev_If",
  ``(by ==> R_ev (y,e,fns1,io1,ok1) (ans2,fns2,io2,ok2)) /\
    (bz ==> R_ev (z,e,fns1,io1,ok1) (ans3,fns3,io3,ok3)) ==>
    (bx ==> R_ev (x,e,fns,io,ok) (ans1,fns1,io1,ok1)) ==>
    bx /\ (isTrue ans1 ==> by) /\ (~isTrue ans1 ==> bz) ==>
                   R_ev (If x y z,e,fns,io,ok)
                         (if isTrue ans1 then ans2 else ans3,
                          if isTrue ans1 then fns2 else fns3,
                          if isTrue ans1 then io2 else io3,
                          if isTrue ans1 then ok2 else ok3)``,
  Cases_on `isTrue ans1` \\ ASM_SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC
  \\ RES_TAC \\ IMP_RES_TAC R_ev_rules \\ ASM_SIMP_TAC std_ss []);

val R_ev_If_GENERAL = store_thm("R_ev_If_GENERAL",
  ``(by ==> R_ev (y,e,fns1,io1,ok1) res2) /\
    (bz ==> R_ev (z,e,fns1,io1,ok1) res3) ==>
    (bx ==> R_ev (x,e,fns,io,ok) (ans1,fns1,io1,ok1)) ==>
    bx /\ (if isTrue ans1 then by else bz) ==>
                   R_ev (If x y z,e,fns,io,ok)
                         (if isTrue ans1 then res2 else res3)``,
  Q.SPEC_TAC (`res3`,`res3`) \\ Q.SPEC_TAC (`res2`,`res2`)
  \\ FULL_SIMP_TAC std_ss [pairTheory.FORALL_PROD]
  \\ Cases_on `isTrue ans1` \\ ASM_SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC
  \\ RES_TAC \\ IMP_RES_TAC R_ev_rules \\ ASM_SIMP_TAC std_ss []);

val R_ev_Or_CONS_CONS = store_thm("R_ev_Or_CONS_CONS",
  ``(bz ==> R_ev (Or (y::xs),e,fns1,io1,ok1) (ans3,fns3,io3,ok3)) ==>
    (bx ==> R_ev (x,e,fns,io,ok) (ans1,fns1,io1,ok1)) ==>
    bx /\ (~isTrue ans1 ==> bz) ==>
                   R_ev (Or (x::y::xs),e,fns,io,ok)
                         (if isTrue ans1 then ans1 else ans3,
                          if isTrue ans1 then fns1 else fns3,
                          if isTrue ans1 then io1 else io3,
                          if isTrue ans1 then ok1 else ok3)``,
  Cases_on `isTrue ans1` \\ ASM_SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC
  \\ RES_TAC \\ IMP_RES_TAC R_ev_rules \\ ASM_SIMP_TAC std_ss []);

val R_ev_Or_CONS_CONS_GENERAL = store_thm("R_ev_Or_CONS_CONS_GENERAL",
  ``(bz ==> R_ev (Or (y::xs),e,fns1,io1,ok1) res3) ==>
    (bx ==> R_ev (x,e,fns,io,ok) (ans1,fns1,io1,ok1)) ==>
    bx /\ (~isTrue ans1 ==> bz) ==>
                   R_ev (Or (x::y::xs),e,fns,io,ok)
                         (if isTrue ans1 then (ans1,fns1,io1,ok1) else res3)``,
  Q.SPEC_TAC (`res3`,`res3`) \\ FULL_SIMP_TAC std_ss [pairTheory.FORALL_PROD]
  \\ Cases_on `isTrue ans1` \\ ASM_SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC
  \\ RES_TAC \\ IMP_RES_TAC R_ev_rules \\ ASM_SIMP_TAC std_ss []);

val R_ev_Or_NIL = store_thm("R_ev_Or_NIL",
  ``T ==> R_ev (Or [],a,fns,io,ok) (Sym "NIL",fns,io,ok)``,
  REPEAT (ONCE_REWRITE_TAC [R_ev_cases] \\ FULL_SIMP_TAC (srw_ss()) []));

val lemma =
  (SIMP_CONV (srw_ss()) [Once R_ev_cases] THENC
   SIMP_CONV (srw_ss()) [Once R_ev_cases]) ``R_ev (Or [],x) y``

val R_ev_Or_SING_EQ = store_thm("R_ev_Or_SING_EQ",
  ``R_ev (t,a,fns,io,ok) res =
    R_ev (Or [t],a,fns,io,ok) res``,
  Q.SPEC_TAC (`res`,`res`) \\ FULL_SIMP_TAC std_ss [pairTheory.FORALL_PROD]
  \\ ONCE_REWRITE_TAC [EQ_SYM_EQ] \\ SIMP_TAC (srw_ss()) [Once R_ev_cases]
  \\ REPEAT STRIP_TAC \\ Cases_on `isTrue p_1` \\ FULL_SIMP_TAC std_ss []
  \\ FULL_SIMP_TAC std_ss [lemma,isTrue_def]);

val R_ev_Or_SING = store_thm("R_ev_Or_SING",
  ``(b ==> R_ev (t,a,fns,io,ok) res) ==>
    (b ==> R_ev (Or [t],a,fns,io,ok) res)``,
  SIMP_TAC std_ss [GSYM R_ev_Or_SING_EQ]);

val R_ap_PrimiveFun = store_thm("R_ap_PrimiveFun",
  ``!fc. (SND (EVAL_DATA_OP fc) = LENGTH args) ==>
         R_ap (PrimitiveFun fc,args,a,fns,io,ok) (FST (EVAL_DATA_OP fc) args,fns,io,ok)``,
  ONCE_REWRITE_TAC [R_ev_cases] \\ SIMP_TAC (srw_ss()) []
  \\ Cases_on `EVAL_DATA_OP fc` \\ FULL_SIMP_TAC std_ss []);

val R_evl_CONS = store_thm("R_evl_CONS",
  ``R_evl (el,a,fns1,io1,ok1) (sl,fns2,io2,ok2) ==>
    R_ev (e,a,fns,io,ok) (s,fns1,io1,ok1) ==>
    R_evl (e::el,a,fns,io,ok) (s::sl,fns2,io2,ok2)``,
  SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC \\ ONCE_REWRITE_TAC [R_ev_cases]
  \\ SIMP_TAC (srw_ss()) [] \\ METIS_TAC []);

val R_evl_CONS_GENERAL = store_thm("R_evl_CONS_GENERAL",
  ``(bl ==> R_evl (el,a,fns1,io1,ok1) (sl,fns2,io2,ok2)) ==>
    (b ==> R_ev (e,a,fns,io,ok) (s,fns1,io1,ok1)) ==>
    (b /\ bl ==> R_evl (e::el,a,fns,io,ok) (s::sl,fns2,io2,ok2))``,
  REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss []
  \\ ONCE_REWRITE_TAC [R_ev_cases]
  \\ SIMP_TAC (srw_ss()) [] \\ METIS_TAC []);

val R_evl_NIL = store_thm("R_evl_NIL",
  ``R_evl ([],a,fns,io,ok) ([],fns,io,ok)``,
  ONCE_REWRITE_TAC [R_ev_cases] \\ SIMP_TAC (srw_ss()) []);

val R_ev_App = store_thm("R_ev_App",
  ``(b1 ==> R_ap (fc,args,a,fns1,io1,ok1) res) ==>
    (b2 ==> R_evl (el,a,fns,io,ok) (args,fns1,io1,ok1)) ==>
    (b1 /\ b2 ==> R_ev (App fc el,a,fns,io,ok) res)``,
  Q.SPEC_TAC (`res`,`res`) \\ FULL_SIMP_TAC std_ss [pairTheory.FORALL_PROD]
  \\ REPEAT STRIP_TAC \\ RES_TAC \\ IMP_RES_TAC R_ev_rules);

val R_ev_App_GENERAL = store_thm("R_ev_App_GENERAL",
  ``(b1 ==> R_ap (fc,FST res1,a,SND res1) res2) ==>
    (b2 ==> R_evl (el,a,fns,io,ok) res1) ==>
    (b1 /\ b2 ==> R_ev (App fc el,a,fns,io,ok) res2)``,
  Q.SPEC_TAC (`res2`,`res2`) \\ Q.SPEC_TAC (`res1`,`res1`)
  \\ FULL_SIMP_TAC std_ss [pairTheory.FORALL_PROD]
  \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss []
  \\ ONCE_REWRITE_TAC [R_ev_cases]
  \\ SIMP_TAC (srw_ss()) [] \\ METIS_TAC []);

val R_ap_Define = store_thm("R_ap_Define",
  ``(LENGTH args = 3) ==>
    R_ap (Define,args,a,fns,io,ok)
         (Sym "NIL",add_def fns (getSym (EL 0 args),MAP getSym (sexp2list (EL 1 args)),sexp2term (EL 2 args)),
          io,ok /\ ~(getSym (EL 0 args) IN FDOM fns))``,
  Cases_on `args` \\ SIMP_TAC std_ss [LENGTH]
  \\ Cases_on `t` \\ SIMP_TAC std_ss [LENGTH]
  \\ Cases_on `t'` \\ SIMP_TAC std_ss [LENGTH]
  \\ REVERSE (Cases_on `t`) \\ SIMP_TAC std_ss [LENGTH,ADD1]
  THEN1 (REPEAT STRIP_TAC \\ `F` by DECIDE_TAC)
  \\ SIMP_TAC std_ss [EVAL ``EL 0 [x1;x2;x3]``,EVAL ``EL 1 [x1;x2;x3]``,EVAL ``EL 2 [x1;x2;x3]``]
  \\ ASM_SIMP_TAC std_ss [R_ev_rules]);

val R_ap_Error = store_thm("R_ap_Error",
  ``T ==> R_ap (Error,args,a,fns,io,ok) (Sym "NIL",fns,STRCAT
           (STRCAT io (sexp2string (list2sexp (Sym "ERROR"::args))))
           "\n",F)``,
  ASM_SIMP_TAC std_ss [R_ev_rules]);

val R_ev_CAR = prove(
  ``R_ev (e,a,fns,io,ok) (s,fns1,io1,ok1) ==>
    R_ev (App (PrimitiveFun opCAR) [e],a,fns,io,ok) (CAR s,fns1,io1,ok1)``,
  REPEAT STRIP_TAC \\ SIMP_TAC std_ss [] \\ RES_TAC
  \\ ONCE_REWRITE_TAC [R_ev_cases] \\ SIMP_TAC (srw_ss()) []
  \\ Q.LIST_EXISTS_TAC [`fns1`,`io1`,`[s]`,`ok1`]
  \\ FULL_SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC THEN1
   (MATCH_MP_TAC (RW [] (MATCH_MP R_evl_CONS R_evl_NIL))
    \\ ASM_SIMP_TAC std_ss [])
  \\ MATCH_MP_TAC (SIMP_RULE std_ss [HD,EVAL_DATA_OP_def,EL]
         (Q.INST [`args`|->`[s]`] (SPEC ``opCAR`` R_ap_PrimiveFun)))
  \\ SIMP_TAC std_ss [LENGTH])

val R_ev_CDR = prove(
  ``R_ev (e,a,fns,io,ok) (s,fns1,io1,ok1) ==>
    R_ev (App (PrimitiveFun opCDR) [e],a,fns,io,ok) (CDR s,fns1,io1,ok1)``,
  REPEAT STRIP_TAC \\ SIMP_TAC std_ss [] \\ RES_TAC
  \\ ONCE_REWRITE_TAC [R_ev_cases] \\ SIMP_TAC (srw_ss()) []
  \\ Q.LIST_EXISTS_TAC [`fns1`,`io1`,`[s]`,`ok1`]
  \\ FULL_SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC THEN1
   (MATCH_MP_TAC (RW [] (MATCH_MP R_evl_CONS R_evl_NIL))
    \\ ASM_SIMP_TAC std_ss [])
  \\ MATCH_MP_TAC (SIMP_RULE std_ss [HD,EVAL_DATA_OP_def,EL]
         (Q.INST [`args`|->`[s]`] (SPEC ``opCDR`` R_ap_PrimiveFun)))
  \\ SIMP_TAC std_ss [LENGTH])

val R_ev_FIRST = store_thm("R_ev_FIRST",
  ``(b ==> R_ev (e,a,fns,io,ok) (s,fns1,io1,ok1)) ==>
    (b ==> R_ev (First e,a,fns,io,ok) (FIRST s,fns1,io1,ok1))``,
  REPEAT STRIP_TAC \\ SIMP_TAC std_ss [FIRST_def] \\ RES_TAC
  \\ ONCE_REWRITE_TAC [R_ev_cases] \\ SIMP_TAC (srw_ss()) []
  \\ FULL_SIMP_TAC std_ss [R_ev_CAR]);

val R_ev_SECOND = store_thm("R_ev_SECOND",
  ``(b ==> R_ev (e,a,fns,io,ok) (s,fns1,io1,ok1)) ==>
    (b ==> R_ev (Second e,a,fns,io,ok) (SECOND s,fns1,io1,ok1))``,
  REPEAT STRIP_TAC \\ SIMP_TAC std_ss [SECOND_def] \\ RES_TAC
  \\ ONCE_REWRITE_TAC [R_ev_cases] \\ SIMP_TAC (srw_ss()) [GSYM FIRST_def]
  \\ MATCH_MP_TAC (RW [AND_IMP_INTRO] R_ev_FIRST)
  \\ FULL_SIMP_TAC std_ss [R_ev_CDR]);

val R_ev_THIRD = store_thm("R_ev_THIRD",
  ``(b ==> R_ev (e,a,fns,io,ok) (s,fns1,io1,ok1)) ==>
    (b ==> R_ev (Third e,a,fns,io,ok) (THIRD s,fns1,io1,ok1))``,
  REPEAT STRIP_TAC \\ SIMP_TAC std_ss [THIRD_def] \\ RES_TAC
  \\ ONCE_REWRITE_TAC [R_ev_cases] \\ SIMP_TAC (srw_ss()) [GSYM SECOND_def]
  \\ MATCH_MP_TAC (RW [AND_IMP_INTRO] R_ev_SECOND)
  \\ FULL_SIMP_TAC std_ss [R_ev_CDR]);

val R_ev_FOURTH = store_thm("R_ev_FOURTH",
  ``(b ==> R_ev (e,a,fns,io,ok) (s,fns1,io1,ok1)) ==>
    (b ==> R_ev (Fourth e,a,fns,io,ok) (FOURTH s,fns1,io1,ok1))``,
  REPEAT STRIP_TAC \\ SIMP_TAC std_ss [FOURTH_def] \\ RES_TAC
  \\ ONCE_REWRITE_TAC [R_ev_cases] \\ SIMP_TAC (srw_ss()) [GSYM THIRD_def]
  \\ MATCH_MP_TAC (RW [AND_IMP_INTRO] R_ev_THIRD)
  \\ FULL_SIMP_TAC std_ss [R_ev_CDR]);

val R_ev_FIFTH = store_thm("R_ev_FIFTH",
  ``(b ==> R_ev (e,a,fns,io,ok) (s,fns1,io1,ok1)) ==>
    (b ==> R_ev (Fifth e,a,fns,io,ok) (FIFTH s,fns1,io1,ok1))``,
  REPEAT STRIP_TAC \\ SIMP_TAC std_ss [FIFTH_def] \\ RES_TAC
  \\ ONCE_REWRITE_TAC [R_ev_cases] \\ SIMP_TAC (srw_ss()) [GSYM FOURTH_def]
  \\ MATCH_MP_TAC (RW [AND_IMP_INTRO] R_ev_FOURTH)
  \\ FULL_SIMP_TAC std_ss [R_ev_CDR]);

val R_ev_FIRST_GENERAL = store_thm("R_ev_FIRST_GENERAL",
  ``(b ==> R_ev (e,a,fns,io,ok) res) ==>
    (b ==> R_ev (First e,a,fns,io,ok) (FIRST (FST res),SND res))``,
  Q.SPEC_TAC (`res`,`res`) \\ FULL_SIMP_TAC std_ss [pairTheory.FORALL_PROD,R_ev_FIRST]);

val R_ev_SECOND_GENERAL = store_thm("R_ev_SECOND_GENERAL",
  ``(b ==> R_ev (e,a,fns,io,ok) res) ==>
    (b ==> R_ev (Second e,a,fns,io,ok) (SECOND (FST res),SND res))``,
  Q.SPEC_TAC (`res`,`res`) \\ FULL_SIMP_TAC std_ss [pairTheory.FORALL_PROD,R_ev_SECOND]);

val R_ev_THIRD_GENERAL = store_thm("R_ev_THIRD_GENERAL",
  ``(b ==> R_ev (e,a,fns,io,ok) res) ==>
    (b ==> R_ev (Third e,a,fns,io,ok) (THIRD (FST res),SND res))``,
  Q.SPEC_TAC (`res`,`res`) \\ FULL_SIMP_TAC std_ss [pairTheory.FORALL_PROD,R_ev_THIRD]);

val R_ev_FOURTH_GENERAL = store_thm("R_ev_FOURTH_GENERAL",
  ``(b ==> R_ev (e,a,fns,io,ok) res) ==>
    (b ==> R_ev (Fourth e,a,fns,io,ok) (FOURTH (FST res),SND res))``,
  Q.SPEC_TAC (`res`,`res`) \\ FULL_SIMP_TAC std_ss [pairTheory.FORALL_PROD,R_ev_FOURTH]);

val R_ev_FIFTH_GENERAL = store_thm("R_ev_FIFTH_GENERAL",
  ``(b ==> R_ev (e,a,fns,io,ok) res) ==>
    (b ==> R_ev (Fifth e,a,fns,io,ok) (FIFTH (FST res),SND res))``,
  Q.SPEC_TAC (`res`,`res`) \\ FULL_SIMP_TAC std_ss [pairTheory.FORALL_PROD,R_ev_FIFTH]);

val R_ev_LetStar_NIL = store_thm("R_ev_LetStar_NIL",
  ``R_ev (x,a,fns,io,ok) res =
    R_ev (LetStar [] x,a,fns,io,ok) res``,
  Q.SPEC_TAC (`res`,`res`) \\ FULL_SIMP_TAC std_ss [pairTheory.FORALL_PROD]
  \\ ONCE_REWRITE_TAC [EQ_SYM_EQ] \\ SIMP_TAC (srw_ss()) [Once R_ev_cases]
  \\ REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [] \\ SIMP_TAC (srw_ss()) [Once R_ev_cases]);

val R_ev_LetStar_CONS = store_thm("R_ev_LetStar_CONS",
  ``R_ev (Let [z] (LetStar zs x),a,fns,io,ok) res =
    R_ev (LetStar (z::zs) x,a,fns,io,ok) res``,
  Q.SPEC_TAC (`res`,`res`) \\ FULL_SIMP_TAC std_ss [pairTheory.FORALL_PROD]
  \\ ONCE_REWRITE_TAC [EQ_SYM_EQ] \\ SIMP_TAC (srw_ss()) [Once R_ev_cases]
  \\ REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [] \\ SIMP_TAC (srw_ss()) [Once R_ev_cases]);

val R_ev_Cond_NIL = store_thm("R_ev_Cond_NIL",
  ``R_ev (Const (Sym "NIL"),a,fns,io,ok) res =
    R_ev (Cond [],a,fns,io,ok) res``,
  Q.SPEC_TAC (`res`,`res`) \\ FULL_SIMP_TAC std_ss [pairTheory.FORALL_PROD]
  \\ ONCE_REWRITE_TAC [EQ_SYM_EQ] \\ SIMP_TAC (srw_ss()) [Once R_ev_cases]
  \\ REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [] \\ SIMP_TAC (srw_ss()) [Once R_ev_cases]);

val R_ev_Cond_CONS = store_thm("R_ev_Cond_CONS",
  ``R_ev (If x1 x2 (Cond qs),a,fns,io,ok) res =
    R_ev (Cond ((x1,x2)::qs),a,fns,io,ok) res``,
  Q.SPEC_TAC (`res`,`res`) \\ FULL_SIMP_TAC std_ss [pairTheory.FORALL_PROD]
  \\ ONCE_REWRITE_TAC [EQ_SYM_EQ] \\ SIMP_TAC (srw_ss()) [Once R_ev_cases]
  \\ REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [] \\ SIMP_TAC (srw_ss()) [Once R_ev_cases]);

val R_ev_And_NIL = store_thm("R_ev_And_NIL",
  ``R_ev (Const (Sym "T"),a,fns,io,ok) res =
    R_ev (And [],a,fns,io,ok) res``,
  Q.SPEC_TAC (`res`,`res`) \\ FULL_SIMP_TAC std_ss [pairTheory.FORALL_PROD]
  \\ ONCE_REWRITE_TAC [EQ_SYM_EQ] \\ SIMP_TAC (srw_ss()) [Once R_ev_cases]
  \\ REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [] \\ SIMP_TAC (srw_ss()) [Once R_ev_cases]);

val R_ev_List_NIL = store_thm("R_ev_List_NIL",
  ``R_ev (Const (Sym "NIL"),a,fns,io,ok) res =
    R_ev (List [],a,fns,io,ok) res``,
  Q.SPEC_TAC (`res`,`res`) \\ FULL_SIMP_TAC std_ss [pairTheory.FORALL_PROD]
  \\ ONCE_REWRITE_TAC [EQ_SYM_EQ] \\ SIMP_TAC (srw_ss()) [Once R_ev_cases]
  \\ REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [] \\ SIMP_TAC (srw_ss()) [Once R_ev_cases]);

val R_ev_And_SING = store_thm("R_ev_And_SING",
  ``R_ev (t,a,fns,io,ok) res =
    R_ev (And [t],a,fns,io,ok) res``,
  Q.SPEC_TAC (`res`,`res`) \\ FULL_SIMP_TAC std_ss [pairTheory.FORALL_PROD]
  \\ ONCE_REWRITE_TAC [EQ_SYM_EQ] \\ SIMP_TAC (srw_ss()) [Once R_ev_cases]
  \\ REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [] \\ SIMP_TAC (srw_ss()) [Once R_ev_cases]);

val R_ev_And_CONS = store_thm("R_ev_And_CONS",
  ``R_ev (If t1 (And (t2::ts)) (Const (Sym "NIL")),a,fns,io,ok) res =
    R_ev (And (t1::t2::ts),a,fns,io,ok) res``,
  Q.SPEC_TAC (`res`,`res`) \\ FULL_SIMP_TAC std_ss [pairTheory.FORALL_PROD]
  \\ ONCE_REWRITE_TAC [EQ_SYM_EQ] \\ SIMP_TAC (srw_ss()) [Once R_ev_cases]
  \\ REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [] \\ SIMP_TAC (srw_ss()) [Once R_ev_cases]);

val R_ev_List_CONS = store_thm("R_ev_List_CONS",
  ``R_ev (App (PrimitiveFun opCONS) [t;List ts],a,fns,io,ok) res =
    R_ev (List (t::ts),a,fns,io,ok) res``,
  Q.SPEC_TAC (`res`,`res`) \\ FULL_SIMP_TAC std_ss [pairTheory.FORALL_PROD]
  \\ ONCE_REWRITE_TAC [EQ_SYM_EQ] \\ SIMP_TAC (srw_ss()) [Once R_ev_cases]
  \\ REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [] \\ SIMP_TAC (srw_ss()) [Once R_ev_cases]);

val R_ev_Defun = store_thm("R_ev_Defun",
  ``R_ev (App Define [Const (Sym fname); Const (list2sexp (MAP Sym ps)); Const body],a,fns,io,ok) res =
    R_ev (Defun fname ps body,a,fns,io,ok) res``,
  Q.SPEC_TAC (`res`,`res`) \\ FULL_SIMP_TAC std_ss [pairTheory.FORALL_PROD]
  \\ ONCE_REWRITE_TAC [EQ_SYM_EQ] \\ SIMP_TAC (srw_ss()) [Once R_ev_cases]
  \\ REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [] \\ SIMP_TAC (srw_ss()) [Once R_ev_cases]);

val MAP_FST_MAP_SND = prove(
  ``!xs ys. (LENGTH xs = LENGTH ys) ==>
            (MAP FST (ZIP (xs,ys)) = xs) /\ (MAP SND (ZIP (xs,ys)) = ys)``,
  Induct \\ Cases_on `ys` \\ FULL_SIMP_TAC (srw_ss()) []);

val R_ev_LamApp_lemma = prove(
  ``!xs.
      (b1 ==> R_evl (ys,a,fns,io,ok) (sl,fns1,io1,ok1)) ==>
      (b2 ==> R_ev (e,FUNION (VarBind xs sl) a,fns1,io1,ok1) (x,fns2,io2,ok2)) ==>
      (LENGTH xs = LENGTH ys) /\ b1 /\ b2 ==>
      R_ev (LamApp xs e ys,a,fns,io,ok) (x,fns2,io2,ok2)``,
  REPEAT STRIP_TAC \\ RES_TAC \\ IMP_RES_TAC R_ev_rules \\ ASM_SIMP_TAC std_ss []);

val R_ev_Let = store_thm("R_ev_Let",
  ``!xs.
      (b1 ==> R_evl (ys,a,fns,io,ok) (sl,fns1,io1,ok1)) ==>
      (b2 ==> R_ev (e,FUNION (VarBind xs sl) a,fns1,io1,ok1) (x,fns2,io2,ok2)) ==>
      (LENGTH xs = LENGTH ys) /\ b1 /\ b2 ==>
      R_ev (Let (ZIP (xs,ys)) e,a,fns,io,ok) (x,fns2,io2,ok2)``,
  REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss []
  \\ ONCE_REWRITE_TAC [R_ev_cases] \\ SIMP_TAC (srw_ss()) []
  \\ MATCH_MP_TAC (RW [AND_IMP_INTRO] R_ev_LamApp_lemma)
  \\ ASM_SIMP_TAC std_ss [LENGTH_MAP,MAP_FST_MAP_SND]);

val R_ev_Let_GENERAL = store_thm("R_ev_Let_GENERAL",
  ``!xs.
      (b1 ==> R_evl (ys,a,fns,io,ok) res1) ==>
      (b2 ==> R_ev (e,FUNION (VarBind xs (FST res1)) a,SND res1) res2) ==>
      (LENGTH xs = LENGTH ys) /\ b1 /\ b2 ==>
      R_ev (Let (ZIP (xs,ys)) e,a,fns,io,ok) res2``,
  Q.SPEC_TAC (`res1`,`res1`) \\ Q.SPEC_TAC (`res2`,`res2`)
  \\ FULL_SIMP_TAC std_ss [pairTheory.FORALL_PROD] \\ METIS_TAC [R_ev_Let]);

val R_ev_LamApp = store_thm("R_ev_LamApp",
  ``(b1 ==> R_ev (Let xs e,a,fns,io,ok) res) ==>
    (b1 ==> R_ev (LamApp (MAP FST xs) e (MAP SND xs),a,fns,io,ok) res)``,
  Q.SPEC_TAC (`res`,`res`) \\ FULL_SIMP_TAC std_ss [pairTheory.FORALL_PROD]
  \\ SIMP_TAC std_ss [Once R_ev_cases] \\ SIMP_TAC (srw_ss()) []
  \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss []
  \\ SIMP_TAC std_ss [Once R_ev_cases] \\ SIMP_TAC (srw_ss()) []);

val funcall_ok_def = Define `
  funcall_ok args fns io ok = ?result. R_ap (Funcall,args,ARB,fns,io,ok) result`;

val funcall_def = Define `
  funcall args fns io ok =
    if funcall_ok args fns io ok
    then @result. R_ap (Funcall,args,ARB,fns,io,ok) result
    else (Sym "NIL",fns,io,ok)`;

val R_ap_Funcall_ARB = prove(
  ``R_ap (Funcall,args,a,fns,io,ok) x = R_ap (Funcall,args,ARB,fns,io,ok) x``,
  ONCE_REWRITE_TAC [R_ev_cases] \\ SIMP_TAC (srw_ss()) []);

val R_ap_Funcall = store_thm("R_ap_Funcall",
  ``funcall_ok args fns io ok ==>
    R_ap (Funcall,args,a,fns,io,ok) (funcall args fns io ok)``,
  SIMP_TAC std_ss [funcall_ok_def,funcall_def]
  \\ ONCE_REWRITE_TAC [R_ap_Funcall_ARB] \\ METIS_TAC []);

val R_ap_Print = store_thm("R_ap_Print",
  ``T ==> R_ap (Print,args,a,fns,io,ok) (Sym "NIL",fns,
          io ++ sexp2string (list2sexp (Sym "PRINT"::args)) ++ "\n",ok)``,
  SIMP_TAC std_ss [R_ev_rules]);

val R_ap_SET_ENV = store_thm("R_ap_SET_ENV",
  ``R_ap (Fun fc,xs,e,rest) result = R_ap (Fun fc,xs,ARB,rest) result``,
  ONCE_REWRITE_TAC [R_ev_cases] \\ SRW_TAC [] []);

val R_ap_Fun = store_thm("R_ap_Fun",
  ``!fns2 io io2 args a fc fns params exp x ok2 res.
      fc IN FDOM fns /\ (fns ' fc = (params,exp)) /\
      (LENGTH params = LENGTH args) /\
      R_ev (exp,VarBind params args,fns,io,ok) res ==>
      R_ap (Fun fc,args,a,fns,io,ok) res``,
  SIMP_TAC std_ss [pairTheory.FORALL_PROD] \\ REPEAT STRIP_TAC
  \\ ONCE_REWRITE_TAC [R_ev_cases] \\ SIMP_TAC (srw_ss()) [] \\ METIS_TAC [])

val R_ap_NOT_OK = store_thm("R_ap_NOT_OK",
  ``!name params args exp2.
      (b ==> R_ap (Fun name,args,e,k,io,ok) exp) ==>
      name IN FDOM k /\ (k ' name = (params,exp2)) /\
      (LENGTH params = LENGTH args) ==>
      ((ok ==> b) ==> R_ap (Fun name,args,e,k,io,ok) (if ok then exp else (Sym "NIL",k,io,ok)))``,
  Cases_on `ok` \\ FULL_SIMP_TAC std_ss []
  \\ ONCE_REWRITE_TAC [R_ev_cases] \\ SIMP_TAC (srw_ss()) [] \\ METIS_TAC []);


(* misc *)

val isTrue_if_lemma = prove(
  ``!b x y. isTrue (if b then x else y) =  b /\ isTrue x \/ ~b /\ isTrue y``,
  Cases \\ SIMP_TAC std_ss []);

val isTrue_if = save_thm("isTrue_if",LIST_CONJ
  [EVAL ``isTrue (Sym "T")``,EVAL ``isTrue (Sym "NIL")``,isTrue_if_lemma]);

val isTrue_LISP_TEST = store_thm("isTrue_LISP_TEST",
  ``!b. isTrue (LISP_TEST b) = b``,Cases \\ EVAL_TAC);

val isTrue_CLAUSES = store_thm("isTrue_CLAUSES",
  ``(isTrue (Sym "T") = T) /\
    (isTrue (Sym "NIL") = F) /\
    (isTrue (LISP_NUMBERP x) = isVal x) /\
    (isTrue (LISP_SYMBOLP x) = isSym x) /\
    (isTrue (LISP_CONSP x) = isDot x) /\
    (isTrue (LISP_ATOMP x) = ~isDot x) /\
    (isTrue (LISP_ADD x y) = T) /\
    (isTrue (LISP_SUB x y) = T) /\
    (isTrue (LISP_CONS x y) = T) /\
    (isTrue (AND []) = T) /\
    (isTrue (AND (x::xs)) = isTrue x /\ isTrue (AND xs)) /\
    (isTrue (OR []) = F) /\
    (isTrue (OR (x::xs)) = isTrue x \/ isTrue (OR xs)) /\
    (isTrue (LISP_EQUAL x y) = (x = y))``,
  Cases_on `xs`
  \\ SIMP_TAC std_ss [LISP_NUMBERP_def,LISP_SYMBOLP_def,LISP_CONSP_def,
       isTrue_LISP_TEST,LISP_ATOMP_def,AND_def,EVAL ``isTrue (Sym "T")``,
       EVAL ``isTrue (Sym "NIL")``,OR_def,LISP_ADD_def,LISP_SUB_def,
       EVAL ``isTrue (Val n)``, EVAL ``isTrue (Dot x y)``,LISP_CONS_def]
  \\ Cases_on `isTrue x` \\ ASM_SIMP_TAC std_ss [] \\ EVAL_TAC
  \\ METIS_TAC [EVAL ``Sym "NIL" = Sym "T"``]);

val fns_assum_def = Define `
  fns_assum k xs =
    EVERY (\(name,params,body). (name:string) IN FDOM k /\
               (k ' name = (params:string list,body:term))) xs`;

val R_ev_fns_assum_lemma = prove(
  ``(!x y. R_ap x y ==> !xs. fns_assum (FST (SND (SND (SND x)))) xs ==>
                             fns_assum (FST (SND y)) xs) /\
    (!x y. R_evl x y ==> !xs. fns_assum (FST (SND (SND x))) xs ==>
                              fns_assum (FST (SND y)) xs) /\
    (!x y. R_ev x y ==> !xs. fns_assum (FST (SND (SND x))) xs ==>
                             fns_assum (FST (SND y)) xs)``,
  HO_MATCH_MP_TAC R_ev_ind \\ SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [fns_assum_def,add_def_def,FUNION_DEF,IN_UNION,
       FDOM_FUPDATE,IN_INSERT,EVERY_MEM,pairTheory.FORALL_PROD,
       FDOM_FEMPTY,NOT_IN_EMPTY] \\ REPEAT STRIP_TAC
  \\ RES_TAC \\ FULL_SIMP_TAC std_ss []);

val R_ev_fns_assum =
  el 3 (CONJUNCTS R_ev_fns_assum_lemma)
  |> Q.SPECL [`(x1,x2,x3,x4)`,`y`] |> UNDISCH |> SPEC_ALL |> DISCH_ALL
  |> SIMP_RULE std_ss [AND_IMP_INTRO] |> RW1 [CONJ_COMM]
  |> RW [GSYM AND_IMP_INTRO];

val R_ap_fns_assum =
  el 1 (CONJUNCTS R_ev_fns_assum_lemma)
  |> Q.SPECL [`(x1,x2,x3,x4,x5)`,`y`] |> UNDISCH |> SPEC_ALL |> DISCH_ALL
  |> SIMP_RULE std_ss [AND_IMP_INTRO] |> RW1 [CONJ_COMM]
  |> RW [GSYM AND_IMP_INTRO]

val fns_assum_UPDATE = store_thm("fns_assum_UPDATE",
  ``(fns_assum x4 xs ==> R_ap (x1,x2,x3,x4,x5) y) ==>
    fns_assum x4 xs ==> fns_assum (FST (SND y)) xs``,
  METIS_TAC [R_ap_fns_assum]);

val fns_assum_funcall_IMP = store_thm("fns_assum_funcall_IMP",
  ``fns_assum fns xs ==>
    fns_assum (FST (SND (funcall args fns io ok))) xs``,
  SIMP_TAC std_ss [funcall_def]
  \\ Cases_on `funcall_ok args fns io ok` \\ ASM_SIMP_TAC std_ss []
  \\ METIS_TAC [fns_assum_UPDATE,funcall_ok_def]);

val fns_assum_add_def_IMP = store_thm("fns_assum_add_def_IMP",
  ``fns_assum fns xs ==>
    fns_assum (add_def fns x) xs``,
  SRW_TAC [] [FUNION_DEF,FDOM_FUPDATE,FDOM_FEMPTY,fns_assum_def,
    add_def_def,EVERY_MEM,pairTheory.FORALL_PROD]
  \\ RES_TAC \\ FULL_SIMP_TAC std_ss []);

val FST_SND_IF = store_thm("FST_SND_IF",
  ``(FST (if b then x else y) = if b then FST x else FST y) /\
    (SND (if b then x else y) = if b then SND x else SND y)``,
  Cases_on `b` \\ FULL_SIMP_TAC std_ss []);

val isTrue_T = save_thm("isTrue_T",EVAL ``isTrue (Sym "T")``);

val isTrue_INTRO = store_thm("isTrue_INTRO",
  ``((x = y) = isTrue (LISP_EQUAL x y)) /\
    (isTrue x /\ isTrue y = isTrue (if isTrue x then y else Sym "NIL")) /\
    (isTrue x \/ isTrue y = isTrue (if isTrue x then Sym "T" else y)) /\
    (LISP_CONS = Dot) /\
    (~isTrue x = isTrue (if isTrue x then Sym "NIL" else Sym "T")) /\
    (getVal x < getVal y = isTrue (LISP_LESS x y)) /\
    (getVal x > getVal y = isTrue (LISP_LESS y x)) /\
    (getVal x <= getVal y = ~(getVal x > getVal y)) /\
    (getVal x >= getVal y = ~(getVal x < getVal y)) /\
    (getSym x < getSym y = isTrue (LISP_SYMBOL_LESS x y)) /\
    (isDot x = isTrue (LISP_CONSP x)) /\
    (isVal x = isTrue (LISP_NUMBERP x)) /\
    (isSym x = isTrue (LISP_SYMBOLP x))``,
  SIMP_TAC std_ss [FUN_EQ_THM] \\ EVAL_TAC \\ SRW_TAC [] [] \\ DECIDE_TAC);

val PAIR_LEMMA = prove(
  ``!x. (x = (FST x,x2)) = (SND x = x2)``,
  Cases \\ SRW_TAC [] []);

val SND_SND_SND_funcall_IMP = store_thm("SND_SND_SND_funcall_IMP",
  ``R_ap (Funcall,(Sym f)::xs,ARB,k,io,ok) (x1,x2,x3,ok2) /\
    SND (SND (SND (funcall ((Sym f)::xs) k io ok))) ==> ok2``,
  SIMP_TAC std_ss [funcall_def] \\ REPEAT STRIP_TAC
  \\ `funcall_ok (Sym f::xs) k io ok` by METIS_TAC [funcall_ok_def]
  \\ FULL_SIMP_TAC std_ss [] \\ Cases_on `ok2` \\ SIMP_TAC std_ss []
  \\ `!res. R_ap (Funcall,Sym f::xs,ARB,k,io,ok) res =
            (res = (FST res, FST (SND res), FST (SND (SND res)),F))` by METIS_TAC [R_ap_F_11,pairTheory.PAIR]
  \\ FULL_SIMP_TAC std_ss [PAIR_LEMMA]
  \\ `?result:SExp # (string |-> string list # term) # string # bool. ~SND (SND (SND result))` by (Q.EXISTS_TAC `(ARB,ARB,ARB,F)` \\ EVAL_TAC)
  \\ METIS_TAC []);

val _ = export_theory();
