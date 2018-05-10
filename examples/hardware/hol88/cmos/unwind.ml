% Rules for unfolding, unwinding, pruning etc. %

% Rules for unfolding %

%
            A1 |- t1 = t1' , ... , An |- tn = tn'
   ---------------------------------------------------------
    A1 u ... u An |- (t1 /\ ... /\ tn) = (t1' /\ ... /\ tn')
%

letrec MK_CONJL thl =
 (if null thl 
  then fail
  if null(tl thl)
  then hd thl
  else
  (let th = MK_CONJL(tl thl)
   in
   let t1,()  = dest_eq(concl(hd thl))
   and (),t2' = dest_eq(concl th)
   in
   (AP_TERM "$/\ ^t1" th) TRANS (AP_THM (AP_TERM "$/\" (hd thl)) t2'))
 ) ? failwith `MK_CONJL`;;

%
            A1 |- t1 = t1' , ... , An |- tn = tn'
      --------------------------------------------------
       A1 u ... u An  |- ?l1 ... lm. t1  /\ ... /\ tn =
                         ?l1 ... lm. t1' /\ ... /\ tn'
%

let UNFOLD thl =
 let net = mk_conv_net thl
 in
 \t.
  ((let vars, eqs = strip_exists t
    and rewrite   = REWRITES_CONV net
    in
    LIST_MK_EXISTS vars (MK_CONJL(map rewrite (conjuncts eqs)))
   ) ? failwith `UNFOLD`);;

%

       A1 |- t1 = t1' , ... , An |- tn = tn'

        A |- t = (?l1 ... lm. t1 /\ ... /\ tn)
      ------------------------------------------
        A |- t = (?l1 ... lm. t1' /\ ... /\ tn')
%

let UNFOLD_RULE thl th =
 RIGHT_CONV_RULE (UNFOLD(map SPEC_ALL thl)) (SPEC_ALL th)
 ? failwith`UNFOLD_RULE`;;

%
   |- (x1 = t1) /\ ... (xm = tm) /\ ... /\ (xn = tn) =
      (x1 = t1') /\ ... /\ (x[m-1] = t[m-1]') /\ (xm = tm) /\ ... /\ (xn = tn)

where:

   1. ti' = ti[tm,...,tn/xm,...,xn]
   
   2. none of x1,...,xn are free in any of tm,...,tn 
      (the xi's need not be variables)

   3. not all of the terms in the conjunction have to be equations
      (only the equations are used in unwinding)

In fact, the equations (xi = ti) (where i is between m and n)
can occur anywhere - they don't have to be bunched up at the right
hand end.

let OLD_UNWIND_ONCE_CONV t =
 (let eqns  = conjuncts t
  in
  letrec check_frees l t = 
   (if null l         then false
    if free_in(hd l)t then true else check_frees (tl l) t)
  in
  let lefts = mapfilter lhs eqns
  in
  let l1,l2 = partition (\t. check_frees lefts (rhs t) ? true) eqns
  in
  if null l1
  then REFL(list_mk_conj l2)
  else
  (let th1 = end_itlist CONJ (map ASSUME l2)
   in
   let subs_list = map 
                    (\th. (th, genvar(type_of(lhs(concl th)))))
                    (CONJUNCTS th1)
   in
   let rn_list = map (\(th,v).(v,lhs(concl th))) subs_list
   in
   let subs_fn t =
    (mk_eq o (I # subst rn_list) o dest_eq) t ? subst rn_list t
   in
   let th2 = SUBST_CONV
              subs_list
               (list_mk_conj
                (map subs_fn l1))
               (list_mk_conj l1)
   in
   let th3 = CONJ_DISCHL l2 th2
   in
   let th4 = CONJUNCTS_CONV(t, lhs(concl th3))
   in
   (th4 TRANS th3))
 ) ? failwith `OLD_UNWIND_ONCE_CONV`;;

%

let OLD_UNWIND_ONCE_CONV t =
 (let eqns  = conjuncts t
  in
  letrec check_frees l t =   %any member of l free in t?%
   (if null l         then false
    if free_in(hd l)t then true else check_frees (tl l) t)
  in
  let lefts = mapfilter lhs eqns
  in
  let l1,l2 = partition (\t. check_frees lefts (rhs t) ? true) eqns
  in
  if null l1
  then REFL(list_mk_conj eqns)
  else
  (let subs_fun = subst(map(flip o dest_eq)l2)
   in
   let l1' = map ((mk_eq o (I # subs_fun) o dest_eq) orelsef subs_fun) l1
   in
   mk_thm([], mk_eq(t, list_mk_conj(l1'@l2))))
 ) ? failwith `OLD_UNWIND_ONCE_CONV`;;

% Unwind until no change - may loop! 

letrec UNWIND_EQS eqs =
 let th = OLD_UNWIND_ONCE_CONV eqs
 in
 if lhs(concl th)=rhs(concl th)
 then th
 else th TRANS (UNWIND_EQS(rhs(concl th)));;
%

letrec UNWIND_EQS eqs =
 (let th = OLD_UNWIND_ONCE_CONV eqs
  in
  let t1,t2 = dest_eq(concl th)
  in
  if t1 = t2
  then th
  else mk_thm([],mk_eq(t1, rhs(concl(UNWIND_EQS t2))))
 ) ? failwith`UNWIND_EQS`;;

% 
   |- (?l1 ... lm. x1 = t1 /\ ... /\ xn = tn) =
      (?l1 ... lm. x1 = t1' /\ ... /\ xn = tn')

Where t1',...,tn' are got from t1,...,tn by unwinding using the equations
%

let UNWIND t = 
 let l,eqs = strip_exists t
 in
 LIST_MK_EXISTS l (UNWIND_EQS eqs);;

let OLD_UNWIND_RULE th =
  RIGHT_CONV_RULE UNWIND th ? failwith `OLD_UNWIND_RULE`;;

%
 "(!x. t1) /\ ... /\ (!x. tn)" --->
   |- (!x. t1) /\ ... /\ (!x. tn) = !x. t1 /\ ... /\ tn 

let AND_FORALL_CONV t =
 (let xt1,xt2 = dest_conj t
  in
  let x = fst(dest_forall xt1)
  in
  let thl1 = CONJUNCTS(ASSUME t)
  in
  let th1 = DISCH_ALL(GEN x (LIST_CONJ(map(SPEC x)thl1)))
  in
  let thl2 =
   CONJUNCTS
    (SPEC x
     (ASSUME
      (mk_forall(x,(list_mk_conj(map(snd o dest_forall o concl)thl1))))))
  in
  let th2 = DISCH_ALL(LIST_CONJ(map (GEN x) thl2))
  in
  IMP_ANTISYM_RULE th1 th2
 ) ? failwith `AND_FORALL_CONV`;;
%

%  "(!x. t1) /\ ... /\ (!x. tn)" ---> ("x", ["t1"; ... ;"tn"]) %

letrec dest_andl t =
 ((let x1,t1 = dest_forall t
   in
   (x1,[t1])
  )
  ?
  (let first,rest = dest_conj t
   in
   let x1,l1 = dest_andl first
   and x2,l2 = dest_andl rest
   in
   if x1=x2 then (x1, l1@l2) else fail)
 ) ? failwith `dest_andl`;;

% Version of AND_FORALL_CONV below will pull quantifiers out and flatten an
  arbitrary tree of /\s, not just a linear list. %
   
let AND_FORALL_CONV t =
 (let x,l = dest_andl t
  in
  mk_thm([], mk_eq(t,mk_forall(x,list_mk_conj l)))
 ) ? failwith `AND_FORALL_CONV`;;

%
 "!x. t1 /\ ... /\ tn" --->
   |- !x. t1 /\ ... /\ tn =  (!x. t1) /\ ... /\ (!x. tn)

let FORALL_AND_CONV t =
 (let x,l = ((I # conjuncts) o dest_forall) t
  in
  SYM(AND_FORALL_CONV(list_mk_conj(map(curry mk_forall x)l)))
 ) ? failwith `AND_FORALL_CONV`;;
%

let FORALL_AND_CONV t =
 (let x,l = ((I # conjuncts) o dest_forall) t
  in
  mk_thm([],mk_eq(t, list_mk_conj(map(curry mk_forall x)l)))
 ) ? failwith `FORALL_AND_CONV`;;

% 
   |- (?l1 ... lm. (!x. x1 = t1)  /\ ... /\ (!x. xn = tn)) =
      (?l1 ... lm. (!x. x1 = t1') /\ ... /\ (!x. xn = tn'))

Where t1',...,tn' are got from t1,...,tn by unwinding using the equations:

   x1 = t1  /\ ... /\ xn = tn

%

let UNWINDF t = 
 (let l,body = strip_exists t
  in
  let th1 = AND_FORALL_CONV body
  in
  let x,eqs = dest_forall(rhs(concl th1))
  in
  let th2 = FORALL_EQ x (UNWIND_EQS eqs)
  in
  let th3 = FORALL_AND_CONV(rhs(concl th2))
  in
  LIST_MK_EXISTS l (th1 TRANS th2 TRANS th3)
 ) ? failwith `UNWINDF`;;

let UNWINDF_RULE th = RIGHT_CONV_RULE UNWINDF th ? failwith `UNWINDF_RULE`;;

%
    A |- t1 = t2
   --------------   (t2' got from t2 by unwinding)
    A |- t1 = t2'
%

% The next lot of rules are for pruning %

% EXISTS_AND_LEFT: term     -> thm
                  "?x.t1/\t2"  

   | - ?x. t1 /\ t2 = t1 /\ (?x. t2)"  (If x not free in t1)
%

let EXISTS_AND_LEFT t =
 (let x,t1,t2 = ((I # dest_conj) o dest_exists) t
  in
  let t1_frees, t2_frees = frees t1, frees t2
  in
  if not(mem x t2_frees & not(mem x t1_frees))
  then fail
  else
  (let th1 = ASSUME "^t1 /\ ^t2"
   and t' = "^t1 /\ (?^x.^t2)"
   in
   let th2 = ASSUME t'
   in
   let th3 = DISCH
              t
              (CHOOSE 
               (x, ASSUME t)
               (CONJ(CONJUNCT1 th1)(EXISTS("?^x.^t2",x)(CONJUNCT2 th1))))
     % th3 = |-"?x. t1  /\  t2  ==>  t1  /\  (?x. t2)" %
   and th4 = DISCH
              t'
              (CHOOSE
               (x, CONJUNCT2 th2)
               (EXISTS(t,x)(CONJ(CONJUNCT1 th2)(ASSUME t2))))
     % th4 = |-"t1  /\  (?x. t2)  ==>  ?x. t1  /\  t2" %
   in 
   IMP_ANTISYM_RULE th3 th4)
 ) ? failwith `EXISTS_AND_LEFT`;;
 
% EXISTS_AND_RIGHT: term    -> thm
                   ?x.t1/\t2 

     |- ?x. t1 /\ t2 = (?x. t1) /\ t2"  (If x not free in t2)
%

let EXISTS_AND_RIGHT t =
 (let x,t1,t2 = ((I # dest_conj) o dest_exists) t
  in
  let t1_frees, t2_frees = frees t1, frees t2
  and th1              = ASSUME "^t1 /\ ^t2"
  in
  if not(mem x t1_frees & not(mem x t2_frees))
  then fail
  else
  (let t' = "(?^x.^t1) /\ ^t2"
   in
   let th2 = ASSUME t'
   in
   let th3 = DISCH
              t
              (CHOOSE 
               (x, ASSUME t)
               (CONJ(EXISTS("?^x.^t1",x)(CONJUNCT1 th1))(CONJUNCT2 th1)))
     % th3 = |-"?x. t1  /\  t2  ==>  (?x.t1)  /\  t2" %
   and th4 = DISCH
              t'
              (CHOOSE
               (x, CONJUNCT1 th2)
               (EXISTS(t,x)(CONJ(ASSUME t1)(CONJUNCT2 th2))))
     % th4 = |-"(?x.t1)  /\  t2  ==>  ?x. t1  /\  t2" %
   in
   IMP_ANTISYM_RULE th3 th4)
 ) ? failwith `EXISTS_AND_RIGHT`;;

% EXISTS_AND_BOTH: term     -> thm
                   ?x.t1/\t2

   |- ?x. t1 /\ t2 = t1 /\ t2"        (If x not free in t1 or t2)
%

let EXISTS_AND_BOTH t =
 (let x,t1,t2 = ((I # dest_conj) o dest_exists) t
  in
  let t1_frees, t2_frees = frees t1, frees t2
  and th1              = ASSUME "^t1 /\ ^t2"
  in
  if (mem x t2_frees) or (mem x t1_frees)
  then fail
  else
  (let t' = "^t1 /\ ^t2"
   in
   let th3 = DISCH
              t
              (CHOOSE
               (x, ASSUME t)
               (ASSUME t'))
     % th3 = |-"?x. t1  /\  t2  ==>  t1  /\  t2" %
   and th4 = DISCH
              t'
              (EXISTS(t, x)(ASSUME t'))
     % th4 = |-"t1  /\ t2  ==>  ?x. t1 /\  t2" %
   in IMP_ANTISYM_RULE th3 th4)
 ) ? failwith `EXISTS_AND_BOTH`;;

% EXISTS_AND: term -> thm
              ?x.t1/\t2

    |- ?x. t1 /\ t2 = t1 /\ (?x. t2)"  (If x not free in t1)

    |- ?x. t1 /\ t2 = (?x. t1) /\ t2"  (If x not free in t2)

    |- ?x. t1 /\ t2 = t1 /\ t2"        (If x not free in t1 or t2)
%

let EXISTS_AND t =
 EXISTS_AND_LEFT  t ?
 EXISTS_AND_RIGHT t ?
 EXISTS_AND_BOTH  t ?
 failwith`EXISTS_AND`;;

%
   A |- ?x.?y.t
   ------------
   A |- ?y.?x.t"
%

let EXISTS_PERM th =
 let x,y,t = ((I # dest_exists) o dest_exists o concl) th
 in
 CHOOSE 
  (x,th)
  (CHOOSE
   (y, ASSUME "?^y.^t")
   (EXISTS("?^y^x.^t",y)(EXISTS("?^x.^t",x)(ASSUME t))));;

% |- (?x y. t) = (?y x.t) %

let EXISTS_PERM_CONV t =
 (let th1 = EXISTS_PERM(ASSUME t)
  in
  let t' = concl th1
  in
  IMP_ANTISYM_RULE (DISCH t th1) (DISCH t' (EXISTS_PERM(ASSUME t')))
 ) ? failwith`EXISTS_PERM_CONV`;;

%
 EXISTS_EQN

   "?l. l x1 ... xn = t" --> |- (?l.l x1 ... xn = t) = T

  (if l not free in t)
%

let EXISTS_EQN t =
 (let l,t1,t2 = ((I # dest_equiv) o dest_exists) t
  in
  let l',xs = strip_comb t1
  in
  let t3 = list_mk_abs(xs,t2)
  in
  let th1 = RIGHT_CONV_RULE LIST_BETA_CONV (REFL(list_mk_comb(t3,xs)))
  in
  EQT_INTRO(EXISTS("?^l.^(list_mk_comb(l,xs))=^(rhs(concl th1))",t3)th1)
 ) ? failwith `EXISTS_EQN`;;

%
 EXISTS_EQNF

   "?l. !x1 ... xn. l x1 ... xn = t" --> 
     |- (?l. !x1 ... xn. l x1 ... xn = t) = T

  (if l not free in t)
%

let EXISTS_EQNF t =
 (let l,vars,t1,t2 =
  ((I # (I # dest_eq)) o (I # strip_forall) o dest_exists) t
  in
  let l',xs = strip_comb t1
  in
  let t3 = list_mk_abs(xs,t2)
  in
  let th1 =
   GENL vars (RIGHT_CONV_RULE LIST_BETA_CONV (REFL(list_mk_comb(t3,xs))))
  in
  EQT_INTRO
   (EXISTS
    ((mk_exists
      (l,
       list_mk_forall
        (xs,
         (mk_eq(list_mk_comb(l,xs), rhs(snd(strip_forall(concl th1)))))))),
     t3)
   th1)
 ) ? failwith `EXISTS_EQNF`;;


% |- (?x.t) = t    if x not free in t 

let EXISTS_DEL1 tm =
 (let x,t = dest_exists tm
  in
  let th1 = DISCH tm (CHOOSE (x, ASSUME tm) (ASSUME t))
  and th2 = DISCH t (EXISTS(tm,x)(ASSUME t))
  in
  IMP_ANTISYM_RULE th1 th2
 ) ? failwith `EXISTS_DEL`;;
%

% |- (?x1 ... xn.t) = t    if x1,...,xn not free in t 

letrec EXISTS_DEL tm =
 (if is_exists tm
  then
  (let th1 = EXISTS_DEL1 tm
   in
   let th2 = EXISTS_DEL(rhs(concl th1))
   in
   th1 TRANS th2)
  else REFL tm
 ) ? failwith`EXISTS_DEL`;;
%

let EXISTS_DEL tm =
 (let l,t = strip_exists tm
  and l'  = frees tm
  in
  if intersect l l' = [] then mk_thm([], mk_eq(tm,t)) else fail
 ) ? failwith`EXISTS_DEL`;;

%
 The pruning rule below will need to be made more complicated.

   |- (?l1 ... lm. t1 /\ ... /\ tn) = (u1 /\ ... /\ up)

 where each ti is an equation "xi = ti'" and the uis are those tis
 for which xi is not one of l1, ... ,lm. The rule below assumes that
 for each li there is exactly one ti with xi=li. This will have to be
 relaxed later.
%

% PRUNE1 prunes one hidden variable %

let PRUNE1 x eqs =
 (let l1,l2 = partition(free_in x)(conjuncts eqs)
  in
  let th1 = LIST_MK_EXISTS [x] (CONJ_SET_CONV (conjuncts eqs) (l1@l2))
  in
  let th2 = th1 TRANS EXISTS_AND_RIGHT(rhs(concl th1))
  in
  let t1,t2 = dest_conj(rhs(concl th2))
  in
  let th3 = th2 TRANS (AP_THM(AP_TERM "$/\" (EXISTS_EQN t1))t2)
  and th4 = SPEC t2 AND_CLAUSE1
  in
  th3 TRANS th4
 ) ? failwith`PRUNE1`;;
 
%

   |- (?l1 ... lm. t1 /\ ... /\ tn) = (u1 /\ ... /\ up)

 where each ti has the form "!x. xi x = ti'" and the uis are those tis
 for which xi is not one of l1, ... ,lm. The rule below assumes that
 for each li there is exactly one ti with xi=li. This will have to be
 relaxed later.
%

% PRUNE1F prunes one hidden variable %

let PRUNE1F x eqs =
 (let l1,l2 = partition(free_in x)(conjuncts eqs)
  in
  let th1 = LIST_MK_EXISTS [x] (CONJ_SET_CONV (conjuncts eqs) (l1@l2))
  in
  let th2 = th1 TRANS EXISTS_AND_RIGHT(rhs(concl th1))
  in
  let t1,t2 = dest_conj(rhs(concl th2))
  in
  let th3 = th2 TRANS (AP_THM(AP_TERM "$/\" (EXISTS_EQNF t1))t2)
  and th4 = SPEC t2 AND_CLAUSE1
  in
  th3 TRANS th4
 ) ? failwith`PRUNE1F`;;
 
letrec PRUNEL vars eqs =
 (if null vars
  then REFL eqs
  if null(tl vars)
  then PRUNE1 (hd vars) eqs
  else 
  (let th1 = PRUNEL (tl vars) eqs
   in
   let th2 = PRUNE1 (hd vars) (rhs(concl th1))
   in
   (LIST_MK_EXISTS [hd vars] th1) TRANS th2)
 ) ? failwith`PRUNEL`;;

let PRUNE t =
 (let vars,eqs = strip_exists t in PRUNEL vars eqs) ? failwith`PRUNE`;;

let PRUNE_RULE th = RIGHT_CONV_RULE PRUNE th ? failwith `PRUNE_RULE`;;
 
letrec PRUNELF vars eqs =
 (if null vars
  then REFL eqs
  if null(tl vars)
  then PRUNE1F (hd vars) eqs
  else 
  (let th1 = PRUNELF (tl vars) eqs
   in
   let th2 = PRUNE1F (hd vars) (rhs(concl th1))
   in
   (LIST_MK_EXISTS [hd vars] th1) TRANS th2)
 ) ? failwith`PRUNELF`;;

let PRUNEF t =
 (let vars,eqs = strip_exists t in PRUNELF vars eqs) ? failwith`PRUNEF`;;

let PRUNEF_RULE th = RIGHT_CONV_RULE PRUNEF th ? failwith `PRUNEF_RULE`;;

% EXPAND below is like EXPAND_IMP of LCF_LSM; it unfolds, unwinds and prunes %

let EXPAND thl th =
 let th1 = UNFOLD_RULE thl th
 in
 let th2 = OLD_UNWIND_RULE th1
 in
 PRUNE_RULE th2;;

let EXPANDF thl th =
 let th1 = UNFOLD_RULE thl th
 in
 let th2 = UNWINDF_RULE th1
 in
 PRUNEF_RULE th2;;

% The stuff below superceeds some of the stuff above. Some cleaning	%
% up is needed ...							%

% New HOL Inference rules for unwinding device implementations.		%
% 									%
% DATE    85.05.21							%
% AUTHOR  T. Melham							%

% AUXILIARY FUNCTION DEFINITIONS -------------------------------------- %


% line_var "!v1 ... vn. f v1 ... vn = t"  ====> "f"	    		%

let line_var tm = fst(strip_comb(lhs(snd(strip_forall tm))));;

% var_name "var" ====> `var`						%

let var_name = fst o dest_var;;

% line_name "!v1 ... vn. f v1 ... vn = t"  ====> `f`	    		%

let line_name = var_name o line_var;;

% UNWIND CONVERSIONS -------------------------------------------------- %

% UNWIND_ONCE_CONV - Basic conversion for parallel unwinding of lines.	%
% 									%
% DESCRIPTION: tm should be a conjunction, t1 /\ t2 ... /\ tn.		%
%	       p:term->bool is a function which is used to partition the%
%	       terms (ti) into two sets.  Those ti which p is true of	%
%	       are then used as a set of rewrite rules (thus they must  %
%	       be equations) to do a top-down one-step parallel rewrite %
%	       of the conjunction of the remaining terms.  I.e.		%
%									%
%	       t1 /\ ... /\ eqn1 /\ ... /\ eqni /\ ... /\ tn		%
%	       ---------------------------------------------		%
%	       |-  t1 /\ ... /\ eqn1 /\ ... /\ eqni /\ ... /\ tn	%
%		    =							%
%		   eqn1 /\ ... /\ eqni /\ ... /\ t1' /\ ... /\ tn'	%
%									%
%		   where tj' is tj rewritten with the equations eqnx	%

let UNWIND_ONCE_CONV p tm =
    let eqns = conjuncts tm in
    let eq1,eq2 = partition (\tm. ((p tm) ? false)) eqns in
    if (null eq1) or (null eq2) 
       then REFL tm
       else let thm = CONJ_DISCHL eq1
		       (ONCE_DEPTH_CONV
                       (REWRITES_CONV (mk_conv_net (map ASSUME eq1)))
	               (list_mk_conj eq2)) in
            let re = CONJUNCTS_CONV(tm,(lhs(concl thm))) in
            re TRANS thm;;

% Unwind until no change using equations selected by p.			%
% WARNING -- MAY LOOP!							%

letrec UNWIND_CONV p tm =
       let th = UNWIND_ONCE_CONV p tm in
       if lhs(concl th)=rhs(concl th)
          then th
          else th TRANS (UNWIND_CONV p (rhs(concl th)));;

% UNWIND CONVERSIONS -------------------------------------------------- %

% One-step unwinding of device behaviour with hidden lines using line   %
% equations selected by p.						%
let UNWIND_ONCE_RULE p th = 
    let rhs_conv = \rhs. (let lines,eqs = strip_exists rhs in
                          LIST_MK_EXISTS lines (UNWIND_ONCE_CONV p eqs)) in
    RIGHT_CONV_RULE rhs_conv th ?  failwith `UNWIND_ONCE_RULE`;;

% Unwind device behaviour using line equations selected by p until no 	%
% change.  WARNING --- MAY LOOP!					%
let UNWIND_RULE p th = 
    let rhs_conv = \rhs. (let lines,eqs = strip_exists rhs in
                          LIST_MK_EXISTS lines (UNWIND_CONV p eqs)) in
    RIGHT_CONV_RULE rhs_conv th ?  failwith `UNWIND_RULE`;;

% Unwind all lines (except those in the list l) as much as possible.	%
let UNWIND_ALL_RULE l th = 
    let rhs_conv = 
	   \rh. (let lines,eqs = strip_exists rh in
		 let eqns = filter (can line_name) (conjuncts eqs) in
		 let line_names = subtract (map line_name eqns) l in
	     let p = \line. \tm. (line_name tm) = line in
             let itfn = \line. \th. th TRANS 
				    UNWIND_CONV (p line) (rhs(concl th)) in
	     LIST_MK_EXISTS lines (itlist itfn line_names (REFL eqs))) in
    RIGHT_CONV_RULE rhs_conv th ?  failwith `UNWIND_ALL_RULE`;; 


let NEW_EXPANDF l thl th =
 let th1 = UNFOLD_RULE thl th
 in
 let th2 = UNWIND_ALL_RULE l th1
 in
 PRUNEF_RULE th2;;

%  TEST CASES ----------------
let imp =     ASSUME
              "IMP(f,g,h) = ?l3 l2 l1. 
              (!x:num. f x = (l1 (x+1)) + (l2 (x+2)) + (l3 (x+3))) /\
	      (!x. g x = (l3 (l3 (l3 x)))) /\
	      (!x. l2 x = (l3 x) - 1) /\
	      (!x. h x = l3 x) /\
	      (!x. l1 x = (l2 x) + 1) /\
	      (!x. l3 x = 7) /\
	      notanequation:bool";;

let tm =     "(!x:num. f x = (l1 (x+1)) + (l2 (x+2)) + (l3 (x+3))) /\
	      (!x. l1 x = (l2 x) + 1) /\
	      (!x. g x = (l3 (l3 (l3 x)))) /\
	      (!x. l2 x = (l3 x) - 1) /\
	      (!x. h x = l3 x) /\
	      (!x. l3 x = 7) /\
	      notanequation:bool";;

UNWIND_ONCE_CONV (\tm. mem (line_name tm) [`l1`;`l2`;`l3`]) tm;;

UNWIND_CONV (\tm. mem (line_name tm) [`l1`;`l2`;`l3`]) tm;;

UNWIND_ONCE_RULE (\tm. mem (line_name tm) [`l1`;`l2`;`l3`]) imp;;

UNWIND_RULE (\tm. mem (line_name tm) [`l1`;`l2`;`l3`]) imp;;

UNWIND_ALL_RULE [] imp;;

UNWIND_ALL_RULE [`l3`] imp;;

%
