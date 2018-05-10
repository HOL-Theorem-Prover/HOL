% Rutherford Only %

%
new_parent `exp`;;
let EXP = theorem `exp` `EXP`;;

let BETA_TAC = CONV_TAC (DEPTH_CONV BETA_CONV);;
let BETA_RULE = CONV_RULE (DEPTH_CONV BETA_CONV);;

let EXISTS_IMP_FORALL_CONV term =
    (let (ante,conse) = dest_imp term in
     let (x,t1) = dest_exists ante in
     let t1_thm = ASSUME t1 in
     let forall_thm =  (ASSUME(mk_forall(x,mk_imp(t1,conse)))) in
     let imp1 = DISCH_ALL (GEN x (DISCH t1 (MP (ASSUME term)
					       (EXISTS (ante,x) t1_thm)))) in
     let imp2 = DISCH_ALL (DISCH ante (CHOOSE(x,(ASSUME ante)) 
					     (UNDISCH(SPEC x forall_thm)))) in
     IMP_ANTISYM_RULE imp1 imp2)?failwith `EXISTS_IMP_FORALL_CONV`;;
%

% Vax and Rutherford %

let num_CONV_TAC = CONV_TAC (REDEPTH_CONV num_CONV);;
let num_CONV_RULE = CONV_RULE (REDEPTH_CONV num_CONV);;
let SUC_FORM_TAC = num_CONV_TAC THEN PURE_REWRITE_TAC [ADD_CLAUSES];;
let SUC_FORM_RULE = (PURE_REWRITE_RULE [ADD_CLAUSES]) o num_CONV_RULE;;

let IMP_TAC ante ((asl,t):goal) =
	 ([(asl,mk_imp (ante,t));(asl,ante)],
	  \[imp_thm;ante_thm].MP imp_thm ante_thm) ? failwith `IMP_TAC`;;

let IMP_TAC imp_thm ((asl,t):goal) =
	(let t1,t2 = dest_imp (concl imp_thm)
	 in
	 if not (t = t2) then failwith `IMP_TAC`
	 else
	 ([asl,t1],\[th].MP imp_thm th)) ? failwith `IMP_TAC`;;
