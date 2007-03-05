(*
  app load ["bossLib", "numLib", "pairTheory", "schneiderUtils",
            "Past_Temporal_LogicTheory"];
*)
open HolKernel Parse boolLib Rsyntax schneiderUtils
     numLib numTheory prim_recTheory arithmeticTheory pairTheory
     Temporal_LogicTheory Past_Temporal_LogicTheory;

infixr 3 -->;
infix ## |-> THEN THENL THENC ORELSE ORELSEC THEN_TCL ORELSE_TCL;

val _ = Rewrite.add_implicit_rewrites pairTheory.pair_rws;

val ZERO_LEMMA = ARITH_PROVE(--`~(x<x) /\ (0<SUC x) /\ ~(SUC x=0)`--);



val _ = new_theory "Omega_Automata";




(* ********************************************************************	*)
(* Some facts about the boolean closure of omega-automata		*)
(* ********************************************************************	*)



val DET_OMEGA_EXISTS_FORALL_THEOREM = TAC_PROOF(
	([],--`(?q:num->'state.
			(q t0 = InitVal) /\
		     	(!t. q(t+(t0+1)) = TransRel((i(t+t0):'input),q(t+t0))) /\
		     	Accept(i,(\t.q(t+t0))))
	       =
	       (!q:num->'state.
			(q t0 = InitVal) /\
		     	(!t. q(t+(t0+1)) = TransRel((i(t+t0):'input),q(t+t0)))
			==>  	Accept(i,(\t.q(t+t0))))
		`--),
	EQ_TAC THEN REPEAT STRIP_TAC
	THENL[
	    MY_MP_TAC (--`(\t.q'(t+t0))=((\t.q(t+t0)):num->'state)`--)
	    THENL[
		CONV_TAC FUN_EQ_CONV THEN BETA_TAC
		THEN INDUCT_TAC
		THEN ASM_REWRITE_TAC[ADD_CLAUSES,ADD1,SYM(SPEC_ALL ADD_ASSOC)],
		DISCH_TAC]
	    THEN ASM_REWRITE_TAC[],
	    (* ------------------------------------------------------------------------	*)
	    ASSUME_TAC(EXISTENCE(REWRITE_RULE[ADD1](BETA_RULE
		(ISPECL[(--`InitVal:'state`--),
			(--`\x:'state.\t:num.TransRel((i(t+t0)):'input,x):'state`--)]
			num_Axiom_old))))
	    THEN LEFT_EXISTS_TAC THEN EXISTS_TAC (--`\t:num.fn1(t-t0):'state`--)
	    THEN LEFT_NO_FORALL_TAC 1 (--`\t:num.fn1(t-t0):'state`--)
	    THEN UNDISCH_HD_TAC THEN BETA_TAC
	    THEN ASM_REWRITE_TAC[
	    		EQT_ELIM(ARITH_CONV(--`n-n=0`--)),
	    		EQT_ELIM(ARITH_CONV(--`(t+t0)-t0=t`--)),
	    		EQT_ELIM(ARITH_CONV(--`(t+(t0+1))-t0=t+1`--))]
	]);



val NEG_DET_AUTOMATA = TAC_PROOF(
	([],--`
	    ~(?q.
          	(q(t0) = (InitVal:'state)) /\
                (!t. q(t+(t0+1)) = TransRel((i(t+t0):'input),(q(t+t0):'state))) /\
                Accept(i,\t. q(t+t0))
	     )
	  = ?q.
          	(q(t0) = InitVal) /\
                (!t. q(t+(t0+1)) = TransRel((i(t+t0):'input),(q(t+t0):'state))) /\
                ~Accept(i,\t. q(t+t0))
	`--),
	SUBST1_TAC DET_OMEGA_EXISTS_FORALL_THEOREM
	THEN CONV_TAC(DEPTH_CONV NOT_FORALL_CONV)
	THEN REWRITE_TAC[TAC_PROOF(([],--`(a==>b) = (~a\/b)`--),PROP_TAC)]
	THEN REWRITE_TAC[DE_MORGAN_THM]
	THEN REWRITE_TAC[TAC_PROOF(([],--`((a/\b)/\c) = (a/\b/\c)`--),PROP_TAC)]
	);







val OMEGA_CONJ_CLOSURE = TAC_PROOF(
    let val cb1 = (--`?q1.
          	    	Phi_I1(q1 t0) /\
                    	(!t. Phi_R1((i(t+t0):'a),(q1(t+t0):'b1))) /\
                    	Psi1(i,q1)`--)
        val cb2 = (--`?q2.
          	    	Phi_I2(q2 t0) /\
                    	(!t. Phi_R2((i(t+t0):'a),(q2(t+t0):'b2))) /\
                    	Psi2(i,q2)`--)
     in
	([],--`(^cb1 /\ ^cb2)
	  = ? q1 q2.
		(Phi_I1(q1 t0) /\ Phi_I2(q2 t0)) /\
		(!t. Phi_R1((i(t+t0):'a),(q1(t+t0):'b1)) /\
		     Phi_R2((i(t+t0):'a),(q2(t+t0):'b2))
		) /\
        	(Psi1(i,q1) /\ Psi2(i,q2))
	`--)
    end,
	EQ_TAC THEN REPEAT STRIP_TAC
	THENL[
	    EXISTS_TAC(--`q1:num->'b1`--) THEN EXISTS_TAC(--`q2:num->'b2`--),
	    EXISTS_TAC(--`q1:num->'b1`--),
	    EXISTS_TAC(--`q2:num->'b2`--)
	    ]
	THEN ASM_REWRITE_TAC[])






val OMEGA_DISJ_CLOSURE = TAC_PROOF(
    let val cb1 = (--`?q1.
          	    	Phi_I1(q1 t0) /\
                    	(!t. Phi_R1((i(t+t0):'a),(q1(t+t0):'b1))) /\
                    	Psi1(i,q1)`--)
        val cb2 = (--`?q2.
          	    	Phi_I2(q2 t0) /\
                    	(!t. Phi_R2((i(t+t0):'a),(q2(t+t0):'b2))) /\
                    	Psi2(i,q2)`--)
     in
	([],--`(^cb1 \/ ^cb2)
	  = ?p q1 q2.
		(~p(t0) /\ Phi_I1(q1 t0) \/
	          p(t0) /\ Phi_I2(q2 t0)
                ) /\
		(!t. ~p(t+t0) /\ Phi_R1((i(t+t0):'a),(q1(t+t0):'b1)) /\ ~p(t+(t0+1))  \/
		      p(t+t0) /\ Phi_R2((i(t+t0):'a),(q2(t+t0):'b2)) /\  p(t+(t0+1))
		) /\
        	(~p t0 /\ Psi1(i,q1) \/ p t0 /\ Psi2(i,q2))
	`--)
    end,
    EQ_TAC THEN REPEAT STRIP_TAC
    THENL[
	EXISTS_TAC (--`\t:num.F`--)
	THEN EXISTS_TAC (--`q1:num->'b1`--) THEN EXISTS_TAC (--`q2:num->'b2`--)
	THEN ASM_REWRITE_TAC[],
	EXISTS_TAC (--`\t:num.T`--)
	THEN EXISTS_TAC (--`q1:num->'b1`--) THEN EXISTS_TAC (--`q2:num->'b2`--)
	THEN ASM_REWRITE_TAC[],
	MY_MP_TAC (--`!t. ~p(t+t0)`--)
	THENL[
	    INDUCT_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES]
	    THEN LEFT_NO_FORALL_TAC 2 (--`t:num`--)
	    THEN UNDISCH_HD_TAC
	    THEN ASM_REWRITE_TAC[ADD_CLAUSES,SYM(SPEC_ALL ADD1)]
	    THEN STRIP_TAC,
	    DISCH_TAC
	    ]
	THEN DISJ1_TAC THEN EXISTS_TAC(--`q1:num->'b1`--)
	THEN POP_ASSUM (fn x => RULE_ASSUM_TAC(REWRITE_RULE[x]) THEN ASSUME_TAC x)
	THEN ASM_REWRITE_TAC[],
	MY_MP_TAC (--`!t. p(t+t0)`--)
	THENL[
	    INDUCT_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES]
	    THEN LEFT_NO_FORALL_TAC 2 (--`t:num`--)
	    THEN UNDISCH_HD_TAC
	    THEN ASM_REWRITE_TAC[ADD_CLAUSES,SYM(SPEC_ALL ADD1)]
	    THEN STRIP_TAC,
	    DISCH_TAC
	    ]
	THEN DISJ2_TAC THEN EXISTS_TAC(--`q2:num->'b2`--)
	THEN POP_ASSUM (fn x => RULE_ASSUM_TAC(REWRITE_RULE[x]) THEN ASSUME_TAC x)
	THEN ASM_REWRITE_TAC[]
	])





(* ********************************************************************	*)
(* some facts about the boolean closure of NDET_G-automata		*)
(* ********************************************************************	*)

val NEG_G = TAC_PROOF(
	([],--`~(!t:num.a(t+t0)) = (?t. ~a(t+t0))`--),
	CONV_TAC (DEPTH_CONV NOT_FORALL_CONV)
	THEN REWRITE_TAC[])


val CONJ_G = TAC_PROOF(
	([],--`(!t:num.a(t+t0)) /\ (!t. b(t+t0)) = (!t. a(t+t0) /\ b(t+t0))`--),
	EQ_TAC THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[])




val DISJ_G = TAC_PROOF(
	([],--`(!t. a(t+t0)) \/ (!t. b(t+t0)) =
	       (?p q.
		   (~p t0 /\ ~q t0) /\
		   (!t. (p(t+(t0+1)) = p(t+t0) \/ ~a(t+t0)) /\
		        (q(t+(t0+1)) = q(t+t0) \/ ~b(t+t0))
		   ) /\
		   (!t.~p(t+t0) \/ ~q(t+t0))) `--),
	REWRITE_TAC[ONE,ADD_CLAUSES]
	THEN EQ_TAC THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[]
	THENL[
	    ASSUME_TAC(EXISTENCE(BETA_RULE
			(ISPECL[(--`F`--),(--`\x:bool.\t:num. x`--)]num_Axiom_old)))
	    THEN ASSUME_TAC(EXISTENCE(BETA_RULE
			(ISPECL[(--`F`--),(--`\x:bool.\t:num. x\/~b(t+t0)`--)]num_Axiom_old)))
	    THEN LEFT_EXISTS_TAC THEN LEFT_NO_EXISTS_TAC 1
	    THEN EXISTS_TAC (--`\t.fn1'(t-t0):bool`--)
	    THEN EXISTS_TAC (--`\t.fn1(t-t0):bool`--)
	    THEN BETA_TAC
	    THEN ASM_REWRITE_TAC[
		EQT_ELIM(ARITH_CONV(--`t0-t0=0`--)),
		EQT_ELIM(ARITH_CONV(--`(t+t0)-t0 = t`--)),
		EQT_ELIM(ARITH_CONV(--`SUC(t+t0)-t0 = SUC t`--))]
	    THEN MY_MP_TAC (--`!t:num.~fn1' t`--)
	    THENL[INDUCT_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES],DISCH_TAC]
	    THEN ASM_REWRITE_TAC[],
	    ASSUME_TAC(EXISTENCE(BETA_RULE
			(ISPECL[(--`F`--),(--`\x:bool.\t:num. x\/~a(t+t0)`--)]num_Axiom_old)))
	    THEN ASSUME_TAC(EXISTENCE(BETA_RULE
			(ISPECL[(--`F`--),(--`\x:bool.\t:num. x`--)]num_Axiom_old)))
	    THEN LEFT_EXISTS_TAC THEN LEFT_NO_EXISTS_TAC 1
	    THEN EXISTS_TAC (--`\t.fn1'(t-t0):bool`--)
	    THEN EXISTS_TAC (--`\t.fn1(t-t0):bool`--)
	    THEN BETA_TAC
	    THEN ASM_REWRITE_TAC[
		EQT_ELIM(ARITH_CONV(--`t0-t0=0`--)),
		EQT_ELIM(ARITH_CONV(--`(t+t0)-t0 = t`--)),
		EQT_ELIM(ARITH_CONV(--`SUC(t+t0)-t0 = SUC t`--))]
	    THEN MY_MP_TAC (--`!t:num.~fn1 t`--)
	    THENL[INDUCT_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES],DISCH_TAC]
	    THEN ASM_REWRITE_TAC[],
	    ALL_TAC]
	(* ----------------------------------------------------------------------------	*)
	(* Here comes the real problem that is to be proved:				*)
	(* 										*)
	(*   (--`(!t. a (t + t0)) \/ (!t. b (t + t0))`--)				*)
	(*  ____________________________						*)
	(*      (--`~(p t0)`--)								*)
	(*      (--`~(q t0)`--)								*)
	(*      (--`!t.									*)
	(*            (p (SUC (t + t0)) = p (t + t0) \/ ~(a (t + t0))) /\		*)
	(*            (q (SUC (t + t0)) = q (t + t0) \/ ~(b (t + t0)))`--)		*)
	(*      (--`!t. ~(p (t + t0)) \/ ~(q (t + t0))`--)				*)
	(* ----------------------------------------------------------------------------	*)
	THEN DISJ_CASES_TAC(SPEC(--`p:num->bool`--)(GEN(--`b:num->bool`--)DELTA_CASES))
	THEN DISJ_CASES_TAC(SPEC(--`q:num->bool`--)(GEN(--`b:num->bool`--)DELTA_CASES))
	THEN UNDISCH_NO_TAC 3
	THEN ASM_REWRITE_TAC[EQT_ELIM(ARITH_CONV(--`SUC(t+t0) = (SUC t)+t0`--))]
	THEN DISCH_TAC THEN ASM_REWRITE_TAC[]
	THEN LEFT_NO_EXISTS_TAC 1 THEN LEFT_NO_EXISTS_TAC 2
	THEN MY_MP_TAC (--`!x. q(x+(d+t0))`--)
	THENL[
	    INDUCT_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES]
	    THEN ASM_REWRITE_TAC[EQT_ELIM(ARITH_CONV(--`SUC(x+(d+t0))=(SUC(x+d))+t0`--))]
	    THEN ASM_REWRITE_TAC[SYM(SPEC_ALL ADD_ASSOC)],
	    DISCH_TAC]
	THEN MY_MP_TAC (--`!x. p(x+(d'+t0))`--)
	THENL[
	    INDUCT_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES]
	    THEN ASM_REWRITE_TAC[EQT_ELIM(ARITH_CONV(--`SUC(x+(d'+t0))=(SUC(x+d'))+t0`--))]
	    THEN ASM_REWRITE_TAC[SYM(SPEC_ALL ADD_ASSOC)],
	    DISCH_TAC]
	THEN LEFT_NO_FORALL_TAC 5 (--`d+d'`--)
	THEN UNDISCH_HD_TAC THEN ASM_REWRITE_TAC[SYM(SPEC_ALL ADD_ASSOC)]
	THEN SUBST1_TAC(EQT_ELIM(ARITH_CONV(--`(d+(d'+t0))=(d'+(d+t0))`--)))
	THEN ASM_REWRITE_TAC[]
	);



val BOOLEAN_CLOSURE_G = TAC_PROOF(
	([],--`
	( ~(!t:num.a(t+t0)) = (?t. ~a(t+t0)) ) /\
	(  (!t:num.a(t+t0)) /\ (!t. b(t+t0)) = (!t. a(t+t0) /\ b(t+t0)) ) /\
	(  (!t. a(t+t0)) \/ (!t. b(t+t0)) =
	       (?p q.
		   (~p t0 /\ ~q t0) /\
		   (!t. (p(t+(t0+1)) = p(t+t0) \/ ~a(t+t0)) /\
		        (q(t+(t0+1)) = q(t+t0) \/ ~b(t+t0))
		   ) /\
		   (!t.~p(t+t0) \/ ~q(t+t0)))
	)
	`--),
	REWRITE_TAC[NEG_G,CONJ_G,DISJ_G]);




(* ********************************************************************	*)
(* some facts about the boolean closure of NDET_F-automata		*)
(* ********************************************************************	*)

val NEG_F = TAC_PROOF(
	([],--`~(?t:num.a(t+t0)) = (!t. ~a(t+t0))`--),
	CONV_TAC (DEPTH_CONV NOT_EXISTS_CONV)
	THEN REWRITE_TAC[])


val CONJ_F = TAC_PROOF(
	([],--`(?t. a(t+t0)) /\ (?t. b(t+t0)) =
	       (?p q.
		   (~p t0 /\ ~q t0) /\
		   (!t. (p(t+(t0+1)) = p(t+t0) \/ a(t+t0)) /\
		        (q(t+(t0+1)) = q(t+t0) \/ b(t+t0))
		   ) /\
		   (?t. p(t+t0) /\ q(t+t0))) `--),
	REWRITE_TAC[ONE,ADD_CLAUSES]
	THEN EQ_TAC THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[]
	THENL[
	(* ----------------------------------------------------------------------------	*)
	    ASSUME_TAC(EXISTENCE(BETA_RULE
			(ISPECL[(--`F`--),(--`\x:bool.\t:num. x\/a(t+t0)`--)]num_Axiom_old)))
	    THEN ASSUME_TAC(EXISTENCE(BETA_RULE
			(ISPECL[(--`F`--),(--`\x:bool.\t:num. x\/b(t+t0)`--)]num_Axiom_old)))
	    THEN LEFT_EXISTS_TAC THEN LEFT_NO_EXISTS_TAC 1
	    THEN EXISTS_TAC (--`\t.fn1'(t-t0):bool`--)
	    THEN EXISTS_TAC (--`\t.fn1(t-t0):bool`--)
	    THEN BETA_TAC
	    THEN ASM_REWRITE_TAC[
		EQT_ELIM(ARITH_CONV(--`t0-t0=0`--)),
		EQT_ELIM(ARITH_CONV(--`(t+t0)-t0 = t`--)),
		EQT_ELIM(ARITH_CONV(--`SUC(t+t0)-t0 = SUC t`--))]
	    THEN MY_MP_TAC (--`!x:num.fn1'(SUC(x+t))`--)
	    THENL[
		INDUCT_TAC
		THENL[
		    ASM_REWRITE_TAC[ADD_CLAUSES],
		    ONCE_ASM_REWRITE_TAC[] THEN REWRITE_TAC[ADD_CLAUSES]
		    THEN POP_ASSUM REWRITE1_TAC],
		DISCH_TAC]
	    THEN MY_MP_TAC (--`!x:num.fn1(SUC(x+t'))`--)
	    THENL[
		INDUCT_TAC
		THENL[
		    ASM_REWRITE_TAC[ADD_CLAUSES],
		    ONCE_ASM_REWRITE_TAC[] THEN REWRITE_TAC[ADD_CLAUSES]
		    THEN POP_ASSUM REWRITE1_TAC],
		DISCH_TAC]
	    THEN EXISTS_TAC (--`SUC(t+t')`--)
	    THEN REWRITE_TAC[ADD_CLAUSES]
	    THEN POP_ASSUM REWRITE1_TAC
	    THEN ONCE_REWRITE_TAC[ADD_SYM]
	    THEN POP_ASSUM REWRITE1_TAC,
	(* ----------------------------------------------------------------------------	*)
	    DISJ_CASES_TAC(SPEC(--`p:num->bool`--)(GEN(--`b:num->bool`--)DELTA_CASES))
	    THENL[ALL_TAC,UNDISCH_NO_TAC 2 THEN ASM_REWRITE_TAC[]]
	    THEN LEFT_EXISTS_TAC
	    THEN MY_MP_TAC (--`0<d`--)
	    THENL[
		DISJ_CASES_TAC(EQT_ELIM(ARITH_CONV(--`(d=0)\/(0<d)`--)))
		THEN ASM_REWRITE_TAC[] THEN UNDISCH_NO_TAC 1
		THEN ASM_REWRITE_TAC[ADD_CLAUSES],
		DISCH_TAC]
	    THEN IMP_RES_TAC LESS_ADD_1
	    THEN LEFT_NO_FORALL_TAC 5 (--`p':num`--) THEN UNDISCH_HD_TAC
	    THEN UNDISCH_NO_TAC 2 THEN STRIP_TAC
	    THEN LEFT_NO_FORALL_TAC 1 (--`p':num`--) THEN UNDISCH_HD_TAC
	    THEN UNDISCH_HD_TAC
	    THEN ASM_REWRITE_TAC[ADD_CLAUSES,SYM(SPEC_ALL ADD1)]
	    THEN DISCH_TAC THEN ASM_REWRITE_TAC[]
	    THEN REWRITE_TAC[EQT_ELIM(ARITH_CONV(--`x<SUC x`--))]
	    THEN DISCH_TAC THEN ASM_REWRITE_TAC[]
	    THEN STRIP_TAC THEN EXISTS_TAC (--`p':num`--) THEN ASM_REWRITE_TAC[],
	(* ----------------------------------------------------------------------------	*)
	    DISJ_CASES_TAC(SPEC(--`q:num->bool`--)(GEN(--`b:num->bool`--)DELTA_CASES))
	    THENL[ALL_TAC,UNDISCH_NO_TAC 1 THEN ASM_REWRITE_TAC[]]
	    THEN LEFT_EXISTS_TAC
	    THEN MY_MP_TAC (--`0<d`--)
	    THENL[
		DISJ_CASES_TAC(EQT_ELIM(ARITH_CONV(--`(d=0)\/(0<d)`--)))
		THEN ASM_REWRITE_TAC[] THEN UNDISCH_NO_TAC 1
		THEN ASM_REWRITE_TAC[ADD_CLAUSES],
		DISCH_TAC]
	    THEN IMP_RES_TAC LESS_ADD_1
	    THEN LEFT_NO_FORALL_TAC 5 (--`p':num`--) THEN UNDISCH_HD_TAC
	    THEN UNDISCH_NO_TAC 2 THEN STRIP_TAC
	    THEN LEFT_NO_FORALL_TAC 1 (--`p':num`--) THEN UNDISCH_HD_TAC
	    THEN UNDISCH_HD_TAC
	    THEN ASM_REWRITE_TAC[ADD_CLAUSES,SYM(SPEC_ALL ADD1)]
	    THEN DISCH_TAC THEN ASM_REWRITE_TAC[]
	    THEN REWRITE_TAC[EQT_ELIM(ARITH_CONV(--`x<SUC x`--))]
	    THEN DISCH_TAC THEN ASM_REWRITE_TAC[]
	    THEN STRIP_TAC THEN EXISTS_TAC (--`p':num`--) THEN ASM_REWRITE_TAC[]
	]
	)




val DISJ_F = TAC_PROOF(
	([],--`(?t:num.a(t+t0)) \/ (?t. b(t+t0)) = (?t. a(t+t0) \/ b(t+t0))`--),
	EQ_TAC THEN REPEAT STRIP_TAC
	THENL[
	    EXISTS_TAC(--`t:num`--),
	    EXISTS_TAC(--`t:num`--),
	    DISJ1_TAC THEN EXISTS_TAC(--`t:num`--),
	    DISJ2_TAC THEN EXISTS_TAC(--`t:num`--)]
	THEN ASM_REWRITE_TAC[])



val BOOLEAN_CLOSURE_F = TAC_PROOF(
	([],--`
	( ~(?t:num.a(t+t0)) = (!t. ~a(t+t0)) ) /\
	(  (?t:num.a(t+t0)) \/ (?t. b(t+t0)) = (?t. a(t+t0) \/ b(t+t0)) ) /\
	(  (?t. a(t+t0)) /\ (?t. b(t+t0)) =
	       (?p q.
		   (~p t0 /\ ~q t0) /\
		   (!t. (p(t+(t0+1)) = p(t+t0) \/ a(t+t0)) /\
		        (q(t+(t0+1)) = q(t+t0) \/ b(t+t0))
		   ) /\
		   (?t. p(t+t0) /\ q(t+t0)))
	)
	`--),
	REWRITE_TAC[NEG_F,CONJ_F,DISJ_F]);




(* ********************************************************************	*)
(* some facts about the boolean closure of NDET_GF-automata		*)
(* ********************************************************************	*)

val NEG_GF = TAC_PROOF(
	([],--`~(!t1.?t2. a(t1+(t2+t0))) = (?t1.!t2. ~a(t1+(t2+t0)))`--),
	CONV_TAC (DEPTH_CONV NOT_FORALL_CONV)
	THEN CONV_TAC (DEPTH_CONV NOT_EXISTS_CONV)
	THEN REWRITE_TAC[]);


val NEG_FG = TAC_PROOF(
	([],--`~(?t1.!t2. a(t1+(t2+t0))) = (!t1.?t2. ~a(t1+(t2+t0)))`--),
	CONV_TAC (DEPTH_CONV NOT_EXISTS_CONV)
	THEN CONV_TAC (DEPTH_CONV NOT_FORALL_CONV)
	THEN REWRITE_TAC[]);


val CONJ_GF = TAC_PROOF(
	([],--`!a b.
		    (!t1.?t2. a(t1+(t2+t0))) /\ (!t1.?t2. b(t1+(t2+t0)))
		=
		    (?q. ~q t0 /\
			 (!t. q(t+(t0+1)) = (if q(t+t0) then ~b(t+t0) else a(t+t0))) /\
			 !t1.?t2. q(t1+(t2+t0)) /\ b(t1+(t2+t0)))`--),
	REPEAT GEN_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC
	THENL[
	(* ----------------------------------------------------------------------------	*)
	    ASSUME_TAC(EXISTENCE(BETA_RULE
		(ISPECL[(--`F`--),(--`\x (t:num). if x then ~b(t+t0) else a(t+t0)`--)]num_Axiom_old)))
	    THEN LEFT_EXISTS_TAC THEN EXISTS_TAC (--`\t.fn1(t-t0):bool`--)
	    THEN BETA_TAC
	    THEN ASM_REWRITE_TAC[
	    		EQT_ELIM(ARITH_CONV(--`n-n=0`--)),
	    		EQT_ELIM(ARITH_CONV(--`(t+t0)-t0=t`--)),
	    		EQT_ELIM(ARITH_CONV(--`(t+(t0+1))-t0=t+1`--))]
	    (* ------------------------------------------------------------------------	*)
	    THEN MY_MP_TAC (--`!t. fn1 t ==> (?d.  fn1(t+d) /\ b(t+(d+t0)))`--)
	    (* ------------------------------------------------------------------------	*)
	    THENL[
		GEN_TAC THEN DISCH_TAC
		THEN LEFT_NO_FORALL_TAC 2 (--`t:num`--)
		THEN POP_ASSUM (fn x=>ASSUME_TAC(MATCH_MP
			(BETA_RULE(SPEC(--`\t2.b(t+(t2+t0)):bool`--)WOP)) x))
		THEN LEFT_EXISTS_TAC
		THEN MY_MP_TAC (--`!m. m<=n ==> fn1(t+m)`--)
		THENL[
		    INDUCT_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES]
		    THEN DISCH_TAC THEN IMP_RES_TAC OR_LESS
		    THEN IMP_RES_TAC LESS_IMP_LESS_OR_EQ
		    THEN RES_TAC THEN ASM_REWRITE_TAC[SYM(SPEC_ALL ADD_ASSOC)],
		    DISCH_TAC]
	    THEN EXISTS_TAC(--`n:num`--) THEN ASM_REWRITE_TAC[]
	    THEN DISJ_CASES_TAC(EQT_ELIM(ARITH_CONV(--`(n=0)\/(0<n)`--)))
	    THENL[ ASM_REWRITE_TAC[ADD_CLAUSES], ALL_TAC]
	    THEN IMP_RES_TAC LESS_ADD_1
	    THEN RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES,num_CONV(--`1`--)])
	    THEN ASM_REWRITE_TAC[ADD_CLAUSES]
	    THEN IMP_RES_TAC(EQT_ELIM(ARITH_CONV(--`(n=SUC p) ==> (p<n)`--)))
	    THEN IMP_RES_TAC(EQT_ELIM(ARITH_CONV(--`(n=SUC p) ==> (p<=n)`--)))
	    THEN RES_TAC THEN ASM_REWRITE_TAC[SYM(SPEC_ALL ADD_ASSOC)],
	    DISCH_TAC]
	    (* ------------------------------------------------------------------------	*)
	    THEN MY_MP_TAC (--`!t. ~fn1 t ==> (?d.  ~fn1(t+d) /\ a(t+(d+t0)))`--)
	    (* ------------------------------------------------------------------------	*)
	    THENL[
		GEN_TAC THEN DISCH_TAC
		THEN LEFT_NO_FORALL_TAC 4 (--`t:num`--)
		THEN POP_ASSUM (fn x=>ASSUME_TAC(MATCH_MP
			(BETA_RULE(SPEC(--`\t2.a(t+(t2+t0)):bool`--)WOP)) x))
		THEN LEFT_EXISTS_TAC
		THEN MY_MP_TAC (--`!m. m<=n ==> ~fn1(t+m)`--)
		THENL[
		    INDUCT_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES]
		    THEN DISCH_TAC THEN IMP_RES_TAC OR_LESS
		    THEN IMP_RES_TAC LESS_IMP_LESS_OR_EQ
		    THEN RES_TAC THEN ASM_REWRITE_TAC[SYM(SPEC_ALL ADD_ASSOC)],
		    DISCH_TAC]
	    THEN EXISTS_TAC(--`n:num`--) THEN ASM_REWRITE_TAC[]
	    THEN DISJ_CASES_TAC(EQT_ELIM(ARITH_CONV(--`(n=0)\/(0<n)`--)))
	    THENL[ ASM_REWRITE_TAC[ADD_CLAUSES], ALL_TAC]
	    THEN IMP_RES_TAC LESS_ADD_1
	    THEN RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES,num_CONV(--`1`--)])
	    THEN ASM_REWRITE_TAC[ADD_CLAUSES]
	    THEN IMP_RES_TAC(EQT_ELIM(ARITH_CONV(--`(n=SUC p) ==> (p<n)`--)))
	    THEN IMP_RES_TAC(EQT_ELIM(ARITH_CONV(--`(n=SUC p) ==> (p<=n)`--)))
	    THEN RES_TAC THEN ASM_REWRITE_TAC[SYM(SPEC_ALL ADD_ASSOC)],
	    DISCH_TAC]
	    (* ------------------------------------------------------------------------	*)
	    THEN ASM_REWRITE_TAC[ADD_CLAUSES,num_CONV(--`1`--)]
	    THEN REWRITE_TAC[EQT_ELIM(ARITH_CONV(--`(t1+(t2+t0))-t0=t1+t2`--))]
	    THEN GEN_TAC
	    THEN DISJ_CASES_TAC(SPEC(--`(fn1:num->bool) t1`--)BOOL_CASES_AX)
	    THENL[
		LEFT_NO_FORALL_TAC 2 (--`t1:num`--)
		THEN UNDISCH_HD_TAC THEN ASM_REWRITE_TAC[],
		LEFT_NO_FORALL_TAC 1 (--`t1:num`--)
		THEN UNDISCH_HD_TAC THEN ASM_REWRITE_TAC[]
		THEN STRIP_TAC
		THEN MY_MP_TAC (--`fn1(SUC(t1+d)):bool`--)
		THENL[ASM_REWRITE_TAC[SYM(SPEC_ALL ADD_ASSOC)],DISCH_TAC]
		THEN LEFT_NO_FORALL_TAC 4 (--`SUC(t1+d)`--)
		THEN UNDISCH_HD_TAC THEN POP_NO_TAC 4 THEN ASM_REWRITE_TAC[]
		THEN REWRITE_TAC[ADD_CLAUSES,SYM(SPEC_ALL ADD_ASSOC)]
		THEN STRIP_TAC THEN EXISTS_TAC(--`SUC(d+d')`--)
		THEN ASM_REWRITE_TAC[ADD_CLAUSES,SYM(SPEC_ALL ADD_ASSOC)]
		],
	(* ----------------------------------------------------------------------------	*)
	    COPY_ASM_NO 0 THEN LEFT_FORALL_TAC (--`t1:num`--)
	    THEN LEFT_EXISTS_TAC THEN DISCH_TAC
	    THEN MY_MP_TAC (--`~q((t1+t2)+(t0+1)):bool`--)
	    THENL[ASM_REWRITE_TAC[SYM(SPEC_ALL ADD_ASSOC)],DISCH_TAC]
	    THEN LEFT_NO_FORALL_TAC 1 (--`SUC(t1+t2)`--)
	    THEN UNDISCH_HD_TAC THEN CONV_TAC CONTRAPOS_CONV
	    THEN CONV_TAC(DEPTH_CONV NOT_EXISTS_CONV)
	    THEN REPEAT STRIP_TAC
	    THEN POP_NO_TAC 0 THEN UNDISCH_HD_TAC
	    THEN REWRITE_TAC[ADD_CLAUSES,SYM(SPEC_ALL ADD_ASSOC)]
	    THEN RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES,SYM(SPEC_ALL ADD_ASSOC),ONE])
	    THEN SPEC_TAC((--`t2':num`--),(--`t2':num`--)) THEN INDUCT_TAC
	    THENL[ASM_REWRITE_TAC[ADD_CLAUSES], ALL_TAC]
	    THEN SUBST1_TAC(EQT_ELIM(ARITH_CONV
			(--`SUC(t1+(t2+(SUC t2'+t0))) = SUC((t1+(t2+(SUC t2')))+t0)`--)))
	    THEN ASM_REWRITE_TAC[] THEN REWRITE_TAC[ADD_CLAUSES,SYM(SPEC_ALL ADD_ASSOC)]
	    THEN ASM_TAC 0 REWRITE1_TAC
	    THEN SUBST1_TAC(EQT_ELIM(ARITH_CONV
			(--`SUC(t1+(t2+(t2'+t0))) = t1+(SUC(t2+t2')+t0)`--)))
	    THEN ASM_TAC 1 REWRITE1_TAC,
	(* ----------------------------------------------------------------------------	*)
	    LEFT_FORALL_TAC (--`t1:num`--) THEN LEFT_EXISTS_TAC
	    THEN EXISTS_TAC (--`t2:num`--) THEN ASM_REWRITE_TAC[]
	(* ----------------------------------------------------------------------------	*)
	]);






val DISJ_FG = TAC_PROOF(
	([],--`!a b.
		    (?t1.!t2. a(t1+(t2+t0))) \/ (?t1.!t2. b(t1+(t2+t0)))
		=
		    (?q. ~q t0 /\
			 (!t. q(t+(t0+1)) = (if q(t+t0) then b(t+t0) else ~a(t+t0))) /\
			 ?t1.!t2. ~q(t1+(t2+t0)) \/ b(t1+(t2+t0)))`--),
	REPEAT GEN_TAC
	THEN PURE_ONCE_REWRITE_TAC[TAC_PROOF(([],--`(a=b)=(~a=~b)`--),PROP_TAC)]
	THEN PURE_REWRITE_TAC[DE_MORGAN_THM]
	THEN CONV_TAC(REPEATC(CHANGED_CONV(DEPTH_CONV
			(NOT_EXISTS_CONV ORELSEC NOT_FORALL_CONV))))
	THEN SUBST1_TAC(BETA_RULE(SPECL
		[(--`\t:num. ~a(t)`--),(--`\t:num. ~b(t)`--)]
		CONJ_GF))
	THEN REWRITE_TAC[TAC_PROOF(([],--`~(a/\b/\c) = (a/\b) ==> ~c`--),PROP_TAC)]
	THEN REWRITE_TAC[ADD_CLAUSES,num_CONV(--`1`--)]
	THEN EQ_TAC THEN REPEAT STRIP_TAC
	THENL[
	    (* ----------------------------------------------------------------	*)
	    MY_MP_TAC (--`!t:num. q'(t+t0) = (q:num->bool)(t+t0)`--)
	    THENL[INDUCT_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES],
		DISCH_TAC]
	    THEN LEFT_NO_FORALL_TAC 4 (--`t1:num`--) THEN LEFT_EXISTS_TAC
	    THEN LEFT_NO_FORALL_TAC 2 (--`t2:num`--)
	    THEN UNDISCH_HD_TAC THEN ASM_REWRITE_TAC[]
	    THEN ASM_REWRITE_TAC[ADD_ASSOC]
	    THEN ASM_REWRITE_TAC[SYM(SPEC_ALL ADD_ASSOC)],
	    (* ----------------------------------------------------------------	*)
	    ASSUME_TAC(EXISTENCE(BETA_RULE
		(ISPECL[(--`F`--),(--`\x t:num. if x then b(t+t0) else ~a(t+t0)`--)] num_Axiom_old)))
	    THEN LEFT_EXISTS_TAC THEN EXISTS_TAC (--`\t.(fn1(t-t0)):bool`--)
	    THEN LEFT_NO_FORALL_TAC 1 (--`\t.(fn1(t-t0)):bool`--) THEN UNDISCH_HD_TAC
	    THEN BETA_TAC
	    THEN ASM_REWRITE_TAC[
	    		EQT_ELIM(ARITH_CONV(--`n-n=0`--)),
	    		EQT_ELIM(ARITH_CONV(--`(t+t0)-t0=t`--)),
	    		EQT_ELIM(ARITH_CONV(--`SUC(t+t0)-t0=SUC t`--))]
	    THEN CONV_TAC(REPEATC(CHANGED_CONV(DEPTH_CONV
			(NOT_EXISTS_CONV ORELSEC NOT_FORALL_CONV))))
	    THEN REWRITE_TAC[DE_MORGAN_THM]
	    (* ----------------------------------------------------------------	*)
	])




val CONJ_FG = TAC_PROOF(
	([],--`!a b.
		  (?t1.!t2.a(t1+(t2+t0))) /\ (?t1.!t2.b(t1+(t2+t0)))
		= ?t1.!t2. a(t1+(t2+t0)) /\ b(t1+(t2+t0))`--),
	REPEAT GEN_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC
	THENL[
	    DISJ_CASES_TAC (SPECL[(--`t1:num`--),(--`t1':num`--)]LESS_CASES)
	    THENL[
		IMP_RES_TAC LESS_ADD_1
		THEN EXISTS_TAC (--`t1+(p+1)`--) THEN GEN_TAC
		THEN POP_ASSUM (fn x=>RULE_ASSUM_TAC(SUBS[x]))
		THEN LEFT_NO_FORALL_TAC 2 (--`p+(1+t2)`--)
		THEN ASM_REWRITE_TAC[] THEN UNDISCH_HD_TAC
		THEN REWRITE_TAC[ADD_ASSOC],
		IMP_RES_TAC LESS_EQUAL_ADD
		THEN EXISTS_TAC (--`t1'+p`--) THEN GEN_TAC
		THEN POP_ASSUM (fn x=>RULE_ASSUM_TAC(SUBS[x]))
		THEN LEFT_NO_FORALL_TAC 1 (--`p+t2`--)
		THEN ASM_REWRITE_TAC[] THEN UNDISCH_HD_TAC
		THEN REWRITE_TAC[ADD_ASSOC]
	    ],
	    EXISTS_TAC(--`t1:num`--) THEN GEN_TAC
	    THEN LEFT_FORALL_TAC (--`t2:num`--) THEN ASM_REWRITE_TAC[],
	    EXISTS_TAC(--`t1:num`--) THEN GEN_TAC
	    THEN LEFT_FORALL_TAC (--`t2:num`--) THEN ASM_REWRITE_TAC[]
	]);




val DISJ_GF = TAC_PROOF(
	([],--`!a b.
		  (!t1.?t2.a(t1+(t2+t0))) \/ (!t1.?t2.b(t1+(t2+t0)))
		= !t1.?t2. a(t1+(t2+t0)) \/ b(t1+(t2+t0))`--),
	REPEAT GEN_TAC
	THEN PURE_ONCE_REWRITE_TAC[TAC_PROOF(([],--`(a=b)=(~a=~b)`--),PROP_TAC)]
	THEN PURE_REWRITE_TAC[DE_MORGAN_THM]
	THEN CONV_TAC(REPEATC(CHANGED_CONV(DEPTH_CONV
			(NOT_EXISTS_CONV ORELSEC NOT_FORALL_CONV))))
	THEN SUBST1_TAC(BETA_RULE(SPECL
		[(--`\t:num. ~a(t)`--),(--`\t:num. ~b(t)`--)]
		CONJ_FG))
	THEN REWRITE_TAC[DE_MORGAN_THM]
	)







val BOOLEAN_CLOSURE_FG = TAC_PROOF(
	([],--`
	( ~(?t1.!t2. a(t1+(t2+t0))) = (!t1.?t2. ~a(t1+(t2+t0))) ) /\
	( (?t1.!t2.a(t1+(t2+t0))) /\ (?t1.!t2.b(t1+(t2+t0)))
		= ?t1.!t2. a(t1+(t2+t0)) /\ b(t1+(t2+t0)) ) /\
	( (?t1.!t2. a(t1+(t2+t0))) \/ (?t1.!t2. b(t1+(t2+t0)))
	  =
	    (?q. ~q t0 /\
		 (!t. q(t+(t0+1)) = (if q(t+t0) then b(t+t0) else ~a(t+t0))) /\
		 ?t1.!t2. ~q(t1+(t2+t0)) \/ b(t1+(t2+t0)))
	)
	`--),
	REWRITE_TAC[NEG_FG,CONJ_FG,DISJ_FG]);



val BOOLEAN_CLOSURE_GF = TAC_PROOF(
	([],--`
	( ~(!t1.?t2. a(t1+(t2+t0))) = (?t1.!t2. ~a(t1+(t2+t0))) ) /\
	( (!t1.?t2.a(t1+(t2+t0))) \/ (!t1.?t2.b(t1+(t2+t0)))
		= !t1.?t2. a(t1+(t2+t0)) \/ b(t1+(t2+t0))) /\
	( (!t1.?t2. a(t1+(t2+t0))) /\ (!t1.?t2. b(t1+(t2+t0)))
  	  =
	    (?q. ~q t0 /\
		 (!t. q(t+(t0+1)) = (if q(t+t0) then ~b(t+t0) else a(t+t0))) /\
		 !t1.?t2. q(t1+(t2+t0)) /\ b(t1+(t2+t0)))
	)
	`--),
	REWRITE_TAC[NEG_GF,CONJ_GF,DISJ_GF]);





(* ********************************************************************	*)
(* some facts on the Borel Hierarchy					*)
(* ********************************************************************	*)


val G_AS_NDET_F = TAC_PROOF(
	([],--` (!t.a(t+t0))
		=
		?q.
		   q t0 /\
		   (!t. q(t+t0) /\ a(t+t0) /\ q(SUC(t+t0))) /\
		   (?t. q(t+t0)) `--),
	EQ_TAC THEN REPEAT STRIP_TAC
	THEN ASM_REWRITE_TAC[]
	THEN EXISTS_TAC (--`\t:num. T`--) THEN BETA_TAC
	THEN REWRITE_TAC[]
	)



val G_AS_NDET_FG = TAC_PROOF(
	([],--` (!t.a(t+t0))
		=
		?q.
		   q t0 /\
		   (!t. q(SUC(t+t0)) = q(t+t0) /\ a(t+t0)) /\
		   (?t1.!t2. q(t1+(t2+t0))) `--),
	EQ_TAC THEN REPEAT STRIP_TAC
	THEN ASM_REWRITE_TAC[]
	THENL[EXISTS_TAC (--`\t:num. T`--) THEN BETA_TAC THEN REWRITE_TAC[],ALL_TAC]
	THEN UNDISCH_HD_TAC THEN CONV_TAC CONTRAPOS_CONV
	THEN DISCH_TAC THEN CONV_TAC(DEPTH_CONV NOT_FORALL_CONV)
	THEN MY_MP_TAC (--`!x. ~q(SUC(x+(t+t0)))`--)
	THENL[
	    INDUCT_TAC THENL[ASM_REWRITE_TAC[ADD_CLAUSES],ALL_TAC]
	    THEN SUBST1_TAC(EQT_ELIM(ARITH_CONV(--`SUC((SUC x)+(t+t0))=SUC((SUC(x+t))+t0)`--)))
	    THEN ONCE_ASM_REWRITE_TAC[]
	    THEN REWRITE_TAC[ADD_CLAUSES,SYM(SPEC_ALL ADD_ASSOC)]
	    THEN POP_ASSUM REWRITE1_TAC,
	    DISCH_TAC]
	THEN POP_NO_TAC 2
	THEN EXISTS_TAC(--`SUC t`--) THEN ASM_REWRITE_TAC[ADD_CLAUSES]
	)



val G_AS_NDET_GF = TAC_PROOF(
	([],--` (!t.a(t+t0))
		=
		?q.
		   q t0 /\
		   (!t. q(SUC(t+t0)) = q(t+t0) /\ a(t+t0)) /\
		   (!t1.?t2. q(t1+(t2+t0))) `--),
	EQ_TAC THEN REPEAT STRIP_TAC
	THEN ASM_REWRITE_TAC[]
	THENL[EXISTS_TAC (--`\t:num. T`--) THEN BETA_TAC THEN REWRITE_TAC[],ALL_TAC]
	THEN UNDISCH_HD_TAC THEN CONV_TAC CONTRAPOS_CONV
	THEN DISCH_TAC THEN CONV_TAC(DEPTH_CONV NOT_FORALL_CONV)
	THEN CONV_TAC(DEPTH_CONV NOT_EXISTS_CONV)
	THEN MY_MP_TAC (--`!x. ~q(SUC(x+(t+t0)))`--)
	THENL[
	    INDUCT_TAC THENL[ASM_REWRITE_TAC[ADD_CLAUSES],ALL_TAC]
	    THEN SUBST1_TAC(EQT_ELIM(ARITH_CONV(--`SUC((SUC x)+(t+t0))=SUC((SUC(x+t))+t0)`--)))
	    THEN ONCE_ASM_REWRITE_TAC[]
	    THEN REWRITE_TAC[ADD_CLAUSES,SYM(SPEC_ALL ADD_ASSOC)]
	    THEN POP_ASSUM REWRITE1_TAC,
	    DISCH_TAC]
	THEN POP_NO_TAC 2
	THEN EXISTS_TAC(--`SUC t`--)
	THEN ONCE_REWRITE_TAC[EQT_ELIM(ARITH_CONV(--`(SUC t)+(t2+t0) = (SUC t2)+(t+t0)`--))]
	THEN ASM_REWRITE_TAC[ADD_CLAUSES]
	)





val F_AS_NDET_GF = TAC_PROOF(
	([],--`(?t.a(t+t0))
		   = ?q.
			~q t0 /\
			(!t. q(SUC(t+t0)) = q(t+t0) \/ a(t+t0)) /\
			(!t1.?t2. q(t1+(t2+t0)))`--),
	EQ_TAC THEN REPEAT STRIP_TAC
	THENL[
	    ASSUME_TAC(EXISTENCE(BETA_RULE
		(ISPECL[(--`F`--),(--`\x (t:num). x \/ a(t+t0)`--)]num_Axiom_old)))
	    THEN LEFT_EXISTS_TAC THEN EXISTS_TAC (--`\t.(fn1(t-t0)):bool`--)
	    THEN BETA_TAC
	    THEN ASM_REWRITE_TAC[
	    		EQT_ELIM(ARITH_CONV(--`n-n=0`--)),
	    		EQT_ELIM(ARITH_CONV(--`(t+t0)-t0=t`--)),
	    		EQT_ELIM(ARITH_CONV(--`(t1+(t2+t0))-t0=t1+t2`--)),
	    		EQT_ELIM(ARITH_CONV(--`SUC(t+t0)-t0=SUC t`--))]
	    THEN GEN_TAC
	    THEN EXISTS_TAC (--`SUC t`--) THEN SPEC_TAC((--`t1:num`--),(--`t1:num`--))
	    THEN INDUCT_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES]
	    THEN UNDISCH_HD_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES]
	    THEN DISCH_TAC THEN ASM_REWRITE_TAC[],
	    LEFT_FORALL_TAC (--`SUC 0`--) THEN UNDISCH_HD_TAC
	    THEN CONV_TAC CONTRAPOS_CONV THEN REWRITE_TAC[ADD_CLAUSES]
	    THEN CONV_TAC (DEPTH_CONV NOT_EXISTS_CONV)
	    THEN DISCH_TAC
	    THEN INDUCT_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES]
	])



val F_AS_NDET_FG = TAC_PROOF(
	([],--`(?t.a(t+t0))
		   = ?q.
			~q t0 /\
			 (!t. q(SUC(t+t0)) = q(t+t0) \/ a(t+t0)) /\
			 (?t1.!t2. q(t1+(t2+t0)))`--),
	EQ_TAC THEN REPEAT STRIP_TAC
	THENL[
	    ASSUME_TAC(EXISTENCE(BETA_RULE
		(ISPECL[(--`F`--),(--`\x (t:num). x \/ a(t+t0)`--)]num_Axiom_old)))
	    THEN LEFT_EXISTS_TAC THEN EXISTS_TAC (--`\t.(fn1(t-t0)):bool`--)
	    THEN BETA_TAC
	    THEN ASM_REWRITE_TAC[
	    		EQT_ELIM(ARITH_CONV(--`n-n=0`--)),
	    		EQT_ELIM(ARITH_CONV(--`(t+t0)-t0=t`--)),
	    		EQT_ELIM(ARITH_CONV(--`(t1+(t2+t0))-t0=t1+t2`--)),
	    		EQT_ELIM(ARITH_CONV(--`SUC(t+t0)-t0=SUC t`--))]
	    THEN ASM_REWRITE_TAC[] THEN EXISTS_TAC (--`SUC t`--)
	    THEN INDUCT_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES]
	    THEN UNDISCH_HD_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES]
	    THEN DISCH_TAC THEN ASM_REWRITE_TAC[],
	    UNDISCH_HD_TAC THEN CONV_TAC CONTRAPOS_CONV
	    THEN CONV_TAC (DEPTH_CONV NOT_EXISTS_CONV)
	    THEN CONV_TAC (DEPTH_CONV NOT_FORALL_CONV)
	    THEN DISCH_TAC
	    THEN MY_MP_TAC (--`!t:num. ~q(t+t0)`--)
	    THENL[
		INDUCT_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES],
		DISCH_TAC]
	    THEN ASM_REWRITE_TAC[ADD_ASSOC]
	])




val FG_AS_NDET_F = TAC_PROOF(
	([],--`(?t1.!t2.a(t1+(t2+t0)))
		   = ?q.
			~q t0 /\
			 (!t. q(t+t0) ==> a(t+t0) /\ q(SUC(t+t0))) /\
			 (?t. q(t+t0))`--),
	EQ_TAC THEN REPEAT STRIP_TAC
	THENL[
	    EXISTS_TAC(--`\x:num. (t1+t0<x)`--) THEN BETA_TAC
	    THEN REWRITE_TAC[EQT_ELIM(ARITH_CONV(--`~(t1+t0<t0)`--))]
	    THEN REWRITE_TAC[EQT_ELIM(ARITH_CONV(--`(t1+t0<t+t0) = (t1<t)`--))]
	    THEN REWRITE_TAC[EQT_ELIM(ARITH_CONV(--`(t1+t0<SUC(t+t0)) = (t1<SUC t)`--))]
	    THEN CONJ_TAC
	    THENL[ALL_TAC, EXISTS_TAC(--`SUC t1`--) THEN CONV_TAC ARITH_CONV]
	    THEN GEN_TAC THEN DISCH_TAC
	    THEN IMP_RES_TAC LESS_ADD_1
	    THEN IMP_RES_TAC(EQT_ELIM(ARITH_CONV(--`t1<t ==> t1 < SUC t`--)))
	    THEN ASM_REWRITE_TAC[]
	    THEN SUBST1_TAC(EQT_ELIM(ARITH_CONV(--`((t1+((p+1))+t0)) = (t1+((p+1)+t0))`--)))
	    THEN ASM_REWRITE_TAC[],
	    EXISTS_TAC(--`t:num`--)
	    THEN MY_MP_TAC (--`!x. q(t+(x+t0))`--)
	    THENL[
		INDUCT_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES,ADD_ASSOC]
		THEN RULE_ASSUM_TAC(REWRITE_RULE[ADD_ASSOC]) THEN RES_TAC,
		DISCH_TAC]
	    THEN GEN_TAC THEN LEFT_FORALL_TAC(--`t2:num`--)
	    THEN REWRITE_TAC[ADD_ASSOC]
	    THEN RULE_ASSUM_TAC(REWRITE_RULE[ADD_ASSOC])
	    THEN RES_TAC
	    ])





val FG_AS_NDET_GF = TAC_PROOF(
	([],--`(?t1.!t2. a(t1+(t2+t0)))
		  = (?p q.
			(~p t0 /\ ~q t0) /\
			(!t. (p(t+t0) ==> p(SUC(t+t0))) /\
			     (p(SUC(t+t0)) ==> p(t+t0) \/ ~q(t+t0)) /\
			     (q(SUC(t+t0)) = (p(t+t0)/\~q(t+t0)/\~a(t+t0)) \/ (p(t+t0) /\ q(t+t0)))) /\
			!t1.?t2. p(t1+(t2+t0)) /\ ~q(t1+(t2+t0)))`--),
  	EQ_TAC THEN STRIP_TAC
	THENL[
	    EXISTS_TAC (--`\t.t1+t0<t`--) THEN EXISTS_TAC (--`\t:num.F`--)
	    THEN BETA_TAC
	    THEN REWRITE_TAC[EQT_ELIM(ARITH_CONV(--`~(t1+t0<t0)`--))]
	    THEN REWRITE_TAC[EQT_ELIM(ARITH_CONV(--`(t1+t0<t+t0) = (t1<t)`--))]
	    THEN REWRITE_TAC[EQT_ELIM(ARITH_CONV(--`(t1+t0<SUC(t+t0)) = (t1<SUC t)`--))]
	    THEN CONJ_TAC
	    THENL[
		GEN_TAC THEN REWRITE_TAC[TAC_PROOF(
				([],--`~(a/\~b) = (a==>b)`--),PROP_TAC)]
		THEN REWRITE_TAC[EQT_ELIM(ARITH_CONV(--`t1<t ==> t1<SUC t`--))]
		THEN DISCH_TAC THEN IMP_RES_TAC LESS_ADD
		THEN POP_ASSUM (SUBST1_TAC o SYM)
		THEN SUBST1_TAC(EQT_ELIM(ARITH_CONV(--`(p+t1)+t0 = t1+(p+t0)`--)))
		THEN ASM_REWRITE_TAC[],
		GEN_TAC THEN EXISTS_TAC (--`SUC t1`--)
		THEN CONV_TAC ARITH_CONV],
	MY_MP_TAC (--`?t:num. p(t+t0) /\ ~q(t+t0)`--)
	THENL[
	    LEFT_FORALL_TAC (--`t1:num`--) THEN LEFT_EXISTS_TAC
	    THEN EXISTS_TAC (--`t1+t2`--)
	    THEN ASM_REWRITE_TAC[SYM(SPEC_ALL ADD_ASSOC)],
	    DISCH_TAC THEN LEFT_EXISTS_TAC]
	THEN MY_MP_TAC (--`!t1. p(t1+t0) /\ q(t1+t0)
				==> !t2. p(t1+(t2+t0)) /\ q(t1+(t2+t0))`--)
	THENL[
	    GEN_TAC THEN DISCH_TAC THEN INDUCT_TAC
	    THENL[
	        ASM_REWRITE_TAC[ADD_CLAUSES],
		LEFT_NO_FORALL_TAC 4 (--`t1+t2`--) THEN UNDISCH_HD_TAC
		THEN ASM_REWRITE_TAC[ADD_CLAUSES,SYM(SPEC_ALL ADD_ASSOC)]
	    ],
	    DISCH_TAC]
	THEN MY_MP_TAC (--`!t:num.~(p(t+t0) /\ q(t+t0))`--)
	THENL[
	    UNDISCH_NO_TAC 2 THEN CONV_TAC CONTRAPOS_CONV
	    THEN CONV_TAC(DEPTH_CONV NOT_FORALL_CONV)
	    THEN CONV_TAC(DEPTH_CONV NOT_EXISTS_CONV)
	    THEN REWRITE_TAC[] THEN STRIP_TAC
	    THEN RES_TAC THEN EXISTS_TAC (--`t':num`--)
	    THEN ASM_REWRITE_TAC[],
	    DISCH_TAC]
	THEN MY_MP_TAC (--`!d. p(t+(d+t0)) /\ ~q(t+(d+t0)) /\ a(t+(d+t0))`--)
	THENL[
	    INDUCT_TAC
	    THENL[
		LEFT_FORALL_TAC (--`SUC t`--) THEN UNDISCH_HD_TAC
		THEN LEFT_NO_FORALL_TAC 3 (--`t:num`--)
		THEN UNDISCH_HD_TAC THEN BOOL_CASES_TAC (--`p(SUC t):bool`--)
		THEN ASM_REWRITE_TAC[ADD_CLAUSES]
		THEN DISCH_TAC THEN ASM_REWRITE_TAC[],
		REWRITE_TAC[ADD_CLAUSES] THEN UNDISCH_HD_TAC THEN COPY_ASM_NO 4
		THEN LEFT_FORALL_TAC (--`t+d`--)
		THEN DISCH_TAC THEN LEFT_FORALL_TAC (--`SUC(t+d)`--)
		THEN UNDISCH_HD_TAC THEN UNDISCH_HD_TAC
		THEN LEFT_FORALL_TAC (--`SUC(SUC(t+d))`--)
		THEN UNDISCH_HD_TAC
		THEN REWRITE_TAC[ADD_CLAUSES,ADD_ASSOC] THEN PROP_TAC
		],
	    DISCH_TAC]
	THEN EXISTS_TAC (--`t:num`--) THEN ASM_REWRITE_TAC[]
	])






val BOREL_HIERARCHY_G = TAC_PROOF(
	([],--`
	( (!t.a(t+t0))
		=
		?q.
		   q t0 /\
		   (!t. q(t+t0) /\ a(t+t0) /\ q(SUC(t+t0))) /\
		   (?t. q(t+t0)) ) /\
	( (!t.a(t+t0))
		=
		?q.
		   q t0 /\
		   (!t. q(SUC(t+t0)) = q(t+t0) /\ a(t+t0)) /\
		   (?t1.!t2. q(t1+(t2+t0))) ) /\
	( (!t.a(t+t0))
		=
		?q.
		   q t0 /\
		   (!t. q(SUC(t+t0)) = q(t+t0) /\ a(t+t0)) /\
		   (!t1.?t2. q(t1+(t2+t0))) )
	`--),
	REWRITE_TAC(map SYM [G_AS_NDET_F,G_AS_NDET_FG,G_AS_NDET_GF]));


val BOREL_HIERARCHY_F = TAC_PROOF(
	([],--`
	( (?t.a(t+t0))
		   = ?q.
			~q t0 /\
			 (!t. q(SUC(t+t0)) = q(t+t0) \/ a(t+t0)) /\
			 (?t1.!t2. q(t1+(t2+t0))) )
	/\
	( (?t.a(t+t0))
		   = ?q.
			~q t0 /\
			(!t. q(SUC(t+t0)) = q(t+t0) \/ a(t+t0)) /\
			(!t1.?t2. q(t1+(t2+t0)))
	)
	`--),
	REWRITE_TAC(map SYM [F_AS_NDET_FG,F_AS_NDET_GF]));



val BOREL_HIERARCHY_FG = TAC_PROOF(
	([],--`
	( (?t1. !t2. a(t1+(t2+t0))) =
	     (?q.
	       ~q t0 /\
	       (!t. q(t+t0) ==> a(t+t0) /\ q (SUC(t+t0))) /\
	       (?t. q(t+t0))) )
	/\
	( (?t1. !t2. a(t1+(t2+t0))) =
	     (?p q.
	       (~p t0 /\ ~q t0) /\
	       (!t.
	         (p(t+t0) ==> p (SUC(t+t0))) /\
	         (p (SUC(t+t0)) ==> p(t+t0) \/ ~(q(t+t0))) /\
	         (q (SUC(t+t0)) =
	          p(t+t0) /\ ~(q(t+t0)) /\ ~(a(t+t0)) \/
	          p(t+t0) /\ q(t+t0))) /\
	       (!t1. ?t2. p(t1+(t2+t0)) /\ ~(q(t1+(t2+t0)))))
	)
	`--),
	REWRITE_TAC(map SYM [FG_AS_NDET_F,FG_AS_NDET_GF]));





(* ************************************************************************************	*)
(* All temporal expressions can be translated into equivalent Buechi automata. For this	*)
(* purpose, the following theorems are of interest. However, they require that the term	*)
(* has to be transformed into definitional normal form and then only a satisfiability	*)
(* equivalent automaton is computed.							*)
(* ************************************************************************************	*)


val WHEN2BUECHI_THM = TAC_PROOF(
	 ([],--`(l = (a WHEN b)) =
	        (!t. l t = (if b t then a t else l(t+1))) /\
		(!t1.?t2. l(t1+t2) \/ b(t1+t2))`--),
	REWRITE_TAC[BETA_RULE(CONV_RULE (DEPTH_CONV FUN_EQ_CONV) WHEN_FIX)]
	THEN CONV_TAC(DEPTH_CONV FUN_EQ_CONV)
	THEN EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[]
	THENL[
	    (* ---- Proving !t1. ?t2. (a SWHEN b) (t1 + t2) ==> b (t1 + t2) ---- *)
	    POP_NO_TAC 0 THEN GEN_TAC
	    THEN DISJ_CASES_TAC (SPEC(--`t1:num`--)(GEN(--`t0:num`--)DELTA_CASES))
	    THENL[
		LEFT_EXISTS_TAC THEN EXISTS_TAC (--`d:num`--)
		THEN ONCE_REWRITE_TAC[ADD_SYM]
		THEN ASM_REWRITE_TAC[],
		ONCE_REWRITE_TAC[ADD_SYM]
		THEN ASM_REWRITE_TAC[WHEN_SIGNAL,ADD_ASSOC]],
	    (* ---- Proving ---------------------------------------------------	*)
	    (*     (!t1. ?t2. (a WHEN b) (t1 + t2) ==> b (t1 + t2)) ==>		*)
      	    (*             (!n. (a WHEN b) n = (a SWHEN b) n)			*)
	    (* ----------------------------------------------------------------	*)
	    UNDISCH_HD_TAC THEN POP_ASSUM REWRITE1_TAC
	    THEN DISCH_TAC
	    THEN ONCE_REWRITE_TAC[TAC_PROOF(([],--`(a:bool=b) = (b=a)`--),PROP_TAC)]
	    THEN MY_MP_TAC (--`
			(!n. EVENTUAL b n)
			==> !n. (a WHEN b) n = (a SWHEN b) n`--)
	    THENL[
		DISCH_TAC THEN GEN_TAC
		THEN MATCH_MP_TAC (snd(EQ_IMP_RULE(SYM(hd(CONJUNCTS SOME_EVENT)))))
	        THEN ASM_REWRITE_TAC[],
		DISCH_TAC]
	    THEN POP_ASSUM MATCH_MP_TAC THEN GEN_TAC
	    THEN LEFT_FORALL_TAC (--`n:num`--)
	    THEN DISJ_CASES_TAC (SPEC(--`n:num`--)(GEN(--`t0:num`--)DELTA_CASES))
	    THENL[
		LEFT_EXISTS_TAC THEN REWRITE_TAC[EVENTUAL]
		THEN EXISTS_TAC(--`d:num`--) THEN ASM_REWRITE_TAC[],
		UNDISCH_NO_TAC 1 THEN ASM_REWRITE_TAC[SWHEN_SIGNAL]
		THEN ONCE_REWRITE_TAC[EQT_ELIM(ARITH_CONV(--`t+(n+t2) = (t+t2)+n`--))]
		THEN ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[ADD_SYM]
		THEN ASM_REWRITE_TAC[]
		]
	    ]);



val SWHEN2BUECHI_THM = TAC_PROOF(
	 ([],--`(l = (a SWHEN b)) =
	        (!t. l t = (if b t then a t else l(t+1))) /\
		(!t1.?t2. l(t1+t2) ==> b(t1+t2))`--),
	REWRITE_TAC[BETA_RULE(CONV_RULE (DEPTH_CONV FUN_EQ_CONV) WHEN_FIX)]
	THEN CONV_TAC(DEPTH_CONV FUN_EQ_CONV)
	THEN EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[]
	THENL[
	    (* ---- Proving !t1. ?t2. (a SWHEN b) (t1 + t2) ==> b (t1 + t2) ---- *)
	    POP_NO_TAC 0 THEN GEN_TAC
	    THEN DISJ_CASES_TAC (SPEC(--`t1:num`--)(GEN(--`t0:num`--)DELTA_CASES))
	    THENL[
		LEFT_EXISTS_TAC THEN EXISTS_TAC (--`d:num`--)
		THEN ONCE_REWRITE_TAC[ADD_SYM]
		THEN ASM_REWRITE_TAC[],
		ONCE_REWRITE_TAC[ADD_SYM]
		THEN ASM_REWRITE_TAC[SWHEN_SIGNAL,ADD_ASSOC]],
	    (* ---- Proving ---------------------------------------------------	*)
	    (*     (!t1. ?t2. (a WHEN b) (t1 + t2) ==> b (t1 + t2)) ==>		*)
      	    (*             (!n. (a WHEN b) n = (a SWHEN b) n)			*)
	    (* ----------------------------------------------------------------	*)
	    UNDISCH_HD_TAC THEN POP_ASSUM REWRITE1_TAC
	    THEN DISCH_TAC
	    THEN MY_MP_TAC (--`
			(!n. EVENTUAL b n)
			==> !n. (a WHEN b) n = (a SWHEN b) n`--)
	    THENL[
		DISCH_TAC THEN GEN_TAC
		THEN MATCH_MP_TAC (snd(EQ_IMP_RULE(SYM(hd(CONJUNCTS SOME_EVENT)))))
	        THEN ASM_REWRITE_TAC[],
		DISCH_TAC]
	    THEN POP_ASSUM MATCH_MP_TAC THEN GEN_TAC
	    THEN LEFT_FORALL_TAC (--`n:num`--)
	    THEN DISJ_CASES_TAC (SPEC(--`n:num`--)(GEN(--`t0:num`--)DELTA_CASES))
	    THENL[
		LEFT_EXISTS_TAC THEN REWRITE_TAC[EVENTUAL]
		THEN EXISTS_TAC(--`d:num`--) THEN ASM_REWRITE_TAC[],
		UNDISCH_NO_TAC 1 THEN ASM_REWRITE_TAC[WHEN_SIGNAL]
		THEN ONCE_REWRITE_TAC[EQT_ELIM(ARITH_CONV(--`delta+(n+t2) = (delta+t2)+n`--))]
		THEN ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[ADD_SYM]
		THEN ASM_REWRITE_TAC[]
		]
	    ]);



val UNTIL2BUECHI_THM = TAC_PROOF(
	 ([],--`(l = (a UNTIL b)) =
	        (!t. l t = ~b t ==> a t /\ l(t+1)) /\
		(!t1.?t2. ~l(t1+t2) ==> ~a(t1+t2) \/ b(t1+t2))`--),
	REWRITE_TAC[UNTIL_AS_WHEN,WHEN2BUECHI_THM] THEN BETA_TAC
	THEN REWRITE_TAC[TAC_PROOF
		(([],--`(if (a ==> b) then b else l) = (~b ==> a /\ l)`--),PROP_TAC)]
	THEN REWRITE_TAC[TAC_PROOF
		(([],--`(l \/(a==>b)) = (~l ==> (~a\/b))`--),PROP_TAC)]);


val SUNTIL2BUECHI_THM = TAC_PROOF(
	 ([],--`(l = (a SUNTIL b)) =
	        (!t. l t = ~b t ==> a t /\ l(t+1)) /\
		(!t1.?t2. l(t1+t2) ==> ~a(t1+t2) \/ b(t1+t2))`--),
	REWRITE_TAC[SUNTIL_AS_SWHEN,SWHEN2BUECHI_THM] THEN BETA_TAC
	THEN REWRITE_TAC[TAC_PROOF
		(([],--`(if (a ==> b) then b else l) = (~b ==> a /\ l)`--),PROP_TAC)]
	THEN REWRITE_TAC[TAC_PROOF
		(([],--`(l ==> a==>b) = (l ==> ~a \/ b)`--),PROP_TAC)]);


val BEFORE2BUECHI_THM = TAC_PROOF(
	 ([],--`(l = (a BEFORE b)) =
	        (!t. l t = ~b t /\ (a t \/ l(t+1))) /\
		(!t1.?t2. ~l(t1+t2) ==> a(t1+t2) \/ b(t1+t2))`--),
	REWRITE_TAC[BEFORE_AS_SUNTIL]
	THEN REWRITE_TAC[TAC_PROOF
		(([],--`(l = ~b/\(a\/l1)) = (~l = ~b ==>~a/\~l1)`--),PROP_TAC)]
	THEN ONCE_REWRITE_TAC[TAC_PROOF
		(([],--`(~l ==> a \/b) = (~l ==> ~~a \/ b)`--),PROP_TAC)]
	THEN REWRITE1_TAC(SYM(BETA_RULE
		  (SPEC(--`\t:num.~l t`--)(GEN(--`l:num->bool`--)
		  (SPEC(--`\t:num.~a t`--)(GEN(--`a:num->bool`--)
			SUNTIL2BUECHI_THM)))) ))
	THEN CONV_TAC(DEPTH_CONV FUN_EQ_CONV) THEN BETA_TAC
	THEN ONCE_REWRITE_TAC[TAC_PROOF
		(([],--`(a = ~b) = (~a = b)`--),PROP_TAC)]
	THEN REWRITE_TAC[]);




val SBEFORE2BUECHI_THM = TAC_PROOF(
	 ([],--`(l = (a SBEFORE b)) =
	        (!t. l t = ~b t /\ (a t \/ l(t+1))) /\
		(!t1.?t2. l(t1+t2) ==> a(t1+t2) \/ b(t1+t2))`--),
	REWRITE_TAC[SBEFORE_AS_UNTIL]
	THEN REWRITE_TAC[TAC_PROOF
		(([],--`(l = ~b/\(a\/l1)) = (~l = ~b ==>~a/\~l1)`--),PROP_TAC)]
	THEN REWRITE1_TAC(SYM(REWRITE_RULE[](BETA_RULE
		  (SPEC(--`\t:num.~l t`--)(GEN(--`l:num->bool`--)
		  (SPEC(--`\t:num.~a t`--)(GEN(--`a:num->bool`--)
			UNTIL2BUECHI_THM)))) )))
	THEN CONV_TAC(DEPTH_CONV FUN_EQ_CONV) THEN BETA_TAC
	THEN ONCE_REWRITE_TAC[TAC_PROOF
		(([],--`(a = ~b) = (~a = b)`--),PROP_TAC)]
	THEN REWRITE_TAC[]);



val ALWAYS2BUECHI_THM = TAC_PROOF(
	 ([],--`(l = (ALWAYS a)) =
	        (!t. l t = a t /\ l(t+1)) /\
		(!t1.?t2. a(t1+t2) ==> l(t1+t2))`--),
	REWRITE_TAC[ALWAYS_AS_UNTIL,UNTIL2BUECHI_THM] THEN BETA_TAC
	THEN REWRITE_TAC[TAC_PROOF
		(([],--`(~a ==> ~l) =( l ==> a)`--),PROP_TAC)]);



val EVENTUAL2BUECHI_THM = TAC_PROOF(
	 ([],--`(l = (EVENTUAL a)) =
	        (!t. l t = a t \/ l(t+1)) /\
		(!t1.?t2. l(t1+t2) ==> a(t1+t2))`--),
	REWRITE_TAC[EVENTUAL_AS_SUNTIL,SUNTIL2BUECHI_THM] THEN BETA_TAC
	THEN REWRITE_TAC[TAC_PROOF
		(([],--`(~a ==> l) = (a \/ l)`--),PROP_TAC)]);






val PSNEXT_PEVENTUAL2OMEGA = TAC_PROOF(
	([],--` (l = PSNEXT(PEVENTUAL a))
		 =
		(l 0 = F) /\
		(!t. l(SUC t) = a t \/ l t)
	`--),
	EQ_TAC THEN STRIP_TAC
	THENL[
	    ASM_REWRITE_TAC[PSNEXT,LESS_REFL]
	    THEN INDUCT_TAC
	    THEN REWRITE_TAC[PRE,LESS_REFL,LESS_0,INITIALISATION]
	    THEN CONV_TAC(LHS_CONV(ONCE_REWRITE_CONV[RECURSION]))
	    THEN BETA_TAC THEN REWRITE_TAC[PSNEXT,ZERO_LEMMA,PRE],
	    CONV_TAC FUN_EQ_CONV
	    THEN INDUCT_TAC THEN ASM_REWRITE_TAC[PSNEXT,PRE,LESS_0,LESS_REFL]
	    THEN DISJ_CASES_TAC(EQT_ELIM(ARITH_CONV(--`(n=0)\/(0<n)`--)))
	    THEN ASM_REWRITE_TAC[INITIALISATION,LESS_REFL]
	    THEN IMP_RES_TAC LESS_ADD_1
	    THEN POP_ASSUM SUBST1_TAC
	    THEN REWRITE_TAC[num_CONV(--`1`--),ADD_CLAUSES,PRE]
	    THEN CONV_TAC(RHS_CONV(ONCE_REWRITE_CONV[RECURSION]))
	    THEN BETA_TAC THEN REWRITE_TAC[PSNEXT,ZERO_LEMMA,PRE]
	    ]);



val PSNEXT_PSUNTIL2OMEGA = TAC_PROOF(
	([],--` (l = PSNEXT(a PSUNTIL b))
		 =
		(l 0 = F) /\
		(!t. l(SUC t) = b t \/ a t /\ l t)
	`--),
	EQ_TAC THEN STRIP_TAC
	THENL[
	    ASM_REWRITE_TAC[PSNEXT,LESS_REFL]
	    THEN INDUCT_TAC
	    THEN REWRITE_TAC[PRE,LESS_REFL,LESS_0,INITIALISATION]
	    THEN CONV_TAC(LHS_CONV(ONCE_REWRITE_CONV[RECURSION]))
	    THEN BETA_TAC THEN REWRITE_TAC[PSNEXT,ZERO_LEMMA,PRE],
	    CONV_TAC FUN_EQ_CONV
	    THEN INDUCT_TAC THEN ASM_REWRITE_TAC[PSNEXT,PRE,LESS_0,LESS_REFL]
	    THEN DISJ_CASES_TAC(EQT_ELIM(ARITH_CONV(--`(n=0)\/(0<n)`--)))
	    THEN ASM_REWRITE_TAC[INITIALISATION,LESS_REFL]
	    THEN IMP_RES_TAC LESS_ADD_1
	    THEN POP_ASSUM SUBST1_TAC
	    THEN REWRITE_TAC[num_CONV(--`1`--),ADD_CLAUSES,PRE]
	    THEN CONV_TAC(RHS_CONV(ONCE_REWRITE_CONV[RECURSION]))
	    THEN BETA_TAC THEN REWRITE_TAC[PSNEXT,ZERO_LEMMA,PRE]
	    ]);


val PSNEXT_PSWHEN2OMEGA = TAC_PROOF(
	([],--` (l = PSNEXT(a PSWHEN b))
		 =
		(l 0 = F) /\
		(!t. l(SUC t) = a t /\ b t \/ ~b t /\ l t)
	`--),
	EQ_TAC THEN STRIP_TAC
	THENL[
	    ASM_REWRITE_TAC[PSNEXT,LESS_REFL]
	    THEN INDUCT_TAC
	    THEN REWRITE_TAC[PRE,LESS_REFL,LESS_0,INITIALISATION]
	    THEN CONV_TAC(LHS_CONV(ONCE_REWRITE_CONV[RECURSION]))
	    THEN BETA_TAC THEN REWRITE_TAC[PSNEXT,ZERO_LEMMA,PRE],
	    CONV_TAC FUN_EQ_CONV
	    THEN INDUCT_TAC THEN ASM_REWRITE_TAC[PSNEXT,PRE,LESS_0,LESS_REFL]
	    THEN DISJ_CASES_TAC(EQT_ELIM(ARITH_CONV(--`(n=0)\/(0<n)`--)))
	    THEN ASM_REWRITE_TAC[INITIALISATION,LESS_REFL]
	    THEN IMP_RES_TAC LESS_ADD_1
	    THEN POP_ASSUM SUBST1_TAC
	    THEN REWRITE_TAC[num_CONV(--`1`--),ADD_CLAUSES,PRE]
	    THEN CONV_TAC(RHS_CONV(ONCE_REWRITE_CONV[RECURSION]))
	    THEN BETA_TAC THEN REWRITE_TAC[PSNEXT,ZERO_LEMMA,PRE]
	    ]);


val PSNEXT_PSBEFORE2OMEGA = TAC_PROOF(
	([],--` (l = PSNEXT(a PSBEFORE b))
		 =
		(l 0 = F) /\
		(!t. l(SUC t) = ~b t /\ (a t \/ l t))
	`--),
	EQ_TAC THEN STRIP_TAC
	THENL[
	    ASM_REWRITE_TAC[PSNEXT,LESS_REFL]
	    THEN INDUCT_TAC
	    THEN REWRITE_TAC[PRE,LESS_REFL,LESS_0,INITIALISATION]
	    THEN CONV_TAC(LHS_CONV(ONCE_REWRITE_CONV[RECURSION]))
	    THEN BETA_TAC THEN REWRITE_TAC[PSNEXT,ZERO_LEMMA,PRE]
	    THEN PROP_TAC,
	    CONV_TAC FUN_EQ_CONV
	    THEN INDUCT_TAC THEN ASM_REWRITE_TAC[PSNEXT,PRE,LESS_0,LESS_REFL]
	    THEN DISJ_CASES_TAC(EQT_ELIM(ARITH_CONV(--`(n=0)\/(0<n)`--)))
	    THEN ASM_REWRITE_TAC[INITIALISATION,LESS_REFL]
	    THEN IMP_RES_TAC LESS_ADD_1
	    THEN POP_ASSUM SUBST1_TAC THENL[PROP_TAC,ALL_TAC]
	    THEN REWRITE_TAC[num_CONV(--`1`--),ADD_CLAUSES,PRE]
	    THEN CONV_TAC(RHS_CONV(ONCE_REWRITE_CONV[RECURSION]))
	    THEN BETA_TAC THEN REWRITE_TAC[PSNEXT,ZERO_LEMMA,PRE]
	    ]);





val PSNEXT_PALWAYS2OMEGA = TAC_PROOF(
	([],--` (l = PNEXT(PALWAYS a))
		 =
		(l 0 = T) /\
		(!t. l(SUC t) = a t /\ l t)
	`--),
	EQ_TAC THEN STRIP_TAC
	THENL[
	    ASM_REWRITE_TAC[PNEXT,LESS_REFL,ZERO_LEMMA,PRE]
	    THEN INDUCT_TAC
	    THEN REWRITE_TAC[PRE,INITIALISATION]
	    THEN CONV_TAC(LHS_CONV(ONCE_REWRITE_CONV[RECURSION]))
	    THEN BETA_TAC THEN REWRITE_TAC[PNEXT,ZERO_LEMMA,PRE],
	    CONV_TAC FUN_EQ_CONV
	    THEN INDUCT_TAC THEN ASM_REWRITE_TAC[PNEXT,PRE,ZERO_LEMMA]
	    THEN DISJ_CASES_TAC(EQT_ELIM(ARITH_CONV(--`(n=0)\/(0<n)`--)))
	    THEN ASM_REWRITE_TAC[INITIALISATION,ZERO_LEMMA]
	    THEN IMP_RES_TAC LESS_ADD_1
	    THEN POP_ASSUM SUBST1_TAC
	    THEN REWRITE_TAC[num_CONV(--`1`--),ADD_CLAUSES,PRE]
	    THEN CONV_TAC(RHS_CONV(ONCE_REWRITE_CONV[RECURSION]))
	    THEN BETA_TAC THEN REWRITE_TAC[PNEXT,ZERO_LEMMA,PRE]
	    ]);




val PSNEXT_PUNTIL2OMEGA = TAC_PROOF(
	([],--` (l = PNEXT(a PUNTIL b))
		 =
		(l 0 = T) /\
		(!t. l(SUC t) = b t \/ a t /\ l t)
	`--),
	EQ_TAC THEN STRIP_TAC
	THENL[
	    ASM_REWRITE_TAC[PNEXT,LESS_REFL,ZERO_LEMMA,PRE]
	    THEN INDUCT_TAC
	    THEN REWRITE_TAC[PRE,INITIALISATION,ZERO_LEMMA]
	    THEN CONV_TAC(LHS_CONV(ONCE_REWRITE_CONV[RECURSION]))
	    THEN BETA_TAC THEN REWRITE_TAC[PNEXT,ZERO_LEMMA,PRE]
	    THEN PROP_TAC,
	    CONV_TAC FUN_EQ_CONV
	    THEN INDUCT_TAC THEN ASM_REWRITE_TAC[PNEXT,PRE,ZERO_LEMMA]
	    THEN DISJ_CASES_TAC(EQT_ELIM(ARITH_CONV(--`(n=0)\/(0<n)`--)))
	    THEN ASM_REWRITE_TAC[INITIALISATION,ZERO_LEMMA]
	    THENL[PROP_TAC,ALL_TAC]
	    THEN IMP_RES_TAC LESS_ADD_1
	    THEN POP_ASSUM SUBST1_TAC
	    THEN REWRITE_TAC[num_CONV(--`1`--),ADD_CLAUSES,PRE,ZERO_LEMMA]
	    THEN CONV_TAC(RHS_CONV(ONCE_REWRITE_CONV[RECURSION]))
	    THEN BETA_TAC THEN REWRITE_TAC[PNEXT,ZERO_LEMMA,PRE]
	    ]);



val PSNEXT_PWHEN2OMEGA = TAC_PROOF(
	([],--` (l = PNEXT(a PWHEN b))
		 =
		(l 0 = T) /\
		(!t. l(SUC t) = a t /\ b t \/ ~b t /\ l t)
	`--),
	EQ_TAC THEN STRIP_TAC
	THENL[
	    ASM_REWRITE_TAC[PNEXT,LESS_REFL,ZERO_LEMMA,PRE]
	    THEN INDUCT_TAC
	    THEN REWRITE_TAC[PRE,INITIALISATION,ZERO_LEMMA]
	    THEN CONV_TAC(LHS_CONV(ONCE_REWRITE_CONV[RECURSION]))
	    THEN BETA_TAC THEN REWRITE_TAC[PNEXT,ZERO_LEMMA,PRE]
	    THEN PROP_TAC,
	    CONV_TAC FUN_EQ_CONV
	    THEN INDUCT_TAC THEN ASM_REWRITE_TAC[PNEXT,PRE,ZERO_LEMMA]
	    THEN DISJ_CASES_TAC(EQT_ELIM(ARITH_CONV(--`(n=0)\/(0<n)`--)))
	    THEN ASM_REWRITE_TAC[INITIALISATION,ZERO_LEMMA]
	    THEN IMP_RES_TAC LESS_ADD_1
	    THEN POP_ASSUM SUBST1_TAC
	    THEN REWRITE_TAC[num_CONV(--`1`--),ADD_CLAUSES,PRE,ZERO_LEMMA]
	    THEN CONV_TAC(RHS_CONV(ONCE_REWRITE_CONV[RECURSION]))
	    THEN BETA_TAC THEN REWRITE_TAC[PNEXT,ZERO_LEMMA,PRE]
	    THEN PROP_TAC
	    ]);


val PSNEXT_PBEFORE2OMEGA = TAC_PROOF(
	([],--` (l = PNEXT(a PBEFORE b))
		 =
		(l 0 = T) /\
		(!t. l(SUC t) = ~b t /\ (a t \/ l t))
	`--),
	EQ_TAC THEN STRIP_TAC
	THENL[
	    ASM_REWRITE_TAC[PNEXT,LESS_REFL,ZERO_LEMMA,PRE]
	    THEN INDUCT_TAC
	    THEN REWRITE_TAC[PRE,INITIALISATION,ZERO_LEMMA]
	    THEN CONV_TAC(LHS_CONV(ONCE_REWRITE_CONV[RECURSION]))
	    THEN BETA_TAC THEN REWRITE_TAC[PNEXT,ZERO_LEMMA,PRE]
	    THEN PROP_TAC,
	    CONV_TAC FUN_EQ_CONV
	    THEN INDUCT_TAC THEN ASM_REWRITE_TAC[PNEXT,PRE,ZERO_LEMMA]
	    THEN DISJ_CASES_TAC(EQT_ELIM(ARITH_CONV(--`(n=0)\/(0<n)`--)))
	    THEN ASM_REWRITE_TAC[INITIALISATION,ZERO_LEMMA]
	    THEN IMP_RES_TAC LESS_ADD_1
	    THEN POP_ASSUM SUBST1_TAC
	    THEN REWRITE_TAC[num_CONV(--`1`--),ADD_CLAUSES,PRE,ZERO_LEMMA]
	    THEN CONV_TAC(RHS_CONV(ONCE_REWRITE_CONV[RECURSION]))
	    THEN BETA_TAC THEN REWRITE_TAC[PNEXT,ZERO_LEMMA,PRE]
	    THEN PROP_TAC
	    ]);



val TEMP_OPS_DEFS_TO_OMEGA = TAC_PROOF(
	([],--`
	((l = (NEXT a)) =
		T /\
	        (!t. l t = a(SUC t)) /\
		T
	) /\
	((l = (ALWAYS a)) =
		T /\
	        (!t. l t = a t /\ l(SUC t)) /\
		(!t1.?t2. a(t1+t2) ==> l(t1+t2))
	) /\
	((l = (EVENTUAL a)) =
		T /\
	        (!t. l t = a t \/ l(SUC t)) /\
		(!t1.?t2. l(t1+t2) ==> a(t1+t2))
	) /\
	((l = (a SUNTIL b)) =
		T /\
	        (!t. l t = ~b t ==> a t /\ l(SUC t)) /\
		(!t1.?t2. l(t1+t2) ==> ~a(t1+t2) \/ b(t1+t2))
	) /\
	((l = (a SWHEN b)) =
		T /\
	        (!t. l t = (if b t then a t else l(SUC t))) /\
		(!t1.?t2. l(t1+t2) ==> b(t1+t2))
	) /\
	((l = (a SBEFORE b)) =
		T /\
	        (!t. l t = ~b t /\ (a t \/ l(SUC t))) /\
		(!t1.?t2. l(t1+t2) ==> a(t1+t2) \/ b(t1+t2))
	) /\
	((l = (a UNTIL b)) =
		T /\
	        (!t. l t = ~b t ==> a t /\ l(SUC t)) /\
		(!t1.?t2. ~l(t1+t2) ==> ~a(t1+t2) \/ b(t1+t2))
	) /\
	((l = (a WHEN b)) =
		T /\
	        (!t. l t = (if b t then a t else l(SUC t))) /\
		(!t1.?t2. l(t1+t2) \/ b(t1+t2))
	) /\
	((l = (a BEFORE b)) =
		T /\
	        (!t. l t = ~b t /\ (a t \/ l(SUC t))) /\
		(!t1.?t2. ~l(t1+t2) ==> a(t1+t2) \/ b(t1+t2))
	) /\
	((l = PNEXT a)
		 =
		(l 0 = T) /\
		(!t. l(SUC t) = a t) /\
		T
	) /\
	((l = PSNEXT a)
		 =
		(l 0 = F) /\
		(!t. l(SUC t) = a t) /\
		T
	) /\
	((l = PNEXT(PALWAYS a))
		 =
		(l 0 = T) /\
		(!t. l(SUC t) = a t /\ l t) /\
		T
	) /\
	((l = PSNEXT(PEVENTUAL a))
		 =
		(l 0 = F) /\
		(!t. l(SUC t) = a t \/ l t)  /\
		T
	) /\
	((l = PSNEXT(a PSUNTIL b))
		 =
		(l 0 = F) /\
		(!t. l(SUC t) = b t \/ a t /\ l t) /\
		T
	) /\
	((l = PSNEXT(a PSWHEN b))
		 =
		(l 0 = F) /\
		(!t. l(SUC t) = a t /\ b t \/ ~b t /\ l t) /\
		T
	) /\
	((l = PSNEXT(a PSBEFORE b))
		 =
		(l 0 = F) /\
		(!t. l(SUC t) = ~b t /\ (a t \/ l t))   /\
		T
	) /\
	((l = PNEXT(a PUNTIL b))
		 =
		(l 0 = T) /\
		(!t. l(SUC t) = b t \/ a t /\ l t) /\
		T
	) /\
	((l = PNEXT(a PWHEN b))
		 =
		(l 0 = T) /\
		(!t. l(SUC t) = a t /\ b t \/ ~b t /\ l t) /\
		T
	) /\
	((l = PNEXT(a PBEFORE b))
		 =
		(l 0 = T) /\
		(!t. l(SUC t) = ~b t /\ (a t \/ l t)) /\
		T
	)
	`--),
	REWRITE_TAC[
		PSNEXT_PEVENTUAL2OMEGA,PSNEXT_PALWAYS2OMEGA,
		PSNEXT_PSUNTIL2OMEGA,PSNEXT_PUNTIL2OMEGA,
		PSNEXT_PSWHEN2OMEGA,PSNEXT_PWHEN2OMEGA,
		PSNEXT_PSBEFORE2OMEGA,PSNEXT_PBEFORE2OMEGA
		]
	THEN REWRITE_TAC[
		ADD1,
		ALWAYS2BUECHI_THM,EVENTUAL2BUECHI_THM,
		SUNTIL2BUECHI_THM,UNTIL2BUECHI_THM,
		WHEN2BUECHI_THM,SWHEN2BUECHI_THM,
		SBEFORE2BUECHI_THM,BEFORE2BUECHI_THM
		]
	THEN CONV_TAC(DEPTH_CONV FUN_EQ_CONV)
	THEN REWRITE_TAC[NEXT] THEN BETA_TAC THEN REWRITE_TAC[ADD1]
	THEN CONJ_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC
	THENL[
	    ASM_REWRITE_TAC[INITIALISATION],
	    ASM_REWRITE_TAC[PNEXT,SYM(SPEC_ALL ADD1),PRE,ZERO_LEMMA],
	    SPEC_TAC((--`n:num`--),(--`n:num`--)) THEN INDUCT_TAC
	    THEN ASM_REWRITE_TAC[INITIALISATION,ADD1]
	    THEN REWRITE_TAC[PNEXT,SYM(SPEC_ALL ADD1),PRE,ZERO_LEMMA],
	    UNDISCH_HD_TAC THEN ASM_REWRITE_TAC[INITIALISATION],
	    ASM_REWRITE_TAC[PSNEXT,SYM(SPEC_ALL ADD1),PRE,ZERO_LEMMA],
	    SPEC_TAC((--`n:num`--),(--`n:num`--)) THEN INDUCT_TAC
	    THEN ASM_REWRITE_TAC[INITIALISATION,ADD1]
	    THEN REWRITE_TAC[PSNEXT,SYM(SPEC_ALL ADD1),PRE,ZERO_LEMMA]
	    ]
	);



(*---------------------------------------------------------------------------
       Closure theorems, leading to a translation theorem.
 ---------------------------------------------------------------------------*)

val AUTOMATON_AUTOMATON_CLOSURE = TAC_PROOF(
	([],--` (?q1:num->'a.
			Phi_I1(q1) /\
			Phi_R1(q1) /\
			?q2:num->'b.
			    Phi_I2(q2) /\
			    Phi_R2(q2,q1) /\
			    Phi_F(q1,q2)
		 )
		=
		?q1:num->'a. ?q2:num->'b.
			(Phi_I1(q1) /\ Phi_I2(q2)) /\
			(Phi_R1(q1) /\ Phi_R2(q2,q1)) /\
			Phi_F(q1,q2)
		`--),
	EQ_TAC THEN REPEAT STRIP_TAC
	THENL[
	    EXISTS_TAC(--`q1:num->'a`--) THEN EXISTS_TAC(--`q2:num->'b`--)
	    THEN ASM_REWRITE_TAC[],
	    EXISTS_TAC(--`q1:num->'a`--) THEN ASM_REWRITE_TAC[]
	    THEN EXISTS_TAC(--`q2:num->'b`--) THEN ASM_REWRITE_TAC[]
	    ]);


val AUTOMATON_NEXT_CLOSURE = TAC_PROOF(
	([],--` Phi(NEXT phi)
		= ? q0 q1.
			(!t. (q0(t) = phi(t)) /\ (q1(t) = q0(t+1)))
			/\ Phi(q1)
		`--),
	EQ_TAC THEN REPEAT STRIP_TAC
	THENL[
	    EXISTS_TAC (--`phi:num->bool`--) THEN EXISTS_TAC(--`NEXT phi`--)
	    THEN ASM_REWRITE_TAC[] THEN REWRITE_TAC[NEXT,num_CONV(--`1`--),ADD_CLAUSES]
	    THEN BETA_TAC THEN REWRITE_TAC[],
	    MY_MP_TAC (--`NEXT phi = q1`--)
	    THENL[
		CONV_TAC FUN_EQ_CONV THEN ASM_REWRITE_TAC[NEXT,num_CONV(--`1`--),ADD_CLAUSES]
	        THEN BETA_TAC THEN REWRITE_TAC[],
		DISCH_TAC]
	    THEN ASM_REWRITE_TAC[]
	    ]);




val AUTOMATON_PNEXT_CLOSURE = TAC_PROOF(
	([],--` Phi(PNEXT phi)
		= ?q.
			q(0) /\
			(!t. q(t+1) = phi(t))
			/\ Phi(q)
		`--),
	EQ_TAC THEN REPEAT STRIP_TAC
	THENL[
	    EXISTS_TAC(--`PNEXT phi`--) THEN ASM_REWRITE_TAC[]
	    THEN REWRITE_TAC[SYM(SPEC_ALL ADD1),PNEXT,PRE]
	    THEN REWRITE_TAC[EQT_ELIM(ARITH_CONV(--`~(SUC t = 0)`--))],
	    MY_MP_TAC (--`PNEXT phi = q`--)
	    THENL[
		CONV_TAC FUN_EQ_CONV
		THEN INDUCT_TAC THEN ASM_REWRITE_TAC[PNEXT,PRE,ADD1]
	    	THEN REWRITE_TAC[EQT_ELIM(ARITH_CONV(--`~(t+1 = 0)`--))],
		DISCH_TAC]
	    THEN ASM_REWRITE_TAC[]
	    ]);




val AUTOMATON_PSNEXT_CLOSURE = TAC_PROOF(
	([],--` Phi(PSNEXT phi)
		= ?q.
			~q(0) /\
			(!t. q(t+1) = phi(t))
			/\ Phi(q)
		`--),
	EQ_TAC THEN REPEAT STRIP_TAC
	THENL[
	    EXISTS_TAC(--`PSNEXT phi`--) THEN ASM_REWRITE_TAC[]
	    THEN REWRITE_TAC[SYM(SPEC_ALL ADD1),PSNEXT,PRE]
	    THEN REWRITE_TAC[EQT_ELIM(ARITH_CONV(--`~(0<0)`--))]
	    THEN REWRITE_TAC[EQT_ELIM(ARITH_CONV(--`(0<SUC t)`--))]
	    THEN ASM_REWRITE_TAC[],
	    MY_MP_TAC (--`PSNEXT phi = q`--)
	    THENL[
		CONV_TAC FUN_EQ_CONV
		THEN INDUCT_TAC THEN ASM_REWRITE_TAC[PSNEXT,PRE,ADD1]
	    	THEN REWRITE_TAC[EQT_ELIM(ARITH_CONV(--`~(0<0)`--))]
	    	THEN REWRITE_TAC[EQT_ELIM(ARITH_CONV(--`(0<t+1)`--))],
		DISCH_TAC]
	    THEN ASM_REWRITE_TAC[]
	    ]);





fun AUTOMATON_CLOSURE_TAC t1 t2 =
	EQ_TAC THEN REPEAT STRIP_TAC
	THENL[
	    EXISTS_TAC t1 THEN ASM_REWRITE_TAC[INITIALISATION,PNEXT]
	    THEN REWRITE_TAC[SYM(SPEC_ALL ADD1),PSNEXT,PRE]
	    THEN REWRITE_TAC[EQT_ELIM(ARITH_CONV(--`~(0<0)`--))]
	    THEN REWRITE_TAC[EQT_ELIM(ARITH_CONV(--`(0<SUC t)`--))]
	    THEN REWRITE_TAC[EQT_ELIM(ARITH_CONV(--`~(SUC t=0)`--))]
	    THEN GEN_TAC THEN CONV_TAC(LHS_CONV(ONCE_REWRITE_CONV[RECURSION]))
	    THEN BETA_TAC THEN REWRITE_TAC[PSNEXT,PNEXT],
	    MY_MP_TAC t2
	    THENL[
		CONV_TAC FUN_EQ_CONV
		THEN INDUCT_TAC THEN ASM_REWRITE_TAC[PSNEXT,PNEXT,PRE,ADD1]
	    	THEN REWRITE_TAC[EQT_ELIM(ARITH_CONV(--`~(0<0)`--)),INITIALISATION]
	    	THEN REWRITE_TAC[EQT_ELIM(ARITH_CONV(--`(0<t+1)`--))]
	    	THEN REWRITE_TAC[EQT_ELIM(ARITH_CONV(--`~(t+1=0)`--))]
		THEN ONCE_REWRITE_TAC[RECURSION] THEN BETA_TAC
	        THEN ASM_REWRITE_TAC[],
		DISCH_TAC]
	    THEN ASM_REWRITE_TAC[]
	    ];

val AUTOMATON_PSUNTIL_CLOSURE = TAC_PROOF(
	([],--` Phi(PSNEXT(a PSUNTIL b))
		= ?q.
			~q(0) /\
			(!t. q(t+1) =  b t \/ a t /\ q t)
			/\ Phi(q)
		`--),
	AUTOMATON_CLOSURE_TAC (--`PSNEXT(a PSUNTIL b)`--) (--`PSNEXT(a PSUNTIL b) = q`--)
	);


val AUTOMATON_PBEFORE_CLOSURE = TAC_PROOF(
	([],--` Phi(PNEXT(a PBEFORE b))
		= ?q.
			q(0) /\
			(!t. q(t+1) = ~b t /\ (a t \/ q t))
			/\ Phi(q)
		`--),
	AUTOMATON_CLOSURE_TAC (--`PNEXT(a PBEFORE b)`--) (--`PNEXT(a PBEFORE b) = q`--)
	);


val AUTOMATON_PALWAYS_CLOSURE = TAC_PROOF(
	([],--` Phi(PNEXT(PALWAYS a))
		= ?q.
			q(0) /\
			(!t. q(t+1) = a t /\ q t)
			/\ Phi(q)
		`--),
	REWRITE1_TAC PBEFORE_EXPRESSIVE THEN CONV_TAC(DEPTH_CONV ETA_CONV)
	THEN REWRITE_TAC[AUTOMATON_PBEFORE_CLOSURE]
	THEN BETA_TAC THEN REWRITE_TAC[]);


val AUTOMATON_PEVENTUAL_CLOSURE = TAC_PROOF(
	([],--` Phi(PSNEXT(PEVENTUAL a))
		= ?q.
			~q(0) /\
			(!t. q(t+1) = a t \/ q t)
			/\ Phi(q)
		`--),
	REWRITE1_TAC PSUNTIL_EXPRESSIVE THEN CONV_TAC(DEPTH_CONV ETA_CONV)
	THEN REWRITE_TAC[AUTOMATON_PSUNTIL_CLOSURE]
	THEN BETA_TAC THEN REWRITE_TAC[]);


val AUTOMATON_PSWHEN_CLOSURE = TAC_PROOF(
	([],--` Phi(PSNEXT(a PSWHEN b))
		= ?q.
			~q(0) /\
			(!t. q(t+1) = a t /\ b t \/ ~b t /\ q t)
			/\ Phi(q)
		`--),
	REWRITE1_TAC PSUNTIL_EXPRESSIVE THEN CONV_TAC(DEPTH_CONV ETA_CONV)
	THEN REWRITE_TAC[AUTOMATON_PSUNTIL_CLOSURE]
	THEN BETA_TAC THEN REWRITE_TAC[]);


val AUTOMATON_PSBEFORE_CLOSURE = TAC_PROOF(
	([],--` Phi(PSNEXT(a PSBEFORE b))
		= ?q.
			~q(0) /\
			(!t. q(t+1) = ~b t /\(a t \/ q t))
			/\ Phi(q)
		`--),
	REWRITE1_TAC PSUNTIL_EXPRESSIVE THEN CONV_TAC(DEPTH_CONV ETA_CONV)
	THEN REWRITE_TAC[AUTOMATON_PSUNTIL_CLOSURE]
	THEN BETA_TAC
	THEN REWRITE_TAC[TAC_PROOF(([],--`a/\~b\/~b/\q = ~b/\(a\/q)`--),PROP_TAC)]);


val AUTOMATON_PUNTIL_CLOSURE = TAC_PROOF(
	([],--` Phi(PNEXT(a PUNTIL b))
		= ?q.
			q(0) /\
			(!t. q(t+1) = b t \/ a t /\ q t)
			/\ Phi(q)
		`--),
	REWRITE1_TAC PBEFORE_EXPRESSIVE THEN CONV_TAC(DEPTH_CONV ETA_CONV)
	THEN REWRITE_TAC[AUTOMATON_PBEFORE_CLOSURE]
	THEN BETA_TAC
	THEN REWRITE_TAC[TAC_PROOF(([],--`~(~a/\~b)/\(b\/q) = b\/a/\q`--),PROP_TAC)]);


val AUTOMATON_PWHEN_CLOSURE = TAC_PROOF(
	([],--` Phi(PNEXT(a PWHEN b))
		= ?q.
			q(0) /\
			(!t. q(t+1) = a t /\ b t \/ ~b t /\ q t)
			/\ Phi(q)
		`--),
	REWRITE1_TAC PBEFORE_EXPRESSIVE THEN CONV_TAC(DEPTH_CONV ETA_CONV)
	THEN REWRITE_TAC[AUTOMATON_PBEFORE_CLOSURE]
	THEN BETA_TAC
	THEN REWRITE_TAC[TAC_PROOF(([],--`~(~a/\b)/\(a/\b\/q) = a/\b\/~b/\q`--),PROP_TAC)]);





val AUTOMATON_TEMP_CLOSURE = TAC_PROOF(
	([],--`
	((?q1:num->'a.
			Phi_I1(q1) /\
			Phi_R1(q1) /\
			?q2:num->'b.
			    Phi_I2(q2) /\
			    Phi_R2(q2,q1) /\
			    Phi_F(q1,q2)
		 )
		=
		?q1:num->'a. ?q2:num->'b.
			(Phi_I1(q1) /\ Phi_I2(q2)) /\
			(Phi_R1(q1) /\ Phi_R2(q2,q1)) /\
			Phi_F(q1,q2)
	) /\
	(Phi(NEXT phi)
		= ? q0 q1.
			T /\
			(!t. (q0(t) = phi(t)) /\ (q1(t) = q0(t+1)))
			/\ Phi(q1)
	) /\
	(Phi(PNEXT phi)
		= ?q.
			q(0) /\
			(!t. q(t+1) = phi(t))
			/\ Phi(q)
	) /\
	(Phi(PSNEXT phi)
		= ?q.
			~q(0) /\
			(!t. q(t+1) = phi(t))
			/\ Phi(q)
	) /\
	(Phi(PNEXT(PALWAYS a))
		= ?q.
			q(0) /\
			(!t. q(t+1) = a t /\ q t)
			/\ Phi(q)
	) /\
	(Phi(PSNEXT(PEVENTUAL a))
		= ?q.
			~q(0) /\
			(!t. q(t+1) = a t \/ q t)
			/\ Phi(q)
	) /\
	(Phi(PSNEXT(a PSUNTIL b))
		= ?q.
			~q(0) /\
			(!t. q(t+1) =  b t \/ a t /\ q t)
			/\ Phi(q)
	) /\
	(Phi(PSNEXT(a PSWHEN b))
		= ?q.
			~q(0) /\
			(!t. q(t+1) = a t /\ b t \/ ~b t /\ q t)
			/\ Phi(q)
	) /\
	(Phi(PSNEXT(a PSBEFORE b))
		= ?q.
			~q(0) /\
			(!t. q(t+1) = ~b t /\(a t \/ q t))
			/\ Phi(q)
	) /\
	(Phi(PNEXT(a PUNTIL b))
		= ?q.
			q(0) /\
			(!t. q(t+1) = b t \/ a t /\ q t)
			/\ Phi(q)
	) /\
	(Phi(PNEXT(a PWHEN b))
		= ?q.
			q(0) /\
			(!t. q(t+1) = a t /\ b t \/ ~b t /\ q t)
			/\ Phi(q)
	) /\
	(Phi(PNEXT(a PBEFORE b))
		= ?q.
			q(0) /\
			(!t. q(t+1) = ~b t /\ (a t \/ q t))
			/\ Phi(q)
	)
	`--),
	REPEAT CONJ_TAC
	THENL[
	    REWRITE_TAC[AUTOMATON_AUTOMATON_CLOSURE],
	    REWRITE_TAC[AUTOMATON_NEXT_CLOSURE],
	    REWRITE_TAC[AUTOMATON_PNEXT_CLOSURE],
	    REWRITE_TAC[AUTOMATON_PSNEXT_CLOSURE],
	    REWRITE_TAC[AUTOMATON_PALWAYS_CLOSURE],
	    REWRITE_TAC[AUTOMATON_PEVENTUAL_CLOSURE],
	    REWRITE_TAC[AUTOMATON_PSUNTIL_CLOSURE],
	    REWRITE_TAC[AUTOMATON_PSWHEN_CLOSURE],
	    REWRITE_TAC[AUTOMATON_PSBEFORE_CLOSURE],
	    REWRITE_TAC[AUTOMATON_PUNTIL_CLOSURE],
	    REWRITE_TAC[AUTOMATON_PWHEN_CLOSURE],
	    REWRITE_TAC[AUTOMATON_PBEFORE_CLOSURE]
	]);









val BUECHI_TRANSLATION = TAC_PROOF(
	([],--`
	(Phi(NEXT phi)
		= ? q0 q1.
			T /\
			(!t. (q0(t) = phi(t)) /\ (q1(t) = q0(t+1)))
			/\ Phi(q1)
	) /\
	(Phi(ALWAYS a) =
	    ?q.
		T /\
		(!t. q t = a t /\ q(t+1)) /\
		( (!t1.?t2. a(t1+t2) ==> q(t1+t2)) /\ Phi(q) )
	) /\
	(Phi(EVENTUAL a) =
	    ?q.
		T /\
		(!t. q t = a t \/ q(t+1)) /\
		( (!t1.?t2. q(t1+t2) ==> a(t1+t2)) /\ Phi(q) )
	) /\
	(Phi(a SUNTIL b) =
	    ?q.
		T /\
		(!t. q t = b t \/ a t /\ q(t+1)) /\
		( (!t1.?t2. q(t1+t2) ==> ~a(t1+t2) \/ b(t1+t2)) /\ Phi(q) )
	) /\
	(Phi(a UNTIL b) =
	    ?q.
		T /\
		(!t. q t = b t \/ a t /\ q(t+1)) /\
		( (!t1.?t2. ~q(t1+t2) ==> ~a(t1+t2) \/ b(t1+t2)) /\ Phi(q) )
	) /\
	(Phi(a SWHEN b) =
	    ?q.
		T /\
		(!t. q t = (if b t then a t else q(t+1))) /\
		( (!t1.?t2. q(t1+t2) ==> b(t1+t2)) /\ Phi(q) )
	) /\
	(Phi(a WHEN b) =
	    ?q.
		T /\
		(!t. q t = (if b t then a t else q(t+1))) /\
		( (!t1.?t2. q(t1+t2) \/ b(t1+t2)) /\ Phi(q) )
	) /\
	(Phi(a SBEFORE b) =
	    ?q.
		T /\
		(!t. q t = ~b t /\ (a t \/ q(t+1))) /\
		( (!t1.?t2. q(t1+t2) ==> a(t1+t2) \/ b(t1+t2)) /\ Phi(q) )
	) /\
	(Phi(a BEFORE b) =
	    ?q.
		T /\
		(!t. q t = ~b t /\ (a t \/ q(t+1))) /\
		( (!t1.?t2. ~q(t1+t2) ==> a(t1+t2) \/ b(t1+t2)) /\ Phi(q) )
	)
	`--),
	REWRITE_TAC[AUTOMATON_NEXT_CLOSURE]
	THEN REWRITE_TAC[TAC_PROOF(([],--`a/\(b/\c) = (a/\b)/\c`--),PROP_TAC)]
	THEN REWRITE_TAC[TAC_PROOF(([],--`b\/a/\q = ~b==>a/\q`--),PROP_TAC)]
	THEN REWRITE_TAC(map SYM (CONJUNCTS (REWRITE_RULE[ADD1]TEMP_OPS_DEFS_TO_OMEGA)))
	THEN REPEAT CONJ_TAC THEN EQ_TAC THEN STRIP_TAC
	THENL[
	    EXISTS_TAC(--`ALWAYS a`--) THEN ASM_REWRITE_TAC[],
	    POP_NO_ASSUM 1 (SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[],
	    EXISTS_TAC(--`EVENTUAL a`--) THEN ASM_REWRITE_TAC[],
	    POP_NO_ASSUM 1 (SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[],
	    EXISTS_TAC(--`a SUNTIL b`--) THEN ASM_REWRITE_TAC[],
	    POP_NO_ASSUM 1 (SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[],
	    EXISTS_TAC(--`a UNTIL b`--) THEN ASM_REWRITE_TAC[],
	    POP_NO_ASSUM 1 (SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[],
	    EXISTS_TAC(--`a SWHEN b`--) THEN ASM_REWRITE_TAC[],
	    POP_NO_ASSUM 1 (SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[],
	    EXISTS_TAC(--`a WHEN b`--) THEN ASM_REWRITE_TAC[],
	    POP_NO_ASSUM 1 (SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[],
	    EXISTS_TAC(--`a SBEFORE b`--) THEN ASM_REWRITE_TAC[],
	    POP_NO_ASSUM 1 (SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[],
	    EXISTS_TAC(--`a BEFORE b`--) THEN ASM_REWRITE_TAC[],
	    POP_NO_ASSUM 1 (SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[]
	]);



(*---------------------------------------------------------------------------
   Co-Buechi closure theorems.
 ---------------------------------------------------------------------------*)


(* ========================== CO_BUECHI_CONJ_CLOSURE ==================================	*)
(*											*)
(* Co-Buechi automata are closed under conjunction. The conjunction is computed as:	*)
(*											*)
(*  |- (?q1.										*)
(*       Phi_I1(q1 t0) /\								*)
(*       (!t. Phi_R1(i(t+t0),q1(t+t0))) /\						*)
(*       (?t1. !t2. Psi1(i(t1+t2+t0),q1(t1+t2+t0)))					*)
(*     ) 										*)
(*     /\										*)
(*     (?q2.										*)
(*       Phi_I2(q2 t0) /\								*)
(*       (!t. Phi_R2(i(t+t0),q2(t+t0))) /\						*)
(*       (?t1. !t2. Psi2(i(t1+t2+t0),q2(t1+t2+t0)))					*)
(*     )										*)
(*     =										*)
(*     (?q1 q2.										*)
(*       (Phi_I1(q1 t0) /\ Phi_I2(q2 t0)) /\						*)
(*       (!t.Phi_R1(i(t+t0),q1(t+t0)) /\ Phi_R2(i(t+t0),q2(t+t0))) /\			*)
(*       (?t1. !t2. Psi1(i(t1+t2+t0),q1(t1+t2+t0)) /\ Psi2(i(t1+t2+t0),q2(t1+t2+t0)))	*)
(*     )										*)
(*											*)
(* ====================================================================================	*)

val CO_BUECHI_CONJ_CLOSURE = TAC_PROOF(
    let val cb1 = (--`?q1.
          	    	Phi_I1(q1 t0) /\
                    	(!t. Phi_R1((i(t+t0):'a),(q1(t+t0):'b1))) /\
                    	(?t1. !t2. Psi1(i(t1+(t2+t0)),q1(t1+(t2+t0))))`--)
        val cb2 = (--`?q2.
          	    	Phi_I2(q2 t0) /\
                    	(!t. Phi_R2((i(t+t0):'a),(q2(t+t0):'b2))) /\
                    	(?t1. !t2. Psi2(i(t1+(t2+t0)),q2(t1+(t2+t0))))`--)
     in
	([],--`(^cb1 /\ ^cb2)
	  = ? q1 q2.
		(Phi_I1(q1 t0) /\ Phi_I2(q2 t0)) /\
		(!t. Phi_R1((i(t+t0):'a),(q1(t+t0):'b1)) /\
		     Phi_R2((i(t+t0):'a),(q2(t+t0):'b2))
		) /\
        	?t1. !t2. Psi1(i(t1+(t2+t0)),q1(t1+(t2+t0))) /\
			  Psi2(i(t1+(t2+t0)),q2(t1+(t2+t0)))
	`--)
    end,
	REWRITE_TAC[
		REWRITE_RULE[SYM(SPEC_ALL ADD_ASSOC)]
		    (SYM(BETA_RULE
			(SPECL[(--`\t:num. Psi1(((i t):'a),((q1 t):'b1)):bool`--),
			       (--`\t:num. Psi2(((i t):'a),((q2 t):'b2)):bool`--)
			       ] CONJ_FG )))]
	THEN EQ_TAC THEN REPEAT STRIP_TAC
	THENL[
	    EXISTS_TAC(--`q1:num->'b1`--) THEN EXISTS_TAC(--`q2:num->'b2`--),
	    EXISTS_TAC(--`q1:num->'b1`--),
	    EXISTS_TAC(--`q2:num->'b2`--)
	    ]
	THEN ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC
	THENL[
	    EXISTS_TAC(--`t1:num`--) THEN ASM_REWRITE_TAC[],
	    EXISTS_TAC(--`t1':num`--) THEN ASM_REWRITE_TAC[],
	    EXISTS_TAC(--`t1:num`--) THEN ASM_REWRITE_TAC[],
	    EXISTS_TAC(--`t1':num`--) THEN ASM_REWRITE_TAC[]
	    ])
;



(* ========================== CO_BUECHI_DISJ_CLOSURE ==================================	*)
(*											*)
(* Co-Buechi automata are closed under disjunction. The disjunction is computed as:	*)
(*											*)
(*  |- (?q1.										*)
(*       Phi_I1(q1 t0) /\								*)
(*       (!t. Phi_R1(i(t+t0),q1(t+t0))) /\						*)
(*       (?t1. !t2. Psi1(i(t1+t2+t0),q1(t1+t2+t0)))					*)
(*     ) 										*)
(*     \/										*)
(*     (?q2.										*)
(*       Phi_I2(q2 t0) /\								*)
(*       (!t. Phi_R2(i(t+t0),q2(t+t0))) /\						*)
(*       (?t1. !t2. Psi2(i(t1+t2+t0),q2(t1+t2+t0)))					*)
(*     )										*)
(*     =										*)
(*     (?p q1 q2. 									*)
(*		(~p(t0) /\ Phi_I1(q1 t0) \/						*)
(*	          p(t0) /\ Phi_I2(q2 t0)						*)
(*                ) /\									*)
(*		(!t. ~p(t+t0) /\ Phi_R1((i(t+t0):'a),(q1(t+t0):'b1)) /\ ~p(t+t0+1)  \/	*)
(*		      p(t+t0) /\ Phi_R2((i(t+t0):'a),(q2(t+t0):'b2)) /\  p(t+t0+1) 	*)
(*		) /\									*)
(*        	?t1. !t2. ~p(t+t0) /\ Psi1(i(t1+t2+t0),q1(t1+t2+t0)) \/			*)
(*			   p(t+t0) /\ Psi2(i(t1+t2+t0),q2(t1+t2+t0))			*)
(*     )										*)
(*											*)
(* ====================================================================================	*)

val CO_BUECHI_DISJ_CLOSURE = TAC_PROOF(
    let val cb1 = (--`?q1.
          	    	Phi_I1(q1 t0) /\
                    	(!t. Phi_R1((i(t+t0):'a),(q1(t+t0):'b1))) /\
                    	(?t1. !t2. Psi1(i(t1+(t2+t0)),q1(t1+(t2+t0))))`--)
        val cb2 = (--`?q2.
          	    	Phi_I2(q2 t0) /\
                    	(!t. Phi_R2((i(t+t0):'a),(q2(t+t0):'b2))) /\
                    	(?t1. !t2. Psi2(i(t1+(t2+t0)),q2(t1+(t2+t0))))`--)
     in
	([],--`(^cb1 \/ ^cb2)
	  = ?p q1 q2.
		(~p(t0) /\ Phi_I1(q1 t0) \/
	          p(t0) /\ Phi_I2(q2 t0)
                ) /\
		(!t. ~p(t+t0) /\ Phi_R1((i(t+t0):'a),(q1(t+t0):'b1)) /\ ~p(t+(t0+1))  \/
		      p(t+t0) /\ Phi_R2((i(t+t0):'a),(q2(t+t0):'b2)) /\  p(t+(t0+1))
		) /\
        	?t1. !t2. ~p(t+t0) /\ Psi1(i(t1+(t2+t0)),q1(t1+(t2+t0))) \/
			   p(t+t0) /\ Psi2(i(t1+(t2+t0)),q2(t1+(t2+t0)))
	`--)
    end,
    EQ_TAC THEN REPEAT STRIP_TAC
    THENL[
	EXISTS_TAC (--`\t:num.F`--)
	THEN EXISTS_TAC (--`q1:num->'b1`--) THEN EXISTS_TAC (--`q2:num->'b2`--)
	THEN ASM_REWRITE_TAC[]
	THEN EXISTS_TAC (--`t1:num`--) THEN ASM_REWRITE_TAC[],
	EXISTS_TAC (--`\t:num.T`--)
	THEN EXISTS_TAC (--`q1:num->'b1`--) THEN EXISTS_TAC (--`q2:num->'b2`--)
	THEN ASM_REWRITE_TAC[]
	THEN EXISTS_TAC (--`t1:num`--) THEN ASM_REWRITE_TAC[],
	MY_MP_TAC (--`!t. ~p(t+t0)`--)
	THENL[
	    INDUCT_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES]
	    THEN LEFT_NO_FORALL_TAC 2 (--`t':num`--)
	    THEN UNDISCH_HD_TAC
	    THEN ASM_REWRITE_TAC[ADD_CLAUSES,SYM(SPEC_ALL ADD1)]
	    THEN STRIP_TAC,
	    DISCH_TAC
	    ]
	THEN DISJ1_TAC THEN EXISTS_TAC(--`q1:num->'b1`--)
	THEN POP_ASSUM (fn x => RULE_ASSUM_TAC(REWRITE_RULE[x]) THEN ASSUME_TAC x)
	THEN ASM_REWRITE_TAC[]
	THEN EXISTS_TAC (--`t1:num`--) THEN ASM_REWRITE_TAC[],
	MY_MP_TAC (--`!t. p(t+t0)`--)
	THENL[
	    INDUCT_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES]
	    THEN LEFT_NO_FORALL_TAC 2 (--`t':num`--)
	    THEN UNDISCH_HD_TAC
	    THEN ASM_REWRITE_TAC[ADD_CLAUSES,SYM(SPEC_ALL ADD1)]
	    THEN STRIP_TAC,
	    DISCH_TAC
	    ]
	THEN DISJ2_TAC THEN EXISTS_TAC(--`q2:num->'b2`--)
	THEN POP_ASSUM (fn x => RULE_ASSUM_TAC(REWRITE_RULE[x]) THEN ASSUME_TAC x)
	THEN ASM_REWRITE_TAC[]
	THEN EXISTS_TAC (--`t1:num`--) THEN ASM_REWRITE_TAC[]
	])
;




(* ========================== CO_BUECHI_NEXT_CLOSURE ==================================	*)
(*											*)
(* The next theorem shows that co-Buechi automata are closed under an appliation of a 	*)
(* NEXT operator.									*)
(*											*)
(*  |- (NEXT										*)
(*      (\t0.										*)
(*        ?q.										*)
(*          Phi_I (q t0) /\								*)
(*          (!t. Phi_R (i (t+t0),q (t+t0))) /\						*)
(*          (?t1. !t2. Psi (i (t1+t2+t0),q (t1+t2+t0)))))				*)
(*       t0 =										*)
(*     (?p q. 										*)
(*		((p t0 = F) /\ (q t0 = c)) /\						*)
(*		(!t. 									*)
(*		        (~p(t+t0) /\ (q(t+t0) = c) /\ p(t+t0+1) /\ Phi_I(q(t+t0+1))) 	*)
(*		     \/ ( p(t+t0) /\ Phi_R((i(t+t0):'a),(q(t+t0):'b)) /\ p(t+t0+1))	*)
(*		) /\									*)
(*       	?t1. !t2. Psi(i(t1+t2+t0),q(t1+t2+t0))					*)
(*											*)
(* ====================================================================================	*)

val NEXT2 = prove(``NEXT P x = P (SUC x)``,
                  REWRITE_TAC [NEXT] THEN BETA_TAC THEN REWRITE_TAC []);

val CO_BUECHI_NEXT_CLOSURE = TAC_PROOF(
    let val cb = (--`?q.
          	    Phi_I(q t0) /\
                    (!t. Phi_R((i(t+t0):'a),(q(t+t0):'b))) /\
                    (?t1. !t2. Psi(i(t1+(t2+t0)),q(t1+(t2+t0))))`--)
     in
	([],--`(NEXT (\t0:num. ^cb)) t0
	  = ?p q.
		((p t0 = F) /\ (q t0 = c)) /\
		(!t.
		     (~p(t+t0) /\ (q(t+t0) = c) /\ p(t+(t0+1)) /\ Phi_I(q(t+(t0+1))))
		     \/
		     ( p(t+t0) /\ Phi_R((i(t+t0):'a),(q(t+t0):'b)) /\ p(t+(t0+1)))
		) /\
        	?t1. !t2. Psi(i(t1+(t2+t0)),q(t1+(t2+t0)))
	`--)
    end,
	PURE_REWRITE_TAC[NEXT2] THEN BETA_TAC
	THEN EQ_TAC THEN REPEAT STRIP_TAC
	THENL[
	(* ----------------------------------------------------------------------------	*)
	(* first implication: from left to right    					*)
	(* ----------------------------------------------------------------------------	*)
	EXISTS_TAC(--`\t:num.t0<t`--)
	THEN EXISTS_TAC (--`\t:num. if (t=t0) then (c:'b) else q t`--)
	THEN BETA_TAC THEN REWRITE_TAC[EQT_ELIM(ARITH_CONV(--`~(x<x)`--))]
	THEN REPEAT STRIP_TAC
	THENL[
	    (* ----------------------------------------------------------------	*)
	    (* correctness of transition relation 				*)
	    (* ----------------------------------------------------------------	*)
	    DISJ_CASES_TAC(EQT_ELIM(ARITH_CONV(--`(t=0) \/ (0<t)`--)))
	    THENL[
		ASM_REWRITE_TAC[ADD_CLAUSES,LESS_REFL,
				 EQT_ELIM(ARITH_CONV(--`(x<x+1)`--)),
				 EQT_ELIM(ARITH_CONV(--`~(x+1=x)`--))]
	    	THEN UNDISCH_NO_TAC 3 THEN REWRITE_TAC[ADD1],
		ASM_REWRITE_TAC[ EQT_ELIM(ARITH_CONV(--`(t0<t+t0) = (0<t)`--)),
				 EQT_ELIM(ARITH_CONV(--`(t+t0=t0) = ~(0<t)`--))]
		THEN IMP_RES_TAC LESS_ADD_1 THEN POP_ASSUM SUBST1_TAC
	 	THEN RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES])
		THEN ASM_REWRITE_TAC[ADD_CLAUSES,SYM(SPEC_ALL ADD1)]
	    	THEN CONV_TAC ARITH_CONV
		],
	    (* ----------------------------------------------------------------	*)
	    (* correctness of acceptance condition 				*)
	    (* ----------------------------------------------------------------	*)
	    EXISTS_TAC(--`SUC t1`--) THEN UNDISCH_HD_TAC
	    THEN REWRITE_TAC[ADD_CLAUSES,EQT_ELIM(ARITH_CONV(--`~(SUC(t1+(t2+t0)) = t0)`--))]
	    ],
	(* ----------------------------------------------------------------------------	*)
	(* second implication: from right to left  					*)
	(* ----------------------------------------------------------------------------	*)
	EXISTS_TAC (--`q:num->'b`--)
	THEN MY_MP_TAC (--`!t. p(t+(t0+1))`--)
	THENL[
	    INDUCT_TAC
	    THENL[
		LEFT_NO_FORALL_TAC 1 (--`0`--) THEN UNDISCH_HD_TAC
		THEN REWRITE_TAC[ADD_CLAUSES] THEN STRIP_TAC,
		LEFT_NO_FORALL_TAC 2 (--`t+1`--) THEN UNDISCH_HD_TAC
		THEN REWRITE_TAC[ADD_CLAUSES,SYM(SPEC_ALL ADD1)] THEN STRIP_TAC
		],
	    DISCH_TAC
	    ]
	THEN REPEAT STRIP_TAC
	THENL[
	    (* ----------------------------------------------------------------	*)
	    (* correctness of initial states	 				*)
	    (* ----------------------------------------------------------------	*)
	    LEFT_NO_FORALL_TAC 2 (--`0`--) THEN UNDISCH_HD_TAC
	    THEN ASM_REWRITE_TAC[ADD_CLAUSES,SYM(SPEC_ALL ADD1)],
	    (* ----------------------------------------------------------------	*)
	    (* correctness of transition relation 				*)
	    (* ----------------------------------------------------------------	*)
	    LEFT_NO_FORALL_TAC 2 (--`SUC t`--) THEN UNDISCH_HD_TAC
	    THEN UNDISCH_HD_TAC
	    THEN ASM_REWRITE_TAC[ADD_CLAUSES,SYM(SPEC_ALL ADD1)]
	    THEN DISCH_TAC THEN ASM_REWRITE_TAC[]
	    THEN STRIP_TAC,
	    (* ----------------------------------------------------------------	*)
	    (* correctness of acceptance condition 				*)
	    (* ----------------------------------------------------------------	*)
	    EXISTS_TAC (--`t1:num`--) THEN GEN_TAC
	    THEN ASM_REWRITE_TAC[EQT_ELIM(ARITH_CONV(--`t1+(t2+(SUC t0)) = t1+(SUC t2+t0)`--))]
	    ]
	])
;







(* ========================== CO_BUECHI_SUNTIL_CLOSURE ================================	*)
(*											*)
(* The next theorem shows that co-Buechi automata are closed under an appliation of a 	*)
(* SUNTIL operator, provided that the left hand side argument is propositional.		*)
(*											*)
(*  |- (phi SUNTIL									*)
(*      (\t0.										*)
(*        ?q.										*)
(*          Phi_I (q t0) /\								*)
(*          (!t. Phi_R (i (t+t0),q (t+t0))) /\						*)
(*          (?t1. !t2. Psi (i (t1+t2+t0),q (t1+t2+t0)))))				*)
(*       t0 =										*)
(*     (?p q.										*)
(*       ((p t0) => (Phi_I (q t0)) | (q t0 = c)) /\					*)
(*       (!t.										*)
(*         ~p(t+t0) /\ (q(t+t0) = c) /\ phi(t+t0) /\ ~p(t+t0+1) /\ (q(t+t0+1) = c) \/	*)
(*         ~p(t+t0) /\ (q(t+t0) = c) /\ phi(t+t0) /\  p(t+t0+1) /\ Phi_I(q(t+t0+1)) \/	*)
(*          p(t+t0) /\ Phi_R(i(t+t0),q(t+t0)) /\ p(t+t0+1)				*)
(*	 ) /\										*)
(*       (?t1. !t2. p(t1+t2+t0) /\ Psi(i(t1+t2+t0),q(t1+t2+t0))))			*)
(*											*)
(* ====================================================================================	*)



val SUNTIL_WEAK_SIGNAL = TAC_PROOF(
	([],--`(a SUNTIL b) t0 =
		?delta. (!t. t<delta ==> a(t+t0)) /\ b(delta+t0)`--),
	REWRITE_TAC[SUNTIL_SIGNAL] THEN EQ_TAC THEN STRIP_TAC
	THENL[
	    EXISTS_TAC(--`delta:num`--) THEN ASM_REWRITE_TAC[]
	    THEN REPEAT STRIP_TAC THEN RES_TAC,
	    ALL_TAC]
	THEN DISJ_CASES_TAC DELTA_CASES
	THENL[ALL_TAC,RES_TAC]
	THEN LEFT_EXISTS_TAC
	THEN MY_MP_TAC (--`d<=delta`--)
	THENL[
	    DISJ_CASES_TAC(SPECL[(--`delta:num`--),(--`d:num`--)]LESS_CASES)
	    THEN ASM_REWRITE_TAC[] THEN RES_TAC,
	    DISCH_TAC]
	THEN EXISTS_TAC(--`d:num`--) THEN ASM_REWRITE_TAC[]
	THEN REPEAT STRIP_TAC THEN RES_TAC
	THEN POP_NO_ASSUM 5 (fn x => MATCH_MP_TAC x)
	THEN UNDISCH_NO_TAC 1 THEN UNDISCH_NO_TAC 1
	THEN CONV_TAC ARITH_CONV
	);




val CO_BUECHI_SUNTIL_CLOSURE = TAC_PROOF(
    let val cb = (--`?q.
          	    Phi_I(q t0) /\
                    (!t. Phi_R((i(t+t0):'a),(q(t+t0):'b))) /\
                    (?t1. !t2. Psi(i(t1+(t2+t0)),q(t1+(t2+t0))))`--)
     in
	([],--`(phi SUNTIL (\t0:num. ^cb)) t0
	  = ?p q.
		(if p t0 then Phi_I(q t0) else (q t0 = c)) /\
		(!t.
		      ~p(t+t0) /\ (q(t+t0) = c) /\ phi(t+t0) /\ ~p(t+(t0+1)) /\  (q(t+(t0+1)) = c)
		  \/  ~p(t+t0) /\ (q(t+t0) = c) /\ phi(t+t0) /\  p(t+(t0+1)) /\  Phi_I(q(t+(t0+1)))
		  \/   p(t+t0) /\ Phi_R((i(t+t0):'a),(q(t+t0):'b)) /\ p(t+(t0+1))
		) /\
        	?t1. !t2. p(t1+(t2+t0)) /\ Psi(i(t1+(t2+t0)),q(t1+(t2+t0)))
	`--)
    end,
	PURE_REWRITE_TAC[SUNTIL_WEAK_SIGNAL] THEN BETA_TAC
	THEN EQ_TAC THEN REPEAT STRIP_TAC
	THENL[
	(* ----------------------------------------------------------------------------	*)
	(* first implication: from left to right    					*)
	(* ----------------------------------------------------------------------------	*)
	    DISJ_CASES_TAC(SPEC(--`delta:num`--)num_CASES)
	    THENL[
		(* ------ 2nd subgoal: delta = 0 --------------- *)
		POP_ASSUM (fn x=> RULE_ASSUM_TAC(REWRITE_RULE[x]))
		THEN RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES])
		THEN ASM_REWRITE_TAC[]
	        THEN EXISTS_TAC(--`\t:num.T`--) THEN EXISTS_TAC(--`q:num->'b`--)
	        THEN BETA_TAC THEN ASM_REWRITE_TAC[]
		THEN EXISTS_TAC (--`t1:num`--) THEN ASM_REWRITE_TAC[],
		(* ------ 2nd subgoal: delta > 0 --------------- *)
	    	LEFT_EXISTS_TAC THEN POP_ASSUM (fn x=> RULE_ASSUM_TAC(REWRITE_RULE[x]))
		THEN EXISTS_TAC(--`\t.t>n+t0`--) THEN EXISTS_TAC(--`\t. if t<=n+t0 then (c:'b) else q t`--)
	    	THEN BETA_TAC THEN REPEAT STRIP_TAC
		THENL[
		    (* ------------ correct initialization ------------	*)
		    REWRITE_TAC[ARITH_CONV(--`t0 <= n + t0`--)]
		    THEN REWRITE_TAC[EQT_ELIM(ARITH_CONV(--`~(t0 > n+t0)`--))],
		    (* ------------ correct transitions ---------------	*)
		    DISJ_CASES_TAC(SPECL[(--`n:num`--),(--`t:num`--)]LESS_LESS_CASES)
		    THENL[ALL_TAC,POP_ASSUM DISJ_CASES_TAC]
		    THENL[
			(* ------------ when the subautomaton starts --------	*)
			ASM_TAC 0 (fn x => REWRITE_TAC[(SYM x)])
			THEN DISJ2_TAC THEN DISJ1_TAC
			THEN REWRITE_TAC[EQT_ELIM(ARITH_CONV(--`~(n+t0 > n+t0)`--))]
			THEN REWRITE_TAC[EQT_ELIM(ARITH_CONV(--`n+(t0+1)>n+t0`--))]
			THEN REWRITE_TAC[EQT_ELIM(ARITH_CONV(--`~(n+(t0+1) <= n+t0)`--))]
			THEN REWRITE_TAC[EQT_ELIM(ARITH_CONV(--`n+t0 <= n+t0`--))]
			THEN REWRITE_TAC[EQT_ELIM(ARITH_CONV(--`n+(t0+1) = (SUC n)+t0`--))]
			THEN IMP_RES_TAC(EQT_ELIM(ARITH_CONV(--`(n = t) ==> t<SUC n`--)))
			THEN RES_TAC THEN ASM_REWRITE_TAC[],
			(* ------------ after the subautomaton started --------	*)
			DISJ2_TAC THEN DISJ2_TAC
			THEN IMP_RES_TAC(EQT_ELIM(ARITH_CONV(--`n < t ==> t+t0 > n+t0`--)))
			THEN POP_ASSUM (fn x => REWRITE_TAC[x])
			THEN IMP_RES_TAC(EQT_ELIM(ARITH_CONV(--`n < t ==> ~(t+t0 <= n+t0)`--)))
			THEN POP_ASSUM (fn x => REWRITE_TAC[x])
			THEN IMP_RES_TAC(EQT_ELIM(ARITH_CONV(--`n < t ==> t+(t0+1) > n+t0`--)))
			THEN POP_ASSUM (fn x => REWRITE_TAC[x])
			THEN IMP_RES_TAC LESS_ADD_1
			THEN POP_ASSUM (fn x => REWRITE_TAC[x])
			THEN REWRITE_TAC[EQT_ELIM(ARITH_CONV(--`(n+(p+1))+t0 = p+(SUC n+t0)`--))]
			THEN ASM_REWRITE_TAC[],
			(* ----------- before the subautomaton started --------	*)
			DISJ1_TAC
			THEN IMP_RES_TAC(EQT_ELIM(ARITH_CONV(--`t<n ==> ~(t+t0 > n+t0)`--)))
			THEN POP_ASSUM (fn x => REWRITE_TAC[x])
			THEN IMP_RES_TAC(EQT_ELIM(ARITH_CONV(--`t<n ==> (t+t0 <= n+t0)`--)))
			THEN POP_ASSUM (fn x => REWRITE_TAC[x])
			THEN IMP_RES_TAC(EQT_ELIM(ARITH_CONV(--`t<n ==> ~(t+(t0+1) > n+t0)`--)))
			THEN POP_ASSUM (fn x => REWRITE_TAC[x])
			THEN IMP_RES_TAC(EQT_ELIM(ARITH_CONV(--`t<n ==> (t+(t0+1) <= n+t0)`--)))
			THEN POP_ASSUM (fn x => REWRITE_TAC[x])
			THEN IMP_RES_TAC(EQT_ELIM(ARITH_CONV(--`t<n ==> t < SUC n`--)))
			THEN RES_TAC
		    ],
		    (* ------------ correct acceptance ----------------	*)
		    EXISTS_TAC(--`t1+SUC n`--)
		    THEN REWRITE_TAC[EQT_ELIM(ARITH_CONV(--`~((t1+SUC n)+(t_2+t0) <= n+t0)`--))]
		    THEN REWRITE_TAC[EQT_ELIM(ARITH_CONV
				(--`(t1+SUC n)+(t2+t0) = t1+(t2+(SUC n+t0))`--))]
		    THEN ASM_REWRITE_TAC[] THEN CONV_TAC ARITH_CONV
		]
	    ],
	(* ----------------------------------------------------------------------------	*)
	(* second implication: from right to left    					*)
	(* ----------------------------------------------------------------------------	*)
	    DISJ_CASES_TAC(SPEC(--`(p:num->bool) t0`--) BOOL_CASES_AX)
	    THENL[
		(* --------------------------------------------------------------------	*)
		(* 1st subgoal: p holds from the begining, i.e., the subautomaton runs	*)
		(* from the begining and therefore, phi need never hold.		*)
		(* --------------------------------------------------------------------	*)
		MY_MP_TAC (--`!t. p(t+t0)`--)
		THENL[
		    INDUCT_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES]
		    THEN LEFT_NO_FORALL_TAC 3 (--`t:num`--)
		    THEN UNDISCH_HD_TAC
		    THEN ASM_REWRITE_TAC[EQT_ELIM(ARITH_CONV(--`t+(t0+1)=SUC(t+t0)`--))]
		    THEN STRIP_TAC,
		    DISCH_TAC
		]
		THEN POP_ASSUM (fn x => RULE_ASSUM_TAC(REWRITE_RULE[x]) THEN ASSUME_TAC x)
		THEN EXISTS_TAC (--`0`--)
		THEN REWRITE_TAC[EQT_ELIM(ARITH_CONV(--`~(t<0)`--))]
		THEN REWRITE_TAC[ADD_CLAUSES]
		THEN EXISTS_TAC(--`q:num->'b`--)
		THEN ASM_REWRITE_TAC[]
		THEN CONJ_TAC
		THENL[
		    UNDISCH_NO_TAC 4
		    THEN LEFT_FORALL_TAC (--`0`--) THEN UNDISCH_HD_TAC
		    THEN REWRITE_TAC[ADD_CLAUSES]
		    THEN DISCH_TAC THEN ASM_REWRITE_TAC[],
		    EXISTS_TAC(--`t1:num`--) THEN ASM_REWRITE_TAC[]
		],
		(* --------------------------------------------------------------------	*)
		(* 2nd subgoal: p is initially false, i.e., the subautomaton must be	*)
		(* started later on and until then, phi must hold.			*)
		(* --------------------------------------------------------------------	*)
		MY_MP_TAC (--`!t1. p(t1+t0) ==> !t. p(t+(t1+t0))`--)
		THENL[
		    GEN_TAC THEN DISCH_TAC THEN INDUCT_TAC
		    THEN ASM_REWRITE_TAC[ADD_CLAUSES]
		    THEN LEFT_NO_FORALL_TAC 4 (--`t+t1'`--)
		    THEN UNDISCH_HD_TAC
		    THEN ASM_REWRITE_TAC[EQT_ELIM(ARITH_CONV(--`(t+t1')+t0 = t+(t1'+t0)`--))]
		    THEN REWRITE_TAC[EQT_ELIM(ARITH_CONV(--`t+(t1'+(t0+1))=SUC(t+(t1'+t0))`--))]
		    THEN STRIP_TAC,
		    DISCH_TAC
		]
		THEN MY_MP_TAC (--`?t1. p(t1+t0)`--)
		THENL[
		    EXISTS_TAC(--`t1:num`--) THEN LEFT_NO_FORALL_TAC 2 (--`0`--)
		    THEN UNDISCH_HD_TAC THEN REWRITE_TAC[ADD_CLAUSES]
		    THEN STRIP_TAC,
		    DISCH_TAC
		]
		THEN ASSUME_TAC(BETA_RULE(SPEC(--`\t1.p(t1+t0):bool`--)WOP))
		THEN UNDISCH_HD_TAC THEN POP_ASSUM (fn x => REWRITE_TAC[x])
		THEN STRIP_TAC
		THEN EXISTS_TAC(--`n:num`--)
		THEN LEFT_NO_FORALL_TAC 2 (--`n:num`--)
		THEN UNDISCH_HD_TAC THEN POP_NO_ASSUM 1 (fn x => REWRITE_TAC[x])
		THEN DISCH_TAC THEN CONJ_TAC
		(* --------------------------------------------------------------------	*)
		(* splits in two subgoals here: 					*)
		(*	  (--`!t. t < n ==> phi (t + t0) `--)				*)
		(* 	  (--`?q.							*)
		(*	        Phi_I (q (n + t0)) /\					*)
		(*	        (!t. Phi_R (i (t + n + t0),q (t + n + t0))) /\		*)
 		(*	       (?t1. !t2. Psi (i (t1 + t2 + n + t0),			*)
		(*			       q (t1 + t2 + n + t0)))`--)		*)
		(*									*)
		(* --------------------------------------------------------------------	*)
		THENL[

		    INDUCT_TAC
		    THENL[
			DISCH_TAC THEN LEFT_NO_FORALL_TAC 5 (--`0`--)
			THEN UNDISCH_HD_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES]
			THEN STRIP_TAC,
			DISCH_TAC
			THEN IMP_RES_TAC(EQT_ELIM(ARITH_CONV(--`SUC t<n ==> t<n`--)))
			THEN LEFT_NO_FORALL_TAC 4 (--`SUC t`--)
			THEN UNDISCH_HD_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_TAC
			THEN LEFT_NO_FORALL_TAC 7 (--`SUC t`--)
			THEN UNDISCH_HD_TAC THEN ASM_REWRITE_TAC[]
			THEN STRIP_TAC
		    ],
		    (* ----------------------------------------------------------------	*)
		    (* 	  (--`?q.							*)
		    (*	        Phi_I (q (n + t0)) /\					*)
		    (*	        (!t. Phi_R (i (t + n + t0),q (t + n + t0))) /\		*)
 		    (*	       (?t1. !t2. Psi (i (t1 + t2 + n + t0),			*)
		    (*			       q (t1 + t2 + n + t0)))`--)		*)
		    (*									*)
		    (* ----------------------------------------------------------------	*)
		    EXISTS_TAC (--`q:num->'b`--)
		    THEN REPEAT STRIP_TAC
		    THENL[
			(* ............................................................	*)
			(*  first prove that Phi_I (q (n + t0)) holds			*)
			(* ............................................................	*)
			MY_MP_TAC(--`?n'. n = SUC n'`--)
			THENL[
			    LEFT_FORALL_TAC(--`0`--) THEN UNDISCH_HD_TAC
			    THEN REWRITE_TAC[ADD_CLAUSES]
			    THEN DISJ_CASES_TAC(SPEC(--`n:num`--)num_CASES)
			    THEN ASM_REWRITE_TAC[ADD_CLAUSES],
			    STRIP_TAC
			]
		        THEN IMP_RES_TAC(EQT_ELIM(ARITH_CONV(--`(n = SUC n') ==> n'<n`--)))
		    	THEN LEFT_NO_FORALL_TAC 3 (--`n':num`--)
		    	THEN UNDISCH_HD_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_TAC
		    	THEN LEFT_NO_FORALL_TAC 3 (--`0`--)
		    	THEN UNDISCH_HD_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES] THEN DISCH_TAC
		    	THEN LEFT_NO_FORALL_TAC 6 (--`n':num`--)
		    	THEN UNDISCH_HD_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES]
		    	THEN REWRITE_TAC[EQT_ELIM(ARITH_CONV(--`n'+(t0+1) = SUC(n'+t0)`--))]
		    	THEN STRIP_TAC THEN RES_TAC,
			(* ............................................................	*)
			(* now prove (!t. Phi_R (i (t + n + t0),q (t + n + t0)))	*)
			(* ............................................................	*)
			LEFT_NO_FORALL_TAC 4 (--`t+n`--)
			THEN UNDISCH_HD_TAC THEN ASM_REWRITE_TAC[SYM(SPEC_ALL ADD_ASSOC)]
			THEN STRIP_TAC,
			(* ............................................................	*)
			(* now prove the acceptance condition				*)
			(* ............................................................	*)
			EXISTS_TAC (--`t1:num`--) THEN GEN_TAC
			THEN LEFT_NO_FORALL_TAC 3 (--`t2+n`--)
			THEN ASM_REWRITE_TAC[EQT_ELIM(ARITH_CONV(--`t1+(t2+(n+t0))=t1+((t2+n)+t0)`--))]
		    ]
		]
	    ]
	]
);







(* ========================== CO_BUECHI_BEFORE_CLOSURE ================================	*)
(*											*)
(* The next theorem shows that co-Buechi automata are closed under an appliation of a 	*)
(* BEFORE operator, provided that the right hand side argument is propositional.	*)
(*											*)
(*  |- ( (\t0.										*)
(*        ?q.										*)
(*          Phi_I(q t0) /\								*)
(*          (!t. Phi_R(i(t+t0),q(t+t0))) /\						*)
(*          (?t1. !t2. Psi(i(t1+t2+t0),q(t1+t2+t0)))					*)
(*       ) 										*)
(*      BEFORE										*)
(*       phi										*)
(*      )										*)
(*       t0 =										*)
(*      (?p1 p2 (q:num->'b). 								*)
(*		(~p1 t0 /\ ~p2 t0 /\ (q t0 = c) \/					*)
(*		  p1 t0 /\ ~p2 t0 /\ Phi_I(q t0)					*)
(*	        ) /\									*)
(*		(!t. 									*)
(*		      ~p1(t+t0) /\ ~p2(t+t0) /\ (q(t+t0) = c) /\ ~phi(t+t0) 		*)
(*		       /\ ~p1(t+t0+1) /\ ~p2(t+t0+1) /\  (q(t+t0+1) = c)		*)
(*		  \/  ~p1(t+t0) /\ ~p2(t+t0) /\ (q(t+t0) = c) /\ ~phi(t+t0) 		*)
(*		       /\  p1(t+t0+1) /\ ~p2(t+t0+1) /\ Phi_I(q(t+t0+1))		*)
(*		  \/   p1(t+t0) /\ ~p2(t+t0) /\ ~phi(t+t0) /\ Phi_I(q(t+t0))		*)
(*		       /\ Phi_R((i(t+t0):'a),q(t+t0)) /\ p1(t+t0+1) /\ p2(t+t0+1) 	*)
(*		  \/   p1(t+t0) /\ p2(t+t0) /\ Phi_R((i(t+t0):'a),q(t+t0)) 		*)
(*		       /\ p1(t+t0+1) /\ p2(t+t0+1) 					*)
(*		) /\									*)
(*        	?t1. !t2. ~p1(t1+t2+t0) \/ Psi(i(t1+t2+t0),q(t1+t2+t0))			*)
(*											*)
(*											*)
(* ====================================================================================	*)



val CO_BUECHI_BEFORE_CLOSURE = TAC_PROOF(
    let val cb = (--`?q.
          	    Phi_I(q t0) /\
                    (!t. Phi_R((i(t+t0):'a),(q(t+t0):'b))) /\
                    (?t1. !t2. Psi(i(t1+(t2+t0)),q(t1+(t2+t0))))`--)
     in
	([],--`((\t0:num. ^cb) BEFORE phi) t0
	  = ?p1 p2 (q:num->'b).
		(~p1 t0 /\ ~p2 t0 /\ (q t0 = c) \/
		  p1 t0 /\ ~p2 t0 /\ Phi_I(q t0)
	        ) /\
		(!t.
		      ~p1(t+t0) /\ ~p2(t+t0) /\ (q(t+t0) = c) /\ ~phi(t+t0)
		       /\ ~p1(t+(t0+1)) /\ ~p2(t+(t0+1)) /\  (q(t+(t0+1)) = c)
		  \/  ~p1(t+t0) /\ ~p2(t+t0) /\ (q(t+t0) = c) /\ ~phi(t+t0)
		       /\  p1(t+(t0+1)) /\ ~p2(t+(t0+1)) /\ Phi_I(q(t+(t0+1)))
		  \/   p1(t+t0) /\ ~p2(t+t0) /\ ~phi(t+t0) /\ Phi_I(q(t+t0))
		       /\ Phi_R((i(t+t0):'a),q(t+t0)) /\ p1(t+(t0+1)) /\ p2(t+(t0+1))
		  \/   p1(t+t0) /\ p2(t+t0) /\ Phi_R((i(t+t0):'a),q(t+t0))
		       /\ p1(t+(t0+1)) /\ p2(t+(t0+1))
		) /\
        	?t1. !t2. ~p1(t1+(t2+t0)) \/ Psi(i(t1+(t2+t0)),q(t1+(t2+t0)))
	`--)
    end,
	PURE_REWRITE_TAC[BEFORE_SIGNAL] THEN BETA_TAC THEN EQ_TAC
	THENL[
	(* ----------------------------------------------------------------------------	*)
	(* first implication: from left to right    					*)
	(* ----------------------------------------------------------------------------	*)
	REPEAT STRIP_TAC
	THEN DISJ_CASES_TAC(SPEC(--`phi:num->bool`--)(GEN(--`b:num->bool`--)DELTA_CASES))
	THENL[
	    (* ------------------------------------------------------------------------	*)
	    (* phi holds at least once, so that the before operation really takes care	*)
	    (* ------------------------------------------------------------------------	*)
	    LEFT_EXISTS_TAC THEN LEFT_NO_FORALL_TAC 1 (--`d:num`--)
	    THEN UNDISCH_HD_TAC THEN ASM_REWRITE_TAC[]
	    THEN STRIP_TAC THEN RES_TAC
	    THEN EXISTS_TAC (--`\x:num. (x>=t+t0)`--)
	    THEN EXISTS_TAC (--`\x:num. (x> t+t0)`--)
	    THEN EXISTS_TAC (--`\x:num. if (x<t+t0) then (c:'b) else q(x)`--)
	    THEN BETA_TAC THEN REWRITE_TAC[]
	    THEN REWRITE_TAC[EQT_ELIM(ARITH_CONV(--`t0>=t+t0 = ~(0<t)`--))]
	    THEN REWRITE_TAC[EQT_ELIM(ARITH_CONV(--`~(t0>t+t0)`--))]
	    THEN REWRITE_TAC[EQT_ELIM(ARITH_CONV(--`t0<t+t0 = (0<t)`--))]
	    THEN REWRITE_TAC[EQT_ELIM(ARITH_CONV(--`t'+t0>=t+t0 = ~(t'<t)`--))]
	    THEN REWRITE_TAC[EQT_ELIM(ARITH_CONV(--`t'+t0> t+t0 =  (t<t')`--))]
	    THEN REWRITE_TAC[EQT_ELIM(ARITH_CONV(--`t'+t0<t+t0 = (t'<t)`--))]
	    THEN REWRITE_TAC[EQT_ELIM(ARITH_CONV(--`t'+(t0+1)>=t+t0 = ~(t'+1<t)`--))]
	    THEN REWRITE_TAC[EQT_ELIM(ARITH_CONV(--`t'+(t0+1)> t+t0 = (t<t'+1)`--))]
	    THEN REWRITE_TAC[EQT_ELIM(ARITH_CONV(--`t'+(t0+1)<t+t0 = t'+1<t`--))]
	    THEN REPEAT STRIP_TAC
	    THENL[
		(* --------------------------------------------------------------------	*)
		(* correct initialization						*)
		(* --------------------------------------------------------------------	*)
		DISJ_CASES_TAC(EQT_ELIM(ARITH_CONV(--`(0<t) \/ ~(0<t)`--)))
		THEN ASM_REWRITE_TAC[]
		THEN IMP_RES_TAC(EQT_ELIM(ARITH_CONV(--`~(0<t) ==> (t=0)`--)))
		THEN UNDISCH_NO_TAC 5 THEN ASM_REWRITE_TAC[ADD_CLAUSES],
		(* --------------------------------------------------------------------	*)
		(* correct transition relation						*)
		(* --------------------------------------------------------------------	*)
		DISJ_CASES_TAC(EQT_ELIM(ARITH_CONV(--`(t'<t) \/ (t'=t) \/ (t<t')`--)))
		THENL[ALL_TAC,POP_ASSUM DISJ_CASES_TAC]
		THEN ASM_REWRITE_TAC[]
		THENL[
		    (* ----------------------------------------------------------------	*)
		    (* case t'<t, i.e. subautomaton not yet started			*)
		    (* ----------------------------------------------------------------	*)
		    MY_MP_TAC (--`~phi(t'+t0)`--)
		    THENL[
			IMP_RES_TAC(EQT_ELIM(ARITH_CONV(--`t'<t /\ t<d ==> t'<d`--)))
			THEN RES_TAC,
			DISCH_TAC
			]
		    THEN ASM_REWRITE_TAC[]
		    THEN IMP_RES_TAC(EQT_ELIM(ARITH_CONV(--`(t'<t) ==> ~(t<t')`--)))
		    THEN ASM_REWRITE_TAC[]
		    THEN IMP_RES_TAC(EQT_ELIM(ARITH_CONV(--`(t'<t) ==> ~(t<t'+1)`--)))
		    THEN ASM_REWRITE_TAC[]
		    THEN IMP_RES_TAC(EQT_ELIM(ARITH_CONV(--`t'<t ==> t'+1<t \/ (t'+1=t)`--)))
		    THEN ASM_REWRITE_TAC[EQT_ELIM(ARITH_CONV(--`~(t<t)`--))]
		    THEN IMP_RES_TAC(EQT_ELIM(ARITH_CONV(--`(t'+1=t) ==> (t'+(t0+1) = t+t0)`--)))
		    THEN ASM_REWRITE_TAC[],
		    (* ----------------------------------------------------------------	*)
		    (* case t'=t, i.e. subautomaton starts at t+t0=t'+t0		*)
		    (* ----------------------------------------------------------------	*)
		    REWRITE_TAC[EQT_ELIM(ARITH_CONV(--`~(t<t) /\ (t<t+1) /\~(t+1<t)`--))]
		    THEN LEFT_NO_FORALL_TAC 3 (--`0`--) THEN UNDISCH_HD_TAC
		    THEN REWRITE_TAC[ADD_CLAUSES] THEN DISCH_TAC
		    THEN ASM_REWRITE_TAC[],
		    (* ----------------------------------------------------------------	*)
		    (* case t<t', i.e. subautomaton starts at t+t0=t'+t0		*)
		    (* ----------------------------------------------------------------	*)
		    IMP_RES_TAC(EQT_ELIM(ARITH_CONV(--`(t<t') ==> ~(t'<t)`--)))
		    THEN ASM_REWRITE_TAC[]
		    THEN LEFT_NO_FORALL_TAC 5 (--`t'-t`--) THEN UNDISCH_HD_TAC
		    THEN IMP_RES_TAC(EQT_ELIM(ARITH_CONV(--`(t<t') ==> ((t'-t)+(t+t0)=t'+t0)`--)))
		    THEN ASM_REWRITE_TAC[]
		    THEN STRIP_TAC THEN ASM_REWRITE_TAC[]
		    THEN UNDISCH_NO_TAC 5 THEN CONV_TAC ARITH_CONV
		],
		(* --------------------------------------------------------------------	*)
		(* correct acceptance condition						*)
		(* --------------------------------------------------------------------	*)
		EXISTS_TAC(--`t+t1`--)
		THEN REWRITE_TAC[EQT_ELIM(ARITH_CONV(--`~((t+t1)+(t2+t0)<t+t0)`--))]
		THEN ASM_REWRITE_TAC[EQT_ELIM(ARITH_CONV(--`(t+t1)+(t2+t0)=t1+(t2+(t+t0))`--))]
		]
	    ,
	    (* ------------------------------------------------------------------------	*)
	    (* phi never holds, so that x BEFORE phi is trivially true			*)
	    (* ------------------------------------------------------------------------	*)
	    EXISTS_TAC (--`\t:num. F`--) THEN EXISTS_TAC (--`\t:num. F`--)
	    THEN EXISTS_TAC (--`\t:num. c:'b`--)
	    THEN BETA_TAC THEN ASM_REWRITE_TAC[]
	    ]
	,
	(* ----------------------------------------------------------------------------	*)
	(* second implication: from right to left    					*)
	(* ----------------------------------------------------------------------------	*)
	REPEAT (CONV_TAC LEFT_IMP_EXISTS_CONV THEN GEN_TAC)
	THEN REWRITE_TAC[TAC_PROOF(([],--`a/\b/\c ==> d
					= a ==> b ==> c ==>d`--),PROP_TAC)]
	THEN REPEAT DISCH_TAC THEN LEFT_EXISTS_TAC
	THEN REPEAT STRIP_TAC
	(* ----------------------------------------------------------------------------	*)
	THEN MY_MP_TAC(--`0<delta`--)
	(* ----------------------------------------------------------------------------	*)
	THENL[
	    REWRITE_TAC[EQT_ELIM(ARITH_CONV(--`0<delta = ~(delta=0)`--))]
	    THEN DISCH_TAC
	    THEN POP_ASSUM (fn x => RULE_ASSUM_TAC(REWRITE_RULE[x,ADD_CLAUSES]))
	    THEN LEFT_NO_FORALL_TAC 3 (--`0`--) THEN UNDISCH_HD_TAC
	    THEN ASM_REWRITE_TAC[ADD_CLAUSES]
	    THEN UNDISCH_NO_TAC 3
	    THEN BOOL_CASES_TAC (--`(p2:num->bool) t0`--)
	    THEN REWRITE_TAC[],
	    DISCH_TAC
	    ]
	(* ----------------------------------------------------------------------------	*)
	(* We now prove that the subautomaton must really be started because phi is	*)
	(* true at delta+t0. Note that staying in the newly added initial state is only	*)
	(* possible if phi is false.							*)
	(* ----------------------------------------------------------------------------	*)
	THEN MY_MP_TAC(--`?x. p1(x+t0) /\ ~p2(x+t0) /\ ~phi(x+t0)
				/\ Phi_I(q(x+t0):'b) /\ (x<delta) `--)
	(* ----------------------------------------------------------------------------	*)
	THENL[
	    POP_NO_ASSUM 5 DISJ_CASES_TAC
		(*---------------------------------------------------------------------	*)
		(* 1st case: we start initially from p1 t0 /\~p2 t0 /\ Phi_I(q t0)	*)
		(* This is pretty easy: instantiate x:= 0 and get the proof by assumpt.	*)
		(*---------------------------------------------------------------------	*)
	    THENL[
		ALL_TAC,
		EXISTS_TAC(--`0`--) THEN RES_TAC
		THEN ASM_REWRITE_TAC[]
		THEN ASM_REWRITE_TAC[ADD_CLAUSES]
	    	]
		(*---------------------------------------------------------------------	*)
		(* 2nd case: we start initially from ~p1 t0 /\ ~p2 t0 /\ (q t0 = c) 	*)
		(* Assume the lemma would be false, then we have to derive a contra-	*)
		(* diction from the other assumptions. To do that, we first prove that	*)
		(* under these (inconsistent) assumptions, we would have to stay in the	*)
		(* initial state up to delta+t0. But then phi(delta+t0) could not hold.	*)
		(*---------------------------------------------------------------------	*)
	    THEN ONCE_REWRITE_TAC[TAC_PROOF(([],--`a = ~~a`--),PROP_TAC)]
	    THEN CONV_TAC(ONCE_DEPTH_CONV NOT_EXISTS_CONV)
	    THEN DISCH_TAC
	    THEN MY_MP_TAC (--`!x. x<delta ==> ~p1(x+t0) /\ ~p2(x+t0) /\ (q(x+t0) = (c:'b))`--)
	    THENL[
		INDUCT_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES,ADD1]
		THEN DISCH_TAC
		THEN IMP_RES_TAC(EQT_ELIM(ARITH_CONV(--`x+1<delta ==> x<delta`--)))
		THEN UNDISCH_NO_TAC 2 THEN ASM_REWRITE_TAC[]
		THEN DISCH_TAC THEN LEFT_NO_FORALL_TAC 9 (--`x:num`--)
		THEN UNDISCH_HD_TAC THEN ASM_REWRITE_TAC[SYM(SPEC_ALL ADD_ASSOC)]
		THEN STRIP_TAC THEN ASM_REWRITE_TAC[]
		THEN LEFT_NO_FORALL_TAC 7 (--`x+1`--) THEN UNDISCH_HD_TAC
		THEN ASM_REWRITE_TAC[EQT_ELIM(ARITH_CONV(--`(x+1)+t0 = x+(t0+1)`--))]
		THEN RES_TAC
		THEN ASM_REWRITE_TAC[EQT_ELIM(ARITH_CONV(--`x+(t0+1)=(x+1)+t0`--))],
		DISCH_TAC
		]
	    THEN IMP_RES_TAC LESS_ADD_1 (* derives that delta = p+1 *)
	    THEN LEFT_NO_FORALL_TAC 1 (--`p:num`--) (* instantiate the above lemma *)
	    THEN IMP_RES_TAC(EQT_ELIM(ARITH_CONV(--`(delta=0+(p+1)) ==> p<delta`--)))
	    THEN UNDISCH_NO_TAC 1 THEN ASM_REWRITE_TAC[] THEN DISCH_TAC
	    THEN COPY_ASM_NO 9
	    THEN LEFT_FORALL_TAC (--`p:num`--) (* instantiate trans. rel. *)
	    THEN DISCH_TAC THEN LEFT_FORALL_TAC (--`p+1`--) (* instantiate trans. rel. *)
	    THEN UNDISCH_HD_TAC THEN UNDISCH_HD_TAC THEN ASM_REWRITE_TAC[]
	    THEN RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES])
	    THEN REWRITE_TAC[EQT_ELIM(ARITH_CONV(--`p+(t0+1) = (p+1)+t0`--))]
	    THEN ASM_TAC 2 (fn x => SUBST1_TAC(SYM x))
	    THEN STRIP_TAC THEN ASM_REWRITE_TAC[],
	    DISCH_TAC
	    ]
	(* ----------------------------------------------------------------------------	*)
	(* Having proved that we finally enter at some point of time x+t0 with x<delta 	*)
	(* state p1(x+t0) /\ ~p2(x+t0) /\ ~phi(x+t0) /\ Phi_I(q(x+t0):'b), we now 	*)
	(* use this as follows: instantiate t with that x and q with q. We then obtain:	*)
	(* ----------------------------------------------------------------------------	*)
	THEN LEFT_EXISTS_TAC
	THEN EXISTS_TAC (--`x:num`--) THEN ASM_REWRITE_TAC[]
	THEN EXISTS_TAC(--`q:num->'b`--) THEN ASM_REWRITE_TAC[]
	(* ----------------------------------------------------------------------------	*)
	(* The following subgoals remain:						*)
	(* 	the transition relation:  !t'. Phi_R(i(t'+x+t0),q(t'+x+t0))		*)
	(* 	the acceptance condition: ?t1.!t2. Psi(i(t1+t2+x+t0),q(t1+t2+x+t0))	*)
	(* to prove them, some further lemmata are helpful:				*)
	(* ----------------------------------------------------------------------------	*)
	(* ----------------------------------------------------------------------------	*)
	THEN MY_MP_TAC(--`!y. p1(y+(x+t0))`--)
	(* ----------------------------------------------------------------------------	*)
	THENL[
	    INDUCT_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES]
	    THEN LEFT_NO_FORALL_TAC 6 (--`y+x`--)
	    THEN UNDISCH_HD_TAC
	    THEN ASM_REWRITE_TAC[SYM(SPEC_ALL ADD_ASSOC),ADD1]
	    THEN STRIP_TAC,
	    DISCH_TAC
	    ]
	(* ----------------------------------------------------------------------------	*)
	THEN MY_MP_TAC(--`p2(x+(t0+1)):bool`--)
	(* ----------------------------------------------------------------------------	*)
	THENL[
	    LEFT_NO_FORALL_TAC 6 (--`x:num`--) THEN UNDISCH_HD_TAC
	    THEN ASM_REWRITE_TAC[SYM(SPEC_ALL ADD_ASSOC),ADD1]
	    THEN STRIP_TAC,
	    DISCH_TAC
	]
	(* ----------------------------------------------------------------------------	*)
	THEN MY_MP_TAC(--`!y. p2(y+(x+(t0+1)))`--)
	(* ----------------------------------------------------------------------------	*)
	THENL[
	    INDUCT_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES]
	    THEN LEFT_NO_FORALL_TAC 8 (--`y+(x+1)`--)
	    THEN UNDISCH_HD_TAC
	    THEN ASM_REWRITE_TAC[SYM(SPEC_ALL ADD_ASSOC),ADD1]
	    THEN ASM_REWRITE_TAC[EQT_ELIM(ARITH_CONV(--`y+(x+(1+t0)) = (y+1)+(x+t0)`--))]
	    THEN ASM_REWRITE_TAC[EQT_ELIM(ARITH_CONV(--`(y+1)+(x+t0) = y+(x+(t0+1))`--))]
	    THEN REWRITE_TAC[EQT_ELIM(ARITH_CONV(--`y+(x+((t0+1)+1)) = y+(x+(t0+(1+1)))`--))]
	    THEN STRIP_TAC,
	    DISCH_TAC
	]
	THEN CONJ_TAC
	THENL[
	    (* ------------------------------------------------------------------------	*)
	    (* 	the transition relation:  !t'. Phi_R(i(t'+x+t0),q(t'+x+t0))		*)
	    (* ------------------------------------------------------------------------	*)
	    Q.X_GEN_TAC `tt` THEN LEFT_NO_FORALL_TAC 8 (--`tt+x`--)
	    THEN UNDISCH_HD_TAC THEN ASM_REWRITE_TAC[SYM(SPEC_ALL ADD_ASSOC)]
	    THEN STRIP_TAC,
	    (* ------------------------------------------------------------------------	*)
	    (* 	the acceptance condition: ?t1.!t2. Psi(i(t1+t2+x+t0),q(t1+t2+x+t0))	*)
	    (* ------------------------------------------------------------------------	*)
	    EXISTS_TAC (--`t1:num`--) THEN GEN_TAC
	    THEN LEFT_NO_FORALL_TAC 7 (--`t2+x`--)
	    THEN UNDISCH_HD_TAC
	    THEN ASM_REWRITE_TAC[EQT_ELIM(ARITH_CONV(--`t1+((t2+x)+t0) = (t1+t2)+(x+t0)`--))]
	    THEN REWRITE_TAC[EQT_ELIM(ARITH_CONV(--`(t1+t2)+(x+t0) = t1+(t2+(x+t0))`--))]
	    ]
	]
);

















(* ========================== CO_BUECHI_UNTIL_CLOSURE =================================	*)
(*											*)
(* The next theorem shows that co-Buechi automata are closed under an appliation of a 	*)
(* UNTIL operator, provided that the left hand side argument is propositional.		*)
(*											*)
(*  |- (phi UNTIL									*)
(*      (\t0.										*)
(*        ?q.										*)
(*          Phi_I (q t0) /\								*)
(*          (!t. Phi_R (i (t+t0),q (t+t0))) /\						*)
(*          (?t1. !t2. Psi (i (t1+t2+t0),q (t1+t2+t0)))))				*)
(*       t0 =										*)
(*     (?p q.										*)
(*       ((p t0) => (Phi_I (q t0)) | (q t0 = c)) /\					*)
(*       (!t.										*)
(*         ~p(t+t0) /\ (q(t+t0) = c) /\ phi(t+t0) /\ ~p(t+t0+1) /\ (q(t+t0+1) = c) \/	*)
(*         ~p(t+t0) /\ (q(t+t0) = c) /\ phi(t+t0) /\  p(t+t0+1) /\ Phi_I(q(t+t0+1)) \/	*)
(*          p(t+t0) /\ Phi_R(i(t+t0),q(t+t0)) /\ p(t+t0+1)				*)
(*	 ) /\										*)
(*       (?t1. !t2. ~p(t1+t2+t0) \/ Psi(i(t1+t2+t0),q(t1+t2+t0))))			*)
(*											*)
(* ====================================================================================	*)



val CO_BUECHI_UNTIL_CLOSURE = TAC_PROOF(
    let val cb = (--`?q.
          	    Phi_I(q t0) /\
                    (!t. Phi_R((i(t+t0):'a),(q(t+t0):'b))) /\
                    (?t1. !t2. Psi(i(t1+(t2+t0)),q(t1+(t2+t0))))`--)
     in
	([],--`(phi UNTIL (\t0:num. ^cb)) t0
	  = ?p q.
		(if p t0 then Phi_I(q t0) else (q t0 = c)) /\
		(!t.
		      ~p(t+t0) /\ (q(t+t0) = c) /\ phi(t+t0) /\ ~p(t+(t0+1)) /\  (q(t+(t0+1)) = c)
		  \/  ~p(t+t0) /\ (q(t+t0) = c) /\ phi(t+t0) /\  p(t+(t0+1)) /\  Phi_I(q(t+(t0+1)))
		  \/   p(t+t0) /\ Phi_R((i(t+t0):'a),(q(t+t0):'b)) /\ p(t+(t0+1))
		) /\
        	?t1. !t2. ~p(t1+(t2+t0)) \/ Psi(i(t1+(t2+t0)),q(t1+(t2+t0)))
	`--)
    end,
	PURE_REWRITE_TAC[UNTIL_AS_SUNTIL,ALWAYS_SIGNAL]
	THEN BETA_TAC
	THEN DISJ_CASES_TAC (SPEC(--`!t'. phi(t'+t0)`--)BOOL_CASES_AX)
	THEN SUBST1_TAC CO_BUECHI_SUNTIL_CLOSURE
	THEN ASM_REWRITE_TAC[]
	THENL[
	    (* this is the case where (--`!t'. phi(t'+t0)`--) holds *)
	    EXISTS_TAC (--`\t:num.F`--) THEN EXISTS_TAC (--`\t:num.c:'b`--)
	    THEN BETA_TAC THEN RULE_ASSUM_TAC EQT_ELIM
	    THEN ASM_REWRITE_TAC[],
	    (* in the other case, we have phi UNTIL cb = phi SUNITL cb *)
	    EQ_TAC THEN REPEAT STRIP_TAC
	    THEN EXISTS_TAC (--`p:num->bool`--)
	    THEN EXISTS_TAC (--`q:num->'b`--)
	    THEN ASM_REWRITE_TAC[]
	    THENL[EXISTS_TAC (--`t1:num`--) THEN ASM_REWRITE_TAC[], ALL_TAC]
	    THEN MY_MP_TAC (--`(?t. ~phi(t+t0)) ==> (?t. p(t+t0))`--)
	    THENL[
		CONV_TAC CONTRAPOS_CONV
		THEN CONV_TAC(DEPTH_CONV NOT_EXISTS_CONV)
		THEN REWRITE_TAC[] THEN DISCH_TAC
		THEN POP_ASSUM (fn x=> RULE_ASSUM_TAC(REWRITE_RULE[x]) THEN ASSUME_TAC x)
		THEN GEN_TAC THEN LEFT_NO_FORALL_TAC 2 (--`t:num`--)
		THEN UNDISCH_HD_TAC
		THEN ASM_REWRITE_TAC[EQT_ELIM(ARITH_CONV(--`t+(t0+1) = (t+1)+t0`--))]
		THEN STRIP_TAC,
		DISCH_TAC
		]
	    THEN UNDISCH_NO_TAC 4 THEN REWRITE_TAC[]
	    THEN CONV_TAC(DEPTH_CONV NOT_FORALL_CONV)
	    THEN STRIP_TAC THEN RES_TAC
	    THEN MY_MP_TAC (--`!x. p(x+(t+t0))`--)
	    THENL[
		INDUCT_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES]
		THEN LEFT_NO_FORALL_TAC 5 (--`x+t`--)
		THEN UNDISCH_HD_TAC
		THEN ASM_REWRITE_TAC[SYM(SPEC_ALL ADD_ASSOC),ADD1]
		THEN STRIP_TAC,
		DISCH_TAC
		]
	    THEN DISJ_CASES_TAC(SPECL[(--`t1:num`--),(--`t:num`--)]LESS_CASES)
	    THENL[
		(* --------- case t1<t ------------ *)
		EXISTS_TAC (--`t:num`--) THEN GEN_TAC
		THEN ONCE_REWRITE_TAC[EQT_ELIM(ARITH_CONV(--`t+(t2+t0) = t2+(t+t0)`--))]
		THEN ASM_REWRITE_TAC[]
		THEN IMP_RES_TAC LESS_ADD THEN LEFT_NO_FORALL_TAC 6 (--`t2+p'`--)
		THEN UNDISCH_HD_TAC THEN UNDISCH_NO_TAC 2
		THEN POP_ASSUM (SUBST1_TAC o SYM)
		THEN SUBST1_TAC(EQT_ELIM(ARITH_CONV(--`t1+((t2+p')+t0) = t2+((p'+t1)+t0)`--)))
		THEN DISCH_TAC THEN ASM_REWRITE_TAC[],
		(* --------- case t<=t1 ------------ *)
		EXISTS_TAC (--`t1:num`--) THEN GEN_TAC
		THEN IMP_RES_TAC LESS_EQUAL_ADD
		THEN POP_ASSUM (fn x => SUBST1_TAC x THEN ASSUME_TAC x)
		THEN POP_ASSUM (fn x => RULE_ASSUM_TAC(REWRITE_RULE[x]))
		THEN SUBST1_TAC(EQT_ELIM(ARITH_CONV(--`(t+p')+(t2+t0) = (p'+t2)+(t+t0)`--)))
		THEN ASM_REWRITE_TAC[]
		THEN LEFT_NO_FORALL_TAC 5 (--`t2:num`--)
		THEN UNDISCH_HD_TAC
		THEN SUBST1_TAC(EQT_ELIM(ARITH_CONV(--`(t+p')+(t2+t0) = (p'+t2)+(t+t0)`--)))
		THEN ASM_REWRITE_TAC[]
	    	]
	    ]
);


















(* ========================== CO_BUECHI_SBEFORE_CLOSURE ===============================	*)
(*											*)
(* The next theorem shows that co-Buechi automata are closed under an appliation of a 	*)
(* SBEFORE operator, provided that the right hand side argument is propositional.	*)
(*											*)
(*  |- ( (\t0.										*)
(*        ?q.										*)
(*          Phi_I(q t0) /\								*)
(*          (!t. Phi_R(i(t+t0),q(t+t0))) /\						*)
(*          (?t1. !t2. Psi(i(t1+t2+t0),q(t1+t2+t0)))					*)
(*       ) 										*)
(*      SBEFORE										*)
(*       phi										*)
(*      )										*)
(*       t0 =										*)
(*      (?p1 p2 (q:num->'b). 								*)
(*		(~p1 t0 /\ ~p2 t0 /\ (q t0 = c) \/					*)
(*		  p1 t0 /\ ~p2 t0 /\ Phi_I(q t0)					*)
(*	        ) /\									*)
(*		(!t. 									*)
(*		      ~p1(t+t0) /\ ~p2(t+t0) /\ (q(t+t0) = c) /\ ~phi(t+t0) 		*)
(*		       /\ ~p1(t+t0+1) /\ ~p2(t+t0+1) /\  (q(t+t0+1) = c)		*)
(*		  \/  ~p1(t+t0) /\ ~p2(t+t0) /\ (q(t+t0) = c) /\ ~phi(t+t0) 		*)
(*		       /\  p1(t+t0+1) /\ ~p2(t+t0+1) /\ Phi_I(q(t+t0+1))		*)
(*		  \/   p1(t+t0) /\ ~p2(t+t0) /\ ~phi(t+t0) /\ Phi_I(q(t+t0))		*)
(*		       /\ Phi_R((i(t+t0):'a),q(t+t0)) /\ p1(t+t0+1) /\ p2(t+t0+1) 	*)
(*		  \/   p1(t+t0) /\ p2(t+t0) /\ Phi_R((i(t+t0):'a),q(t+t0)) 		*)
(*		       /\ p1(t+t0+1) /\ p2(t+t0+1) 					*)
(*		) /\									*)
(*        	?t1. !t2. p1(t1+t2+t0) /\ Psi(i(t1+t2+t0),q(t1+t2+t0))			*)
(*											*)
(*											*)
(* ====================================================================================	*)



val CO_BUECHI_SBEFORE_CLOSURE = TAC_PROOF(
    let val cb = (--`?q.
          	    Phi_I(q t0) /\
                    (!t. Phi_R((i(t+t0):'a),(q(t+t0):'b))) /\
                    (?t1. !t2. Psi(i(t1+(t2+t0)),q(t1+(t2+t0))))`--)
     in
	([],--`((\t0:num. ^cb) SBEFORE phi) t0
	  = ?p1 p2 (q:num->'b).
		(~p1 t0 /\ ~p2 t0 /\ (q t0 = c) \/
		  p1 t0 /\ ~p2 t0 /\ Phi_I(q t0)
	        ) /\
		(!t.
		      ~p1(t+t0) /\ ~p2(t+t0) /\ (q(t+t0) = c) /\ ~phi(t+t0)
		       /\ ~p1(t+(t0+1)) /\ ~p2(t+(t0+1)) /\  (q(t+(t0+1)) = c)
		  \/  ~p1(t+t0) /\ ~p2(t+t0) /\ (q(t+t0) = c) /\ ~phi(t+t0)
		       /\  p1(t+(t0+1)) /\ ~p2(t+(t0+1)) /\ Phi_I(q(t+(t0+1)))
		  \/   p1(t+t0) /\ ~p2(t+t0) /\ ~phi(t+t0) /\ Phi_I(q(t+t0))
		       /\ Phi_R((i(t+t0):'a),q(t+t0)) /\ p1(t+(t0+1)) /\ p2(t+(t0+1))
		  \/   p1(t+t0) /\ p2(t+t0) /\ Phi_R((i(t+t0):'a),q(t+t0))
		       /\ p1(t+(t0+1)) /\ p2(t+(t0+1))
		) /\
        	?t1. !t2. p1(t1+(t2+t0)) /\ Psi(i(t1+(t2+t0)),q(t1+(t2+t0)))
	`--)
    end,
	PURE_REWRITE_TAC[SBEFORE_SIGNAL] THEN BETA_TAC THEN EQ_TAC
	THENL[
	(* ----------------------------------------------------------------------------	*)
	(* first implication: from left to right    					*)
	(* ----------------------------------------------------------------------------	*)
	    REPEAT STRIP_TAC
	    THEN EXISTS_TAC(--`\x. delta+t0<=x`--)
	    THEN EXISTS_TAC(--`\x. delta+t0<x`--)
	    THEN EXISTS_TAC(--`\x. if (delta+t0<=x) then q x else (c:'b)`--)
	    THEN BETA_TAC
	    THEN REWRITE_TAC[EQT_ELIM(ARITH_CONV(--`~(delta+t0<t0)`--))]
	    THEN REWRITE_TAC[LESS_MONO_ADD_EQ,LESS_EQ_MONO_ADD_EQ]
	    THEN REPEAT STRIP_TAC
	    THENL[
		(* --------------------------------------------------------------------	*)
		(* initial condition			  				*)
		(* --------------------------------------------------------------------	*)
		REWRITE_TAC[EQT_ELIM(ARITH_CONV(--`(delta+t0<=t0) = (delta=0)`--))]
		THEN DISJ_CASES_TAC(EQT_ELIM(ARITH_CONV(--`(delta=0) \/ ~(delta=0)`--)))
		THEN ASM_REWRITE_TAC[] THEN UNDISCH_NO_TAC 4
		THEN ASM_REWRITE_TAC[ADD_CLAUSES],
		(* --------------------------------------------------------------------	*)
		(* transition relation			  				*)
		(* --------------------------------------------------------------------	*)
		DISJ_CASES_TAC(EQT_ELIM(ARITH_CONV(--`(t<delta) \/ (delta=t) \/ (delta<t)`--)))
		THEN ASM_REWRITE_TAC[] THENL[ALL_TAC,POP_ASSUM DISJ_CASES_TAC]
		THENL[
		    (* here is the case (t<delta) *)
		    IMP_RES_TAC(EQT_ELIM(ARITH_CONV(--`(t<delta) ==> ~(delta <= t)`--)))
		    THEN POP_ASSUM REWRITE1_TAC
		    THEN IMP_RES_TAC(EQT_ELIM(ARITH_CONV(--`(t<delta) ==> ~(delta < t)`--)))
		    THEN POP_ASSUM REWRITE1_TAC
		    THEN IMP_RES_TAC(EQT_ELIM(ARITH_CONV
				(--`(t<delta) ==> ~(delta+t0<t+(t0+1))`--)))
		    THEN POP_ASSUM REWRITE1_TAC
		    THEN IMP_RES_TAC(EQT_ELIM(ARITH_CONV
				(--`(t<delta) ==> ~(delta+t0<=t+(t0+1)) \/ (t+(t0+1)=delta+t0)`--)))
		    THEN LEFT_FORALL_TAC (--`t0:num`--)
		    THEN POP_ASSUM DISJ_CASES_TAC THEN ASM_REWRITE_TAC[]
		    THENL[
			POP_NO_ASSUM 2 MATCH_MP_TAC THEN UNDISCH_NO_TAC 1
			THEN CONV_TAC ARITH_CONV,
			ASM_REWRITE_TAC[LESS_EQ_REFL]
			THEN POP_NO_ASSUM 2 MATCH_MP_TAC THEN UNDISCH_NO_TAC 1
			THEN CONV_TAC ARITH_CONV
			],
		    (* here is the case (delta=t) *)
		    POP_ASSUM (SUBST1_TAC o SYM)
		    THEN ASM_REWRITE_TAC[LESS_EQ_REFL,LESS_REFL]
		    THEN LEFT_FORALL_TAC (--`delta:num`--) THEN UNDISCH_HD_TAC
		    THEN LEFT_NO_FORALL_TAC 1 (--`0`--) THEN UNDISCH_HD_TAC
		    THEN REWRITE_TAC[LESS_EQ_REFL,ADD_CLAUSES]
		    THEN DISCH_TAC THEN ASM_REWRITE_TAC[]
		    THEN DISCH_TAC THEN ASM_REWRITE_TAC[]
		    THEN CONV_TAC ARITH_CONV,
		    (* here is the case (delta<t) *)
		    ASM_REWRITE_TAC[]
		    THEN IMP_RES_TAC(EQT_ELIM(ARITH_CONV(--`(delta<t) ==> (delta<=t)`--)))
		    THEN POP_ASSUM REWRITE1_TAC
		    THEN IMP_RES_TAC(EQT_ELIM(ARITH_CONV
				(--`(delta<t) ==> (delta+t0<t+(t0+1))`--)))
		    THEN POP_ASSUM REWRITE1_TAC
		    THEN IMP_RES_TAC(EQT_ELIM(ARITH_CONV
				(--`(delta<t) ==> (delta+t0<=t+(t0+1))`--)))
		    THEN POP_ASSUM REWRITE1_TAC
		    THEN IMP_RES_TAC LESS_ADD_1
		    THEN POP_ASSUM REWRITE1_TAC
		    THEN ASM_REWRITE_TAC[EQT_ELIM(ARITH_CONV
				(--`(delta+(p+1))+t0 = (p+1)+(delta+t0)`--))]
		    ],
		(* --------------------------------------------------------------------	*)
		(* acceptance condition			  				*)
		(* --------------------------------------------------------------------	*)
		EXISTS_TAC(--`t1+delta`--) THEN GEN_TAC
	    	THEN REWRITE_TAC[ARITH_CONV(--`delta+t0<=(t1+delta)+(t2+t0)`--)]
		THEN REWRITE_TAC[EQT_ELIM(ARITH_CONV
				(--`(t1+delta)+(t2+t0) = t1+(t2+(delta+t0))`--))]
		THEN ASM_REWRITE_TAC[]
	    ],
	(* ----------------------------------------------------------------------------	*)
	(* second implication: from right to left    					*)
	(* ----------------------------------------------------------------------------	*)
	    REPEAT STRIP_TAC
	    THENL[
		ALL_TAC,
		(* --------------------------------------------------------------------	*)
		(* First consider the case where the automaton starts in state 		*)
		(* p1 t0 /\ ~p2 t0 /\ Phi_I(q t0), i.e. the subautomaton starts right	*)
		(* now. Hence, instantiate delta := 0 in the SBEFORE_SIGNAL_THM.	*)
		(* --------------------------------------------------------------------	*)
		MY_MP_TAC(--`!y. p1(y+t0)`--)
		(* --------------------------------------------------------------------	*)
		THENL[
		    INDUCT_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES]
		    THEN LEFT_NO_FORALL_TAC 2 (--`y:num`--)
		    THEN UNDISCH_HD_TAC
		    THEN ASM_REWRITE_TAC[SYM(SPEC_ALL ADD_ASSOC),ADD1]
		    THEN STRIP_TAC,
		    DISCH_TAC
		    ]
		THEN POP_ASSUM (fn x => RULE_ASSUM_TAC(REWRITE_RULE[x]) THEN ASSUME_TAC x)
		THEN EXISTS_TAC(--`0`--) THEN ASM_REWRITE_TAC[ADD_CLAUSES]
		THEN REPEAT STRIP_TAC
		THENL[
		    ALL_TAC,
		    IMP_RES_TAC(EQT_ELIM(ARITH_CONV(--`(t<=0) ==> (t=0)`--)))
		    THEN POP_ASSUM (fn x => RULE_ASSUM_TAC(REWRITE_RULE[x]))
		    THEN UNDISCH_HD_TAC THEN LEFT_NO_FORALL_TAC 3 (--`0`--)
		    THEN UNDISCH_HD_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES]
		    THEN STRIP_TAC
		    ]
	 	THEN EXISTS_TAC(--`q:num->'b`--)
		THEN ASM_REWRITE_TAC[] THEN CONJ_TAC
		THENL[
		    ALL_TAC,
		    EXISTS_TAC(--`t1:num`--) THEN GEN_TAC THEN ASM_REWRITE_TAC[]
		    ]
		THEN GEN_TAC THEN LEFT_NO_FORALL_TAC 2 (--`t:num`--)
		THEN UNDISCH_HD_TAC THEN STRIP_TAC
		]
	    (* ------------------------------------------------------------------------	*)
	    (* Now consider the case where the automaton starts in state 		*)
	    (* ~p1 t0 /\ ~p2 t0 /\ (q t0 = c), i.e. the subautomaton starts at a later	*)
	    (* point of time. We first prove that the automaton will eventually start.	*)
	    (* ------------------------------------------------------------------------	*)
	    (* We first prove that the automaton will move from at some time d+t0 to 	*)
	    (* state p1(d+t0) /\ ~p2(d+t0) /\ Phi_I(q(d+t0)) and stays until then in	*)
	    (* in the initial state, i.e., ~p1(x+t0) /\ ~p2(x+t0) /\ (q(x+t0) = c) 	*)
	    (* holds for all x<d.							*)
	    (* ------------------------------------------------------------------------	*)
	    THEN MY_MP_TAC(--`?d. (!t. t<d ==> ~p1(t+t0)) /\ p1(d+t0)`--)
	    (* ------------------------------------------------------------------------	*)
	    THENL[
		DISJ_CASES_TAC(SPEC(--`p1:num->bool`--)(GEN(--`b:num->bool`--)DELTA_CASES))
		THEN ASM_REWRITE_TAC[]
		THEN UNDISCH_NO_TAC 1 THEN ASM_REWRITE_TAC[ADD_ASSOC],
		STRIP_TAC]
	    (* ------------------------------------------------------------------------	*)
	    THEN MY_MP_TAC(--`!t. t<d ==> ~p1(t+t0) /\ ~p2(t+t0) /\ (q(t+t0) = (c:'b))`--)
	    (* ------------------------------------------------------------------------	*)
	    THENL[
		INDUCT_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES] THEN DISCH_TAC
		THEN IMP_RES_TAC(EQT_ELIM(ARITH_CONV(--`(SUC t<d) ==> (t<d)`--)))
		THEN RES_TAC THEN LEFT_NO_FORALL_TAC 10 (--`t:num`--)
		THEN UNDISCH_HD_TAC THEN UNDISCH_HD_TAC
		THEN ASM_REWRITE_TAC[ADD_CLAUSES,SYM(SPEC_ALL ADD1)]
		THEN DISCH_TAC THEN ASM_REWRITE_TAC[]
		THEN STRIP_TAC THEN ASM_REWRITE_TAC[],
		DISCH_TAC
		]
	    (* ------------------------------------------------------------------------	*)
	    THEN MY_MP_TAC(--`!t. t<d ==> ~phi(t+t0)`--)
	    (* ------------------------------------------------------------------------	*)
	    THENL[
		INDUCT_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES] THEN DISCH_TAC
		THENL[
		    LEFT_NO_FORALL_TAC 5 (--`0`--) THEN UNDISCH_HD_TAC
		    THEN ASM_REWRITE_TAC[ADD_CLAUSES] THEN STRIP_TAC,
		    RES_TAC THEN LEFT_NO_FORALL_TAC 9 (--`SUC t`--)
		    THEN UNDISCH_HD_TAC THEN ASM_REWRITE_TAC[]
		    THEN REWRITE_TAC[ADD_CLAUSES]
		    THEN STRIP_TAC],
		DISCH_TAC
		]
	    (* ------------------------------------------------------------------------	*)
	    THEN MY_MP_TAC(--`0<d`--)
	    (* ------------------------------------------------------------------------	*)
	    THENL[
		UNDISCH_NO_TAC 2
		THEN DISJ_CASES_TAC(EQT_ELIM(ARITH_CONV(--`(0<d) \/ (d=0)`--)))
		THEN ASM_REWRITE_TAC[ADD_CLAUSES],
		DISCH_TAC]
	    (* ------------------------------------------------------------------------	*)
	    THEN MY_MP_TAC(--`p1(d+t0) /\ ~p2(d+t0) /\ Phi_I(q(d+t0):'b) /\ ~phi(d+t0)`--)
	    (* ------------------------------------------------------------------------	*)
	    THENL[
	        IMP_RES_TAC LESS_ADD_1	(* derives that d = 0+p+1  *)
		THEN RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES])
		THEN ASM_TAC 0 SUBST1_TAC
		THEN POP_ASSUM (fn x=> RULE_ASSUM_TAC(REWRITE_RULE[x]))
		THEN COPY_ASM_NO 6 THEN LEFT_FORALL_TAC(--`p+1`--)
		THEN DISCH_TAC THEN LEFT_FORALL_TAC (--`p:num`--)
		THEN UNDISCH_HD_TAC THEN UNDISCH_HD_TAC
		THEN POP_NO_TAC 0 THEN LEFT_FORALL_TAC(--`p:num`--)
		THEN LEFT_NO_FORALL_TAC 1(--`p:num`--)
		THEN UNDISCH_HD_TAC THEN UNDISCH_HD_TAC
		THEN REWRITE_TAC[EQT_ELIM(ARITH_CONV(--`p<p+1`--))]
		THEN DISCH_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[]
		THEN REWRITE_TAC[ADD_CLAUSES,SYM(SPEC_ALL ADD1)]
		THEN STRIP_TAC THEN ASM_REWRITE_TAC[],
		DISCH_TAC]
	    (* ------------------------------------------------------------------------	*)
	    THEN MY_MP_TAC(--`!y. p1(y+(d+t0))`--)
	    (* ------------------------------------------------------------------------	*)
	    THENL[
	        INDUCT_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES]
	        THEN LEFT_NO_FORALL_TAC 8 (--`y+d`--)
	        THEN UNDISCH_HD_TAC
	        THEN ASM_REWRITE_TAC[SYM(SPEC_ALL ADD_ASSOC),ADD1]
	        THEN STRIP_TAC,
	        DISCH_TAC]
	    (* ------------------------------------------------------------------------	*)
	    THEN MY_MP_TAC(--`p2(d+(t0+1)):bool`--)
	    (* ------------------------------------------------------------------------	*)
	    THENL[
	        LEFT_NO_FORALL_TAC 8 (--`d:num`--) THEN UNDISCH_HD_TAC
	        THEN ASM_REWRITE_TAC[SYM(SPEC_ALL ADD_ASSOC),ADD1]
	        THEN STRIP_TAC,
	        DISCH_TAC]
	    (* ------------------------------------------------------------------------	*)
	    THEN MY_MP_TAC(--`!y. p2(y+(d+(t0+1)))`--)
	    (* ------------------------------------------------------------------------	*)
	    THENL[
	        INDUCT_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES]
	        THEN LEFT_NO_FORALL_TAC 10 (--`y+(d+1)`--)
	        THEN UNDISCH_HD_TAC
	        THEN ASM_REWRITE_TAC[SYM(SPEC_ALL ADD_ASSOC),ADD1]
	        THEN ASM_REWRITE_TAC[EQT_ELIM(ARITH_CONV(--`y+(d+(1+t0)) = (y+1)+(d+t0)`--))]
	        THEN ASM_REWRITE_TAC[EQT_ELIM(ARITH_CONV(--`(y+1)+(d+t0) = y+(d+(t0+1))`--))]
	        THEN REWRITE_TAC[EQT_ELIM(ARITH_CONV(--`y+(d+((t0+1)+1)) = y+(d+(t0+(1+1)))`--))]
	        THEN STRIP_TAC,
	        DISCH_TAC]
	    (* ------------------------------------------------------------------------	*)
	    (* Now consider what has to be proved:					*)
	    (* (--`?delta.								*)
	    (*    (?q.									*)
	    (*       Phi_I(q(delta+t0)) /\						*)
	    (*       (!t. Phi_R(i(t+delta+t0),q(t+delta+t0))) /\			*)
	    (*       (?t1. !t2. Psi(i(t1+t2+delta+t0),q(t1+t2+delta+t0)))) /\		*)
 	    (*    (!t. t <= delta ==> ~phi(t+t0))`--)					*)
	    (* 										*)
	    (* We clearly instantiate delta:=d, and q:= q prove the arising subgoals.	*)
	    (* ------------------------------------------------------------------------	*)
	    THEN EXISTS_TAC (--`d:num`--) THEN CONJ_TAC
	    THENL[
		ALL_TAC,
		(* prove that  (!t. t <= d ==> ~phi(t+t0)) holds (by previous lemmata)	*)
		GEN_TAC THEN REWRITE_TAC[LESS_OR_EQ] THEN STRIP_TAC
		THEN ASM_REWRITE_TAC[] THEN RES_TAC]
	    THEN EXISTS_TAC(--`q:num->'b`--) THEN ASM_REWRITE_TAC[] THEN CONJ_TAC
	    THENL[
	        (* --------------------------------------------------------------------	*)
	        (* the transition relation:  !t'. Phi_R(i(t'+d+t0),q(t'+d+t0))		*)
	        (* --------------------------------------------------------------------	*)
	        GEN_TAC THEN LEFT_NO_FORALL_TAC 10 (--`t+d`--)
	        THEN UNDISCH_HD_TAC THEN ASM_REWRITE_TAC[SYM(SPEC_ALL ADD_ASSOC)]
	        THEN STRIP_TAC,
	        (* --------------------------------------------------------------------	*)
	        (* the acceptance condition: ?t1.!t2. Psi(i(t1+t2+d+t0),q(t1+t2+d+t0))	*)
	        (* --------------------------------------------------------------------	*)
	        EXISTS_TAC (--`t1:num`--) THEN GEN_TAC
	        THEN LEFT_NO_FORALL_TAC 9 (--`t2+d`--)
	        THEN UNDISCH_HD_TAC
	        THEN ASM_REWRITE_TAC[EQT_ELIM(ARITH_CONV(--`t1+((t2+d)+t0) = (t1+t2)+(d+t0)`--))]
	        THEN REWRITE_TAC[EQT_ELIM(ARITH_CONV(--`(t1+t2)+(d+t0) = t1+(t2+(d+t0))`--))]
	        ]
	]
);






(* ========================== CO_BUECHI_SWHEN_CLOSURE ===============================	*)
(*											*)
(* The next theorem shows that co-Buechi automata are closed under an appliation of a 	*)
(* SWHEN operator, provided that the right hand side argument is propositional.		*)
(*											*)
(*  |- ( (\t0.										*)
(*        ?q.										*)
(*          Phi_I(q t0) /\								*)
(*          (!t. Phi_R(i(t+t0),q(t+t0))) /\						*)
(*          (?t1. !t2. Psi(i(t1+t2+t0),q(t1+t2+t0)))					*)
(*       ) 										*)
(*      SWHEN										*)
(*       phi										*)
(*      )										*)
(*       t0 =										*)
(*      (?p1 p2 (q:num->'b). 								*)
(*		(~p1 t0 /\ ~p2 t0 /\ (q t0 = c) \/					*)
(*		  p1 t0 /\ ~p2 t0 /\ Phi_I(q t0)					*)
(*	        ) /\									*)
(*		(!t. 									*)
(*		      ~p1(t+t0) /\ ~p2(t+t0) /\ (q(t+t0) = c) /\ ~phi(t+t0) 		*)
(*		       /\ ~p1(t+t0+1) /\ ~p2(t+t0+1) /\  (q(t+t0+1) = c)		*)
(*		  \/  ~p1(t+t0) /\ ~p2(t+t0) /\ (q(t+t0) = c) /\ ~phi(t+t0) 		*)
(*		       /\  p1(t+t0+1) /\ ~p2(t+t0+1) /\ Phi_I(q(t+t0+1))		*)
(*		  \/   p1(t+t0) /\ ~p2(t+t0) /\ phi(t+t0) /\ Phi_I(q(t+t0))		*)
(*		       /\ Phi_R((i(t+t0):'a),q(t+t0)) /\ p1(t+t0+1) /\ p2(t+t0+1) 	*)
(*		  \/   p1(t+t0) /\ p2(t+t0) /\ Phi_R((i(t+t0):'a),q(t+t0)) 		*)
(*		       /\ p1(t+t0+1) /\ p2(t+t0+1) 					*)
(*		) /\									*)
(*        	?t1. !t2. p1(t1+t2+t0) /\ Psi(i(t1+t2+t0),q(t1+t2+t0))			*)
(*											*)
(*											*)
(* ====================================================================================	*)




val CO_BUECHI_SWHEN_CLOSURE = TAC_PROOF(
    let val cb = (--`?q.
          	    Phi_I(q t0) /\
                    (!t. Phi_R((i(t+t0):'a),(q(t+t0):'b))) /\
                    (?t1. !t2. Psi(i(t1+(t2+t0)),q(t1+(t2+t0))))`--)
     in
	([],--`((\t0:num. ^cb) SWHEN phi) t0
	  = ?p1 p2 (q:num->'b).
		(~p1 t0 /\ ~p2 t0 /\ (q t0 = c) \/
		  p1 t0 /\ ~p2 t0 /\ Phi_I(q t0)
	        ) /\
		(!t.
		      ~p1(t+t0) /\ ~p2(t+t0) /\ (q(t+t0) = c) /\ ~phi(t+t0)
		       /\ ~p1(t+(t0+1)) /\ ~p2(t+(t0+1)) /\  (q(t+(t0+1)) = c)
		  \/  ~p1(t+t0) /\ ~p2(t+t0) /\ (q(t+t0) = c) /\ ~phi(t+t0)
		       /\  p1(t+(t0+1)) /\ ~p2(t+(t0+1)) /\ Phi_I(q(t+(t0+1)))
		  \/   p1(t+t0) /\ ~p2(t+t0) /\ phi(t+t0) /\ Phi_I(q(t+t0))
		       /\ Phi_R((i(t+t0):'a),q(t+t0)) /\ p1(t+(t0+1)) /\ p2(t+(t0+1))
		  \/   p1(t+t0) /\ p2(t+t0) /\ Phi_R((i(t+t0):'a),q(t+t0))
		       /\ p1(t+(t0+1)) /\ p2(t+(t0+1))
		) /\
        	?t1. !t2. p1(t1+(t2+t0)) /\ Psi(i(t1+(t2+t0)),q(t1+(t2+t0)))
	`--)
    end,
	PURE_REWRITE_TAC[SWHEN_SIGNAL] THEN BETA_TAC THEN EQ_TAC
	THENL[
	(* ----------------------------------------------------------------------------	*)
	(* first implication: from left to right    					*)
	(* ----------------------------------------------------------------------------	*)
	    REPEAT STRIP_TAC
	    THEN EXISTS_TAC(--`\x. delta+t0<=x`--)
	    THEN EXISTS_TAC(--`\x. delta+t0<x`--)
	    THEN EXISTS_TAC(--`\x. if (delta+t0<=x) then q x else (c:'b)`--)
	    THEN BETA_TAC
	    THEN REWRITE_TAC[EQT_ELIM(ARITH_CONV(--`~(delta+t0<t0)`--))]
	    THEN REWRITE_TAC[LESS_MONO_ADD_EQ,LESS_EQ_MONO_ADD_EQ]
	    THEN REPEAT STRIP_TAC
	    THENL[
		(* --------------------------------------------------------------------	*)
		(* initial condition			  				*)
		(* --------------------------------------------------------------------	*)
		REWRITE_TAC[EQT_ELIM(ARITH_CONV(--`(delta+t0<=t0) = (delta=0)`--))]
		THEN DISJ_CASES_TAC(EQT_ELIM(ARITH_CONV(--`(delta=0) \/ ~(delta=0)`--)))
		THEN ASM_REWRITE_TAC[] THEN UNDISCH_NO_TAC 3
		THEN ASM_REWRITE_TAC[ADD_CLAUSES],
		(* --------------------------------------------------------------------	*)
		(* transition relation			  				*)
		(* --------------------------------------------------------------------	*)
		DISJ_CASES_TAC(EQT_ELIM(ARITH_CONV(--`(t<delta) \/ (delta=t) \/ (delta<t)`--)))
		THEN ASM_REWRITE_TAC[] THENL[ALL_TAC,POP_ASSUM DISJ_CASES_TAC]
		THENL[
		    (* here is the case (t<delta) *)
		    IMP_RES_TAC(EQT_ELIM(ARITH_CONV(--`(t<delta) ==> ~(delta <= t)`--)))
		    THEN POP_ASSUM REWRITE1_TAC
		    THEN IMP_RES_TAC(EQT_ELIM(ARITH_CONV(--`(t<delta) ==> ~(delta < t)`--)))
		    THEN POP_ASSUM REWRITE1_TAC
		    THEN IMP_RES_TAC(EQT_ELIM(ARITH_CONV
				(--`(t<delta) ==> ~(delta+t0<t+(t0+1))`--)))
		    THEN POP_ASSUM REWRITE1_TAC
		    THEN IMP_RES_TAC(EQT_ELIM(ARITH_CONV
				(--`(t<delta) ==> ~(delta+t0<=t+(t0+1)) \/ (t+(t0+1)=delta+t0)`--)))
		    THEN LEFT_FORALL_TAC (--`t0:num`--)
		    THEN POP_ASSUM DISJ_CASES_TAC THEN ASM_REWRITE_TAC[]
		    THENL[
			POP_NO_ASSUM 6 MATCH_MP_TAC THEN ASM_REWRITE_TAC[],
			ASM_REWRITE_TAC[LESS_EQ_REFL]
			THEN POP_NO_ASSUM 6 MATCH_MP_TAC THEN ASM_REWRITE_TAC[]
			],
		    (* here is the case (delta=t) *)
		    POP_ASSUM (SUBST1_TAC o SYM)
		    THEN ASM_REWRITE_TAC[LESS_EQ_REFL,LESS_REFL]
		    THEN LEFT_NO_FORALL_TAC 1 (--`0`--) THEN UNDISCH_HD_TAC
		    THEN REWRITE_TAC[ADD_CLAUSES]
		    THEN DISCH_TAC THEN ASM_REWRITE_TAC[]
		    THEN CONV_TAC ARITH_CONV,
		    (* here is the case (delta<t) *)
		    ASM_REWRITE_TAC[]
		    THEN IMP_RES_TAC(EQT_ELIM(ARITH_CONV(--`(delta<t) ==> (delta<=t)`--)))
		    THEN POP_ASSUM REWRITE1_TAC
		    THEN IMP_RES_TAC(EQT_ELIM(ARITH_CONV
				(--`(delta<t) ==> (delta+t0<t+(t0+1))`--)))
		    THEN POP_ASSUM REWRITE1_TAC
		    THEN IMP_RES_TAC(EQT_ELIM(ARITH_CONV
				(--`(delta<t) ==> (delta+t0<=t+(t0+1))`--)))
		    THEN POP_ASSUM REWRITE1_TAC
		    THEN IMP_RES_TAC LESS_ADD_1
		    THEN POP_ASSUM REWRITE1_TAC
		    THEN ASM_REWRITE_TAC[EQT_ELIM(ARITH_CONV
				(--`(delta+(p+1))+t0 = (p+1)+(delta+t0)`--))]
		    ],
		(* --------------------------------------------------------------------	*)
		(* acceptance condition			  				*)
		(* --------------------------------------------------------------------	*)
		EXISTS_TAC(--`t1+delta`--) THEN GEN_TAC
	    	THEN REWRITE_TAC[ARITH_CONV(--`delta+t0<=(t1+delta)+(t2+t0)`--)]
		THEN REWRITE_TAC[EQT_ELIM(ARITH_CONV
				(--`(t1+delta)+(t2+t0) = t1+(t2+(delta+t0))`--))]
		THEN ASM_REWRITE_TAC[]
	    ],
	(* ----------------------------------------------------------------------------	*)
	(* second implication: from right to left    					*)
	(* ----------------------------------------------------------------------------	*)
	    REPEAT STRIP_TAC
	    THENL[
		ALL_TAC,
		(* --------------------------------------------------------------------	*)
		(* First consider the case where the automaton starts in state 		*)
		(* p1 t0 /\ ~p2 t0 /\ Phi_I(q t0), i.e. the subautomaton starts right	*)
		(* now. Hence, instantiate delta := 0 in the SWHEN_SIGNAL_THM.		*)
		(* --------------------------------------------------------------------	*)
		MY_MP_TAC(--`!y. p1(y+t0)`--)
		(* --------------------------------------------------------------------	*)
		THENL[
		    INDUCT_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES]
		    THEN LEFT_NO_FORALL_TAC 2 (--`y:num`--)
		    THEN UNDISCH_HD_TAC
		    THEN ASM_REWRITE_TAC[SYM(SPEC_ALL ADD_ASSOC),ADD1]
		    THEN STRIP_TAC,
		    DISCH_TAC
		    ]
		THEN POP_ASSUM (fn x => RULE_ASSUM_TAC(REWRITE_RULE[x]) THEN ASSUME_TAC x)
		THEN EXISTS_TAC(--`0`--) THEN ASM_REWRITE_TAC[ADD_CLAUSES]
		THEN REWRITE_TAC[NOT_LESS_0]
		THEN REPEAT STRIP_TAC
		THENL[
		    LEFT_NO_FORALL_TAC 2 (--`0`--) THEN UNDISCH_HD_TAC
		    THEN ASM_REWRITE_TAC[ADD_CLAUSES]
		    THEN STRIP_TAC,
		    EXISTS_TAC(--`q:num->'b`--) THEN ASM_REWRITE_TAC[]
		    THEN CONJ_TAC
		    THENL[
			GEN_TAC THEN LEFT_NO_FORALL_TAC 2 (--`t:num`--)
			THEN UNDISCH_HD_TAC THEN STRIP_TAC,
			EXISTS_TAC(--`t1:num`--) THEN ASM_REWRITE_TAC[]
			]
		    ]
		]
	    (* ------------------------------------------------------------------------	*)
	    (* Now consider the case where the automaton starts in state 		*)
	    (* ~p1 t0 /\ ~p2 t0 /\ (q t0 = c), i.e. the subautomaton starts at a later	*)
	    (* point of time. We first prove that the automaton will eventually start.	*)
	    (* ------------------------------------------------------------------------	*)
	    (* We first prove that the automaton will move from at some time d+t0 to 	*)
	    (* state p1(d+t0) /\ ~p2(d+t0) /\ Phi_I(q(d+t0)) and stays until then in	*)
	    (* in the initial state, i.e., ~p1(x+t0) /\ ~p2(x+t0) /\ (q(x+t0) = c) 	*)
	    (* holds for all x<d.							*)
	    (* ------------------------------------------------------------------------	*)
	    THEN MY_MP_TAC(--`?d. (!t. t<d ==> ~p1(t+t0)) /\ p1(d+t0)`--)
	    (* ------------------------------------------------------------------------	*)
	    THENL[
		DISJ_CASES_TAC(SPEC(--`p1:num->bool`--)(GEN(--`b:num->bool`--)DELTA_CASES))
		THEN ASM_REWRITE_TAC[]
		THEN UNDISCH_NO_TAC 1 THEN ASM_REWRITE_TAC[ADD_ASSOC],
		STRIP_TAC]
	    (* ------------------------------------------------------------------------	*)
	    THEN MY_MP_TAC(--`!t. t<d ==> ~p1(t+t0) /\ ~p2(t+t0) /\ (q(t+t0) = (c:'b))`--)
	    (* ------------------------------------------------------------------------	*)
	    THENL[
		INDUCT_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES] THEN DISCH_TAC
		THEN IMP_RES_TAC(EQT_ELIM(ARITH_CONV(--`(SUC t<d) ==> (t<d)`--)))
		THEN RES_TAC THEN LEFT_NO_FORALL_TAC 10 (--`t:num`--)
		THEN UNDISCH_HD_TAC THEN UNDISCH_HD_TAC
		THEN ASM_REWRITE_TAC[ADD_CLAUSES,SYM(SPEC_ALL ADD1)]
		THEN DISCH_TAC THEN ASM_REWRITE_TAC[]
		THEN STRIP_TAC THEN ASM_REWRITE_TAC[],
		DISCH_TAC
		]
	    (* ------------------------------------------------------------------------	*)
	    THEN MY_MP_TAC(--`!t. t<d ==> ~phi(t+t0)`--)
	    (* ------------------------------------------------------------------------	*)
	    THENL[
		INDUCT_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES] THEN DISCH_TAC
		THENL[
		    LEFT_NO_FORALL_TAC 5 (--`0`--) THEN UNDISCH_HD_TAC
		    THEN ASM_REWRITE_TAC[ADD_CLAUSES] THEN STRIP_TAC,
		    RES_TAC THEN LEFT_NO_FORALL_TAC 9 (--`SUC t`--)
		    THEN UNDISCH_HD_TAC THEN ASM_REWRITE_TAC[]
		    THEN REWRITE_TAC[ADD_CLAUSES]
		    THEN STRIP_TAC],
		DISCH_TAC
		]
	    (* ------------------------------------------------------------------------	*)
	    THEN MY_MP_TAC(--`0<d`--)
	    (* ------------------------------------------------------------------------	*)
	    THENL[
		UNDISCH_NO_TAC 2
		THEN DISJ_CASES_TAC(EQT_ELIM(ARITH_CONV(--`(0<d) \/ (d=0)`--)))
		THEN ASM_REWRITE_TAC[ADD_CLAUSES],
		DISCH_TAC]
	    (* ------------------------------------------------------------------------	*)
	    THEN MY_MP_TAC(--`p1(d+t0) /\ ~p2(d+t0) /\ Phi_I(q(d+t0):'b) /\ phi(d+t0)`--)
	    (* ------------------------------------------------------------------------	*)
	    THENL[
	        IMP_RES_TAC LESS_ADD_1	(* derives that d = 0+p+1  *)
		THEN RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES])
		THEN ASM_TAC 0 SUBST1_TAC
		THEN POP_ASSUM (fn x=> RULE_ASSUM_TAC(REWRITE_RULE[x]))
		THEN COPY_ASM_NO 6 THEN LEFT_FORALL_TAC(--`p+1`--)
		THEN DISCH_TAC THEN LEFT_FORALL_TAC (--`p:num`--)
		THEN UNDISCH_HD_TAC THEN UNDISCH_HD_TAC
		THEN POP_NO_TAC 0 THEN LEFT_FORALL_TAC(--`p:num`--)
		THEN LEFT_NO_FORALL_TAC 1(--`p:num`--)
		THEN UNDISCH_HD_TAC THEN UNDISCH_HD_TAC
		THEN REWRITE_TAC[EQT_ELIM(ARITH_CONV(--`p<p+1`--))]
		THEN DISCH_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[]
		THEN REWRITE_TAC[ADD_CLAUSES,SYM(SPEC_ALL ADD1)]
		THEN STRIP_TAC THEN ASM_REWRITE_TAC[],
		DISCH_TAC]
	    (* ------------------------------------------------------------------------	*)
	    THEN MY_MP_TAC(--`!y. p1(y+(d+t0))`--)
	    (* ------------------------------------------------------------------------	*)
	    THENL[
	        INDUCT_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES]
	        THEN LEFT_NO_FORALL_TAC 8 (--`y+d`--)
	        THEN UNDISCH_HD_TAC
	        THEN ASM_REWRITE_TAC[SYM(SPEC_ALL ADD_ASSOC),ADD1]
	        THEN STRIP_TAC,
	        DISCH_TAC]
	    (* ------------------------------------------------------------------------	*)
	    THEN MY_MP_TAC(--`p2(d+(t0+1)):bool`--)
	    (* ------------------------------------------------------------------------	*)
	    THENL[
	        LEFT_NO_FORALL_TAC 8 (--`d:num`--) THEN UNDISCH_HD_TAC
	        THEN ASM_REWRITE_TAC[SYM(SPEC_ALL ADD_ASSOC),ADD1]
	        THEN STRIP_TAC,
	        DISCH_TAC]
	    (* ------------------------------------------------------------------------	*)
	    THEN MY_MP_TAC(--`!y. p2(y+(d+(t0+1)))`--)
	    (* ------------------------------------------------------------------------	*)
	    THENL[
	        INDUCT_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES]
	        THEN LEFT_NO_FORALL_TAC 10 (--`y+(d+1)`--)
	        THEN UNDISCH_HD_TAC
	        THEN ASM_REWRITE_TAC[SYM(SPEC_ALL ADD_ASSOC),ADD1]
	        THEN ASM_REWRITE_TAC[EQT_ELIM(ARITH_CONV(--`y+(d+(1+t0)) = (y+1)+(d+t0)`--))]
	        THEN ASM_REWRITE_TAC[EQT_ELIM(ARITH_CONV(--`(y+1)+(d+t0) = y+(d+(t0+1))`--))]
	        THEN REWRITE_TAC[EQT_ELIM(ARITH_CONV(--`y+(d+((t0+1)+1)) = y+(d+(t0+(1+1)))`--))]
	        THEN STRIP_TAC,
	        DISCH_TAC]
	    (* ------------------------------------------------------------------------	*)
	    (* Now consider what has to be proved:					*)
	    (* (--`?delta.								*)
	    (*       (!t. t<delta ==> ~phi(t+t0)) /\					*)
	    (*       phi(delta+t0) /\							*)
	    (*       (?q.								*)
	    (*           Phi_I(q(delta+t0)) /\						*)
	    (*           (!t. Phi_R(i(t+delta+t0),q(t+delta+t0))) /\			*)
	    (*           (?t1. !t2. Psi(i(t1+t2+delta+t0),q(t1+t2+delta+t0)))) /\	*)
	    (* 										*)
	    (* We clearly instantiate delta:=d, and q:= q prove the arising subgoals.	*)
	    (* ------------------------------------------------------------------------	*)
	    THEN EXISTS_TAC (--`d:num`--) THEN ASM_REWRITE_TAC[]
	    THEN EXISTS_TAC(--`q:num->'b`--) THEN ASM_REWRITE_TAC[] THEN CONJ_TAC
	    THENL[
	        (* --------------------------------------------------------------------	*)
	        (* the transition relation:  !t'. Phi_R(i(t'+d+t0),q(t'+d+t0))		*)
	        (* --------------------------------------------------------------------	*)
	        GEN_TAC THEN LEFT_NO_FORALL_TAC 10 (--`t+d`--)
	        THEN UNDISCH_HD_TAC THEN ASM_REWRITE_TAC[SYM(SPEC_ALL ADD_ASSOC)]
	        THEN STRIP_TAC,
	        (* --------------------------------------------------------------------	*)
	        (* the acceptance condition: ?t1.!t2. Psi(i(t1+t2+d+t0),q(t1+t2+d+t0))	*)
	        (* --------------------------------------------------------------------	*)
	        EXISTS_TAC (--`t1:num`--) THEN GEN_TAC
	        THEN LEFT_NO_FORALL_TAC 9 (--`t2+d`--)
	        THEN UNDISCH_HD_TAC
	        THEN ASM_REWRITE_TAC[EQT_ELIM(ARITH_CONV(--`t1+((t2+d)+t0) = (t1+t2)+(d+t0)`--))]
	        THEN REWRITE_TAC[EQT_ELIM(ARITH_CONV(--`(t1+t2)+(d+t0) = t1+(t2+(d+t0))`--))]
	        ]
	]
);













(* ========================== CO_BUECHI_WHEN_CLOSURE ===============================	*)
(*											*)
(*											*)
(*  |- ( (\t0.										*)
(*        ?q.										*)
(*          Phi_I(q t0) /\								*)
(*          (!t. Phi_R(i(t+t0),q(t+t0))) /\						*)
(*          (?t1. !t2. Psi(i(t1+t2+t0),q(t1+t2+t0)))					*)
(*       ) 										*)
(*      WHEN										*)
(*       phi										*)
(*      )										*)
(*       t0 =										*)
(*      (?p1 p2 (q:num->'b). 								*)
(*		(~p1 t0 /\ ~p2 t0 /\ (q t0 = c) \/					*)
(*		  p1 t0 /\ ~p2 t0 /\ Phi_I(q t0)					*)
(*	        ) /\									*)
(*		(!t. 									*)
(*		      ~p1(t+t0) /\ ~p2(t+t0) /\ (q(t+t0) = c) /\ ~phi(t+t0) 		*)
(*		       /\ ~p1(t+t0+1) /\ ~p2(t+t0+1) /\  (q(t+t0+1) = c)		*)
(*		  \/  ~p1(t+t0) /\ ~p2(t+t0) /\ (q(t+t0) = c) /\ ~phi(t+t0) 		*)
(*		       /\  p1(t+t0+1) /\ ~p2(t+t0+1) /\ Phi_I(q(t+t0+1))		*)
(*		  \/   p1(t+t0) /\ ~p2(t+t0) /\ phi(t+t0) /\ Phi_I(q(t+t0))		*)
(*		       /\ Phi_R((i(t+t0):'a),q(t+t0)) /\ p1(t+t0+1) /\ p2(t+t0+1) 	*)
(*		  \/   p1(t+t0) /\ p2(t+t0) /\ Phi_R((i(t+t0):'a),q(t+t0)) 		*)
(*		       /\ p1(t+t0+1) /\ p2(t+t0+1) 					*)
(*		) /\									*)
(*        	?t1. !t2. ~p1(t1+t2+t0) \/ Psi(i(t1+t2+t0),q(t1+t2+t0))			*)
(*											*)
(*											*)
(* ====================================================================================	*)




val CO_BUECHI_WHEN_CLOSURE = TAC_PROOF(
    let val cb = (--`?q.
          	    Phi_I(q t0) /\
                    (!t. Phi_R((i(t+t0):'a),(q(t+t0):'b))) /\
                    (?t1. !t2. Psi(i(t1+(t2+t0)),q(t1+(t2+t0))))`--)
     in
	([],--`((\t0:num. ^cb) WHEN phi) t0
	  = ?p1 p2 (q:num->'b).
		(~p1 t0 /\ ~p2 t0 /\ (q t0 = c) \/
		  p1 t0 /\ ~p2 t0 /\ Phi_I(q t0)
	        ) /\
		(!t.
		      ~p1(t+t0) /\ ~p2(t+t0) /\ (q(t+t0) = c) /\ ~phi(t+t0)
		       /\ ~p1(t+(t0+1)) /\ ~p2(t+(t0+1)) /\  (q(t+(t0+1)) = c)
		  \/  ~p1(t+t0) /\ ~p2(t+t0) /\ (q(t+t0) = c) /\ ~phi(t+t0)
		       /\  p1(t+(t0+1)) /\ ~p2(t+(t0+1)) /\ Phi_I(q(t+(t0+1)))
		  \/   p1(t+t0) /\ ~p2(t+t0) /\ phi(t+t0) /\ Phi_I(q(t+t0))
		       /\ Phi_R((i(t+t0):'a),q(t+t0)) /\ p1(t+(t0+1)) /\ p2(t+(t0+1))
		  \/   p1(t+t0) /\ p2(t+t0) /\ Phi_R((i(t+t0):'a),q(t+t0))
		       /\ p1(t+(t0+1)) /\ p2(t+(t0+1))
		) /\
        	?t1. !t2. ~p1(t1+(t2+t0)) \/ Psi(i(t1+(t2+t0)),q(t1+(t2+t0)))
	`--)
    end,
	PURE_REWRITE_TAC[WHEN_AS_SWHEN,ALWAYS_SIGNAL] THEN BETA_TAC
	THEN DISJ_CASES_TAC (SPEC(--`!t'. ~phi(t'+t0)`--)BOOL_CASES_AX)
	THEN SUBST1_TAC CO_BUECHI_SWHEN_CLOSURE
	THEN ASM_REWRITE_TAC[]
	THENL[
	    EXISTS_TAC (--`\t:num.F`--) THEN EXISTS_TAC (--`\t:num.F`--)
	    THEN EXISTS_TAC (--`\t:num.c:'b`--)
	    THEN BETA_TAC THEN RULE_ASSUM_TAC EQT_ELIM
	    THEN ASM_REWRITE_TAC[],
	    ALL_TAC]
	THEN EQ_TAC
	THEN (CONV_TAC(DEPTH_CONV LEFT_IMP_EXISTS_CONV))
	THEN (CONV_TAC(DEPTH_CONV LEFT_IMP_EXISTS_CONV))
	THEN (CONV_TAC(DEPTH_CONV LEFT_IMP_EXISTS_CONV))
	THEN REPEAT GEN_TAC THEN DISCH_TAC
	THEN POP_ASSUM (fn x=> MAP_EVERY ASSUME_TAC (CONJUNCTS x))
	THEN LEFT_EXISTS_TAC
	THEN EXISTS_TAC (--`p1:num->bool`--)
	THEN EXISTS_TAC (--`p2:num->bool`--)
	THEN EXISTS_TAC (--`q:num->'b`--)
	THEN ASM_REWRITE_TAC[]
        THENL[ EXISTS_TAC (--`t1:num`--) THEN ASM_REWRITE_TAC[], ALL_TAC]
	THEN MY_MP_TAC (--`(?t. phi(t+t0)) ==> (?t. p1(t+t0))`--)
	THENL[
	    CONV_TAC CONTRAPOS_CONV
	    THEN CONV_TAC(DEPTH_CONV NOT_EXISTS_CONV)
	    THEN DISCH_TAC
	    THEN POP_ASSUM (fn x=> RULE_ASSUM_TAC(REWRITE_RULE[x]) THEN ASSUME_TAC x)
	    THEN GEN_TAC THEN LEFT_NO_FORALL_TAC 2 (--`t:num`--)
	    THEN UNDISCH_HD_TAC
	    THEN ASM_REWRITE_TAC[EQT_ELIM(ARITH_CONV(--`t+(t0+1) = (t+1)+t0`--))]
	    THEN STRIP_TAC,
	    DISCH_TAC
	    ]



	THEN UNDISCH_NO_TAC 4 THEN REWRITE_TAC[]
	THEN CONV_TAC(DEPTH_CONV NOT_FORALL_CONV) THEN REWRITE_TAC[]
	THEN STRIP_TAC THEN RES_TAC
	THEN MY_MP_TAC (--`!x. p1(x+(t+t0))`--)
	THENL[
	    INDUCT_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES]
	    THEN LEFT_NO_FORALL_TAC 5 (--`x+t`--)
	    THEN UNDISCH_HD_TAC
	    THEN ASM_REWRITE_TAC[SYM(SPEC_ALL ADD_ASSOC),ADD1]
	    THEN STRIP_TAC,
	    DISCH_TAC
	    ]
	THEN EXISTS_TAC (--`t+t1`--) THEN GEN_TAC
	THEN LEFT_NO_FORALL_TAC 4 (--`t+t2`--) THEN UNDISCH_HD_TAC
	THEN SUBST1_TAC(EQT_ELIM(ARITH_CONV(--`t1+((t+t2)+t0) = (t1+t2)+(t+t0)`--)))
	THEN POP_NO_TAC 2 THEN POP_NO_TAC 2 THEN POP_NO_TAC 2 THEN POP_NO_TAC 2
	THEN ASM_REWRITE_TAC[]
	THEN SUBST1_TAC(EQT_ELIM(ARITH_CONV(--`(t1+t2)+(t+t0) = (t+t1)+(t2+t0)`--)))
	THEN STRIP_TAC THEN ASM_REWRITE_TAC[]
	THEN SUBST1_TAC(EQT_ELIM(ARITH_CONV(--`(t+t1)+(t2+t0) = (t1+t2)+(t+t0)`--)))
	THEN ASM_REWRITE_TAC[]
);


(*---------------------------------------------------------------------------
      Temporal operators as co-Buechi expressions.
 ---------------------------------------------------------------------------*)

val NEXT_AS_CO_BUECHI = TAC_PROOF(
	([],--`(NEXT a) t0
	       = ?p q.
			(~p t0 /\ ~q t0) /\
			(!t.
			    ~p(t+t0) /\ ~q(t+t0) /\             p(t+(1+t0)) /\ ~q(t+(1+t0)) \/
			     p(t+t0) /\ ~q(t+t0) /\ a(t+t0) /\  p(t+(1+t0)) /\  q(t+(1+t0)) \/
			     p(t+t0) /\  q(t+t0)            /\  p(t+(1+t0)) /\  q(t+(1+t0))
			) /\
			(?t1.!t2. q(t1+(t2+t0)))
	    `--),
	REWRITE_TAC[EQT_ELIM(ARITH_CONV(--`t+(1+t0) = SUC(t+t0)`--))]
	THEN REWRITE_TAC[NEXT] THEN BETA_TAC
	THEN EQ_TAC THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[]
	THENL[
	    EXISTS_TAC(--`\x.t0<x`--) THEN EXISTS_TAC(--`\x.SUC t0<x`--)
	    THEN BETA_TAC THEN REWRITE_TAC[LESS_REFL]
	    THEN REWRITE_TAC[EQT_ELIM(ARITH_CONV(--`~(SUC t0 < t0)`--))]
	    THEN CONJ_TAC
	    THENL[ALL_TAC,EXISTS_TAC (--`SUC(SUC 0)`--) THEN CONV_TAC ARITH_CONV]
	    THEN GEN_TAC
	    THEN DISJ_CASES_TAC(EQT_ELIM(ARITH_CONV(--`(t=0) \/ (t=SUC 0) \/ ((SUC 0) <t)`--)))
	    THENL[ALL_TAC,POP_ASSUM DISJ_CASES_TAC]
	    THENL[
		DISJ1_TAC
		THEN POP_ASSUM SUBST1_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES,LESS_REFL]
		THEN CONV_TAC ARITH_CONV,
		DISJ2_TAC THEN DISJ1_TAC
		THEN POP_ASSUM SUBST1_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES]
		THEN CONV_TAC ARITH_CONV,
		DISJ2_TAC THEN DISJ2_TAC
		THEN IMP_RES_TAC LESS_ADD_1
		THEN POP_ASSUM SUBST1_TAC THEN CONV_TAC ARITH_CONV
		],
	    MY_MP_TAC (--`p(SUC t0) /\~q(SUC t0)`--)
	    THENL[
		LEFT_NO_FORALL_TAC 1 (--`0`--) THEN UNDISCH_HD_TAC
	    	THEN ASM_REWRITE_TAC[ADD_CLAUSES],
		DISCH_TAC]
	    THEN LEFT_NO_FORALL_TAC 2 (--`SUC 0`--) THEN UNDISCH_HD_TAC
	    THEN ASM_REWRITE_TAC[ADD_CLAUSES]
	    THEN STRIP_TAC
	    ]);




val SUNTIL_AS_CO_BUECHI = TAC_PROOF(
	([],--`(a SUNTIL b) t0
	       = ?q.
			(~q t0) /\
			(!t.
			    ~q(t+t0) /\ a(t+t0) /\ ~b(t+t0) /\ ~q(t+(1+t0)) \/
			    ~q(t+t0) /\             b(t+t0) /\  q(t+(1+t0)) \/
			     q(t+t0) /\  q(t+(1+t0))
			) /\
			(?t1.!t2. q(t1+(t2+t0)))
	    `--),
	REWRITE_TAC[EQT_ELIM(ARITH_CONV(--`t+(1+t0) = SUC(t+t0)`--))]
	THEN REWRITE_TAC[SUNTIL,WATCH]
	THEN EQ_TAC THEN REPEAT STRIP_TAC
	THENL[
	    EXISTS_TAC(--`q:num->bool`--) THEN ASM_REWRITE_TAC[]
	    THEN CONJ_TAC
	    THENL[
		GEN_TAC THEN LEFT_NO_FORALL_TAC 1 (--`t':num`--)
	    	THEN UNDISCH_HD_TAC THEN PROP_TAC,
		EXISTS_TAC (--`SUC t`--)
		THEN INDUCT_TAC	THEN ASM_REWRITE_TAC[ADD_CLAUSES]
		THEN ASM_REWRITE_TAC[EQT_ELIM(ARITH_CONV
			(--`SUC(SUC(t+(t2+t0))) = SUC((SUC t + t2)+t0)`--))]
		THEN ASM_REWRITE_TAC[EQT_ELIM(ARITH_CONV
			(--`(SUC t + t2)+t0 = (SUC t)+(t2+t0)`--))]
		],
	    EXISTS_TAC(--`q:num->bool`--) THEN ASM_REWRITE_TAC[]
	    THEN REWRITE_TAC[TAC_PROOF(([],--`a/\b/\c = (a/\b)/\c`--),PROP_TAC)]
	    THEN CONV_TAC(DEPTH_CONV AND_FORALL_CONV)
	    THEN LEFT_CONJ_TAC
	    THENL[
		GEN_TAC THEN LEFT_NO_FORALL_TAC 1 (--`t:num`--)
		THEN UNDISCH_HD_TAC THEN PROP_TAC,
		ONCE_REWRITE_TAC[TAC_PROOF(([],--`a = ~~a`--),PROP_TAC)]
		THEN CONV_TAC(DEPTH_CONV NOT_EXISTS_CONV)
		THEN DISCH_TAC
		THEN POP_ASSUM (fn x=> RULE_ASSUM_TAC(REWRITE_RULE[x]))
		THEN MY_MP_TAC(--`!t. ~q(t+t0)`--)
		THENL[
		    INDUCT_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES],
		    DISCH_TAC]
		THEN UNDISCH_NO_TAC 2 THEN ASM_REWRITE_TAC[ADD_ASSOC]
		]
	    ]);





val UNTIL_AS_CO_BUECHI = TAC_PROOF(
	([],--`(a UNTIL b) t0
	       = ?q.
			(~q t0) /\
			(!t.
			    ~q(t+t0) /\ a(t+t0) /\ ~b(t+t0) /\ ~q(t+(1+t0)) \/
			    ~q(t+t0) /\             b(t+t0) /\  q(t+(1+t0)) \/
			     q(t+t0) /\  q(t+(1+t0))
			) /\
			(?t1.!t2. ~q(t1+(t2+t0)) \/ q(t1+(t2+t0)))
	    `--),
	REWRITE_TAC[EQT_ELIM(ARITH_CONV(--`t+(1+t0) = SUC(t+t0)`--))]
	THEN REWRITE_TAC[UNTIL,WATCH]
	THEN EQ_TAC THEN REPEAT STRIP_TAC
	THENL[
	    EXISTS_TAC(--`q:num->bool`--) THEN ASM_REWRITE_TAC[]
	    THEN REWRITE_TAC[TAC_PROOF(([],--`~a\/a`--),PROP_TAC)]
	    THEN GEN_TAC THEN LEFT_FORALL_TAC (--`t:num`--)
	    THEN UNDISCH_HD_TAC THEN PROP_TAC,
	    POP_NO_TAC 0
	    THEN EXISTS_TAC(--`q:num->bool`--) THEN ASM_REWRITE_TAC[]
	    THEN LEFT_CONJ_TAC
	    THENL[
		INDUCT_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES]
		THENL[
		    LEFT_FORALL_TAC (--`0`--) THEN UNDISCH_HD_TAC
		    THEN ASM_REWRITE_TAC[ADD_CLAUSES]
		    THEN PROP_TAC,
		    LEFT_NO_FORALL_TAC 1 (--`SUC t`--) THEN UNDISCH_HD_TAC
		    THEN ASM_REWRITE_TAC[ADD_CLAUSES]
		    THEN PROP_TAC],
		GEN_TAC THEN DISJ_CASES_TAC(SPEC(--`q(t+t0):bool`--)BOOL_CASES_AX)
		THEN ASM_REWRITE_TAC[]
		THEN LEFT_NO_FORALL_TAC 2 (--`t:num`--)
		THEN UNDISCH_HD_TAC THEN ASM_REWRITE_TAC[]
		THEN PROP_TAC
		]
	    ]);





val WHEN_AS_CO_BUECHI = TAC_PROOF(
	([],--`(a WHEN b) t0
	       = ?q.
			(~q t0) /\
			(!t.
			    ~q(t+t0) /\            ~b(t+t0) /\ ~q(t+(1+t0)) \/
			    ~q(t+t0) /\  a(t+t0) /\ b(t+t0) /\  q(t+(1+t0)) \/
			     q(t+t0) /\  q(t+(1+t0))
			) /\
			(?t1.!t2. ~q(t1+(t2+t0)) \/ q(t1+(t2+t0)))
	    `--),
	REWRITE_TAC[EQT_ELIM(ARITH_CONV(--`t+(1+t0) = SUC(t+t0)`--))]
	THEN REWRITE_TAC[WHEN,WATCH]
	THEN EQ_TAC THEN REPEAT STRIP_TAC
	THENL[
	    EXISTS_TAC(--`q:num->bool`--) THEN ASM_REWRITE_TAC[]
	    THEN REWRITE_TAC[TAC_PROOF(([],--`~a\/a`--),PROP_TAC)]
	    THEN GEN_TAC THEN LEFT_FORALL_TAC (--`t:num`--)
	    THEN UNDISCH_HD_TAC THEN PROP_TAC,
	    POP_NO_TAC 0
	    THEN EXISTS_TAC(--`q:num->bool`--) THEN ASM_REWRITE_TAC[]
	    THEN LEFT_CONJ_TAC
	    THENL[
		INDUCT_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES]
		THENL[
		    LEFT_FORALL_TAC (--`0`--) THEN UNDISCH_HD_TAC
		    THEN ASM_REWRITE_TAC[ADD_CLAUSES]
		    THEN PROP_TAC,
		    LEFT_NO_FORALL_TAC 1 (--`SUC t`--) THEN UNDISCH_HD_TAC
		    THEN ASM_REWRITE_TAC[ADD_CLAUSES]
		    THEN PROP_TAC],
		GEN_TAC THEN DISJ_CASES_TAC(SPEC(--`q(t+t0):bool`--)BOOL_CASES_AX)
		THEN ASM_REWRITE_TAC[]
		THEN LEFT_NO_FORALL_TAC 2 (--`t:num`--)
		THEN UNDISCH_HD_TAC THEN ASM_REWRITE_TAC[]
		THEN PROP_TAC
		]
	    ]);




val SWHEN_AS_CO_BUECHI = TAC_PROOF(
	([],--`(a SWHEN b) t0
	       = ?q.
			(~q t0) /\
			(!t.
			    ~q(t+t0) /\            ~b(t+t0) /\ ~q(t+(1+t0)) \/
			    ~q(t+t0) /\  a(t+t0) /\ b(t+t0) /\  q(t+(1+t0)) \/
			     q(t+t0) /\  q(t+(1+t0))
			) /\
			(?t1.!t2. q(t1+(t2+t0)))
	    `--),
	REWRITE_TAC[SWHEN_SIGNAL]
	THEN EQ_TAC THEN REPEAT STRIP_TAC
	THENL[
	    EXISTS_TAC(--`\x.delta+t0<x`--)
	    THEN BETA_TAC THEN ASM_REWRITE_TAC[]
	    THEN REWRITE_TAC[EQT_ELIM(ARITH_CONV(--`~(delta+t0<t0)`--))]
	    THEN CONJ_TAC
	    THENL[
		ALL_TAC,
		EXISTS_TAC(--`delta+(t0+1)`--) THEN CONV_TAC ARITH_CONV
		]
	    THEN REPEAT STRIP_TAC
	    THEN DISJ_CASES_TAC(EQT_ELIM(ARITH_CONV(--`(delta<t) \/ (delta=t) \/ (t<delta)`--)))
	    THENL[ALL_TAC,POP_ASSUM DISJ_CASES_TAC]
	    THENL[
		IMP_RES_TAC(EQT_ELIM(ARITH_CONV(--`(delta<t) ==> delta+t0<t+t0`--)))
		THEN IMP_RES_TAC(EQT_ELIM(ARITH_CONV(--`(delta<t) ==> delta+t0<t+(1+t0)`--)))
		THEN POP_ASSUM REWRITE1_TAC THEN POP_ASSUM REWRITE1_TAC,
		DISJ2_TAC THEN DISJ1_TAC THEN POP_ASSUM(SUBST1_TAC o SYM)
		THEN ASM_REWRITE_TAC[] THEN CONV_TAC ARITH_CONV,
		DISJ1_TAC
		THEN IMP_RES_TAC(EQT_ELIM(ARITH_CONV(--`(t<delta) ==> ~(delta+t0<t+t0)`--)))
		THEN IMP_RES_TAC(EQT_ELIM(ARITH_CONV(--`(t<delta) ==> ~(delta+t0<t+(1+t0))`--)))
		THEN POP_ASSUM REWRITE1_TAC THEN POP_ASSUM REWRITE1_TAC
		THEN RES_TAC THEN ASM_REWRITE_TAC[]
		],
	    DISJ_CASES_TAC DELTA_CASES
	    THENL[
		LEFT_EXISTS_TAC THEN EXISTS_TAC (--`d:num`--)
		THEN ASM_REWRITE_TAC[]
		THEN MY_MP_TAC (--`!t. t<=d ==> ~q(t+t0)`--)
		THENL[
		    INDUCT_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES]
		    THEN DISCH_TAC
		    THEN IMP_RES_TAC(EQT_ELIM(ARITH_CONV(--`(SUC t<=d) ==> t<d`--)))
		    THEN IMP_RES_TAC(EQT_ELIM(ARITH_CONV(--`(t<d) ==> t<=d`--)))
		    THEN RES_TAC THEN ASM_REWRITE_TAC[]
		    THEN LEFT_NO_FORALL_TAC 8 (--`t:num`--)
		    THEN UNDISCH_HD_TAC
		    THEN ASM_REWRITE_TAC[ADD_CLAUSES,ADD_ASSOC,SYM(SPEC_ALL ADD1)],
		    DISCH_TAC]
		THEN LEFT_NO_FORALL_TAC 0 (--`d:num`--)
		THEN LEFT_NO_FORALL_TAC 3 (--`d:num`--)
		THEN UNDISCH_HD_TAC THEN UNDISCH_HD_TAC
		THEN REWRITE_TAC[LESS_EQ_REFL]
		THEN DISCH_TAC THEN ASM_REWRITE_TAC[]
		THEN DISCH_TAC THEN ASM_REWRITE_TAC[],
		ASM_REWRITE_TAC[]
		THEN UNDISCH_NO_TAC 2 THEN ASM_REWRITE_TAC[]
		THEN DISCH_TAC
		THEN MY_MP_TAC (--`!t. ~q(t+t0)`--)
		THENL[
		    INDUCT_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES]
		    THEN LEFT_NO_FORALL_TAC 1 (--`t:num`--)
		    THEN UNDISCH_HD_TAC THEN ASM_REWRITE_TAC[]
		    THEN REWRITE_TAC[ADD_CLAUSES,ADD_ASSOC,SYM(SPEC_ALL ADD1)]
		    THEN STRIP_TAC,
		    DISCH_TAC]
		THEN UNDISCH_NO_TAC 3
		THEN ASM_REWRITE_TAC[ADD_ASSOC]
		]
	    ]);







val SBEFORE_AS_CO_BUECHI = TAC_PROOF(
	([],--`(a SBEFORE b) t0
	       = ?q.
			(~q t0) /\
			(!t.
			    ~q(t+t0) /\ ~a(t+t0) /\ ~b(t+t0) /\ ~q(t+(1+t0)) \/
			    ~q(t+t0) /\  a(t+t0) /\ ~b(t+t0) /\  q(t+(1+t0)) \/
			     q(t+t0) /\  q(t+(1+t0))
			) /\
			(?t1.!t2. q(t1+(t2+t0)))
	    `--),
	REWRITE_TAC[SBEFORE_SIGNAL]
	THEN EQ_TAC THEN REPEAT STRIP_TAC
	THENL[
	    DISJ_CASES_TAC(SPEC(--`a:num->bool`--)(GEN(--`b:num->bool`--)DELTA_CASES))
	    THENL[UNDISCH_HD_TAC THEN STRIP_TAC, UNDISCH_NO_TAC 2 THEN ASM_REWRITE_TAC[]]
	    THEN MY_MP_TAC (--`d<=delta`--)
	    THENL[
		ONCE_REWRITE_TAC[TAC_PROOF(([],--`a = ~~a`--),PROP_TAC)]
		THEN SUBST1_TAC(EQT_ELIM(ARITH_CONV(--`~(d<=delta) = delta<d`--)))
		THEN DISCH_TAC THEN RES_TAC,
		DISCH_TAC]
	    THEN MY_MP_TAC (--`!t. t<=d ==> ~b(t+t0)`--)
	    THENL[
		REPEAT STRIP_TAC THEN IMP_RES_TAC LESS_EQ_TRANS
		THEN RES_TAC,
		DISCH_TAC]
	    THEN MAP_EVERY POP_NO_TAC [5,4,1]
	    THEN EXISTS_TAC(--`\x. d+t0<x`--)
	    THEN BETA_TAC THEN ASM_REWRITE_TAC[]
	    THEN REWRITE_TAC[EQT_ELIM(ARITH_CONV(--`~(d+t0<t0)`--))]
	    THEN CONJ_TAC (* prove the acceptance condition in advance *)
	    THENL[
		ALL_TAC,
		EXISTS_TAC(--`d+(t0+1)`--) THEN CONV_TAC ARITH_CONV
		]
	    (* now only the transition relation remains to be proved *)
	    THEN GEN_TAC
	    THEN DISJ_CASES_TAC(EQT_ELIM(ARITH_CONV(--`(d<t) \/ (d=t) \/ (t<d)`--)))
	    THENL[ALL_TAC,POP_ASSUM DISJ_CASES_TAC]
	    THENL[
		IMP_RES_TAC(EQT_ELIM(ARITH_CONV(--`(d<t) ==> d+t0<t+t0`--)))
		THEN IMP_RES_TAC(EQT_ELIM(ARITH_CONV(--`(d<t) ==> d+t0<t+(1+t0)`--)))
		THEN POP_ASSUM REWRITE1_TAC THEN POP_ASSUM REWRITE1_TAC,
		DISJ2_TAC THEN DISJ1_TAC THEN POP_ASSUM(SUBST1_TAC o SYM)
		THEN ASM_REWRITE_TAC[] THEN LEFT_FORALL_TAC (--`d:num`--)
		THEN UNDISCH_HD_TAC THEN REWRITE_TAC[LESS_EQ_REFL]
		THEN DISCH_TAC THEN ASM_REWRITE_TAC[]
		THEN CONV_TAC ARITH_CONV,
		DISJ1_TAC
		THEN IMP_RES_TAC(EQT_ELIM(ARITH_CONV(--`(t<d) ==> ~(d+t0<t+t0)`--)))
		THEN IMP_RES_TAC(EQT_ELIM(ARITH_CONV(--`(t<d) ==> ~(d+t0<t+(1+t0))`--)))
		THEN IMP_RES_TAC(EQT_ELIM(ARITH_CONV(--`(t<d) ==> (t<=d)`--)))
		THEN RES_TAC THEN ASM_REWRITE_TAC[]
		],
  	    DISJ_CASES_TAC(SPEC(--`q:num->bool`--)(GEN(--`b:num->bool`--)DELTA_CASES))
	    THENL[ALL_TAC, UNDISCH_NO_TAC 1 THEN ASM_REWRITE_TAC[ADD_ASSOC]]
	    THEN UNDISCH_HD_TAC THEN STRIP_TAC
	    THEN MY_MP_TAC (--`0<d`--)
	    THENL[
		SUBST1_TAC(EQT_ELIM(ARITH_CONV(--`(0<d) = ~(d=0)`--)))
		THEN DISCH_TAC THEN UNDISCH_NO_TAC 1 THEN ASM_REWRITE_TAC[ADD_CLAUSES],
		DISCH_TAC]
	    THEN IMP_RES_TAC LESS_ADD_1
	    THEN EXISTS_TAC(--`p:num`--)
	    THEN MY_MP_TAC (--`!t. t<d ==> ~b(t+t0)`--)
	    THENL[
		ONCE_REWRITE_TAC[TAC_PROOF(([],--`a = ~~a`--),PROP_TAC)]
		THEN CONV_TAC(DEPTH_CONV NOT_FORALL_CONV)
		THEN REWRITE_TAC[TAC_PROOF(([],--`~(a==>b) = a/\~b`--),PROP_TAC)]
		THEN STRIP_TAC THEN RES_TAC THEN LEFT_NO_FORALL_TAC 9 (--`t:num`--)
		THEN UNDISCH_HD_TAC THEN ASM_REWRITE_TAC[],
		DISCH_TAC]
	    THEN UNDISCH_HD_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES]
	    THEN REWRITE_TAC[EQT_ELIM(ARITH_CONV(--`(t<p+1) = (t<=p)`--))]
	    THEN DISCH_TAC THEN ASM_REWRITE_TAC[]
	    THEN LEFT_NO_FORALL_TAC 6 (--`p:num`--) THEN UNDISCH_HD_TAC
	    THEN LEFT_NO_FORALL_TAC 0 (--`p:num`--) THEN UNDISCH_HD_TAC
	    THEN LEFT_NO_FORALL_TAC 3 (--`p:num`--) THEN UNDISCH_HD_TAC
	    THEN ASM_REWRITE_TAC[ADD_CLAUSES]
	    THEN REWRITE_TAC[EQT_ELIM(ARITH_CONV(--`p<p+1`--))]
	    THEN REWRITE_TAC[EQT_ELIM(ARITH_CONV(--`p<=p`--))]
	    THEN DISCH_TAC THEN ASM_REWRITE_TAC[]
	    THEN DISCH_TAC THEN ASM_REWRITE_TAC[]
	    THEN STRIP_TAC
	    THEN UNDISCH_NO_TAC 6
	    THEN ASM_REWRITE_TAC[ADD_CLAUSES,SYM(SPEC_ALL ADD_ASSOC)]
	    ]);






val BEFORE_AS_CO_BUECHI = TAC_PROOF(
	([],--`(a BEFORE b) t0
	       = ?q.
			(~q t0) /\
			(!t.
			    ~q(t+t0) /\ ~a(t+t0) /\ ~b(t+t0) /\ ~q(t+(1+t0)) \/
			    ~q(t+t0) /\  a(t+t0) /\ ~b(t+t0) /\  q(t+(1+t0)) \/
			     q(t+t0) /\  q(t+(1+t0))
			) /\
			(?t1.!t2. ~q(t1+(t2+t0)) \/ q(t1+(t2+t0)))
	    `--),
	REWRITE_TAC[BEFORE_AS_SBEFORE,ALWAYS_SIGNAL]
	THEN BETA_TAC
	THEN REWRITE_TAC[SBEFORE_AS_CO_BUECHI]
	THEN REWRITE_TAC[TAC_PROOF(([],--`~a \/ a`--),PROP_TAC)]
	THEN EQ_TAC THEN STRIP_TAC
	THENL[
	    EXISTS_TAC(--`q:num->bool`--) THEN ASM_REWRITE_TAC[],
	    POP_ASSUM REWRITE1_TAC
	    THEN DISJ_CASES_TAC(SPEC(--`a:num->bool`--)(GEN(--`b:num->bool`--)DELTA_CASES))
	    THEN ASM_REWRITE_TAC[]
	    THENL[
		UNDISCH_HD_TAC THEN STRIP_TAC
		THEN EXISTS_TAC (--`\x. d+t0<x`--) THEN BETA_TAC
		THEN REWRITE_TAC[EQT_ELIM(ARITH_CONV(--`~(d+t0<t0)`--))]
	    	THEN GEN_TAC
		THEN DISJ_CASES_TAC(EQT_ELIM(ARITH_CONV(--`(d<t) \/ (d=t) \/ (t<d)`--)))
	    	THENL[ALL_TAC,POP_ASSUM DISJ_CASES_TAC]
	    	THENL[
		    IMP_RES_TAC(EQT_ELIM(ARITH_CONV(--`(d<t) ==> d+t0<t+t0`--)))
		    THEN IMP_RES_TAC(EQT_ELIM(ARITH_CONV(--`(d<t) ==> d+t0<t+(1+t0)`--)))
		    THEN POP_ASSUM REWRITE1_TAC THEN POP_ASSUM REWRITE1_TAC,
		    DISJ2_TAC THEN DISJ1_TAC THEN POP_ASSUM(SUBST1_TAC o SYM)
		    THEN ASM_REWRITE_TAC[] THEN CONV_TAC ARITH_CONV,
		    DISJ1_TAC
		    THEN IMP_RES_TAC(EQT_ELIM(ARITH_CONV(--`(t<d) ==> ~(d+t0<t+t0)`--)))
		    THEN IMP_RES_TAC(EQT_ELIM(ARITH_CONV(--`(t<d) ==> ~(d+t0<t+(1+t0))`--)))
		    THEN POP_ASSUM REWRITE1_TAC THEN POP_ASSUM REWRITE1_TAC
		    THEN RES_TAC THEN ASM_REWRITE_TAC[]
		    ],
		EXISTS_TAC (--`\t:num.F`--) THEN BETA_TAC
		THEN REWRITE_TAC[]
		],
	    ONCE_REWRITE_TAC[TAC_PROOF(([],--`a \/ b = (~b ==> a)`--),PROP_TAC)]
	    THEN CONV_TAC(DEPTH_CONV NOT_FORALL_CONV)
	    THEN REWRITE_TAC[] THEN DISCH_TAC
	    THEN EXISTS_TAC (--`q:num->bool`--) THEN ASM_REWRITE_TAC[]
	    THEN MY_MP_TAC (--`(?t. q(t+t0)) ==> ?t1.!t2. q(t1+(t2+t0))`--)
	    THENL[
		STRIP_TAC THEN EXISTS_TAC (--`t:num`--)
		THEN INDUCT_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES]
		THEN LEFT_NO_FORALL_TAC 3 (--`t+t2`--)
		THEN UNDISCH_HD_TAC THEN ASM_REWRITE_TAC[SYM(SPEC_ALL ADD_ASSOC)]
		THEN REWRITE_TAC[num_CONV(--`1`--),ADD_CLAUSES],
		DISCH_TAC]
	    THEN POP_ASSUM MATCH_MP_TAC
	    THEN UNDISCH_HD_TAC THEN CONV_TAC CONTRAPOS_CONV
	    THEN CONV_TAC(DEPTH_CONV NOT_EXISTS_CONV)
	    THEN DISCH_TAC THEN UNDISCH_NO_TAC 1
	    THEN ASM_REWRITE_TAC[ADD_ASSOC] THEN DISCH_TAC
	    THEN INDUCT_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES]
	    ]);


(*---------------------------------------------------------------------------
       Periodicity
 ---------------------------------------------------------------------------*)

val REPETITION_LEMMA = TAC_PROOF(
	([],--`(!t1.?t2.Phi(q(t1+t2):'state)) /\ (!s:num->'state.?x0 l. (0<l) /\ (s x0 = s(x0+l)))
		==> (?x0 l. (0<l) /\ (q x0 = q(x0+l)) /\ Phi(q x0))`--),
	REPEAT STRIP_TAC
	THEN ASSUME_TAC(EXISTENCE(BETA_RULE(ISPECL
		[(--`@d.Phi((q d):'state) /\ !d'. d'<d==>~Phi((q d'))`--),
		 (--`\x y:num.x+(1+(@d.Phi(q(x+(1+d)):'state) /\
				      !d'. d'<d==>~Phi(q(x+(1+d')))))`--)]num_Axiom_old)))
	THEN LEFT_EXISTS_TAC
	THEN MY_MP_TAC (--`!t:num.Phi((q((fn1 t):num)):'state)`--)
	THENL[
	    GEN_TAC THEN DISJ_CASES_TAC(SPEC(--`t:num`--)num_CASES)
	    THENL[
		ASM_REWRITE_TAC[]
		THEN SELECT_EXISTS_TAC (--`@d.Phi((q d):'state) /\
					      (!d'.d'<d ==> ~(Phi(q d')))`--)
		THENL[
		    MATCH_MP_TAC(BETA_RULE(SPEC(--`\x:num.(Phi:'state->bool)(q x)`--)WOP))
		    THEN LEFT_NO_FORALL_TAC 3 (--`0`--) THEN LEFT_EXISTS_TAC
		    THEN EXISTS_TAC (--`0+t2`--) THEN ASM_TAC 0 REWRITE1_TAC,
		    REPEAT STRIP_TAC],
		LEFT_EXISTS_TAC THEN ASM_REWRITE_TAC[]
		THEN SELECT_EXISTS_TAC (--`@d.(Phi:'state->bool)(q((fn1(n:num))+(1+d))) /\
           				      (!d'.d'<d ==>~Phi(q((fn1 n)+(1+d'))))`--)
		THENL[
		    MATCH_MP_TAC(BETA_RULE
				(SPEC(--`\x.(Phi:'state->bool)(q((fn1(n:num))+(1+x)))`--)WOP))
		    THEN LEFT_NO_FORALL_TAC 3 (--`fn1(n:num) + 1`--) THEN LEFT_EXISTS_TAC
		    THEN EXISTS_TAC (--`t2:num`--) THEN ASM_REWRITE_TAC[ADD_ASSOC],
		    REPEAT STRIP_TAC]],
	    DISCH_TAC]
	THEN MY_MP_TAC (--`!t. fn1 t < fn1(SUC t)`--)
	THENL[
	    GEN_TAC THEN ASM_REWRITE_TAC[EQT_ELIM(ARITH_CONV(--`x<x+(1+y)`--))],
	    DISCH_TAC]
	THEN MY_MP_TAC (--`!t1 t2. t1<t2 ==> fn1 t1 < fn1 t2`--)
	THENL[
	    REPEAT STRIP_TAC THEN IMP_RES_TAC LESS_ADD_1
	    THEN POP_ASSUM SUBST1_TAC THEN SPEC_TAC((--`p:num`--),(--`p:num`--))
	    THEN INDUCT_TAC THEN REWRITE_TAC[ADD_CLAUSES]
	    THENL[
		REWRITE_TAC[SYM(SPEC_ALL ADD1)] THEN ASM_TAC 1 REWRITE1_TAC,
		MATCH_MP_TAC LESS_TRANS THEN EXISTS_TAC (--`fn1(t1+(p+1)):num`--)
		THEN POP_ASSUM REWRITE1_TAC THEN ASM_TAC 1 REWRITE1_TAC],
	DISCH_TAC]
	THEN LEFT_NO_FORALL_TAC 4 (--`\t:num.q((fn1 t):num):'state`--)
	THEN LEFT_EXISTS_TAC THEN LEFT_EXISTS_TAC
	THEN UNDISCH_HD_TAC THEN BETA_TAC THEN STRIP_TAC
	THEN LEFT_NO_FORALL_TAC 4 (--`x0:num`--)
	THEN EXISTS_TAC (--`(fn1:num->num) x0`--)
	THEN LEFT_NO_FORALL_TAC 3 (--`x0:num`--)
	THEN LEFT_FORALL_TAC (--`x0+l`--)
	THEN IMP_RES_TAC(EQT_ELIM(ARITH_CONV(--`(0<l)==>(x0<x0+l)`--)))
	THEN UNDISCH_NO_TAC 1 THEN ASM_REWRITE_TAC[]
	THEN DISCH_TAC THEN IMP_RES_TAC LESS_ADD_1
	THEN EXISTS_TAC (--`p+1`--)
	THEN ASM_REWRITE_TAC[SYM(SPEC_ALL ADD1),LESS_0]);




val REPETITION_BOOL_LEMMA = TAC_PROOF(
	([],--` (!s:num->'state.?x0 l. (0<l) /\ (s(x0)=s(x0+l))) ==>
		(!s:num->'state.!q:num->bool.?x0 l.
				(0<l) /\ (s x0 =s(x0+l)) /\ (q x0 = q(x0+l)))`--),
	REPEAT STRIP_TAC
	THEN DISJ_CASES_TAC(SPEC(--`?t0.!t.~q(t+t0)`--)
				(REWRITE_RULE[]BOOL_CASES_AX))
	THENL[
	    LEFT_EXISTS_TAC THEN LEFT_NO_FORALL_TAC 1 (--`\t. s(t+t0):'state`--)
	    THEN RULE_ASSUM_TAC BETA_RULE
	    THEN LEFT_EXISTS_TAC THEN LEFT_EXISTS_TAC
	    THEN EXISTS_TAC(--`x0+t0`--) THEN EXISTS_TAC (--`l:num`--)
	    THEN SUBST1_TAC(EQT_ELIM(ARITH_CONV(--`(x0+t0)+l=(x0+l)+t0`--)))
	    THEN ASM_REWRITE_TAC[],
	    ALL_TAC]
	THEN ASSUME_TAC(EXISTENCE(BETA_RULE(ISPECL
		[(--`@d:num. q d /\ (!d'. d'<d==>~q d')`--),
		 (--`\x y:num.x+(1+(@d.q(x+(1+d)) /\
				      (!d'.d'<d==>~q(x+(1+d')))))`--)]num_Axiom_old)))
	THEN LEFT_EXISTS_TAC
	THEN MY_MP_TAC (--`!t. fn1 t < fn1(SUC t)`--)
	THENL[
	    GEN_TAC THEN ASM_REWRITE_TAC[EQT_ELIM(ARITH_CONV(--`x<x+(1+y)`--))],
	    DISCH_TAC]
	THEN MY_MP_TAC (--`!t1 t2. t1<t2 ==> fn1 t1 < fn1 t2`--)
	THENL[
	    REPEAT STRIP_TAC THEN IMP_RES_TAC LESS_ADD_1
	    THEN POP_ASSUM SUBST1_TAC THEN SPEC_TAC((--`p:num`--),(--`p:num`--))
	    THEN INDUCT_TAC THEN REWRITE_TAC[ADD_CLAUSES]
	    THENL[
		REWRITE_TAC[SYM(SPEC_ALL ADD1)] THEN ASM_TAC 1 REWRITE1_TAC,
		MATCH_MP_TAC LESS_TRANS THEN EXISTS_TAC (--`fn1(t1+(p+1)):num`--)
		THEN POP_ASSUM REWRITE1_TAC THEN ASM_TAC 1 REWRITE1_TAC],
	DISCH_TAC]
	THEN MY_MP_TAC (--`!t. q((fn1:num->num) t)`--)
	THENL[
	    UNDISCH_NO_TAC 3 THEN CONV_TAC(DEPTH_CONV NOT_EXISTS_CONV)
	    THEN CONV_TAC(DEPTH_CONV NOT_FORALL_CONV) THEN REWRITE_TAC[]
	    THEN DISCH_TAC THEN INDUCT_TAC THEN ASM_REWRITE_TAC[]
	    THENL[
		SELECT_EXISTS_TAC (--`@d:num. q d /\ (!d'. d'<d ==> ~q d')`--)
		THENL[ALL_TAC,REPEAT STRIP_TAC]
	        THEN MATCH_MP_TAC WOP THEN LEFT_FORALL_TAC (--`0`--)
		THEN LEFT_EXISTS_TAC THEN EXISTS_TAC (--`t:num`--)
		THEN UNDISCH_HD_TAC THEN REWRITE_TAC[ADD_CLAUSES],
		SELECT_EXISTS_TAC (--`@d:num.q((fn1 (t:num))+(1+d))/\
					     (!d'.d'<d==>~(q((fn1 t)+(1+d'))))`--)
		THENL[ALL_TAC,REPEAT STRIP_TAC]
		THEN MATCH_MP_TAC(BETA_RULE(SPEC(--`\x.q((fn1(t:num))+(1+x)):bool`--)WOP))
		THEN LEFT_NO_FORALL_TAC 1 (--`(fn1(t:num))+1`--)
		THEN LEFT_EXISTS_TAC THEN EXISTS_TAC (--`t':num`--)
		THEN UNDISCH_HD_TAC
		THEN SUBST1_TAC(SPECL[(--`t':num`--),(--`(fn1(t:num))+1`--)]ADD_SYM)
		THEN REWRITE_TAC[ADD_ASSOC]],
	    DISCH_TAC]
	THEN LEFT_NO_FORALL_TAC 5 (--`\t:num.(s:num->'state)(fn1 t)`--)
	THEN LEFT_EXISTS_TAC THEN LEFT_EXISTS_TAC
	THEN RULE_ASSUM_TAC BETA_RULE
	THEN EXISTS_TAC(--`(fn1:num->num) x0`--)
	THEN EXISTS_TAC(--`(fn1:num->num) (x0 + l) - (fn1:num->num) x0`--)
	THEN UNDISCH_HD_TAC THEN STRIP_TAC
	THEN IMP_RES_TAC(EQT_ELIM(ARITH_CONV(--`(0<l) ==> (x0<x0+l)`--)))
	THEN LEFT_FORALL_TAC (--`x0:num`--) THEN RES_TAC
	THEN IMP_RES_TAC LESS_IMP_LESS_OR_EQ
	THEN IMP_RES_TAC(ONCE_REWRITE_RULE[ADD_SYM]SUB_ADD)
	THEN ASM_TAC 1 SUBST1_TAC THEN ASM_REWRITE_TAC[]
	THEN UNDISCH_NO_TAC 9 THEN CONV_TAC ARITH_CONV)
;



val SUC_MOD_LEMMA = TAC_PROOF(
	([],--`0<y ==> ((x+1) MOD y = (if ((x MOD y)+1=y) then 0 else (x MOD y)+1))`--),
	DISCH_TAC THEN MATCH_MP_TAC MOD_UNIQUE THEN IMP_RES_TAC DIVISION
	THEN POP_NO_ASSUM 1 (fn x=> ASSUME_TAC(GEN_ALL(SYM(SPEC_ALL x))))
	THEN LEFT_NO_FORALL_TAC 1 (--`x:num`--) THEN IMP_RES_TAC LESS_OR
	THEN POP_NO_TAC 0 THEN UNDISCH_HD_TAC THEN REWRITE_TAC[ADD1,LESS_OR_EQ]
	THEN DISJ_CASES_TAC(SPEC(--`(x MOD y)+1 = y`--)(REWRITE_RULE[]BOOL_CASES_AX))
	THEN ASM_REWRITE_TAC[]
	THENL[
	    LEFT_NO_FORALL_TAC 2 (--`x:num`--)
	    THEN POP_ASSUM (SUBST1_TAC o SYM)
	    THEN ASM_REWRITE_TAC[SYM(SPEC_ALL ADD_ASSOC)]
	    THEN EXISTS_TAC (--`(x DIV y)+1`--)
	    THEN REWRITE_TAC[ADD_CLAUSES,MULT_CLAUSES,RIGHT_ADD_DISTRIB],
	    DISCH_TAC THEN EXISTS_TAC (--`x DIV y`--)
	    THEN ASM_REWRITE_TAC[ADD_ASSOC]])
;




val BUECHI_PERIODIC_MODEL = TAC_PROOF(
	([],--` (!s:num->'state.?x0 l. (0<l) /\ (s(x0)=s(x0+l)))
		  ==>
		    ((?(i:num->'a) (q:num->'state).
			    InitState(q 0) /\
			    (!t.TransRel(i t,q t,q(t+1))) /\
			    (!t1.?t2. Accept(q(t1+t2))))
		   =
		     (?x0 l j p.
			    (0<l) /\
			    (!t2. j(x0+t2) = j(x0+(t2 MOD l))) /\
			    (!t2. p(x0+t2) = p(x0+(t2 MOD l))) /\
			    InitState(p 0) /\ (!t.TransRel(j t,p t,p(t+1))) /\
			    (!t1.?t2. Accept(p(t1+t2)))))`--),
	REPEAT STRIP_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC
	THENL[
	    ALL_TAC,
	    EXISTS_TAC (--`j:num->'a`--) THEN EXISTS_TAC (--`p:num->'state`--)
	    THEN ASM_REWRITE_TAC[]]
	THEN IMP_RES_TAC REPETITION_LEMMA
	THEN MAP_EVERY POP_NO_TAC [9,6,2,1,0]
	THEN EXISTS_TAC(--`x0:num`--) THEN EXISTS_TAC(--`l:num`--)
	THEN EXISTS_TAC(--`\t. if (t<=x0) then i t else i(x0+((t-x0)MOD l)):'a`--)
	THEN EXISTS_TAC(--`\t. if (t<=x0) then q t else q(x0+((t-x0)MOD l)):'state`--)
	THEN BETA_TAC
	THEN IMP_RES_TAC(EQT_ELIM(ARITH_CONV(--`0<l ==> ~(x0+l<=x0)`--)))
	THEN IMP_RES_TAC MOD_MOD THEN IMP_RES_TAC ZERO_MOD
	THEN ASM_REWRITE_TAC
		[(EQT_ELIM(ARITH_CONV(--`(x0+l)-x0=l`--))),
		 (EQT_ELIM(ARITH_CONV(--`(x0+t2<=x0) = (t2=0)`--))),
		 SUB,ZERO_LESS_EQ,
		 TAC_PROOF(([],--`(if a then (b:'a) else b) = b`--),
			   BOOL_CASES_TAC (--`a:bool`--) THEN REWRITE_TAC[])]
	THEN REPEAT STRIP_TAC
	THENL[
	    COND_CASES_TAC THEN ASM_REWRITE_TAC[],
	    COND_CASES_TAC THEN ASM_REWRITE_TAC[],
	    DISJ_CASES_TAC(SPEC(--`t+1<=x0`--)BOOL_CASES_AX)
	    THEN IMP_RES_TAC (EQT_ELIM(ARITH_CONV(--`((t+1<=x0)=T)==>(t<=x0)`--)))
	    THEN IMP_RES_TAC (EQT_ELIM(ARITH_CONV(--`((t+1<=x0)=F)==>(x0<=t)`--)))
	    THEN IMP_RES_TAC (EQT_ELIM(ARITH_CONV(--`x0<=t==>((t+1)-x0=(t-x0)+1)`--)))
	    THEN IMP_RES_TAC SUC_MOD_LEMMA
	    THEN ASM_REWRITE_TAC[] THEN RULE_ASSUM_TAC(REWRITE_RULE[LESS_OR_EQ])
	    THEN POP_NO_ASSUM 2 DISJ_CASES_TAC
	    THENL[
		IMP_RES_TAC (EQT_ELIM(ARITH_CONV(--`(x0<t)==>~(t<=x0)`--)))
		THEN DISJ_CASES_TAC(SPEC(--`((t-x0) MOD l)+1 = l`--)BOOL_CASES_AX)
		THEN ASM_REWRITE_TAC[ADD_ASSOC,ADD_CLAUSES]
		THEN IMP_RES_TAC (EQT_ELIM(ARITH_CONV(--`(0<l)==>((x+1=l)=(x=l-1))`--)))
		THEN LEFT_NO_FORALL_TAC 2 (--`(t-x0) MOD l`--)
		THEN UNDISCH_HD_TAC THEN ASM_TAC 2 REWRITE1_TAC
		THEN DISCH_TAC THEN POP_ASSUM SUBST1_TAC
		THEN IMP_RES_TAC (EQT_ELIM(ARITH_CONV(--`(0<l)==>(x0+l=(x0+(l-1))+1)`--)))
		THEN POP_ASSUM REWRITE1_TAC
		THEN ASM_TAC 15 REWRITE1_TAC,
		ASM_REWRITE_TAC[LESS_EQ_REFL,SUB_EQUAL_0,ADD_CLAUSES]
		THEN DISJ_CASES_TAC(SPEC(--`1=l`--)BOOL_CASES_AX)
		THEN ASM_REWRITE_TAC[] THEN ASM_TAC 1 (SUBST1_TAC o SYM)
		THEN MY_MP_TAC (--`(q(x0+0):'state) = q(x0+1)`--)
		THENL[
		    UNDISCH_HD_TAC THEN REWRITE_TAC[ADD_CLAUSES]
		    THEN DISCH_TAC THEN ASM_TAC 0 REWRITE1_TAC
		    THEN ASM_TAC 9 REWRITE1_TAC,
		    DISCH_TAC THEN POP_ASSUM SUBST1_TAC
		    THEN ASM_TAC 11 REWRITE1_TAC]],
	    DISJ_CASES_TAC(SPEC(--`t1<=x0`--)BOOL_CASES_AX)
	    THENL[
		EXISTS_TAC (--`x0-t1`--)
		THEN IMP_RES_TAC(EQT_ELIM(ARITH_CONV(--`((t1<=x0)=T)==>(t1+(x0-t1)=x0)`--)))
		THEN ASM_REWRITE_TAC[LESS_EQ_REFL,SUB_EQUAL_0]
		THEN POP_NO_ASSUM 6 (SUBST1_TAC o SYM)
		THEN ASM_TAC 5 REWRITE1_TAC,
		IMP_RES_TAC(EQT_ELIM(ARITH_CONV(--`((t1<=x0)=F) ==> (x0<t1)`--)))
		THEN MY_MP_TAC (--`!p.?k. p <= k*l`--)
		THENL[
		   INDUCT_TAC THEN REWRITE_TAC[ZERO_LESS_EQ]
		   THEN LEFT_EXISTS_TAC THEN EXISTS_TAC (--`SUC k`--)
		   THEN REWRITE_TAC[MULT_CLAUSES] THEN REWRITE_TAC[ADD1]
		   THEN MATCH_MP_TAC LESS_EQ_LESS_EQ_MONO
		   THEN ASM_REWRITE_TAC[] THEN UNDISCH_NO_TAC 8
		   THEN CONV_TAC ARITH_CONV,
		   DISCH_TAC THEN LEFT_FORALL_TAC (--`t1-x0`--)
		   THEN LEFT_EXISTS_TAC THEN EXISTS_TAC (--`k*l - (t1-x0)`--)
		   THEN IMP_RES_TAC(EQT_ELIM(ARITH_CONV
			(--`(x0<t1) /\ (t1-x0<=z) ==> ((t1+(z-(t1-x0))) = z+x0)`--)))
		   THEN IMP_RES_TAC(EQT_ELIM(ARITH_CONV
			(--`(x0<t1) /\ (t1-x0<=z) ==> ~(z+x0<=x0)`--)))
		   THEN IMP_RES_TAC MOD_TIMES THEN LEFT_FORALL_TAC (--`0`--)
		   THEN LEFT_FORALL_TAC (--`k:num`--) THEN UNDISCH_HD_TAC
		   THEN ASM_REWRITE_TAC[ADD_SUB,ADD_CLAUSES] THEN DISCH_TAC
		   THEN POP_ASSUM REWRITE1_TAC THEN REWRITE_TAC[ADD_CLAUSES]
		   THEN ASM_TAC 10 REWRITE1_TAC]]]);




val BUECHI_PERIODIC_REDUCTION_THM = TAC_PROOF(
	([],--` (!s:num->'state.?x0 l. (0<l) /\ (s(x0)=s(x0+l)))
		  ==>
		    ((?(i:num->'a) (q:num->'state).
			    InitState(q 0) /\
			    (!t.TransRel(i t,q t,q(t+1))) /\
			    (!t1.?t2. Accept(q(t1+t2))))
		   =
		     (?x0 l j p.
			    (0<l) /\
			    (!t2. j(x0+t2) = j(x0+(t2 MOD l))) /\
			    (!t2. p(x0+t2) = p(x0+(t2 MOD l))) /\
			    InitState(p 0) /\
			    (!t. t< x0+l ==> TransRel(j t,p t,p(t+1))) /\
			    (?t. t<l /\ Accept(p(x0+t)))))`--),
	DISCH_TAC THEN SUBST1_TAC(UNDISCH BUECHI_PERIODIC_MODEL)
	THEN EQ_TAC THEN STRIP_TAC
	THEN MAP_EVERY EXISTS_TAC [(--`x0:num`--),(--`l:num`--),
				   (--`j:num->'a`--),(--`p:num->'state`--)]
	THENL[
	    ASM_TAC 4 (REWRITE1_TAC o SYM o SPEC_ALL)
	    THEN ASM_TAC 3 (REWRITE1_TAC o SYM o SPEC_ALL)
	    THEN ASM_TAC 2 REWRITE1_TAC THEN ASM_TAC 5 REWRITE1_TAC
	    THEN ASM_TAC 1 REWRITE1_TAC
	    THEN LEFT_FORALL_TAC (--`x0:num`--) THEN LEFT_EXISTS_TAC
	    THEN EXISTS_TAC (--`t2 MOD l`--)
	    THEN ASM_TAC 3 (REWRITE1_TAC o SYM o SPEC_ALL)
	    THEN ASM_TAC 0 REWRITE1_TAC
	    THEN IMP_RES_TAC DIVISION
	    THEN ASM_TAC 0 REWRITE1_TAC,
	    ASM_TAC 5 (REWRITE1_TAC o SYM o SPEC_ALL)
	    THEN ASM_TAC 4 (REWRITE1_TAC o SYM o SPEC_ALL)
	    THEN ASM_TAC 3 REWRITE1_TAC THEN ASM_TAC 6 REWRITE1_TAC
	    THEN MY_MP_TAC (--`!t1.?k. t1<=k*l + t`--)
	    THENL[
		INDUCT_TAC THEN REWRITE_TAC[ZERO_LESS_EQ]
		THEN LEFT_EXISTS_TAC
		THEN EXISTS_TAC (--`SUC k`--)
		THEN REWRITE_TAC[ADD_CLAUSES,MULT_CLAUSES,ADD1]
		THEN ONCE_REWRITE_TAC[EQT_ELIM(ARITH_CONV(--`(a+b)+c = (a+c)+b`--))]
		THEN MATCH_MP_TAC(EQT_ELIM(ARITH_CONV(--`a<=b /\ c<=d ==> a+c<=b+d`--)))
		THEN ASM_TAC 0 REWRITE1_TAC
		THEN SUBST1_TAC (num_CONV(--`1`--)) THEN MATCH_MP_TAC LESS_OR
		THEN ASM_TAC 7 REWRITE1_TAC,
		DISCH_TAC]
	    THEN CONJ_TAC
	    THENL[
		GEN_TAC
		THEN DISJ_CASES_TAC(SPECL[(--`t':num`--),(--`x0:num`--)]LESS_CASES)
		THENL[
		    POP_NO_ASSUM 4 MATCH_MP_TAC
		    THEN UNDISCH_HD_TAC THEN CONV_TAC ARITH_CONV,
		    IMP_RES_TAC LESS_EQUAL_ADD THEN POP_ASSUM SUBST1_TAC
		    THEN REWRITE_TAC[SYM(SPEC_ALL ADD_ASSOC)]
		    THEN ASM_TAC 7 (fn x=> ONCE_REWRITE_TAC[x])
		    THEN ASM_TAC 6 (fn x=> ONCE_REWRITE_TAC[x])
		    THEN IMP_RES_TAC SUC_MOD_LEMMA
		    THEN POP_ASSUM REWRITE1_TAC
		    THEN DISJ_CASES_TAC(SPEC(--`(p' MOD l) + 1 = l`--)BOOL_CASES_AX)
		    THEN ASM_TAC 0 REWRITE1_TAC
		    THENL[
			MY_MP_TAC (--`p(x0+0):'state=p((x0+(p' MOD l))+1)`--)
			THENL[
			    REWRITE_TAC[SYM(SPEC_ALL ADD_ASSOC)]
			    THEN POP_ASSUM (SUBST1_TAC o EQT_ELIM)
			    THEN ASM_TAC 6 (fn x=> CONV_TAC(RHS_CONV(ONCE_REWRITE_CONV[x])))
			    THEN IMP_RES_TAC MOD_EQ_0 THEN LEFT_FORALL_TAC (--`1`--)
			    THEN RULE_ASSUM_TAC (REWRITE_RULE[MULT_CLAUSES])
			    THEN POP_ASSUM REWRITE1_TAC,
			    DISCH_TAC THEN POP_ASSUM SUBST1_TAC
			    THEN ASM_TAC 5 MATCH_MP_TAC
			    THEN ONCE_REWRITE_TAC[ADD_SYM] THEN REWRITE_TAC[LESS_MONO_ADD_EQ]
			    THEN IMP_RES_TAC DIVISION THEN ASM_TAC 0 REWRITE1_TAC],
			REWRITE_TAC[ADD_ASSOC] THEN ASM_TAC 5 MATCH_MP_TAC
			THEN ONCE_REWRITE_TAC[ADD_SYM] THEN REWRITE_TAC[LESS_MONO_ADD_EQ]
			THEN IMP_RES_TAC DIVISION THEN ASM_TAC 0 REWRITE1_TAC]],
		GEN_TAC THEN LEFT_FORALL_TAC (--`t1:num`--)
		THEN LEFT_EXISTS_TAC
		THEN EXISTS_TAC (--`x0+((k*l+t)-t1)`--)
		THEN IMP_RES_TAC (ONCE_REWRITE_RULE[ADD_SYM]SUB_ADD)
		THEN ONCE_REWRITE_TAC[EQT_ELIM(ARITH_CONV(--`t1+(x0+z) = x0+(t1+z)`--))]
		THEN POP_ASSUM SUBST1_TAC
		THEN ASM_TAC 5 (fn x=> ONCE_REWRITE_TAC[x])
		THEN IMP_RES_TAC MOD_TIMES
		THEN POP_ASSUM REWRITE1_TAC
		THEN IMP_RES_TAC LESS_MOD
		THEN ASM_TAC 1 REWRITE1_TAC
		THEN ASM_TAC 3 REWRITE1_TAC]]);






val BUECHI_PROP_REDUCTION = TAC_PROOF(
	([],--` (!s:num->'state.?x0 l. (0<l) /\ (s(x0)=s(x0+l)))
		  ==>
		    ((?(i:num->'a) (q:num->'state).
			    InitState(q 0) /\
			    (!t.TransRel(i t,q t,q(t+1))) /\
			    (!t1.?t2. Accept(q(t1+t2))))
		   =
		     (?x0 l j p.
			    (0<l) /\ InitState(p 0) /\
			    (!t. t<x0+l ==> TransRel(j t,p t,p(t+1))) /\
			    (?t. t<l /\ Accept(p(x0+t)))/\
			    (p(x0)=p(x0+l)) ))`--),
	DISCH_TAC THEN SUBST1_TAC(UNDISCH BUECHI_PERIODIC_REDUCTION_THM)
	THEN EQ_TAC THEN STRIP_TAC
	THENL[
	    MAP_EVERY EXISTS_TAC [(--`x0:num`--),(--`l:num`--),
				   (--`j:num->'a`--),(--`p:num->'state`--)]
	    THEN ASM_TAC 3 REWRITE1_TAC THEN ASM_TAC 2 REWRITE1_TAC
	    THEN ASM_TAC 6 REWRITE1_TAC THEN CONJ_TAC
	    THENL[
		EXISTS_TAC (--`t:num`--) THEN ASM_TAC 1 REWRITE1_TAC
		THEN ASM_TAC 0 REWRITE1_TAC,
		MY_MP_TAC (--`l MOD l = 0`--)
		THENL[
		    MATCH_MP_TAC MOD_UNIQUE THEN EXISTS_TAC (--`1`--)
		    THEN ASM_REWRITE_TAC[ADD_CLAUSES,MULT_CLAUSES],
		    DISCH_TAC]
		THEN ONCE_ASM_REWRITE_TAC[] THEN  POP_ASSUM SUBST1_TAC
		THEN REWRITE_TAC[ADD_CLAUSES]],
	    ALL_TAC]
	THEN MY_MP_TAC (--`?j1.!t. j1 t = (if (t<=x0) then j t else j(x0+((t-x0)MOD l)):'a)`--)
	THENL[
	    EXISTS_TAC (--`\t. if (t<=x0) then j t else j(x0+((t-x0)MOD l)):'a`--)
	    THEN BETA_TAC THEN REWRITE_TAC[],STRIP_TAC]
	THEN MY_MP_TAC (--`?p1.!t. p1 t = (if (t<=x0) then p t else p(x0+((t-x0)MOD l)):'state)`--)
	THENL[
	    EXISTS_TAC (--`\t. if (t<=x0) then p t else p(x0+((t-x0)MOD l)):'state`--)
	    THEN BETA_TAC THEN REWRITE_TAC[],STRIP_TAC]
	THEN MAP_EVERY EXISTS_TAC [(--`x0:num`--),(--`l:num`--),
				  (--`j1:num->'a`--),(--`p1:num->'state`--)]
	THEN ASM_REWRITE_TAC
		[(EQT_ELIM(ARITH_CONV(--`(x0+l)-x0=l`--))),
		 (EQT_ELIM(ARITH_CONV(--`(x0+t2<=x0) = (t2=0)`--))),
		 SUB,ZERO_LESS_EQ]
	THEN REPEAT STRIP_TAC
	THENL[
	IMP_RES_TAC ZERO_MOD THEN IMP_RES_TAC DIVISION THEN POP_NO_TAC 1
	THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES]
	THEN LEFT_NO_FORALL_TAC 1 (--`t2:num`--) THEN IMP_RES_TAC LESS_MOD
	THEN POP_NO_ASSUM 1 SUBST1_TAC THEN BOOL_CASES_TAC(--`t2 MOD l = 0`--)
	THEN REWRITE_TAC[],
	IMP_RES_TAC ZERO_MOD THEN IMP_RES_TAC DIVISION THEN POP_NO_TAC 1
	THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES]
	THEN LEFT_NO_FORALL_TAC 1 (--`t2:num`--) THEN IMP_RES_TAC LESS_MOD
	THEN POP_NO_ASSUM 1 SUBST1_TAC THEN BOOL_CASES_TAC(--`t2 MOD l = 0`--)
	THEN REWRITE_TAC[],
	MAP_EVERY POP_NO_TAC [9,7,5,4]
	THEN ASM_TAC 1 (REWRITE1_TAC o SYM o SPEC_ALL)
	THEN ASM_TAC 2 (REWRITE1_TAC o SYM o SPEC_ALL)
	THEN DISJ_CASES_TAC(SPECL[(--`x0:num`--),(--`t'+1`--)]LESS_CASES)
	THENL[
	    IMP_RES_TAC(EQT_ELIM(ARITH_CONV(--`(x0<t'+1) ==> (x0=t') \/ (x0<t')`--)))
	    THENL[
		ASM_REWRITE_TAC[LESS_EQ_REFL,EQT_ELIM(ARITH_CONV(--`~(t'+1<=t')`--)),
			ONCE_REWRITE_RULE[ADD_SYM]ADD_SUB]
		THEN POP_ASSUM (SUBST1_TAC o SYM)
		THEN MY_MP_TAC (--`p(x0+ 1 MOD l):'state = p(x0+1)`--)
		THENL[
	    	    IMP_RES_TAC(EQT_ELIM(ARITH_CONV(--`(0<l)==>(1<l) \/ (l=1)`--)))
	    	    THENL[
			MY_MP_TAC(--`1 MOD l = 1`--)
			THENL[
			    MATCH_MP_TAC MOD_UNIQUE THEN EXISTS_TAC (--`0`--)
			    THEN ASM_REWRITE_TAC[MULT_CLAUSES,ADD_CLAUSES],
			    DISCH_TAC THEN POP_ASSUM SUBST1_TAC]
			THEN REWRITE_TAC[],
			MY_MP_TAC(--`1 MOD l = 0`--)
			THENL[
			    MATCH_MP_TAC MOD_UNIQUE THEN EXISTS_TAC (--`1`--)
			    THEN ASM_REWRITE_TAC[MULT_CLAUSES,ADD_CLAUSES],
			    DISCH_TAC THEN POP_ASSUM SUBST1_TAC]
			THEN ASM_REWRITE_TAC[ADD_CLAUSES]],
		    DISCH_TAC THEN POP_ASSUM SUBST1_TAC]
		THEN POP_NO_ASSUM 5 MATCH_MP_TAC
		THEN UNDISCH_NO_TAC 5 THEN CONV_TAC ARITH_CONV,
		IMP_RES_TAC(EQT_ELIM(ARITH_CONV(--`x0<t' ==> ((t'+1)-x0=(t'-x0)+1)`--)))
		THEN IMP_RES_TAC SUC_MOD_LEMMA
		THEN ASM_REWRITE_TAC[SYM(SPEC_ALL NOT_LESS)]
		THEN IMP_RES_TAC DIVISION THEN LEFT_FORALL_TAC (--`t'-x0`--)
		THEN IMP_RES_TAC LESS_OR
		THEN MAP_EVERY POP_NO_TAC [11,10,9,8,7,6,5,3,2,1,0]
		THEN RULE_ASSUM_TAC(REWRITE_RULE[ADD1,LESS_OR_EQ])
		THEN POP_ASSUM RIGHT_LEMMA_DISJ_CASES_TAC
		THEN ASM_TAC 0 REWRITE1_TAC THEN REWRITE_TAC[ADD_ASSOC]
		THENL[
		    POP_NO_ASSUM 8 MATCH_MP_TAC
		    THEN ONCE_REWRITE_TAC[ADD_SYM] THEN REWRITE_TAC[LESS_MONO_ADD_EQ]
		    THEN IMP_RES_TAC DIVISION THEN ASM_TAC 0 REWRITE1_TAC,
		    IMP_RES_TAC(EQT_ELIM(ARITH_CONV
			(--`(x0<t'+1)/\(t'<x0+l) ==> (t'-x0<l) /\ (x0<=t')`--)))
		    THEN IMP_RES_TAC(SPECL[(--`l:num`--),(--`t'-x0`--)]LESS_MOD)
		    THEN ASM_REWRITE_TAC[ADD_CLAUSES] THEN IMP_RES_TAC SUB_ADD
		    THEN ONCE_REWRITE_TAC[ADD_SYM] THEN ASM_TAC 0 SUBST1_TAC
		    THEN POP_NO_ASSUM 6 (SUBST1_TAC o SYM)
		    THEN POP_NO_ASSUM 1 SUBST1_TAC
		    THEN REWRITE_TAC[SYM(SPEC_ALL ADD1), ADD_CLAUSES]
		    THEN POP_NO_ASSUM 0 SUBST1_TAC THEN REWRITE_TAC[ADD1]
		    THEN POP_NO_ASSUM 10 MATCH_MP_TAC
		    THEN ASM_TAC 6 REWRITE1_TAC]],
	    IMP_RES_TAC(EQT_ELIM(ARITH_CONV(--`(t'+1<=x0)==>t'<=x0`--)))
	    THEN ASM_REWRITE_TAC[] THEN POP_NO_ASSUM 6 MATCH_MP_TAC
	    THEN ASM_TAC 2 REWRITE1_TAC],
	EXISTS_TAC (--`t:num`--) THEN ASM_REWRITE_TAC[]
	THEN DISJ_CASES_TAC(SPEC(--`t:num`--)num_CASES)
	THENL[ALL_TAC,LEFT_EXISTS_TAC]
	THEN UNDISCH_NO_TAC 4 THEN ASM_REWRITE_TAC[ADD_CLAUSES,LESS_EQ_REFL]
	THEN SUBST1_TAC(EQT_ELIM(ARITH_CONV(--`(SUC(x0+n)<=x0)=F`--)))
	THEN SUBST1_TAC(EQT_ELIM(ARITH_CONV(--`SUC(x0+n)-x0=SUC n`--)))
	THEN REWRITE_TAC[EQT_ELIM(ARITH_CONV(--`~(SUC n=0)`--))]
	THEN IMP_RES_TAC LESS_MOD THEN POP_NO_TAC 0
	THEN UNDISCH_HD_TAC THEN POP_ASSUM SUBST1_TAC
	THEN DISCH_TAC THEN POP_ASSUM SUBST1_TAC
	THEN REWRITE_TAC[ADD_CLAUSES]]);



(*---------------------------------------------------------------------------
     Some useful lemmas
 ---------------------------------------------------------------------------*)


val EQUALITY_THM = TAC_PROOF(
	([],--`!x y. (x = y) = !P:'a->bool. P(x) = P(y)`--),
	REPEAT GEN_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC
	THEN ASM_REWRITE_TAC[]
	THEN LEFT_FORALL_TAC (--`\t:'a. t=x`--)
	THEN UNDISCH_HD_TAC THEN BETA_TAC
	THEN REWRITE_TAC[] THEN DISCH_TAC
	THEN ASM_REWRITE_TAC[])


val LESS_THM = TAC_PROOF(
	([],--`!x y. (x<y) = ?P. P x /\ ~ P y /\ !z. P(SUC z) ==> P z`--),
	REPEAT GEN_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC
	THEN ASM_REWRITE_TAC[]
	THENL[
	    EXISTS_TAC (--`\t. t < SUC x`--) THEN BETA_TAC
	    THEN IMP_RES_TAC LESS_OR
	    THEN ASM_REWRITE_TAC[LESS_SUC_REFL,NOT_LESS,LESS_MONO_EQ]
	    THEN REPEAT STRIP_TAC THEN IMP_RES_TAC LESS_SUC,
	    RULE_ASSUM_TAC (CONV_RULE(ONCE_DEPTH_CONV CONTRAPOS_CONV))
	    THEN MY_MP_TAC (--`!t. ~P(y+t)`--)
	    THENL[
		INDUCT_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES]
		THEN RES_TAC,
		DISCH_TAC]
	    THEN DISJ_CASES_TAC (SPECL[(--`x:num`--),(--`y:num`--)]LESS_CASES)
	    THEN ASM_REWRITE_TAC[]
	    THEN UNDISCH_HD_TAC THEN REWRITE_TAC[LESS_OR_EQ]
	    THEN STRIP_TAC
	    THENL[
		IMP_RES_TAC LESS_ADD_1
		THEN UNDISCH_NO_TAC 5 THEN POP_ASSUM SUBST1_TAC
		THEN LEFT_NO_FORALL_TAC 1 (--`p+1`--) THEN ASM_REWRITE_TAC[],
		UNDISCH_HD_TAC THEN CONV_TAC CONTRAPOS_CONV
		THEN DISCH_TAC THEN ONCE_REWRITE_TAC[EQUALITY_THM]
		THEN CONV_TAC NOT_FORALL_CONV
		THEN EXISTS_TAC (--`P:num->bool`--) THEN ASM_REWRITE_TAC[]]]);



val FORALL_EXISTS_THM = TAC_PROOF(
	([],--`!P.(!t1.?t2. P(t1+t2)) = (!t1.?t2. t1<t2 /\ P t2)`--),
	GEN_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC
	THENL[
	    LEFT_FORALL_TAC (--`SUC t1`--) THEN LEFT_EXISTS_TAC
	    THEN EXISTS_TAC (--`SUC(t1+t2)`--)
	    THEN RULE_ASSUM_TAC (REWRITE_RULE[ADD])
	    THEN ASM_REWRITE_TAC[] THEN CONV_TAC ARITH_CONV,
	    LEFT_FORALL_TAC (--`t1:num`--) THEN LEFT_EXISTS_TAC
	    THEN EXISTS_TAC (--`t2-t1`--) THEN UNDISCH_HD_TAC
	    THEN STRIP_TAC THEN IMP_RES_TAC
		(EQT_ELIM(ARITH_CONV(--`t1<t2 ==> (t1+(t2-t1) = t2)`--)))
	    THEN ASM_REWRITE_TAC[]]);



val EXISTS_FORALL_THM = TAC_PROOF(
	([],--`!P.(?t1.!t2. P(t1+t2)) = (?t1.!t2. t1<t2 ==> P t2)`--),
	GEN_TAC
	THEN PURE_ONCE_REWRITE_TAC[TAC_PROOF(([],--`(a=b)=(~a=~b)`--),PROP_TAC)]
	THEN CONV_TAC(REPEATC(CHANGED_CONV(DEPTH_CONV
			(NOT_EXISTS_CONV ORELSEC NOT_FORALL_CONV))))
	THEN SUBST1_TAC(BETA_RULE(SPEC(--`\t:num. ~P t`--)FORALL_EXISTS_THM))
	THEN REWRITE_TAC[TAC_PROOF(([],--`~(a==>b) = a/\~b`--),PROP_TAC)])





val ELGOT_LEMMA = TAC_PROOF(
	([],--`!PHI:('a->bool)->'a->bool.
		(?x.!p. PHI p x) = ?q.(!x.(q x ==> !p.PHI p x)) /\ ?z. q z`--),
	GEN_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC
	THENL[
	    EXISTS_TAC (--`\x. !p.(PHI:('a->bool)->'a->bool) p x`--)
	    THEN BETA_TAC THEN REWRITE_TAC[]
	    THEN EXISTS_TAC (--`x:'a`--) THEN ASM_REWRITE_TAC[],
	    RES_TAC THEN EXISTS_TAC(--`z:'a`--) THEN GEN_TAC
	    THEN ASM_REWRITE_TAC[]])



val ELGOT1_THM = TAC_PROOF(
	([],--` !PHI. (?x.!p:'a->bool. PHI p x) =
		      (?q:'a->bool.!p.!x.?z.(q x ==> PHI p x) /\ q z)`--),
	GEN_TAC THEN SUBST1_TAC(SPEC_ALL ELGOT_LEMMA)
	THEN EQ_TAC THEN REPEAT STRIP_TAC
	THEN EXISTS_TAC (--`q:'a->bool`--) THEN REPEAT STRIP_TAC
	THENL[
	    EXISTS_TAC (--`z:'a`--) THEN ASM_REWRITE_TAC[]
	    THEN DISCH_TAC THEN RES_TAC THEN ASM_REWRITE_TAC[],
	    UNDISCH_HD_TAC THEN LEFT_FORALL_TAC (--`p:'a->bool`--)
	    THEN LEFT_FORALL_TAC (--`x:'a`--) THEN LEFT_EXISTS_TAC
	    THEN ASM_REWRITE_TAC[],
	    LEFT_FORALL_TAC (--`p:'a->bool`--) THEN LEFT_FORALL_TAC (--`x:'a`--)
	    THEN LEFT_EXISTS_TAC THEN EXISTS_TAC (--`z:'a`--)
	    THEN ASM_REWRITE_TAC[]])



val ELGOT2_THM = TAC_PROOF(
	([],--`!PHI. (!x:'a.?p:'a->bool. PHI p x)
			= (!q:'a->bool.?p.?x.!z. q z ==> PHI p x /\ q x)`--),
	GEN_TAC THEN ONCE_REWRITE_TAC[TAC_PROOF(([],--` (a=b) = (~a=~b)`--),PROP_TAC)]
	THEN CONV_TAC(REPEATC(CHANGED_CONV(DEPTH_CONV
			(NOT_FORALL_CONV ORELSEC NOT_EXISTS_CONV))))
	THEN SUBST1_TAC(BETA_RULE(SPEC(--`\(p:'a->bool) (x:'a).~PHI p x`--)ELGOT1_THM))
	THEN REWRITE_TAC[TAC_PROOF(([],--`((qz ==> ~PHI) /\ qx) = ~(qx ==> PHI /\ qz)`--),
				PROP_TAC)]);





val _ = save_thm("DET_OMEGA_EXISTS_FORALL_THEOREM",DET_OMEGA_EXISTS_FORALL_THEOREM);
val _ = save_thm("NEG_DET_AUTOMATA",NEG_DET_AUTOMATA);
val _ = save_thm("OMEGA_CONJ_CLOSURE",OMEGA_CONJ_CLOSURE);
val _ = save_thm("OMEGA_DISJ_CLOSURE",OMEGA_DISJ_CLOSURE);

val _ = save_thm("BOOLEAN_CLOSURE_G",BOOLEAN_CLOSURE_G);
val _ = save_thm("BOOLEAN_CLOSURE_F",BOOLEAN_CLOSURE_F);
val _ = save_thm("BOOLEAN_CLOSURE_FG",BOOLEAN_CLOSURE_FG);
val _ = save_thm("BOOLEAN_CLOSURE_GF",BOOLEAN_CLOSURE_GF);

val _ = save_thm("BOREL_HIERARCHY_G",BOREL_HIERARCHY_G);
val _ = save_thm("BOREL_HIERARCHY_F",BOREL_HIERARCHY_F);
val _ = save_thm("BOREL_HIERARCHY_FG",BOREL_HIERARCHY_FG);

(* ----------------- from file templog2buechi.sml ------------------ *)
val _ = save_thm("TEMP_OPS_DEFS_TO_OMEGA",TEMP_OPS_DEFS_TO_OMEGA);

(* ----------------- from file automaton_closures.sml ------------------ *)
val _ = save_thm("AUTOMATON_TEMP_CLOSURE",AUTOMATON_TEMP_CLOSURE);
val _ = save_thm("BUECHI_TRANSLATION",BUECHI_TRANSLATION);

(* ----------------- from file co_buechi_closures.sml ------------------ *)
val _ = save_thm("CO_BUECHI_CONJ_CLOSURE",CO_BUECHI_CONJ_CLOSURE);
val _ = save_thm("CO_BUECHI_DISJ_CLOSURE",CO_BUECHI_DISJ_CLOSURE);
val _ = save_thm("CO_BUECHI_NEXT_CLOSURE",CO_BUECHI_NEXT_CLOSURE);
val _ = save_thm("CO_BUECHI_SUNTIL_CLOSURE",CO_BUECHI_SUNTIL_CLOSURE);
val _ = save_thm("CO_BUECHI_UNTIL_CLOSURE",CO_BUECHI_UNTIL_CLOSURE);
val _ = save_thm("CO_BUECHI_SBEFORE_CLOSURE",CO_BUECHI_SBEFORE_CLOSURE);
val _ = save_thm("CO_BUECHI_BEFORE_CLOSURE",CO_BUECHI_BEFORE_CLOSURE);
val _ = save_thm("CO_BUECHI_SWHEN_CLOSURE",CO_BUECHI_SWHEN_CLOSURE);
val _ = save_thm("CO_BUECHI_WHEN_CLOSURE",CO_BUECHI_WHEN_CLOSURE);

(* ----------------- from file tempop_as_co_buechi.sml ------------------ *)
val _ = save_thm("NEXT_AS_CO_BUECHI",NEXT_AS_CO_BUECHI);
val _ = save_thm("SUNTIL_AS_CO_BUECHI",SUNTIL_AS_CO_BUECHI);
val _ = save_thm("UNTIL_AS_CO_BUECHI",UNTIL_AS_CO_BUECHI);
val _ = save_thm("SBEFORE_AS_CO_BUECHI",SBEFORE_AS_CO_BUECHI);
val _ = save_thm("BEFORE_AS_CO_BUECHI",BEFORE_AS_CO_BUECHI);
val _ = save_thm("SWHEN_AS_CO_BUECHI",SWHEN_AS_CO_BUECHI);
val _ = save_thm("WHEN_AS_CO_BUECHI",WHEN_AS_CO_BUECHI);

(* ----------------- from file periodic.sml ------------------ *)
val _ = save_thm("BUECHI_PERIODIC_MODEL",BUECHI_PERIODIC_MODEL);
val _ = save_thm("BUECHI_PERIODIC_REDUCTION_THM",BUECHI_PERIODIC_REDUCTION_THM);
val _ = save_thm("BUECHI_PROP_REDUCTION",BUECHI_PROP_REDUCTION);

(* ----------------- from file linord2buechi.sml ------------------ *)
val _ = save_thm("EQUALITY_THM",EQUALITY_THM);
val _ = save_thm("LESS_THM",LESS_THM);
val _ = save_thm("FORALL_EXISTS_THM",FORALL_EXISTS_THM);
val _ = save_thm("EXISTS_FORALL_THM",EXISTS_FORALL_THM);
val _ = save_thm("ELGOT_LEMMA",ELGOT_LEMMA);
val _ = save_thm("ELGOT1_THM",ELGOT1_THM);
val _ = save_thm("ELGOT2_THM",ELGOT2_THM);


val _ = export_theory();
