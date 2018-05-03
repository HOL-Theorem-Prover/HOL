timer true;;

new_theory `MULT_FUN`;;

new_parent `MULT_FUN_CURRY`;;

%
 |- !i1 i2 m n t.
     MULT_FUN((i1,i2),m,n,t) =
      (t => 
       (m,n,t) | 
       MULT_FUN((i1,i2),((i1=0)=>m|i2+m),n-1,((((n-1)-1)=0) \/ (i2=0))))
%

let MULT_FUN_DEF = theorem `MULT_FUN_CURRY` `MULT_FUN_DEF`;;

let MULT_FUN_T =
 prove_thm
  (`MULT_FUN_T`,
   "!i1 i2 m n.
     MULT_FUN((i1,i2),m,n,T) = (m,n,T)",
   REPEAT GEN_TAC
    THEN ASM_CASES_TAC "t"
    THEN REWRITE_TAC[INST["T","t:bool"](SPEC_ALL MULT_FUN_DEF)]);;

let MULT_FUN_F =
 prove_thm
  (`MULT_FUN_F`,
   "!i1 i2 m n.
     MULT_FUN((i1,i2),m,n,F) = 
     MULT_FUN((i1,i2),((i1=0)=>m|i2+m),n-1,((((n-1)-1)=0) \/ (i2=0)))",
   REPEAT GEN_TAC
    THEN ASM_CASES_TAC "t:bool"
    THEN REWRITE_TAC[INST["F","t:bool"](SPEC_ALL MULT_FUN_DEF)]);;

let LESS_EQ_0 =
 prove_thm
  (`LESS_EQ_0`,
   "!m. 0 <= m",
   INDUCT_TAC
    THEN ASM_REWRITE_TAC[LESS_OR_EQ;LESS_0]);;

let LESS_EQ_SUC_1 =
 prove_thm
  (`LESS_EQ_SUC_1`,
   "!m. 1 <= SUC m",
   INDUCT_TAC
    THEN ASM_REWRITE_TAC[num_CONV "1";LESS_OR_EQ;LESS_MONO_EQ;LESS_0]);;

let SUB_LEMMA1 =
 prove_thm
  (`SUB_LEMMA1`,
   "!m.~(m=0) ==> (m-1=0) ==> (m=1)",
   INDUCT_TAC
    THEN REWRITE_TAC
          [SYM
           (SUBS
             [SPECL["0";"(SUC m)-1"](INST_TYPE[":num",":*"]EQ_SYM_EQ)]
             (MP
              (SPECL
                ["0";"1";"SUC m"]ADD_EQ_SUB)(SPEC "m:num" LESS_EQ_SUC_1)));
           ADD_CLAUSES]
    THEN REPEAT STRIP_TAC
    THEN ASM_REWRITE_TAC[]);;

let SUB_LEMMA2 =
 prove_thm
  (`SUB_LEMMA2`,
    "!m.(m=0) ==> ~(m-1=0) ==> F",
    GEN_TAC
     THEN DISCH_TAC
     THEN ASM_REWRITE_TAC[SUB_0]);;

let MULT_NOT_0_LESS =
 prove_thm
  (`MULT_NOT_0_LESS`,
   "!m n. ~(m = 0) ==> n <= (m * n)",
   INDUCT_TAC
    THEN GEN_TAC
    THEN REWRITE_TAC
          [MULT_CLAUSES;SUBS[SPEC_ALL ADD_SYM](SPEC_ALL LESS_EQ_ADD)]);;

let MULT_ADD_LEMMA1 =
 prove_thm
  (`MULT_ADD_LEMMA1`,
   "!m. ~(m=0) ==> !n p. (((m-1)*n)+(n+p) = (m*n)+p)",
   REPEAT STRIP_TAC
    THEN REWRITE_TAC[ADD_ASSOC;RIGHT_SUB_DISTRIB;MULT_CLAUSES]
    THEN IMP_RES_TAC MULT_NOT_0_LESS
    THEN IMP_RES_TAC SUB_ADD
    THEN ASM_REWRITE_TAC[]);;

let MULT_FUN_THM =
 prove_thm
  (`MULT_FUN_THM`,
   "!n i1 i2 m t.
     MULT_FUN((i1,i2),m,n,t) =
      (t => 
       (m,n,t) |
       (((n-1)=0)\/(i2=0)) =>
        (((i1=0)=>m|i2+m),n-1,T) |
        (((i1=0)=>m|((n-1)*i2)+m),1,T))",
       INDUCT_TAC
	THEN REPEAT GEN_TAC
	THEN ASM_CASES_TAC "t:bool" 
	THEN ASM_REWRITE_TAC[MULT_FUN_T;MULT_FUN_F;SUC_SUB1;SUB_0]
	THEN ASM_CASES_TAC "i1=0" 
	THEN ASM_CASES_TAC "i2=0"
	THEN ASM_CASES_TAC "n=0"
	THEN ASM_CASES_TAC "(n-1)=0"
	THEN ASM_REWRITE_TAC[MULT_FUN_T;MULT_FUN_F;SUC_SUB1;SUB_0]
	THEN IMP_RES_TAC SUB_LEMMA1
	THEN IMP_RES_TAC SUB_LEMMA2
	THEN IMP_RES_TAC MULT_ADD_LEMMA1
	THEN ASM_REWRITE_TAC[MULT_CLAUSES]);;

let MULT_ADD_LEMMA2 =
 prove_thm
  (`MULT_ADD_LEMMA2`,
   "!m. ~(m=0) ==> !n. ((m-1)*n)+n = m*n",
   REPEAT STRIP_TAC
    THEN REWRITE_TAC[RIGHT_SUB_DISTRIB;MULT_CLAUSES]
    THEN IMP_RES_TAC MULT_NOT_0_LESS
    THEN IMP_RES_TAC SUB_ADD
    THEN ASM_REWRITE_TAC[]);;

let MULT_FUN_LEMMA =
     prove_thm
      (`MULT_FUN_LEMMA`,
       "!i1 i2.
	 MULT_FUN((i1,i2),((i1=0)=>0|i2),i1,(((i1-1)=0)\/(i2=0))) =
	  (i1*i2, ((((i1-1)=0)\/(i2=0))=>i1|1), T)",
       REPEAT GEN_TAC
	THEN ASM_CASES_TAC "i1=0"
	THEN ASM_CASES_TAC "i2=0"
	THEN ASM_REWRITE_TAC[MULT_FUN_THM;MULT_CLAUSES;SUB_0]
	THEN ASM_CASES_TAC "i1-1=0"
	THEN IMP_RES_TAC SUB_LEMMA1
	THEN IMP_RES_TAC MULT_ADD_LEMMA2
        THEN ASM_REWRITE_TAC[MULT_CLAUSES]);;
