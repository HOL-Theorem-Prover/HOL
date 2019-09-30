
% Luis's Example % 

new_theory `Lumis`;;

% The 'proof' below was generated interactively on Tuesday (20 Nov)
  and then tidied-up the next morning % 

let LESS_EQ_0 =
 prove_thm
  (`LESS_EQ_0`,
   "!m. (m <= 0) ==> (m = 0)",
   GEN_TAC
    THEN REWRITE_TAC[LESS_OR_EQ]
    THEN REPEAT STRIP_TAC
    THEN IMP_RES_TAC NOT_LESS_0);;

let LESS_EQ_LEMMA1 =
 prove_thm
  (`LESS_EQ_LEMMA1`,
   "(m < n) /\ (n <= p) ==> (m < p)",
   REWRITE_TAC[LESS_OR_EQ]
    THEN REPEAT STRIP_TAC
    THEN IMP_RES_TAC LESS_TRANS
    THEN ASM_REWRITE_TAC[]
    THEN REWRITE_TAC[SYM(ASSUME "n:num=p")]
    THEN ASM_REWRITE_TAC[SYM(ASSUME "n:num=p")]);;

let LESS_EQ_LEMMA2 =
 prove_thm
  (`LESS_EQ_LEMMA2`,
   "(m <= n) /\ (n < p) ==> (m < p)",
   REWRITE_TAC[LESS_OR_EQ]
    THEN REPEAT STRIP_TAC
    THEN IMP_RES_TAC LESS_TRANS
    THEN ASM_REWRITE_TAC[]
    THEN REWRITE_TAC[SYM(ASSUME "n:num=p")]
    THEN ASM_REWRITE_TAC[SYM(ASSUME "n:num=p")]);;

let LESS_EQ_SUC_LEMMA =
 prove_thm
  (`LESS_EQ_SUC_LEMMA`,
   "(m < SUC n) ==> (m <= n)",
   REWRITE_TAC[LESS_THM;LESS_OR_EQ]
    THEN REPEAT STRIP_TAC
    THEN ASM_REWRITE_TAC[]);;

% When we did the proof of LUIS_THM interactively, we used ASS1 where:

    let ASS1 = ASSUME "~(!i. i < n ==> ~P i) ==> ?i. (i <n ) /\ P i";;

  Unfortunately the proof part of the tactic fails with `GEN`
  because the free variables "P" and "n" in ASS1 prevent the use
  of GEN to add "!P.!m.!n." when the theorem is being proved after
  the goal is solved. This means that the tactic IMP_RES_TAC ASS1 
  is not valid. The solution is to close-up the term being assumed by
  definining ASS1 as below rather than as above. This ensures that there
  are no free variables in the assumption of ASS1 to block the use of GEN.
% 

let ASS1 =
 SPEC_ALL(ASSUME(gen_all"~(!i. i < n ==> ~P i) ==> ?i. (i <n ) /\ P i"));;

let ASS2 = 
 ASSUME "?n0. P n0 /\ n0 <= (@i. i < n /\ P i) /\ (!p. p < n0 ==> ~P p)";;

let LUIS_THM =
 prove_thm
  (`LUIS_THM`,
   "!P.!m.!n. 
     (n <= m) /\ P n ==> 
      ?n0. P n0 /\ (n0 <= n) /\ !p. (p < n0) ==> ~(P p)",
   GEN_TAC
    THEN INDUCT_TAC
    THENL
     [STRIP_TAC
       THEN STRIP_TAC
       THEN EXISTS_TAC "0"
       THEN IMP_RES_TAC LESS_EQ_0
       THEN ASM_REWRITE_TAC[LESS_EQ_REFL;NOT_LESS_0]
       THEN REWRITE_TAC[SYM(ASSUME "n=0")]
       THEN ASM_REWRITE_TAC[];
      STRIP_TAC
       THEN STRIP_TAC
       THEN ASM_CASES_TAC "!i. (i < n) ==> ~(P i)"
       THENL
        [EXISTS_TAC "n:num"
          THEN ASM_REWRITE_TAC[LESS_EQ_REFL];
         IMP_RES_TAC ASS1
          THEN STRIP_ASSUME_TAC(SELECT_RULE(ASSUME "?i. i < n /\ P i"))
          THEN IMP_RES_TAC LESS_EQ_LEMMA1
          THEN IMP_RES_TAC LESS_EQ_SUC_LEMMA
          THEN RES_TAC
          THEN STRIP_ASSUME_TAC(SELECT_RULE ASS2)
          THEN EXISTS_TAC 
                "@n0. P n0 /\ 
                      n0 <= (@i. i < n /\ P i) /\ 
                      (!p. p < n0 ==> ~P p)"
          THEN ASM_REWRITE_TAC[]
          THEN IMP_RES_TAC LESS_EQ_LEMMA2
          THEN ASM_REWRITE_TAC[LESS_OR_EQ]]]);;

% The following rule and theorem are needed for proving ASS1 % 

% "~!x.t" ---> |- (~!x.t) = (?x.~t) % 

let NOT_FORALL_CONV t =
 (let x,t = dest_forall(dest_neg t)
  in
  let th1 = SPEC t (hd(CONJUNCTS NOT_CLAUSES))
  in
  let th2 = FORALL_EQ x th1
  in
  let th3 = NOT_EXISTS_CONV "~?^x.~^t"
  in
  let th4 = SYM(AP_TERM "$~" (th3 TRANS th2))
  in
  let th5 = SPEC "?^x.~^t" (hd(CONJUNCTS NOT_CLAUSES))
  in
  th4 TRANS th5
 ) ? failwith `NOT_FORALL_CONV`;;

% |- !t1 t2. ~(t1==>t2) = t1 /\ ~t2 % 

let NOT_IMP =
 prove_thm
  (`NOT_IMP`,
   "!t1 t2. ~(t1==>t2) = t1 /\ ~t2",
   REPEAT GEN_TAC
    THEN ASM_CASES_TAC "t1:bool"
    THEN ASM_CASES_TAC "t2:bool"
    THEN ASM_REWRITE_TAC[]);;

% The following proves ASS1 %

let ASS1 = 
 let th1 = fst(EQ_IMP_RULE(NOT_FORALL_CONV "~(!i. i < n ==> ~P i)"))
 in
 PURE_REWRITE_RULE[NOT_IMP;NOT_CLAUSES]th1;;

% We can now get rid of the assumption in LUIS_THM.
  First we delete the version of LUIS_THM stored in the current theory. % 

delete_thm `-` `LUIS_THM`;;

% Note that the occurrence of LUIS_THM in the right hand side of the
  following declaration denotes the old theorem (i.e. the one with ASS1). % 
  
let LUIS_THM = 
 save_thm(`LUIS_THM`, MP (DISCH_ALL LUIS_THM) (GEN_ALL ASS1));;

print_theory`Luis`;;
