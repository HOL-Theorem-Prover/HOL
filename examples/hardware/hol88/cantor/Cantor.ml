% Proof of Cantor's Theorem %

let Th1 = ASSUME "!fn:*->bool. ?x:*. fn = FN x";;

let Th2 = SPEC "\x. ~((FN:*->*->bool) x x)" Th1;;

let Th3 = SELECT_RULE Th2;;

let t = rand(rhs(concl Th3));;

let Th4 = AP_THM Th3 t;;

let Th5 = CONV_RULE(DEPTH_CONV BETA_CONV) Th4;;

let Lemma1 =
 TAC_PROOF
  (([],"!t. (~t = t) = F"), 
   GEN_TAC THEN BOOL_CASES_TAC "t:bool" THEN REWRITE_TAC[]);;

let Th6 = REWRITE_RULE[Lemma1] Th5;;

let Th7 =
 CHOOSE ("FN:*->*->bool", ASSUME "?FN. !fn:*->bool. ?x:*. fn = FN x") Th6;;

let Th8 = DISCH_ALL Th7;;

let Cantors_Thm = NOT_INTRO Th8;;


