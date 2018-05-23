
% The (corrected) dynamic CMOS adder from "CMOS Design Techniques to Eliminate
  the Stuck-open Fault Problem of Testability" by A. F. Murray
  in "Electronics letters" Vol. 20, No. 19 (13 Sept. 1984). Verification using
  a unidirectional model %

timer true;;

new_theory `DYN_ADD`;;

new_parent `INV`;;

let tri = ":tri_word1";;

let time = ":num";;
let sig  = ":^time -> ^tri";;

new_definition
 (`ADD_IMP_BODY`,
  "ADD_IMP_BODY
    (a,a_bar,b,b_bar,cin,cin_bar,ph1,ph1_bar,ph2,ph2_bar,
     sum,sum_bar,cout,cout_bar,
     p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,
     p19,p20,p21,p22) =
    PWR(p0) /\ GND(p8) /\
    PTRAN(ph1,p0,p1) /\ PTRAN(a_bar,p1,p2) /\ PTRAN(b_bar,p2,p9) /\
    PTRAN(a_bar,p1,p3) /\ PTRAN(cin_bar,p22,p12) /\ NTRAN(ph1,p8,p10) /\
    PTRAN(b_bar,p1,p21) /\ NTRAN(b_bar,p4,p13) /\ NTRAN(cin_bar,p4,p14) /\
    NTRAN(a_bar,p4,p16) /\ NTRAN(cout,p7,p4) /\ PTRAN(ph1_bar,p0,p18) /\
    NTRAN(a_bar,p5,p20) /\ NTRAN(b_bar,p6,p5) /\ NTRAN(cin_bar,p7,p6) /\
    NTRAN(ph1_bar,p8,p7) /\
    J(p9,p10,p11) /\ J(p11,p12,cout) /\ J(p13,p14,p15) /\ 
    J(p15,p16,p17) /\ J(p17,p18,p19) /\ J(p19,p20,sum) /\ J(p3,p21,p22) /\
    INV(a,a_bar,ph1,ph1_bar) /\ INV(b,b_bar,ph1,ph1_bar) /\
    INV(cin,cin_bar,ph1,ph1_bar) /\
    INV(sum,sum_bar,ph2,ph2_bar) /\ INV(cout,cout_bar,ph2,ph2_bar)");;

new_definition
 (`ADD_IMP`,
  "ADD_IMP(a,b,cin,ph1,ph1_bar,ph2,ph2_bar,sum_bar,cout_bar) =
    ?p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 
     p15 p16 p17 p18 p19 p20 p21 p22 a_bar b_bar cin_bar sum cout.
    ADD_IMP_BODY
    (a,a_bar,b,b_bar,cin,cin_bar,ph1,ph1_bar,ph2,ph2_bar,
     sum,sum_bar,cout,cout_bar,
     p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,
     p19,p20,p21,p22)");;

new_definition
 (`PHASE1`,
  "!ph1 ph2 ph1_bar ph2_bar t.
    PHASE1 (ph1,ph1_bar,ph2,ph2_bar) t = ((ph1 t        = HI) /\
                                          (ph1_bar t    = LO) /\
                                          (ph2 t        = LO) /\
                                          (ph2_bar t    = HI) /\
                                          (ph1(t+1)     = LO) /\
                                          (ph2(t+1)     = HI) /\
                                          (ph1_bar(t+1) = HI) /\
                                          (ph2_bar(t+1) = LO))");;
 

close_theory();;

load_theory`DYN_ADD`;;

let PWR            = definition `cmos` `PWR`
and GND            = definition `cmos` `GND`
and J              = definition `cmos` `J`
and CAPACITOR      = definition `cmos` `CAPACITOR`
and DEF            = definition `cmos` `DEF`;;

let NTRAN          = theorem `cmos` `NTRAN_THM`
and PTRAN          = theorem `cmos` `PTRAN_THM`;;

let INV            = theorem `INV` `INV_THM`;;

let PHASE1         = definition `DYN_ADD` `PHASE1`
and ADD_IMP_BODY   = definition `DYN_ADD` `ADD_IMP_BODY`
and ADD_IMP        = definition `DYN_ADD` `ADD_IMP`;;

let TRI_EQ_CLAUSES = theorem `cmos` `TRI_EQ_CLAUSES`
and DEF_CLAUSES    = theorem `cmos` `DEF_CLAUSES`;;

let ph1_thms = CONJUNCTS(UNDISCH(fst(EQ_IMP_RULE(SPEC_ALL PHASE1))));;

letrec iterate f x =
 let x' = f x
 in
 if x=x' then x else iterate f x';;

let ADD1_SUB1 =
 prove_thm
  (`ADD1_SUB1`,
   "!m. ((m + 1) - 1) = m",
   GEN_TAC
    THEN REWRITE_TAC[SUC_SUB1;SYM(SPEC "m:num" ADD1)]);;

let ADD1_SUB1_SIMP = PURE_REWRITE_RULE[ADD1_SUB1]
and DEF_SIMP       = PURE_REWRITE_RULE[DEF_CLAUSES];;

let UCMOS_UNWIND =
 CONV_RULE
  (UNWIND_EQS
    THENC bool_CONV
    THENC EQ_CONV
    THENC U_CONV
    THENC COND_CONV);;


% prove_case(a,b,cin) `simulates' the adder with the input values
  a, b and cin. It uses a very crude forward proof strategy which
  is only feasible when running on the Atlas-10. Gigantic
  intermediate terms are produced; the hack in the code seems to prevent
  crashes due to lisp running out of space. %

let prove_case(a,b,cin) =
 let thl1 = CONJUNCTS(UNDISCH(fst(EQ_IMP_RULE ADD_IMP_BODY)))
 in
 let thl2 = map (\th. GEN_ALL(MATCH_MP NTRAN th) ? 
                      GEN_ALL(MATCH_MP PTRAN th) ? 
                      GEN_ALL(MATCH_MP INV   th) ?
                      PURE_REWRITE_RULE[PWR;GND;J] th)
                thl1
 in
 let thl3 = map(SPEC "t:num")thl2
            @
            map(ADD1_SUB1_SIMP o SPEC "t+1")thl2
 and thl4 = [ASSUME "(a:num->^tri)t       = ^a";
             ASSUME "(b:num->^tri)t       = ^b";
             ASSUME "(cin:num->^tri)t     = ^cin"]

 in
 let th1 = LIST_CONJ(itlist append (map CONJUNCTS (thl3@thl4@ph1_thms)) nil)
 in
 let th2 = UCMOS_UNWIND(UCMOS_UNWIND(UCMOS_UNWIND th1)) 
             %hack to reduce space usage%
 in
 iterate (DEF_SIMP o UCMOS_UNWIND) th2;;
 

% Extract out values on sum and cout and undischarge assumptions %

let prune_list = ["sum_bar:^sig";"cout_bar:^sig"];;

let OUTS_PRUNE th =
 let thl1 = CONJUNCTS th
 in
 let thl2 = filter(\th.mem(fst(dest_comb(lhs(concl th))))prune_list)thl1
 in 
 DISCH_ALL(LIST_CONJ thl2);;


let HHH_Thm = save_thm(`HHH_Thm`, prove_case("HI","HI","HI"));;

let HHL_Thm = save_thm(`HHL_Thm`, prove_case("HI","HI","LO"));;

let HLH_Thm = save_thm(`HLH_Thm`, prove_case("HI","LO","HI"));;

let HLL_Thm = save_thm(`HLL_Thm`, prove_case("HI","LO","LO"));;

let LHH_Thm = save_thm(`LHH_Thm`, prove_case("LO","HI","HI"));;

let LHL_Thm = save_thm(`LHL_Thm`, prove_case("LO","HI","LO"));;

let LLH_Thm = save_thm(`LLH_Thm`, prove_case("LO","LO","HI"));;

let LLL_Thm = save_thm(`LLL_Thm`, prove_case("LO","LO","LO"));;


let HHH_SIMP_Thm = save_thm(`HHH_SIMP_Thm`, OUTS_PRUNE HHH_Thm);;

let HHL_SIMP_Thm = save_thm(`HHL_SIMP_Thm`, OUTS_PRUNE HHL_Thm);;

let HLH_SIMP_Thm = save_thm(`HLH_SIMP_Thm`, OUTS_PRUNE HLH_Thm);;

let HLL_SIMP_Thm = save_thm(`HLL_SIMP_Thm`, OUTS_PRUNE HLL_Thm);;

let LHH_SIMP_Thm = save_thm(`LHH_SIMP_Thm`, OUTS_PRUNE LHH_Thm);;

let LHL_SIMP_Thm = save_thm(`LHL_SIMP_Thm`, OUTS_PRUNE LHL_Thm);;

let LLH_SIMP_Thm = save_thm(`LLH_SIMP_Thm`, OUTS_PRUNE LLH_Thm);;

let LLL_SIMP_Thm = save_thm(`LLL_SIMP_Thm`, OUTS_PRUNE LLL_Thm);;



