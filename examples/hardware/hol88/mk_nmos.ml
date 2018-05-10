% Sledgehammer-style verification of Mike Fourman's shift-register example:

          ph1                          ph3
           |                            |
  |--------|                   |--------|
  |        |                   |        |
  |    | |-|                   |    | |-|
  |----| |                     |----| |
       | |-|                        | |-|
           |                            |    
         b3|-----|                    b7|-----|
                 *-------------|              *--------------|
           |-----|             |        |-----|              |
           |                   |        |                    |
           |                   |        |                    |
         b2|                 b4|      b6|                  b8|
           |                   |        |                    |
           |                   |        |                    |
       | |-|                   |    | |-|                    |   ||
 i-----| |                     |----| |                      |---||---o
       | |-|                        | |-|                        ||
           |                            |
         b1|                          b5|
           |                            |
           |                            |
       | |-|                        | |-|
ph2----| |                   ph4----| |
       | |-|                        | |-|
           |                            |
           |                            |
          ph1                          ph3
%

new_theory`nmos`;;

new_type 0 `tri`;;

let time = ":num";;
let sig  = ":^time -> tri";;

maptok (\t. new_constant(t,":tri")) `HI LO ZZ`;;

let TRI_EQ_DISTINCT =
 new_axiom(`TRI_EQ_DISTINCT`, "~(HI=LO) /\ ~(HI=ZZ) /\ ~(LO=ZZ)");;

let TRI_EQ_CLAUSES =
 let thl1 = CONJUNCTS TRI_EQ_DISTINCT
 in
 let thl2 = map NOT_EQ_SYM thl1
 in
 save_thm(`TRI_EQ_CLAUSES`, LIST_CONJ(thl1@thl2));;

% DEF x is true if x is HI or LO %

new_definition
 (`DEF`,
  "!x:tri. DEF x = ((x = HI) \/ (x = LO))");;

% JOIN below is the behaviour of a wired join %

new_curried_infix(`JOIN`, ":tri->tri->tri");;

new_axiom
 (`JOIN_CLAUSES`,
  "!x:tri.
   (x  JOIN ZZ = x) /\
   (ZZ JOIN x  = x) /\
   (x  JOIN x  = x)");;

% Transistors need to remember gate-values from ph1 to ph4 (three cycles).
  (If i(t-2)=LO then the ph1 precharge of b4 is used at ph4 to switch on the
  transistor between b5 and b6). %

new_definition
 (`TRAN`,
  "!g:^sig. !s:^sig. !d:^sig.
    TRAN(g,s,d) =
     (d = \t. (((g t=HI)                                    \/ 
               ((g t=ZZ) /\ (g(t-1) = HI))                  \/ 
               ((g t=ZZ) /\ (g(t-1) = ZZ) /\ (g(t-2) = HI)) \/
               ((g t=ZZ) /\ (g(t-1) = ZZ) /\ (g(t-2) = ZZ) /\ (g(t-3) = HI)))
              => s t 
              | ZZ))");;

% Is this definition correct when t<3? %

new_definition
 (`WIRED_JOIN`,
  "!i1:^sig. !i2:^sig. !o:^sig.
    WIRED_JOIN(i1,i2,o) = (o = \t. (i1 t) JOIN (i2 t))");;

% A capacitor is needed to hold the phase3 precharge on the output line o
  when i(t-2)=LO %

new_definition
 (`CAPACITOR`,
  "!i:^sig. !o:^sig.
    CAPACITOR(i,o) = (o = \t. (DEF(i t) => i t | i(t-1)))");;

new_definition
 (`SHIFT_BODY`,
   "!ph1 ph2 ph3 ph4 b1 b2 b3 b4 b5 b6 b7 b8 i o.
     SHIFT_BODY(ph1,ph2,ph3,ph4,b1,b2,b3,b4,b5,b6,b7,b8,i,o) =
      TRAN(ph1,ph1,b3)     /\
      TRAN(i  ,b1 ,b2)     /\
      TRAN(ph2,ph1,b1)     /\
      TRAN(ph3,ph3,b7)     /\
      TRAN(b4 ,b5 ,b6)     /\
      TRAN(ph4,ph3,b5)     /\
      WIRED_JOIN(b2,b3,b4) /\
      WIRED_JOIN(b6,b7,b8) /\
      CAPACITOR(b8,o)");;

new_definition
 (`SHIFT`,
   "SHIFT(ph1,ph2,ph3,ph4,i,o) =
    ?b1 b2 b3 b4 b5 b6 b7 b8.
     SHIFT_BODY(ph1,ph2,ph3,ph4,b1,b2,b3,b4,b5,b6,b7,b8,i,o)");;

new_definition
 (`FOUR_PHASE`,
  "!ph1 ph2 ph3 ph4.
    FOUR_PHASE(ph1,ph2,ph3,ph4) (t:^time) = 
     (ph1(t-3)=HI) /\ (ph2(t-3)=LO) /\ (ph3(t-3)=LO) /\ (ph4(t-3)=LO) /\
     (ph1(t-2)=LO) /\ (ph2(t-2)=HI) /\ (ph3(t-2)=LO) /\ (ph4(t-2)=LO) /\
     (ph1(t-1)=LO) /\ (ph2(t-1)=LO) /\ (ph3(t-1)=HI) /\ (ph4(t-1)=LO) /\
     (ph1 t   =LO) /\ (ph2 t   =LO) /\ (ph3 t   =LO) /\ (ph4 t   =HI)");;

%
Is this the right definition? What about when t<3?
Maybe a better definition would be:

new_definition
 (`FOUR_PHASE`,
  "!ph1 ph2 ph3 ph4.
    FOUR_PHASE(ph1,ph2,ph3,ph4) (t:^time) = 
     ?t1 t2 t3 t4. 
      (t2=SUC t1) /\ (t3 = SUC t2) /\ (t4 = SUC t3) /\ (t = t4) /\
        (ph1 t1 = HI) /\ (ph2 t1 = LO) /\ (ph3 t1 = LO) /\ (ph4 t1 = LO) /\
        (ph1 t2 = LO) /\ (ph2 t2 = HI) /\ (ph3 t2 = LO) /\ (ph4 t2 = LO) /\
        (ph1 t3 = LO) /\ (ph2 t3 = LO) /\ (ph3 t3 = HI) /\ (ph4 t3 = LO) /\
        (ph1 t4 = LO) /\ (ph2 t4 = LO) /\ (ph3 t4 = LO) /\ (ph4 t4 = HI)");;
%

close_theory();;

% The proof that follows uses a sledgehammer approach! %

load_theory`nmos`;;

let TRAN            = axiom `nmos` `TRAN`
and SHIFT_BODY      = axiom `nmos` `SHIFT_BODY`
and SHIFT           = axiom `nmos` `SHIFT`
and JOIN_CLAUSES    = axiom `nmos` `JOIN_CLAUSES`
and WIRED_JOIN      = axiom `nmos` `WIRED_JOIN`
and CAPACITOR       = axiom `nmos` `CAPACITOR`
and TRI_EQ_DISTINCT = axiom `nmos` `TRI_EQ_DISTINCT`
and DEF             = axiom `nmos` `DEF`
and FOUR_PHASE      = axiom `nmos` `FOUR_PHASE`;;

% The theorem TRIV_COND below will be put in the HOL system as part of
  basic-rewrites %

let TRIV_COND =
 TAC_PROOF
  (([],"!b. !x:*. (b => x | x) = x"),
   REPEAT STRIP_TAC
    THEN COND_CASES_TAC
    THEN REWRITE_TAC[]);;

% MINUS_ASSUM can be derived as a theorem, but I havn't yet done so %

let MINUS_ASSUM =
 ASSUME "!x. (((x-1)-1) = (x-2)) /\ 
             (((x-1)-2) = (x-3)) /\ 
             (((x-2)-1) = (x-3)) /\
             (((x-2)-2) = (x-4))";;

let SHIFT_BODY_THM1 =
 LIST_CONJ
 (map
  (\th.RIGHT_BETA(AP_THM th "(t-3):^time"))
  (CONJUNCTS
   (UNDISCH
    (fst
     (EQ_IMP_RULE(UNFOLD_RULE [TRAN;WIRED_JOIN;CAPACITOR] SHIFT_BODY))))));;

let SHIFT_BODY_THM2 =
 REWRITE_RULE
  [UNDISCH(fst(EQ_IMP_RULE(SPEC_ALL FOUR_PHASE)));TRI_EQ_CLAUSES;MINUS_ASSUM]
  SHIFT_BODY_THM1;;

let SHIFT_BODY_THM3 =
 LIST_CONJ
 (map
  (\th.RIGHT_BETA(AP_THM th "(t-2):^time"))
  (CONJUNCTS
   (UNDISCH
    (fst
     (EQ_IMP_RULE(UNFOLD_RULE [TRAN;WIRED_JOIN;CAPACITOR] SHIFT_BODY))))));;

let SHIFT_BODY_THM4 =
 REWRITE_RULE
  [UNDISCH(fst(EQ_IMP_RULE(SPEC_ALL FOUR_PHASE)));TRI_EQ_CLAUSES;MINUS_ASSUM]
  SHIFT_BODY_THM3;;

let SHIFT_BODY_THM5 =
 LIST_CONJ
 (map
  (\th.RIGHT_BETA(AP_THM th "(t-1):^time"))
  (CONJUNCTS
   (UNDISCH
    (fst
     (EQ_IMP_RULE(UNFOLD_RULE [TRAN;WIRED_JOIN;CAPACITOR] SHIFT_BODY))))));;

let SHIFT_BODY_THM6 =
 REWRITE_RULE
  [UNDISCH(fst(EQ_IMP_RULE(SPEC_ALL FOUR_PHASE)));TRI_EQ_CLAUSES;MINUS_ASSUM]
  SHIFT_BODY_THM5;;

let SHIFT_BODY_THM7 =
 LIST_CONJ
 (map
  (\th.RIGHT_BETA(AP_THM th "t:^time"))
  (CONJUNCTS
   (UNDISCH
    (fst
     (EQ_IMP_RULE(UNFOLD_RULE [TRAN;WIRED_JOIN;CAPACITOR] SHIFT_BODY))))));;

let SHIFT_BODY_THM8 =
 REWRITE_RULE
  [UNDISCH(fst(EQ_IMP_RULE(SPEC_ALL FOUR_PHASE)));TRI_EQ_CLAUSES]
  SHIFT_BODY_THM7;;

let B4_ph1 =
 (let thl = CONJUNCTS SHIFT_BODY_THM2
  in
  REWRITE_RULE
   [el 1 thl;el 2 thl;el 3 thl;TRI_EQ_CLAUSES;JOIN_CLAUSES;TRIV_COND]
   (el 7 thl));;

let B4_HI_ph2 = 
 (let thl = CONJUNCTS SHIFT_BODY_THM4
  in
  REWRITE_RULE
   [el 1 thl;el 2 thl;el 3 thl;TRI_EQ_CLAUSES;JOIN_CLAUSES;ASSUME"i(t-2)=HI"]
   (el 7 thl));;

let B4_LO_ph2 = 
 (let thl = CONJUNCTS SHIFT_BODY_THM4
  in
  REWRITE_RULE
   [el 1 thl;el 2 thl;TRI_EQ_CLAUSES;JOIN_CLAUSES;ASSUME"i(t-2)=LO"]
   (el 7 thl));;

let B4_ph3 = 
 (let thl = CONJUNCTS SHIFT_BODY_THM6
  in
  REWRITE_RULE
   [el 1 thl;el 2 thl;el 3 thl;
    TRI_EQ_CLAUSES;JOIN_CLAUSES;TRIV_COND]
   (el 7 thl));;

let B8_ph3 = 
 (let thl = CONJUNCTS SHIFT_BODY_THM6
  in
  REWRITE_RULE
   [el 4 thl;el 5 thl;el 6 thl;
    TRI_EQ_CLAUSES;JOIN_CLAUSES;TRIV_COND]
   (el 8 thl));;

let B4_ph4 = 
 (let thl = CONJUNCTS SHIFT_BODY_THM8
  in
  REWRITE_RULE
   [el 1 thl;el 2 thl;el 3 thl;
    TRI_EQ_CLAUSES;JOIN_CLAUSES;TRIV_COND]
   (el 7 thl));;

let o_HI_ph4 =
 (let thl = CONJUNCTS SHIFT_BODY_THM8
  in
  REWRITE_RULE
   [el 4 thl;el 5 thl;el 6 thl;el 8 thl;
    B4_HI_ph2;B4_ph3;B8_ph3;B4_ph4;
    TRI_EQ_CLAUSES;JOIN_CLAUSES;DEF;TRIV_COND]
   (el 9 thl));;

let o_LO_ph4 =
 (let thl = CONJUNCTS SHIFT_BODY_THM8
  in
  REWRITE_RULE
   [el 4 thl;el 5 thl;el 6 thl;el 8 thl;
    B4_ph1;B4_LO_ph2;B4_ph3;B4_ph4;
    TRI_EQ_CLAUSES;JOIN_CLAUSES;DEF;TRIV_COND]
   (el 9 thl));;

let SHIFT_CORRECTNESS =
 TAC_PROOF
  ((["SHIFT(ph1,ph2,ph3,ph4,i,o)";
     "FOUR_PHASE(ph1,ph2,ph3,ph4) t";
     "DEF(i(t-2))"],
    "(o:^sig) t = i(t-2)"),
   IMP_RES_TAC(fst(EQ_IMP_RULE(SPEC_ALL DEF)))
    THENL[ASM_REWRITE_TAC[o_HI_ph4];
          ASM_REWRITE_TAC[o_LO_ph4]]);;

save_thm
 (`SHIFT_CORRECTNESS`,
  (DISCH
   "SHIFT_BODY(ph1,ph2,ph3,ph4,b1,b2,b3,b4,b5,b6,b7,b8,i,o)"
   (GEN
    "t:^time"
    (DISCH
     "FOUR_PHASE(ph1,ph2,ph3,ph4)t"
     (DISCH "DEF(i(t - 2))" SHIFT_CORRECTNESS)))));;
