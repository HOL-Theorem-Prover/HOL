

%----------------------------------------------------------------------------%
% In this file we specify and verify a resetable parity checker.             %
% This computes the parity of the input since the last reset.                %
%                                                                            %
%               reset   in                                                   %
%                 |     |                                                    %
%                 |     |                                                    %
%            *--------------*                                                %
%            | RESET_PARITY |                                                %
%            *--------------*                                                %
%                    |                                                       %
%                    |                                                       %
%                   out                                                      %
%                                                                            %
%----------------------------------------------------------------------------%

new_theory `RESET_PARITY`;;

%----------------------------------------------------------------------------%
%                                                                            %
% To specify RESET_PARITY we first define:                                   %
%                                                                            %
%                       *-                                                   %
%                       | T  if t1 was the last time before t2 that f was T  %
%    LAST (t1,t2) f  =  <                                                    %
%                       | F  otherwise                                       %
%                       *-                                                   %
%                                                                            %
% Formally:                                                                  %
%                                                                            %
%    LAST (t1,t2) f  =  (t1 <= t2) /\ (f t1) /\ !t. t1<t /\ t<=t2 ==> ~(f t) %
%                                                                            %
%----------------------------------------------------------------------------%

let LAST =
 new_definition
  (`LAST`,
   "LAST (t1,t2) f =
     (t1 <= t2) /\ (f t1) /\ !t. (t1<t) /\ (t<=t2) ==> ~(f t)");;

let LAST_LEMMA1 =
 prove_thm
  (`LAST_LEMMA1`,
   "LAST(t, SUC(t+d))f ==> LAST(t,t+d)f",
   REWRITE_TAC[LAST]
    THEN STRIP_TAC
    THEN STRIP_TAC
    THEN ASM_REWRITE_TAC[LESS_EQ_ADD]
    THEN STRIP_TAC
    THEN STRIP_TAC
    THEN ASSUME_TAC (SPEC "t + d" LESS_EQ_SUC_REFL)
    THEN IMP_RES_TAC LESS_EQ_TRANS
    THEN RES_TAC);;

let SUC_ADD =
 prove_thm
  (`SUC_ADD`,
   "!d. t < SUC(t + d)",
   INDUCT_TAC
    THEN ASM_REWRITE_TAC[LESS_THM;ADD_CLAUSES]);;
    
let LAST_LEMMA2 =
 prove_thm
  (`LAST_LEMMA2`,
   "LAST(t, SUC(t+d))f ==> ~f(SUC(t+d))",
   REWRITE_TAC[LAST]
    THEN STRIP_TAC
    THEN ASSUME_TAC (SPEC "d:num" SUC_ADD)
    THEN ASSUME_TAC (SPEC "SUC(t+d)" LESS_EQ_REFL)
    THEN RES_TAC);;

%----------------------------------------------------------------------------%
% LAST_LEMMA3 = |- LAST(t,SUC t)f ==> ~f(SUC t)                              %
%----------------------------------------------------------------------------%

let LAST_LEMMA3 =
 REWRITE_RULE[ADD_CLAUSES](INST["0","d:num"]LAST_LEMMA2);;

%----------------------------------------------------------------------------%
%                                                                            %
% We also define:                                                            %
%                                                                            %
%                     *-                                                     %
%                     | T if f is T an even number of times between t1 and t2%
%   PTY (t1,t2) f  =  <                                                      %
%                     | F if f is T an odd number of times between t1 and t2 %
%                     *-                                                     %
%                                                                            %
% Using the function PARITY (from the theory PARITY; see PARITY.ml) we can   %
% define PTY by:                                                             %
%                                                                            %
%    PTY (t1,t2) f = PARITY (t2-t1) (\t. f(t+t1))                            %
%                                                                            %
%----------------------------------------------------------------------------%

new_parent `PARITY`;;

let PTY =
 new_definition
  (`PTY`, "PTY (t1,t2) f = PARITY (t2-t1) (\t. f(t+t1))");;

%----------------------------------------------------------------------------%
%                                                                            %
% From this definition it follows that:                                      %
%                                                                            %
%    PTY (t,t) f = T                                                         %
%                                                                            %
%    PTY (t1, SUC t2) f = (f(SUC t2) => ~PTY(t1,t2)f | PTY(t1,t2)f)          %
%                                                                            %
%----------------------------------------------------------------------------%

let PARITY = theorem `PARITY` `PARITY_DEF`;;

%----------------------------------------------------------------------------%
% SUB_REFL = |- n - n = 0                                                    %
%----------------------------------------------------------------------------%

let SUB_REFL =
 prove_thm
  (`SUB_REFL`,
   "!n. n-n = 0",
   REWRITE_TAC[SUB_EQ_0;LESS_EQ_REFL]);;

let SUB_SUC =
 prove_thm
  (`SUB_SUC`,
   "!m n. (n <= m) ==> (((SUC m) - n) = SUC(m -n))",
   REWRITE_TAC[SYM(SPEC_ALL NOT_LESS)]
    THEN REPEAT STRIP_TAC
    THEN REWRITE_TAC[REWRITE_RULE[ASSUME "~(m<n)"]SUB]);;


let PTY_LEMMA1 =
 prove_thm
  (`PTY_LEMMA1`,
   "(!t f. PTY (t,t) f = T) /\
    (!t1 t2 f.
       (t1 <= t2) ==> 
        (PTY (t1, SUC t2) f = (f(SUC t2) => ~PTY(t1,t2)f | PTY(t1,t2)f)))",
   REWRITE_TAC[PTY;SUB_REFL;PARITY]
    THEN BETA_TAC
    THEN REPEAT STRIP_TAC
    THEN IMP_RES_TAC SUB_SUC
    THEN ASM_REWRITE_TAC[PARITY]
    THEN BETA_TAC
    THEN REWRITE_TAC[SYM(ASSUME "(SUC t2) - t1 = SUC(t2 - t1)")]
    THEN ASSUME_TAC(SPEC "t2:num" LESS_EQ_SUC_REFL)
    THEN IMP_RES_TAC LESS_EQ_TRANS
    THEN IMP_RES_TAC SUB_ADD
    THEN ASM_REWRITE_TAC[]);;

%----------------------------------------------------------------------------%
% A useful corollary.                                                        %
%----------------------------------------------------------------------------%

let PTY_LEMMA2 =
 prove_thm
  (`PTY_LEMMA2`,
   "PTY (t, SUC(t+d)) f = (f(SUC(t+d)) => ~PTY(t,(t+d))f | PTY(t,(t+d))f)",
   REWRITE_TAC
    [MATCH_MP (CONJUNCT2 PTY_LEMMA1) (SPECL["t:num";"d:num"]LESS_EQ_ADD)]);;

%----------------------------------------------------------------------------%
% PTY_LEMMA3 = |- PTY(t,SUC t)f = (f(SUC t) => ~PTY(t,t)f | PTY(t,t)f)       %
%----------------------------------------------------------------------------%

let PTY_LEMMA3 =
 REWRITE_RULE[ADD_CLAUSES](INST["0","d:num"]PTY_LEMMA2);;

%----------------------------------------------------------------------------%
%                                                                            %
% We can now specify our resetable parity checker by:                        %
%                                                                            %
%    RESET_PARITY(reset,in,out)  =                                           %
%     !t1 t2. LAST(t1,t2)reset ==> (out t2 = PTY(t1,t2)in)                   %
%                                                                            %
%----------------------------------------------------------------------------%


let RESET_PARITY =
 new_definition
  (`RESET_PARITY`,
   "RESET_PARITY(reset,in,out)  =
     !t1 t2. LAST(t1,t2)reset ==> (out t2 = PTY(t1,t2)in)");;

%  %

%----------------------------------------------------------------------------%
%                                                                            %
% We implement this specification using a resetable register:                %
%                                                                            %
%    reset      in                                                           %
%      |        |      |------------|                                        %
%      |        |      |            |                                        %
%      |        |   *-----*         |                                        %
%      |        |   | NOT |         |                                        %
%      |        |   *-----*         |                                        %
%      |        |      |l1    |-----|l2                                      %
%      |        |      |      |     |                                        %
%      |      *-----------------*   |                                        %
%      |      |       MUX       |   |                                        %
%      |      *-----------------*   |                                        %
%      |               |            |                                        %
%      |---------|     |------|l3   |                                        %
%      |         |     |      |     |                                        %
%      |      *-----------*   |     |                                        %
%      |      | RESET_REG |   |     |                                        %
%      |      *-----------*   |     |                                        %
%      |            |         |     |                                        %
%      |--|         |---------------|                                        %
%         |         |         |                                              %
%       *-----------------------*                                            %
%       |          MUX          |                                            %
%       *-----------------------*                                            %
%                   |                                                        %
%                  out                                                       %
%                                                                            %
%----------------------------------------------------------------------------%


new_parent `RESET_REG`;;

let RESET_PARITY_IMP =
 new_definition
  (`RESET_PARITY_IMP`,
   "RESET_PARITY_IMP(reset,in,out) =
    ?l1 l2 l3. NOT(l2,l1)        /\
               MUX(in,l1,l2,l3) /\
               RESET_REG(reset,l3,l2) /\
               MUX(reset,l2,l3,out)");;

            
let NOT       = definition `PARITY` `NOT_DEF`
and MUX       = definition `PARITY` `MUX_DEF`
and RESET_REG = definition `RESET_REG` `RESET_REG`;;


let RESET_PARITY_IMP_LEMMA1 =
 prove_thm
  (`RESET_PARITY_IMP_LEMMA1`,
   "RESET_PARITY_IMP(reset,in,out) 
    ==>
    !d t. LAST(t,t)reset  ==>  (out t = PTY(t,t)in)",
   REWRITE_TAC[RESET_PARITY_IMP;MUX;RESET_REG;LAST;PTY_LEMMA1]
    THEN REPEAT STRIP_TAC
    THEN RES_TAC
    THEN ASM_REWRITE_TAC[]);;


%----------------------------------------------------------------------------%
% The proof that follows is a bad example of `proof hacking', i.e. the use   %
% of ad-hoc low-level manipulations instead of thought. It is likely that    %
% a much more elegant proof is possible.                                     %
%                                                                            %
% First we prove a lemma and then define a couple of special purpose         %
% functions.                                                                 %
%----------------------------------------------------------------------------%

%----------------------------------------------------------------------------%
% LAST(t,t + (SUC d))reset |- ~reset(t + (SUC d))                            %
%----------------------------------------------------------------------------%

let reset_LEMMA =
 let [();();();th] = CONJUNCTS ADD_CLAUSES
 in
 REWRITE_RULE[SYM th]
  (MATCH_MP (GEN_ALL LAST_LEMMA2)
            (REWRITE_RULE[ADD_CLAUSES](ASSUME "LAST(t,t + (SUC d))reset")));;

%----------------------------------------------------------------------------%
% lines `l1 l2 ... ln` tm is true if tm has the form "!t. li t = ..."        %
% for some li.                                                               %
%----------------------------------------------------------------------------%

let lines tok t =
 (let x = (fst o dest_var o rator o lhs o snd o dest_forall) t
  in
  mem x (words tok)) ? false;;

%----------------------------------------------------------------------------%
% UNWIND_LINES_TAC `l` tm finds an assumption "!t. l t =  ... t ..."         %
% and then unwinds with "l tm = ... tm ...".                                 %
%----------------------------------------------------------------------------%

let UNWIND_LINES_TAC l t =
 FIRST_ASSUM
  (\th. if lines l (concl th) then SUBST_TAC[SPEC t th] else NO_TAC);;


let RESET_PARITY_IMP_LEMMA2 =
 prove_thm
  (`RESET_PARITY_IMP_LEMMA2`,
   "RESET_PARITY_IMP(reset,in,out) 
    ==>
    !d t. LAST(t, t+(SUC d))reset
          ==>
          (out(t+(SUC d)) = PTY(t, t+(SUC d))in)",
    REWRITE_TAC[NOT;MUX;RESET_REG;RESET_PARITY_IMP]
     THEN STRIP_TAC
     THEN INDUCT_TAC
     THENL
      [REWRITE_TAC[ADD_CLAUSES]
        THEN STRIP_TAC
        THEN STRIP_TAC
        THEN IMP_RES_TAC LAST_LEMMA3
        THEN IMP_RES_TAC (fst (EQ_IMP_RULE LAST))
        THEN RES_TAC
        THEN ASM_REWRITE_TAC[PTY_LEMMA1;PTY_LEMMA3;ADD1];
       ALL_TAC]
     THEN ONCE_REWRITE_TAC[ADD_CLAUSES]
     THEN STRIP_TAC
     THEN STRIP_TAC
     THEN IMP_RES_TAC LAST_LEMMA1
     THEN IMP_RES_TAC LAST_LEMMA2
     THEN REWRITE_TAC[PTY_LEMMA2]
     THEN RES_THEN (\th. REWRITE_TAC[SYM th])
     THEN UNWIND_LINES_TAC `out` "SUC(t+(SUC d))"
     THEN FILTER_ASM_REWRITE_TAC is_neg []
     THEN UNWIND_LINES_TAC `l3` "SUC(t+(SUC d))"
     THEN UNWIND_LINES_TAC `l1` "SUC(t+(SUC d))"
     THEN ONCE_REWRITE_TAC[ADD1]
     THEN UNWIND_LINES_TAC `l2` "t+(SUC d)"
     THEN UNWIND_LINES_TAC `out` "t+(d+1)"
     THEN REWRITE_TAC [SYM(SPEC_ALL ADD1)]
     THEN ASSUME_TAC reset_LEMMA
     THEN FILTER_ASM_REWRITE_TAC is_neg []);;

let RESET_PARITY_IMP_LEMMA3 =
 prove_thm
  (`RESET_PARITY_IMP_LEMMA3`,
   "RESET_PARITY_IMP(reset,in,out) 
    ==>
    !d t. LAST(t,t+d)reset  ==>  (out(t+d) = PTY(t,t+d)in)",
   STRIP_TAC
    THEN INDUCT_TAC
    THENL
     [REWRITE_TAC[ADD_CLAUSES]
       THEN IMP_RES_TAC RESET_PARITY_IMP_LEMMA1;
      IMP_RES_TAC RESET_PARITY_IMP_LEMMA2]
    THEN ASM_REWRITE_TAC[]);;

%----------------------------------------------------------------------------%
% RESET_PARITY_IMP_LEMMA4 =                                                  %
% |- RESET_PARITY_IMP(reset,in,out) ==>                                      %
%    t1 <= t2 ==>                                                            %
%    LAST(t1,t2)reset ==>                                                    %
%    (out t2 = PTY(t1,t2)in)                                                 %
%----------------------------------------------------------------------------%

let RESET_PARITY_IMP_LEMMA4 =
 let th1 = UNDISCH RESET_PARITY_IMP_LEMMA3
 in
 let th2 = SPECL["t2-t1";"t1:num"]th1
 in
 let th3 = ONCE_REWRITE_RULE[ADD_SYM]th2
 in
 let th4 = REWRITE_RULE[MATCH_MP SUB_ADD (ASSUME "t1<=t2")]th3
 in
 DISCH_ALL th4;;


%----------------------------------------------------------------------------%
% From the various lemmas we can now prove the implementation correct.       %
%----------------------------------------------------------------------------%

let RESET_PARITY_IMP_CORRECT =
 prove_thm
  (`RESET_PARITY_IMP_CORRECT`,
   "!reset in out.
     RESET_PARITY_IMP(reset,in,out) ==> RESET_PARITY(reset,in,out)",
   REWRITE_TAC[RESET_PARITY]
    THEN REPEAT GEN_TAC
    THEN DISCH_TAC
    THEN REPEAT GEN_TAC
    THEN ASM_CASES_TAC "t1<=t2"
    THENL
     [IMP_RES_TAC RESET_PARITY_IMP_LEMMA4;
      ASM_REWRITE_TAC[LAST]]);;
