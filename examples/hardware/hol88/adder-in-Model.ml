

%----------------------------------------------------------------------------%
%----------------------------------------------------------------------------%
% The example in this file is incomplete.                                    %
%----------------------------------------------------------------------------%
%----------------------------------------------------------------------------%


%----------------------------------------------------------------------------%
% This file defines a HOL specification of an adder that mimics the          %
% following part specification in Lattice Logic's MODEL language.            %
%                                                                            %
%    PART ADDER_IMP (n) [a(0:n),b(0:n),cin] -> sum(0:n),cout                 %
%     SIGNAL c(0:n+1)                                                        %
%     INTEGER i                                                              %
%     cin -> c(0)                                                            %
%     FOR i = 0:n CYCLE                                                      %
%      ADD1[a(i),b(i),c(i)] -> sum(i),c(i+1)                                 %
%     REPEAT                                                                 %
%     c(n+1) -> cout                                                         %
%    END                                                                     %
%                                                                            %
% This example is discussed in the paper "Why Higher-Order Logic is a Good   %
% Formalism for Specifying and Verifying Hardware" in the book "Formal       %
% Aspects of VLSI Design", edited by G. Milne and P.A. Subrahmanyam,         %
% North Holland, 1986.                                                       %
%                                                                            %
% The HOL representation of this MODEL specification is:                     %
%                                                                            %
%    ADDER_IMP n (a,b,cin,sum,cout) =                                        %
%     ?c.                                                                    %
%      (cin = c 0) /\                                                        %
%      ITERATE (0,n) (\i. ADD1(a i, b i, c i, sum i, c(i+1))) /\             %
%      (c(n+1) = cout)                                                       %
%                                                                            %
% We then show this specification is equivalent to a straightforward         %
% primitive recursion, namely ADDER_IMP = ADDER, where:                      %
%                                                                            %
%    ADDER 0 (a,b,cin,sum,cout) = ADD1(a(0),b(0),cin,sum(0),cout)            %
%                                                                            %
%    ADDER (SUC n) (a,b,cin,sum,cout) =                                      %
%     ?c.ADDER n (a,b,cin,sum,c) /\                                          %
%        ADD1(a(SUC n),b(SUC n),c,sum(SUC n),cout))                          %
%                                                                            %
% The higher-order function ITERATE has type:                                %
%                                                                            %
%    ITERATE : (num#num) -> (num -> bool) -> bool                            %
%                                                                            %
% and satisfies:                                                             %
%                                                                            %
%    ITERATE (m,n) f = f(n) /\ f(n-1) /\ ... /\ f(m+1) /\ f(m)               %
%                                                                            %
% It would be nice to define this directly by:                               %
%                                                                            %
%    ITERATE (m,n) f = ((m=n) => f(m) | ITERATE(m+1,n) /\ f(m))              %
%                                                                            %
% but this won't work (consider the case when m>n, e.g. ITERATE(1,0)f).      %
%                                                                            %
% To define ITERATE we first define another function ITER by primitive       %
% recursion:                                                                 %
%                                                                            %
%    ITER   0   n f  =  T                                                    %
%    ITER (m+1) n f  =  ITER m (n+1) f /\ f n                                %
%                                                                            %
% the we can define:                                                         %
%                                                                            %
%    ITERATE (m,n) f = ITER((n-m)+1)                                         %
%                                                                            %
%                                                                            %
% For the adder we only need to show:                                        %
%                                                                            %
%    ITERATE (0,n+1) f = f(n+1) /\ ITERATE (0,n) f                           %
%                                                                            %
% We start by defining ITER and ITERATE.                                     %
%                                                                            %
%----------------------------------------------------------------------------%

new_theory `model_adder`;;

let ITER =
 new_prim_rec_definition
  (`ITER`,
   "(ITER    0    n f  =  T) /\
    (ITER (SUC m) n f  =  ITER m (n+1) f /\ f n)");;

let ITERATE =
 new_definition
  (`ITERATE`,
   "ITERATE (m,n) f  =  ITER ((n-m)+1) m f");;

%----------------------------------------------------------------------------%
% We can easily prove that ITERATE (m,n) f satisfies the recursion equation  %
% we want (as long as m is less than or equal to n).                         %
%----------------------------------------------------------------------------%

%----------------------------------------------------------------------------%
% ADD1_SYM = |- m + 1 = SUC m                                                %
%----------------------------------------------------------------------------%

let ADD1_SYM = SYM(SPEC_ALL ADD1);;

let ITER_LEMMA1 =
 prove_thm
  (`ITER_LEMMA1`,
   "!m n f. ITER (m+1) n f = f(m+n) /\ ITER m n f",
   INDUCT_TAC
    THEN REWRITE_TAC[ITER;ADD_CLAUSES]
    THENL
     [REWRITE_TAC[ITER;num_CONV "1"];
      ASM_REWRITE_TAC[num_CONV "1";ADD_CLAUSES;CONJ_ASSOC]]);;

%----------------------------------------------------------------------------%
% SUB_REFL = |- n - n = 0                                                    %
%----------------------------------------------------------------------------%

let SUB_REFL =
 prove_thm
  (`SUB_REFL`,
   "!n. n-n = 0",
   REWRITE_TAC[SUB_EQ_0;LESS_EQ_REFL]);;


%----------------------------------------------------------------------------%
% ITER_LEMMA2 = |- ITER m(SUC n)f /\ f n = ITER(SUC m)n f                    %
%----------------------------------------------------------------------------%

let ITER_LEMMA2 = REWRITE_RULE[ADD1_SYM](SYM(CONJUNCT2 ITER));;

let SUB_MONO_EQ =
 prove_thm
  (`SUB_MONO_EQ`,
   "!m n. (SUC m) - (SUC n) = m - n",
   INDUCT_TAC
    THEN ASM_REWRITE_TAC[SUB;LESS_0;LESS_MONO_EQ]);;


let SUB_LEMMA =
 prove_thm
  (`SUB_LEMMA`,
   "(m < n) ==> (SUC(n - m) = SUC(SUC(n - (SUC m))))",
   STRIP_TAC
    THEN REWRITE_TAC[INV_SUC_EQ]
    THEN IMP_RES_TAC LESS_SUC_NOT
    THEN ASSUM_LIST 
          (\thl. REWRITE_TAC
                  [REWRITE_RULE thl 
                                (INST["n:num","m:num";"SUC m","n:num"]
                                     (SYM(CONJUNCT2 SUB)))])
    THEN REWRITE_TAC[SUB_MONO_EQ]);;


let LESS_EQ_LEMMA =
 prove_thm
  (`LESS_EQ_LEMMA`,
   "(m <= n) ==> ~(m = n) ==> (m < n)",
   REWRITE_TAC[LESS_OR_EQ]
    THEN REPEAT STRIP_TAC
    THEN IMP_RES_TAC NOT_LESS_EQ
    THEN RES_TAC
    THEN ASM_REWRITE_TAC[]);;


let ITERATE_LEMMA1 =
 prove_thm
  (`ITERATE_LEMMA1`,
   "!m n f.
     (m <= n) ==> 
      (ITERATE (m,n) f = ((m=n) => f(m) | ITERATE ((m+1),n) f /\ f m))",
   REWRITE_TAC [ITERATE]
    THEN REPEAT STRIP_TAC
    THEN ASM_CASES_TAC "m:num=n"
    THEN ASM_REWRITE_TAC[ADD1_SYM;ADD_CLAUSES;ITER;SUB_REFL]
    THEN IMP_RES_TAC LESS_EQ_LEMMA
    THEN IMP_RES_TAC SUB_LEMMA
    THEN ASM_REWRITE_TAC[ITER_LEMMA2]);;


let ITERATE_LEMMA2 =
 prove_thm
  (`ITERATE_LEMMA2`,
   "ITERATE (0,n+1) f = f(n+1) /\ ITERATE (0,n) f",
   REWRITE_TAC[ITERATE;ADD1_SYM;SUB_0;ADD_CLAUSES;ITER_LEMMA1]
    THEN REWRITE_TAC[ADD1;ITER_LEMMA1;ADD_CLAUSES]);;


new_constant(`ADD1`, ":bool#bool#bool#bool#bool->bool");;

let ADDER_IMP =
 new_definition
  (`ADDER_IMP`,
   "ADDER_IMP n (a,b,cin,sum,cout) =
     ?c.
      (cin = c 0) /\
      ITERATE (0,n) (\i. ADD1(a i, b i, c i, sum i, c(i+1))) /\
      (c(n+1) = cout)");;


let ADDER = 
 new_prim_rec_definition
  (`ADDER`,
   "(ADDER 0 a b cin sum cout = ADD1(a(0),b(0),cin,sum(0),cout))
    /\
    (ADDER (SUC n) a b cin sum cout =
      ?c.ADDER n  a b cin sum c /\
         ADD1(a(SUC n),b(SUC n),c,sum(SUC n),cout))");;


let ADDER0_LEMMA =
 prove_thm
 (`ADDER0_LEMMA`,
  "ADDER_IMP 0 (a,b,cin,sum,cout) = ADDER 0 a b cin sum cout",
  REWRITE_TAC[ADDER_IMP;ADDER;ITERATE;ITER;SUB;ADD_CLAUSES;num_CONV "1"]
   THEN BETA_TAC
       THEN EQ_TAC
       THEN REPEAT STRIP_TAC
       THENL 
        [ASM_REWRITE_TAC[]
          THEN REWRITE_TAC[SYM(ASSUME "c(SUC 0) = (cout:bool)")]
          THEN ASM_REWRITE_TAC[];
         EXISTS_TAC"\x. ((x=0) => cin:bool | cout:bool)"
          THEN BETA_TAC
          THEN ASM_REWRITE_TAC[NOT_SUC]]);;

% The proof below is incomplete

let ADDER_THM =
 prove_thm
 (`ADDER_THM`,
  "!n. ADDER_IMP n (a,b,cin,sum,cout) = ADDER n a b cin sum cout",
  INDUCT_TAC
   THENL 
    [REWRITE_TAC[ADDER0_LEMMA];
     REWRITE_TAC
      [ADDER_IMP;ADDER;ITERATE;ITER;SUB;ADD_CLAUSES;
       num_CONV "1";SUB_0;NOT_LESS_0]
      THEN BETA_TAC
      THEN EQ_TAC
      THENL
       [REPEAT STRIP_TAC

%

