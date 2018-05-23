
%<----------------------------------------------------------------------------

  The difference model of transistors and its use to distinguish the good and
  bad XOR circuits described in "Hardware Verification using Higher-Order 
  Logic" (Camilleri, Gordon and Melham, Technical Report 91).

  The bad circuit is:

    
              |-----|
              | Pwr |
              |-----|
                 | p1
                --
               ||
           |--0||
           |   ||
           |    --
           |     |
           |     |
      i1---+---- | ---------------------------|
           |     |                            |
           |     |                           --
           |     |                          ||
           |     |                      |--0||
           |     |                      |   ||
           |     |                      |    --
           |     |                      |     |
      i2-- | --- | ---------------------|     |---o
           |     |                      |     |
           |     |                      |    --
           |     |                      |   ||
           |     |                      |---||
           |     |                          ||
           |     |                           --
           |     | p2                         |
           |     |----------------------------|
           |     |
           |    --
           |   ||
           |---||
               ||
                --
                 | p3
              |-----|
              | Gnd |
              |-----|

  The good circuit has two extra transistors forming a transmission gate:


              |-----|
              | Pwr |
              |-----|
                 | p1
                --
               ||
           |--0||
           |   ||
           |    --
           |     |
           |     |
   i1------+---- | ------+--------------------|
           |     |       |          +-------- | --+
           |     |    ___O___       |        --   |
           |     |    |-----|       |       ||    |
        +- | --- | ---|     |-------+   |--0||    |--o
        |  |     |    |-----|           |   ||    |
   i2---|  |     |    -------           |    --   |
        |  |     |       |              |     |   |
        +- | --- | ---------------------|     |---+
           |     |       |              |     |
           |     |       |              |    --
           |     |       |              |   ||
           |     |       |              |---||
           |     |       |                  ||
           |     |       |                   --
           |     | p3    |                    |
           |     |-------+--------------------|
           |     |
           |    --
           |   ||
           |---||
               ||
                --
                 | p2
              |-----|
              | Gnd |
              |-----|


---------------------------------------------------------------------------->%


%----------------------------------------------------------------------------%
% For HOL88 compatibility:                                                   %
%                                                                            %

hide_constant`o`;;
load_library`unwind`;;
load_library`eval`;;

%                                                                            %
%----------------------------------------------------------------------------%

system `rm XOR.th`;; % removes XOR.th if it exists %

new_theory `XOR`;;

% The type of the two values HI and LO. %

new_type 0 `val`;;

new_constant(`HI`, ":val");;
new_constant(`LO`, ":val");;

%----------------------------------------------------------------------------%
% Power.                                                                     %
%----------------------------------------------------------------------------%

let PWR =
 new_definition
  (`PWR`, "PWR o = (o=HI)");;

%----------------------------------------------------------------------------%
% Ground.                                                                    %
%----------------------------------------------------------------------------%

let GND =
 new_definition
  (`GND`, "GND o = (o=LO)");;

%----------------------------------------------------------------------------%
% n-transistor.                                                              %
%----------------------------------------------------------------------------%

let NTRAN =
 new_definition
  (`NTRAN`, "NTRAN(g,a,b) = (g=HI) ==> ((a=LO) = (b=LO))");;

%----------------------------------------------------------------------------%
% p-transistor.                                                              %
%----------------------------------------------------------------------------%

let PTRAN =
 new_definition
  (`PTRAN`, "PTRAN(g,a,b) = (g=LO) ==> ((a=HI) = (b=HI))");;

%----------------------------------------------------------------------------%
% The bad XOR gate.                                                          %
%----------------------------------------------------------------------------%

let BAD_XOR =
 new_definition
  (`BAD_XOR`,
   "BAD_XOR(i1,i2,o) =
     ?p1 p2 p3.
      PWR p1 /\ GND p2 /\
      PTRAN(i1,p1,p3) /\ NTRAN(i1,p3,p2) /\ 
      PTRAN(i2,i1,o)  /\ NTRAN(i2,o,p3)");;
 
%----------------------------------------------------------------------------%
% The good XOR gate.                                                         %
%----------------------------------------------------------------------------%

let GOOD_XOR =
 new_definition
  (`GOOD_XOR`,
   "GOOD_XOR(i1,i2,o) =
     ?p1 p2 p3.
      PWR p1 /\ GND p2 /\
      PTRAN(i1,p1,p3) /\ NTRAN(i1,p3,p2) /\ 
      PTRAN(i2,i1,o)  /\ NTRAN(i2,o,p3)  /\
      PTRAN(i1,i2,o)  /\ NTRAN(p3,i2,o)");;

close_theory();;


%----------------------------------------------------------------------------%
% Some INCREDIBLY INEFFICIENT ML functions for `running' CMOS circuits.      %
% Massive speed ups should be possible by using less brute-force methods.    %
%----------------------------------------------------------------------------%


%----------------------------------------------------------------------------%
%   |- (x=y) = (y=x)    if y is a variable and                               %
%                       either x is not a variable or x is in l              %
%----------------------------------------------------------------------------%

let EQ_FLIP_CONV l t =
 (let x,y = dest_eq t
  in
  if is_var y & (not(is_var x) or mem x l)
   then  SPECL[x;y](INST_TYPE[type_of x, ":*"]EQ_SYM_EQ)
   else fail
 ) ? failwith `EQ_FLIP_CONV`;;

%----------------------------------------------------------------------------%
% extract_vars "t = ?p1 ... pm. (l1=t1)/\ ... /\(ln=tn)"                     %
%   --->                                                                     %
% the list of those li such that ti is not a variable.                       %
%----------------------------------------------------------------------------%

let extract_vars th =
 let (), right = dest_eq(concl th)
 in
 let (),conjs = (I # conjuncts)(strip_exists right)
 in 
 mapfilter(\t. not(is_var(rhs t)) => lhs t | fail)conjs;;

%----------------------------------------------------------------------------%
% remove repeated members from an existentially quantified conjunction       %
% on the right of an equation.                                               %
%----------------------------------------------------------------------------%

let CONJ_SIMP_RULE th =
 let left,right = dest_eq(concl th)
 in
 let vars,body = strip_exists right
 in
 let l = conjuncts body
 in
 let l' = setify l
 in
  if l=l' 
  then th 
  else th TRANS LIST_MK_EXISTS vars (CONJ_SET_CONV l l');;

%----------------------------------------------------------------------------%
% I added the stuff below to convert "T=x" into "x" and "F=x" into "~x" etc  %
% when making the file run in HOL88. I don't know why it was not             %
% needed before.                                                             %
%----------------------------------------------------------------------------%

load_library`taut`;;

let EQTL_OUT = TAUT_RULE "(T = x) = x"
and EQFL_OUT = TAUT_RULE "(F = x) = ~x"
and EQTR_OUT = TAUT_RULE "(x = T) = x"
and EQFR_OUT = TAUT_RULE "(x = F) = ~x";;

let CMOS_UNWIND th =
 CONJ_SIMP_RULE
  (OLD_UNWIND_RULE
   (CONV_RULE
    (bool_CONV THENC
     EQ_CONV   THENC
     COND_CONV THENC 
     DEPTH_CONV(REWRITE_CONV EQTL_OUT) THENC  % Added for HOL88 %
     DEPTH_CONV(REWRITE_CONV EQFL_OUT) THENC  % Added for HOL88 %
     DEPTH_CONV(REWRITE_CONV EQTR_OUT) THENC  % Added for HOL88 %
     DEPTH_CONV(REWRITE_CONV EQFR_OUT) THENC  % Added for HOL88 %
     DEPTH_CONV(EQ_FLIP_CONV(extract_vars th)))
    th));;

letrec iterate f x =
 let x' = f x
 in
 if x=x' then x else iterate f x';;

let CMOS_EXPAND th =
 let th1 = UNFOLD_RULE [NTRAN;PTRAN;PWR;GND] th
 in
 let th2 = iterate CMOS_UNWIND th1
 in
 let th3 = CONV_RULE (DEPTH_CONV(REWRITE_CONV EXISTS_SIMP)) th2
 in
 let th4 = REWRITE_RULE[]th3
 in 
 (PRUNE_RULE th4 ? th4);;

let prove_case xor_spec (i1,i2) =
 CMOS_EXPAND(INST[i1,"i1:val";i2,"i2:val"](SPEC_ALL xor_spec));;

let BAD_HH_THM = prove_case BAD_XOR ("HI","HI");;

let BAD_HL_THM = prove_case BAD_XOR ("HI","LO");;

let BAD_LH_THM = prove_case BAD_XOR ("LO","HI");;

let BAD_LL_THM = prove_case BAD_XOR ("LO","LO");;


let GOOD_HH_THM = prove_case GOOD_XOR ("HI","HI");;

let GOOD_HL_THM = prove_case GOOD_XOR ("HI","LO");;

let GOOD_LH_THM = prove_case GOOD_XOR ("LO","HI");;

let GOOD_LL_THM = prove_case GOOD_XOR ("LO","LO");;
