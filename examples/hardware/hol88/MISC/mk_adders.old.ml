
% Inder's adder slice (ADD_SLICE)


                          |-----|
                          | PWR |
                          |-----|
                             |
                             |p0
                             |
      |---------+------------+----------+------------+-------------|
      |         |            |          |            |             |
     --         --           |       ---+---         --            |
    ||           ||          |      ||     ||         ||           |
p1-0||     b     ||0--cin    |  a--0||     ||0--b     ||0--a       |
    ||     |     ||          |      ||     ||         ||           |
     --    0    --           |       ---+---         --            |
      |  -----  |            |          |            |             |
      |  -----  |            |          |            |             |
    p2|--|   |--|p3          |          |p7          |p8           |
      |         |            |          |            |             |
      |         |            |          |            |             |
     --         --           |          --           --            |
    ||           ||         --           ||           ||          --
a--0||           ||0--p1   ||            ||0--cin     ||0--b     ||
    ||           ||     |-0||            ||           ||      |-0||
     --         --      |  ||           --           --       |  ||
      |         |       |   --          |            |        |   --
    p4|---------+-------|    |--sum   p1|------------+--------|    |--cout
      |         |       |   --          |            |        |   --
     --         --      |  ||          --           --        |  ||
    ||           ||     |--||         ||           ||         |--||
a---||     b     ||---p1   ||   cin---||       b---||            ||
    ||     |     ||         --        ||           ||             --
     --    |    --           |         --           --             |
      |  -----  |            |          |            |             |
      |  -----  |            |          |            |             |
    p5|--|   |--|p6          |          |p9          |p10          |
      |         |            |          |            |             |
      |         |            |          |            |             |
     --         --           |       ---+---         --            |
    ||           ||          |      ||     ||         ||           |
p1--||           ||---cin    |  a---||     ||---b     ||---a       |
    ||           ||          |      ||     ||         ||           |
     --         --           |       ---+---         --            |
      |         |            |          |            |             |
      |---------+------------+----------+------------+-------------|
                             |
                             |p11
                             |
                          |-----|
                          | GND |
                          |-----|

%

timer true;;

new_theory`adders`;;


new_definition
 (`PWR`,
  "PWR(o:bool) = (o=T)");;

new_definition
 (`GND`,
  "GND(o:bool) = (o=F)");;

new_definition
 (`PTRAN`,
  "PTRAN(g,s:bool,d:bool) = ((g=F) ==> (s=d))");;

new_definition
 (`NTRAN`,
  "NTRAN(g,s:bool,d:bool) = ((g=T) ==> (s=d))");;

new_definition
 (`ADD1_IMP`,
  "ADD1_IMP(a,b,cin,sum,cout) =
    ?p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11.
     PTRAN(p1,p0,p2)  /\ PTRAN(cin,p0,p3)                       /\
     PTRAN(b,p2,p3)   /\ PTRAN(a,p2,p4)    /\ PTRAN(p1,p3,p4)   /\
     NTRAN(a,p4,p5)   /\ NTRAN(p1,p4,p6)                        /\
     NTRAN(b,p5,p6)   /\ NTRAN(p1,p5,p11)  /\ NTRAN(cin,p6,p11) /\
     PTRAN(a,p0,p7)   /\ PTRAN(b,p0,p7)                         /\
     PTRAN(a,p0,p8)   /\ PTRAN(cin,p7,p1)  /\ PTRAN(b,p8,p1)    /\
     NTRAN(cin,p1,p9) /\ NTRAN(b,p1,p10)                        /\
     NTRAN(a,p9,p11)  /\ NTRAN(b,p9,p11)   /\ NTRAN(a,p10,p11)  /\
     PWR(p0)          /\ PTRAN(p4,p0,sum)  /\ NTRAN(p4,sum,p11) /\
     GND(p11)         /\ PTRAN(p1,p0,cout) /\ NTRAN(p1,cout,p11)");;


let PTRAN    = definition `adders` `PTRAN`
and NTRAN    = definition `adders` `NTRAN`
and PWR      = definition `adders` `PWR`
and GND      = definition `adders` `GND`
and ADD1_IMP = definition `adders` `ADD1_IMP`;;

% |- (x=y) = (y=x)    if y is a variable and 
                      either x is not a variable or x is in l %

let EQ_FLIP_CONV l t =
 (let x,y = dest_eq t
  in
  if is_var y & (not(is_var x) or mem x l)
   then  SPECL[x;y](INST_TYPE[type_of x, ":*"]EQ_SYM_EQ)
   else fail
 ) ? failwith `EQ_FLIP_CONV`;;

% extract_vars "t = ?p1 ... pm. (l1=t1)/\ ... /\(ln=tn)" 
  --->
  the list of those li such that ti is not a variable %

let extract_vars th =
 let (), right = dest_eq(concl th)
 in
 let (),conjs = (I # conjuncts)(strip_exists right)
 in 
 mapfilter(\t. not(is_var(rhs t)) => lhs t | fail)conjs;;

% remove repeated members from an existentially quantified conjunction
  on the right of an equation %

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

let CMOS_UNWIND th =
 CONJ_SIMP_RULE
  (UNWIND_RULE
   (CONV_RULE
    (bool_CONV THENC
     EQ_CONV   THENC
     COND_CONV THENC 
     (DEPTH_CONV (EQ_FLIP_CONV(extract_vars th))))
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
 (PRUNE_RULE th3 ? th3);;

let prove_case1(a,b,cin) =
 CMOS_EXPAND(INST[a,"a:bool";b,"b:bool";cin,"cin:bool"]ADD1_IMP);;

let TTT_Thm1 = save_thm(`TTT_Thm1`, prove_case1("T","T","T"));;

let TTF_Thm1 = save_thm(`TTF_Thm1`, prove_case1("T","T","F"));;

let TFT_Thm1 = save_thm(`TFT_Thm1`, prove_case1("T","F","T"));;

let TFF_Thm1 = save_thm(`TFF_Thm1`, prove_case1("T","F","F"));;

let FTT_Thm1 = save_thm(`FTT_Thm1`, prove_case1("F","T","T"));;

let FTF_Thm1 = save_thm(`FTF_Thm1`, prove_case1("F","T","F"));;

let FFT_Thm1 = save_thm(`FFT_Thm1`, prove_case1("F","F","T"));;

let FFF_Thm1 = save_thm(`FFF_Thm1`, prove_case1("F","F","F"));;


% Full adder from page 92 "Introduction to MOS LSI Design" by
  Mavor, Jack and Denyer. This circuit (with some bits missing) also
  occurrs in "Let's Design CMOS Circuits! (Part 1)" by M. Annaratone,
  CMU-CS-84-101 %

new_definition
 (`ADD2_IMP`,
  "ADD2_IMP(a,b,cin,sum,cout) =
    ?p0 p1 p2 p3 p4 p5.
     PWR(p0) /\ GND(p5) /\
     PTRAN(cin,p0,p1) /\ NTRAN(cin,p1,p5) /\ PTRAN(p3,p1,sum) /\
     NTRAN(p2,p1,sum) /\ PTRAN(p2,cin,sum) /\ NTRAN(p3,cin,sum) /\
     PTRAN(p3,cin,cout) /\ NTRAN(p2,cin,cout) /\ PTRAN(p2,a,cout) /\
     NTRAN(p3,a,cout) /\ PTRAN(a,p2,b) /\ NTRAN(p4,p2,b) /\
     PTRAN(p4,p3,b) /\ NTRAN(a,p3,b) /\ PTRAN(b,a,p2) /\ NTRAN(b,p2,p4) /\
     PTRAN(b,p4,p3) /\ NTRAN(b,p3,a) /\ PTRAN(a,p0,p4) /\ NTRAN(a,p4,p5)");;


let ADD2_IMP = definition `adders` `ADD2_IMP`;;

let prove_case2(a,b,cin) =
 CMOS_EXPAND(INST[a,"a:bool";b,"b:bool";cin,"cin:bool"]ADD2_IMP);;

let TTT_Thm2 = save_thm(`TTT_Thm2`, prove_case2("T","T","T"));;

let TTF_Thm2 = save_thm(`TTF_Thm2`, prove_case2("T","T","F"));;

let TFT_Thm2 = save_thm(`TFT_Thm2`, prove_case2("T","F","T"));;

let TFF_Thm2 = save_thm(`TFF_Thm2`, prove_case2("T","F","F"));;

let FTT_Thm2 = save_thm(`FTT_Thm2`, prove_case2("F","T","T"));;

let FTF_Thm2 = save_thm(`FTF_Thm2`, prove_case2("F","T","F"));;

let FFT_Thm2 = save_thm(`FFT_Thm2`, prove_case2("F","F","T"));;

let FFF_Thm2 = save_thm(`FFF_Thm2`, prove_case2("F","F","F"));;

close_theory();;


