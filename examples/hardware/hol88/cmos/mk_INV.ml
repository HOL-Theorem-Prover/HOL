% Verification of the inverter used in the NORA dynamic adder 

                           |---|
                           |PWR|
                           |---|
                             |p0
                            --
                           ||
               |----------0||
               |           ||
               |            --
               |             |p1
               |            --
               |           ||
               |   ph_bar--||
               |           ||
               |            --
               |             |p2
               |           |---|
           i---|           | J |---o
               |           |---|
               |             |p3
               |            --
               |           ||
               |   ph------||
               |           ||
               |            --
               |             |p4
               |            --
               |           ||
               |-----------||
                           ||
                            --
                             |p5
                           |---|
                           |GND|
                           |---|
%

new_theory`INV`;;

new_parent`cmos`;;

let tri  = ":tri_word1"
and time = ":num";;

let sig  = ":^time -> ^tri";;

let PWR = definition `cmos` `PWR`
and GND = definition `cmos` `GND`
and J   = definition `cmos` `J`;;

let NTRAN = theorem `cmos` `NTRAN_THM`
and PTRAN = theorem `cmos` `PTRAN_THM`;;

let INV =
 new_definition
  (`INV`,
   "INV(i,o,ph,ph_bar) =
     ?p0 p1 p2 p3 p4 p5.
      PWR p0 /\ GND p5 /\
      PTRAN(i,p0,p1) /\ NTRAN(i,p5,p4) /\
      PTRAN(ph_bar,p1,p2) /\ NTRAN(ph,p4,p3) /\
      J(p2,p3,o)");;

let INV_THM =
 prove_thm
  (`INV_THM`,
   "!i o ph ph_bar.
     INV(i,o,ph,ph_bar) ==>
      (((ph t = HI) /\ (ph_bar t = LO)) ==>
       (((i t = HI) \/ ((i t = FLOAT1) /\ (i(t-1) = HI)) ==> (o t = LO)) /\
        ((i t = LO) \/ ((i t = FLOAT1) /\ (i(t-1) = LO)) ==> (o t = HI))))
      /\ 
      ((ph t = LO) /\ (ph_bar t = HI) ==> (o t = FLOAT1))",
   REPEAT GEN_TAC
    THEN REWRITE_TAC[INV;PWR;GND;J]
    THEN REPEAT STRIP_TAC
    THEN IMP_RES_TAC PTRAN
    THEN IMP_RES_TAC NTRAN
    THEN RES_TAC
    THEN ASM_REWRITE_TAC[]
    THEN CONV_TAC U_CONV
    THEN ASM_REWRITE_TAC[]);; 

close_theory();;
