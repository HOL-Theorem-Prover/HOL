% The Counter Example using "temporal" operators %

new_theory `COUNT`;;

let time = ":num"
and val  = ":num";;

let sig = ":^time -> ^val";;

new_definition
 (`DEL`, "DEL(x:^sig,x':^sig) = !t. x t = x'(t-1)");;

new_definition(`INC`, "(INC:^sig->^sig) x = \t. (x t)+1");;

new_definition
 (`COUNT_SPEC`,
  "COUNT_SPEC (sw,i,o) = DEL(o,(sw -> i | INC o))");;

% The primitives: MUX, REG and INCR %

new_definition
 (`MUX`,
  "MUX(switch,i1:^sig,i2:^sig,o:^sig) = (o = (switch -> i1 | i2))");;

new_definition
 (`REG`,
  "REG (i:^sig,o:^sig) = DEL(o,i)");;

new_definition
 (`INCR`,
  "INCR(i:^sig,o:^sig) = (o = INC i)");;

new_definition
 (`COUNT_IMP`,
  "COUNT_IMP (sw,i,o) = ?l1 l2. 
                         MUX (sw,i,l2,l1) /\
                         REG (l1,o)       /\
                         INCR (o,l2)");;

let COUNT_SPEC = definition `COUNT` `COUNT_SPEC`
and COUNT_IMP  = definition `COUNT` `COUNT_IMP`;;

let MUX  = definition `COUNT` `MUX`
and REG  = definition `COUNT` `REG`
and INCR = definition `COUNT` `INCR`;;


let prims = [MUX;REG;INCR];;

let th1 = UNFOLD_RULE prims COUNT_IMP;;

let th2 = OLD_UNWIND_RULE th1;;

let th3 = PRUNE_RULE th2;;

let EXPAND thl th =
 let th1 = UNFOLD_RULE thl th
 in
 let th2 = OLD_UNWIND_RULE th1
 in
 PRUNE_RULE th2;;

let COUNT_CORRECTNESS =
 prove_thm
  (`COUNT_CORRECTNESS`,
   "COUNT_SPEC(sw,i,o) = COUNT_IMP(sw,i,o)",
   REWRITE_TAC[COUNT_SPEC;EXPAND prims COUNT_IMP]);;
