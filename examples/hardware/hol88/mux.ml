new_theory`mux`;;

new_definition
 (`NAND_SPEC`, "!i1 i2 o. NAND_SPEC(i1,i2,o)  =  o  =  ~(i1  /\  i2)");;

new_definition
 (`INV_SPEC`, "!i o. INV_SPEC(i,o)  =  o  =  ~i");;

new_definition
 (`MUX_SPEC`, "!c i1 i2 o. MUX_SPEC(c,i1,i2,o)  =  o  =  (c => i1 | i2)");;

 new_definition
  (`MUX_IMP`,
   "!c i1 i2 o.
    MUX_IMP(c,i1,i2,o)  =
    ?l1 l2 l3.
     INV_SPEC(c,l1)  /\
     NAND_SPEC(l1,i2,l2)  /\
     NAND_SPEC(c,i1,l3)  /\
     NAND_SPEC(l2,l3,o)");;

close_theory();;

load_theory`mux`;;

let prims = maptok (axiom `mux`) `INV_SPEC NAND_SPEC`;;

let MUX_IMP = axiom `mux` `MUX_IMP`;;

let MUX_THM1 = save_thm(`MUX_THM1`, EXPAND prims MUX_IMP);;
