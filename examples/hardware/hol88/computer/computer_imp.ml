%  MICROCODED COMPUTER PROOF : HOL                                      %
%                                                                       %
%  'computer_imp.ml'                                                    %
%                                                                       %
%  Description                                                          % 
%                                                                       %
%     This theory is the specification of the register-transfer level   %
%  implementation of the computer.  This specification is the HOL       %
%  equivalent to the specification in Mike Gordon's technical report    %
%  with a minor modification in the decode unit (see the definition     %
%  of DECODE).                                                          %
%                                                                       %
%  Author:  Jeff Joyce                                                  %
%  Date:    August 4, 1985                                              %

new_theory `computer_imp`;;

new_parent `values`;;

%  Define macros for the types ":num->word13", ":num->word16",          %
%  ":num->bool" and ":num->tri_word16".                                 %

let sig13 = ":num->word13";;
let sig16 = ":num->word16";;
let sigbool = ":num->bool";;
let sigtri16 = ":num->tri_word16";;

let REG16 = new_definition
(
 `REG16`, 
 "REG16 (input:^sig16,load:^sigbool,output:^sig16) =
   !t:num. output(t+1) = ((load t) => input t | output t)"
);;

let REG13 = new_definition
(
 `REG13`, 
 "REG13 (input:^sig16,load:^sigbool,output:^sig13) =
   !t:num. output(t+1) = (load t => CUT16_13(input t) | output t)"
);;

let IR = new_definition (`IR`,"IR = REG16");;
let PC = new_definition (`PC`,"PC = REG13");;
let ACC = new_definition (`ACC`,"ACC = REG16");;
let ARG = new_definition (`ARG`,"ARG = REG16");;
let MAR = new_definition (`MAR`,"MAR = REG13");;

let BUF = new_definition
(
 `BUF`, 
 "BUF (input:^sig16,output:^sig16) = !t:num. output(t+1) = input t"
);;

let GATE16 = new_definition
(
 `GATE16`,
 "GATE16 (input:^sig16,control:^sigbool,output:^sigtri16) =
   !t:num. output t = (control t => MK_TRI16(input t) | FLOAT16)"
);;

let GATE13 = new_definition
(
 `GATE13`,
 "GATE13 (input:^sig13,control:^sigbool,output:^sigtri16) =
   !t:num. output t = (control t => MK_TRI16(PAD13_16 (input t)) | FLOAT16)"
);;

let G0 = new_definition (`G0`,"G0 = GATE16");;
let G1 = new_definition (`G1`,"G1 = GATE13");;
let G2 = new_definition (`G2`,"G2 = GATE16");;
let G3 = new_definition (`G3`,"G3 = GATE16");;
let G4 = new_definition (`G4`,"G4 = GATE16");;

let MEM = new_definition
(
 `MEM`,
 "MEM
   (memory:num->mem13_16,
    mar:^sig13,bus:^sig16,memcntl:num->word2,memout:^sigtri16) =
  !t:num.
   (memout t = 
    ((VAL2(memcntl t) = 1) =>
      MK_TRI16(FETCH13(memory t)(mar t)) | FLOAT16)) /\
   (memory(t+1) = 
    ((VAL2(memcntl t) = 2) =>
      STORE13(mar t)(bus t)(memory t) | memory t))"
);;
  
let ALU = new_definition
(
 `ALU`,
 "ALU
   (arg:^sig16,bus:^sig16,alucntl:num->word2,alu:^sig16) =
  !t:num.
   (alu t =
    ((VAL2(alucntl t) = 0) => bus t |
     (VAL2(alucntl t) = 1) => INC16(bus t) |
     (VAL2(alucntl t) = 2) => ADD16(arg t)(bus t) | SUB16(arg t)(bus t)))"
);;

let BUS = new_definition
(
 `BUS`,
 "BUS
   (memout:^sigtri16,g0:^sigtri16,g1:^sigtri16,
    g2:^sigtri16,g3:^sigtri16,g4:^sigtri16,bus:^sig16) =
  !t:num.
   bus t =
    DEST_TRI16 (memout t U16 g0 t U16 g1 t U16 g2 t U16 g3 t U16 g4 t)"
);;

let DATA = new_definition
(
 `DATA`,
 "DATA
   (memory,mar,pc,acc,ir,arg,buf,switches,rsw,wmar,memcntl,
    wpc,rpc,wacc,racc,wir,rir,warg,alucntl,rbuf) =
  ?g0 g1 g2 g3 g4 memout alu bus.
   MEM(memory,mar,bus,memcntl,memout) /\
   MAR(bus,wmar,mar) /\
   PC(bus,wpc,pc) /\
   ACC(bus,wacc,acc) /\
   IR(bus,wir,ir) /\
   ARG(bus,warg,arg) /\
   BUF(alu,buf) /\
   G0(switches,rsw,g0) /\
   G1(pc,rpc,g1) /\ 
   G2(acc,racc,g2) /\ 
   G3(ir,rir,g3) /\ 
   G4(buf,rbuf,g4) /\
   ALU(arg,bus,alucntl,alu) /\
   BUS(memout,g0,g1,g2,g3,g4,bus)"
);;

let ROM = new_definition
(
 `ROM`,
 "ROM (microcode:mem5_30) (mpc,rom) = !t:num. rom t = FETCH5 microcode (mpc t)"
);;

let MPC = new_definition
(
 `MPC`,
 "MPC(nextaddress,mpc:num->word5) = !t:num. mpc(t+1) = nextaddress t"
);;

let CNTL_BIT = new_definition
(
 `CNTL_BIT`,"CNTL_BIT n w = EL n (BITS30 w)"
);;

let CNTL_FIELD = new_definition
(
 `CNTL_FIELD`,"CNTL_FIELD (m,n) w = WORD2(V(SEG(m,n)(BITS30 w)))"
);;

let B_ADDR = new_definition
(
 `B_ADDR`,"B_ADDR w = WORD5(V(SEG(3,7)(BITS30 w)))"
);;

let A_ADDR = new_definition
(
 `A_ADDR`,"A_ADDR w = WORD5(V(SEG(8,12)(BITS30 w)))"
);;

let TEST = new_definition
(
 `TEST`,"TEST w = V(SEG(0,2)(BITS30 w))"
);;

%  Modification                                                         %
%                                                                       %
%  The decode unit has been modified slightly from the specification    %
%  in Mike Gordon's technical report.  The decode unit does not add 1   %
%  to the 'A_ADDR' to obtain the next microinstruction address when the %
%  test field is 3 (ie. 'jump_knob').  This results in a change in the  %
%  microcode such that the 'A_ADDR' field of word 1 is 2 instead of 1.  %

let DECODE = new_definition
(
 `DECODE`,
 "DECODE
   (rom,knob,button,acc,ir,nextaddress,rsw,wmar,memcntl,
    wpc,rpc,wacc,racc,wir,rir,warg,alucntl,rbuf,ready,idle) =
  !t:num.
   (nextaddress t =
    (((TEST(rom t) = 1) /\ (button t)) => B_ADDR(rom t) |
     ((TEST(rom t) = 2) /\ (VAL16(acc t) = 0)) => B_ADDR(rom t) |
     (TEST(rom t) = 3) => WORD5(VAL2(knob t) + VAL5(A_ADDR(rom t))) |
     (TEST(rom t) = 4) => WORD5(VAL3(OPCODE(ir t)) + VAL5(A_ADDR(rom t))) |
     A_ADDR(rom t))) /\
   (rsw t = CNTL_BIT 28 (rom t)) /\
   (wmar t = CNTL_BIT 27 (rom t)) /\
   (memcntl t = CNTL_FIELD (25,26) (rom t)) /\
   (wpc t = CNTL_BIT 24 (rom t)) /\
   (rpc t = CNTL_BIT 23 (rom t)) /\
   (wacc t = CNTL_BIT 22 (rom t)) /\
   (racc t = CNTL_BIT 21 (rom t)) /\
   (wir t = CNTL_BIT 20 (rom t)) /\
   (rir t = CNTL_BIT 19 (rom t)) /\
   (warg t = CNTL_BIT 18 (rom t)) /\
   (alucntl t = CNTL_FIELD (16,17) (rom t)) /\
   (rbuf t = CNTL_BIT 15 (rom t)) /\
   (ready t = CNTL_BIT 14 (rom t)) /\
   (idle t = CNTL_BIT 13 (rom t))"
);;

new_constant(`MICROCODE`,":mem5_30");;

let CONTROL = new_definition
(
 `CONTROL`,
 "CONTROL
   microcode
   (mpc,knob,button,acc,ir,rsw,wmar,memcntl,
    wpc,rpc,wacc,racc,wir,rir,warg,alucntl,rbuf,ready,idle) = 
  ?rom nextaddress.
   ROM microcode (mpc,rom) /\  
   MPC(nextaddress,mpc) /\
   DECODE
    (rom,knob,button,acc,ir,nextaddress,rsw,wmar,memcntl,
     wpc,rpc,wacc,racc,wir,rir,warg,alucntl,rbuf,ready,idle)"
);;

let COMPUTER_IMP = new_definition
(
 `COMPUTER_IMP`,
 "COMPUTER_IMP
   (mpc,mar,ir,arg,buf)
   (memory,knob,button,switches,pc,acc,idle,ready) = 
  ?rsw wmar memcntl wpc rpc wacc racc wir rir warg alucntl rbuf.
   CONTROL
    MICROCODE
    (mpc,knob,button,acc,ir,rsw,wmar,memcntl,
     wpc,rpc,wacc,racc,wir,rir,warg,alucntl,rbuf,ready,idle) /\
   DATA
    (memory,mar,pc,acc,ir,arg,buf,switches,rsw,wmar,memcntl,
     wpc,rpc,wacc,racc,wir,rir,warg,alucntl,rbuf)"
);;

let CONTROL_prims = [ROM;MPC;DECODE];;

let CONTROL_EXP = EXPANDF CONTROL_prims CONTROL;;

let DATA_prims =
 [MEM;ALU;BUS;BUF] @
 [
  SUBS [SYM PC] REG13;
  SUBS [SYM IR] REG16;
  SUBS [SYM MAR] REG13;
  SUBS [SYM ACC] REG16;
  SUBS [SYM ARG] REG16;
  SUBS [SYM G0] GATE16;
  SUBS [SYM G1] GATE13;
  SUBS [SYM G2] GATE16;
  SUBS [SYM G3] GATE16;
  SUBS [SYM G4] GATE16];;

let DATA_EXP = EXPANDF DATA_prims DATA;;

let COMPUTER_IMP_EXP = EXPANDF [CONTROL_EXP;DATA_EXP] COMPUTER_IMP;;

let COMPUTER_IMP_EXP_ASM = 
 PURE_REWRITE_RULE [TEST;A_ADDR;B_ADDR;CNTL_BIT;CNTL_FIELD]
  (SUBS [COMPUTER_IMP_EXP]
   (ASSUME
    "COMPUTER_IMP
      (mpc,mar,ir,arg,buf)
      (memory,knob,button,switches,pc,acc,idle,ready)"));;

save_thm (`COMPUTER_IMP_EXP_ASM`,COMPUTER_IMP_EXP_ASM);;

close_theory ();;
