%  MICROCODED COMPUTER PROOF : HOL                                      %
%                                                                       %
%  'computer.ml'                                                        %
%                                                                       %
%  Description                                                          % 
%                                                                       %
%     This theory is the target level specification of the computer.    %
%  The definition of EXECUTE evaluates to the next state of the         %
%  computer which results from the execution of a single target level   %
%  instruction.  COMPUTER is an overall specification of the computer   %
%  including its behaviour when it is idling as well as when it is      %
%  running.  COMPUTER expresses the intended behaviour of the computer  %
%  from a register-transfer point of view.  It is used in the first     %
%  part of the verification procedure.  The final version of the        %
%  correctness statement uses the specification given by COMPUTER_abs.  %
%  COMPUTER_abs expresses the intended behaviour of the computer from   %
%  target level point of view.                                          %
%                                                                       %
%  Author:  Jeff Joyce                                                  %
%  Date:    July 26, 1985                                               %

new_theory `computer`;;

new_parent `values`;;

%  'memory_val', 'pc_val', 'acc_val' are values of signals at           %
%  a single point in time.                                              %
%                                                                       %
%       memory_val  : mem13_16                                          %
%       pc_val      : word13                                            %
%       acc_val     : word16                                            %

new_definition
(
 `EXECUTE`,
  "EXECUTE (memory_val,pc_val,acc_val) =
   let op   = VAL3(OPCODE(FETCH13 memory_val pc_val)) in
   let addr = CUT16_13(FETCH13 memory_val pc_val)     in
   ((op=0) =>
     (memory_val, pc_val, acc_val, T) |
    (op=1) =>
     (memory_val, addr, acc_val, F) |
    (op=2) =>
     ((VAL16 acc_val = 0) =>
      (memory_val, addr, acc_val, F) |
      (memory_val, INC13 pc_val, acc_val, F)) |
    (op=3) =>
     (memory_val, INC13 pc_val, ADD16 acc_val (FETCH13 memory_val addr), F) |
    (op=4) =>
     (memory_val, INC13 pc_val, SUB16 acc_val (FETCH13 memory_val addr), F) |
    (op=5) =>
     (memory_val, INC13 pc_val, FETCH13 memory_val addr, F) |
    (op=6) =>
     (STORE13 addr acc_val memory_val, INC13 pc_val, acc_val, F) |
     (memory_val, INC13 pc_val, acc_val, F))"
);;

%  'memory', 'knob', 'button', 'switches', 'pc', 'acc', and 'idle' are  %
%  signals which map points in time to values.                          %
%                                                                       %
%       memory    : num->mem13_16                                       %
%       knob      : num->word2                                          %
%       button    : num->bool                                           %
%       switches  : num->word16                                         %
%       pc        : num->word13                                         %
%       acc       : num->word16                                         %
%       idle      : num->bool                                           %

new_definition
(
  `COMPUTER`,
  "COMPUTER
    (t1:num,t2:num)
    (memory,knob,button,switches,pc,acc,idle) =
   (memory t2,pc t2,acc t2,idle t2) =
    (idle t1 => 
     (button t1 => 
      ((VAL2(knob t1) = 0) =>
        (memory t1, CUT16_13(switches t1), acc t1, T) |
       (VAL2(knob t1) = 1) =>
        (memory t1, pc t1, switches t1, T) |
       (VAL2(knob t1) = 2) =>
        (STORE13(pc t1)(acc t1)(memory t1), pc t1, acc t1, T) |
        (memory t1, pc t1, acc t1, F)) |
      (memory t1, pc t1, acc t1, T)) |
     (button t1 =>
      (memory t1, pc t1, acc t1, T) |
      EXECUTE(memory t1, pc t1, acc t1)))"
);;

let COMPUTER_abs = new_definition
(
 `COMPUTER_abs`,
  "COMPUTER_abs
    (memory_abs,knob_abs,button_abs,switches_abs,pc_abs,acc_abs,idle_abs) =
   !t:num.
    (memory_abs (t+1),pc_abs (t+1),acc_abs (t+1),idle_abs (t+1)) =
     (idle_abs t => 
      (button_abs t => 
       ((VAL2(knob_abs t) = 0) =>
         (memory_abs t, CUT16_13(switches_abs t), acc_abs t, T) |
        (VAL2(knob_abs t) = 1) =>
         (memory_abs t, pc_abs t, switches_abs t, T) |
        (VAL2(knob_abs t) = 2) =>
         (STORE13(pc_abs t)(acc_abs t)(memory_abs t), pc_abs t, acc_abs t, T) |
         (memory_abs t, pc_abs t, acc_abs t, F)) |
       (memory_abs t, pc_abs t, acc_abs t, T)) |
      (button_abs t =>
       (memory_abs t, pc_abs t, acc_abs t, T) |
       EXECUTE(memory_abs t, pc_abs t, acc_abs t)))"
);;

close_theory ();;
