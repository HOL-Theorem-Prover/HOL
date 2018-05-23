%  MICROCODED COMPUTER PROOF : HOL                                      %
%                                                                       %
%  'microcode.ml'                                                       %
%                                                                       %
%  Description                                                          % 
%                                                                       %
%     This theory is the specification of the microcode resulting in    %
%  32 axioms (one for each word of microcode).  The microcode and the   %
%  assembler are taken from Mike Gordon's technical report.             %
%     Where Gordon's original specification of the microcode only       %
%  used the top 26 words of microcode store, we now specify the         %
%  'unused' part of the store.  This was needed to eliminate the        %
%  possibility of the computer looping forever in the 'unused' part     %
%  of the store upon powering up.                                       %
%     The 'A_ADDR' field of word 1 (ie. 'jump_knob') has been changed   %
%  from 1 to 2 because of a minor change in the decode unit which is    %
%  is described in 'computer_imp.ml'.                                   %
%                                                                       %
%  Author:  Jeff Joyce                                                  %
%  Date:    August 4, 1985                                              %

new_theory `microcode`;;

new_parent `computer_imp`;;

%  Symbolic names for subfields of a microcode instruction              %

let rsw   = [28]
and wmar  = [27]
and write = [26]
and read  = [25]
and wpc   = [24]
and rpc   = [23]
and wacc  = [22]
and racc  = [21]
and wir   = [20]
and rir   = [19]
and warg  = [18]
and add   = [17]
and inc   = [16]
and sub   = [16;17]
and rbuf  = [15]
and ready = [14]
and idle  = [13];;

%
 mk_ADDR [b4;b3;b2;b1;b0] n  gives a list of the positions of bits that
                             are 1 if n is represented in the 5-bit
                             files [b4;b3;b2;b1;b0]
%

let mk_ADDR l n = 
 if n<0 or n>31 or (not(length l= 5))
 then failwith `mk_A_ADDR`
 else
  mapfilter
   (\n. n=0=>fail|n)
   (map2 $* (map(\t. t=`0`=>0|1)(mk_bin_rep(5,n)), l));;

%
 mk_A_ADDR n gives a list of the positions of bits in the A-address
             field which are 1 if n is in that field

 mk_B_ADDR n gives a list of the positions of bits in the B-address
             field which are 1 if n is in that field
%

let mk_A_ADDR = mk_ADDR [12;11;10;9;8]
and mk_B_ADDR = mk_ADDR [7 ;6 ;5 ;4;3];;

%
 test_button(n,m) gives a list of the bits that are 1 if the address of the
                  next microinstruction is "button->n|m"
%

let test_button (n,m) =
 [0]@(mk_A_ADDR m)@(mk_B_ADDR n);;

%
 test_acc(n,m) gives a list of the bits that are 1 if the address of the
               next microinstruction is "acc=0->n|m"
%

let test_acc (n,m) =
 [1]@(mk_A_ADDR m)@(mk_B_ADDR n);;

%
 jump n  gives a list of the bits that are 1 if the address of the
         next microinstruction is "n"
%

let jump = mk_A_ADDR;;

%
 jump_knob n  gives a list of the bits that are 1 if the address of the
              next microinstruction is "knob+2"
%

let jump_knob n =
 [1;0]@(mk_A_ADDR n);;

%
 jump_opcode n  gives a list of the bits that are 1 if the address of the
                next microinstruction is "opcode+10"
%

let jump_opcode n =
 [2]@(mk_A_ADDR n);;

let word30_ty = ":word30";;

%
 mk_micro_ins l  takes a list of numbers representing the positions of bits
                 in a microinstuction that should be 1, and constructs
                 a micro-word (i.e. a value of type ":word30") with the
                 appropriate bits on
%

let mk_micro_ins l =
 mk_const
  (implode
    (`#`.
      map
       (\n. mem n l=>`1`|`0`)
       [29;28;27;26;25;24;23;22;21;20;19;18;17;16;15;14;13;12;11;10;
        9;8;7;6;5;4;3;2;1;0]),
   word30_ty);;

%
 define_microinstruction(addr,cont)  generates an axiom of the form:
                                     |- "FETCH5 MICROCODE (WORD5 ^n) = ^w"
                                     where n is the ROM-address corresponding
                                     to the ML integer addr, and w is a
                                     microinstruction word generated from the
                                     list cont of bits that are on
%

let define_microinstruction (addr,cont) =
 new_axiom
  (concat `MICROCODE` (tok_of_int addr),
   "FETCH5 MICROCODE (WORD5 ^(int_to_term addr)) =  ^(mk_micro_ins cont)");;

%
 The following generates axioms defining the host's microcode MICROCODE
%

map 
 define_microinstruction
  [0 , ready @ idle  @ (test_button(1,0));	% begin idling cycle %
   1 ,                 (jump_knob 2);		% decode knob position %
   2 , rsw   @ wpc   @ (jump 0);		% switches --> PC %
   3 , rsw   @ wacc  @ (jump 0);		% switches --> ACC %
   4 , rpc   @ wmar  @ (jump 7);		% PC --> MAR %
   5 , ready @         (test_button(0,6));	% begin instruction execution %
   6 , rpc   @ wmar  @ (jump 8);		% PC --> MAR %
   7 , racc  @ write @ (jump 0);		% ACC --> MEM (MAR) %
   8 , read  @ wir   @ (jump 9);		% MEM (MAR) --> IR %
   9 ,                 (jump_opcode 10);	% decode instruction %
   10,                 (jump 0);		% HALT %
   11, rir   @ wpc   @ (jump 5);		% JMP, IR --> PC %
   12,                 (test_acc(11,17));	% JZR %
   13, racc  @ warg  @ (jump 19);		% ADD, ACC --> ARG %
   14, racc  @ warg  @ (jump 22);		% SUB, ACC --> ARG %
   15, rir   @ wmar  @ (jump 24);		% LD, IR --> MAR %
   16, rir   @ wmar  @ (jump 25);		% ST, IR --> MAR %
   17, rpc   @ inc   @ (jump 18);		% SKIP, PC + 1 --> BUF %
   18, rbuf  @ wpc   @ (jump 5);		% BUF --> PC %
   19, rir   @ wmar  @ (jump 20);		% IR --> MAR %
   20, read  @ add   @ (jump 21);		% ARG + MEM (MAR) --> BUF %
   21, rbuf  @ wacc  @ (jump 17);		% BUF --> ACC %
   22, rir   @ wmar  @ (jump 23);		% IR --> MAR %
   23, read  @ sub   @ (jump 21);		% ARG - MEM (MAR) --> BUF %
   24, read  @ wacc  @ (jump 17);		% MEM (MAR) --> ACC %
   25, racc  @ write @ (jump 17);		% ACC --> MEM (MAR) %
   26,                 (jump 0);		% unused %
   27,                 (jump 0);		% unused %
   28,                 (jump 0);		% unused %
   29,                 (jump 0);		% unused %
   30,                 (jump 0);		% unused %
   31,                 (jump 0)];;		% unused %

close_theory ();;
