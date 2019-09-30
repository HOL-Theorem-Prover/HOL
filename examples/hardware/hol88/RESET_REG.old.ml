
%----------------------------------------------------------------------------%
% Specification of a register with a reset line.                             %
%----------------------------------------------------------------------------%

new_theory `RESET_REG`;;

let RESET_REG =
 new_definition
  (`RESET_REG`,
   "RESET_REG(reset,in,out) =
     !t. out(t+1) = (reset(t+1) => T | in t)");;

%----------------------------------------------------------------------------%
% Note that the above specification is only partial; it doesn't specify the  %
% output at time 0.                                                          %
%----------------------------------------------------------------------------%

%----------------------------------------------------------------------------%
% An implementation of the restable register using non-resetable registers   %
% that power-up storing F.                                                   %
%                                                                            %
%   reset                  in                                                %
%     |                     |                                                %
%     |       *-----*    *-----*                                             %
%     |       | ONE |    | REG |                                             %
%     |       *-----*    *-----*                                             %
%     |          |          |                                                %
%     |          |l1        |l2                                              %
%     |          |          |                                                %
%   *-------------------------*                                              %
%   |           MUX           |                                              %
%   *-------------------------*                                              %
%                |                                                           %
%               out                                                          %
%                                                                            %
% ONE, MUX and REG are as used in the PARITY example                         %
% (hol/examples/PARITY.ml).                                                  %
%----------------------------------------------------------------------------%

new_parent `PARITY`;;

let RESET_REG_IMP =
 new_definition
  (`RESET_REG_IMP`,
   "RESET_REG_IMP(reset,in,out) =
     ?l1 l2. ONE l1 /\ REG(in,l2) /\ MUX(reset,l1,l2,out)");;

%----------------------------------------------------------------------------%
% We load in the definitions of the primitive parts from the theory PARITY.  %
%----------------------------------------------------------------------------%

let ONE = definition `PARITY` `ONE_DEF`
and REG = definition `PARITY` `REG_DEF`
and MUX = definition `PARITY` `MUX_DEF`;;

%----------------------------------------------------------------------------%
% We verify the correctness of the implementation. Since the sepcification is%
% only partial, we can only prove an implication, not an equivalence.        %
%----------------------------------------------------------------------------%

let RESET_REG_THM =
 prove_thm
  (`RESET_REG_THM`,
   "RESET_REG_IMP(reset,in,out) ==> RESET_REG(reset,in,out)",
   REWRITE_TAC[RESET_REG;RESET_REG_IMP;REG;ONE;MUX]
    THEN REPEAT STRIP_TAC
    THEN ASM_REWRITE_TAC[SUC_SUB1;NOT_SUC;SYM(SPEC_ALL ADD1)]);;
