% This example isn't finished %

%============================================================================%
% The example proof in this file comes from the paper "Traces for Hardware   %
% Verification" by Roger Stokes of ICL.                                      %
%============================================================================%

new_theory `trace_counter`;;

new_prim_rec_definition
 (`COUNTER`,
  "(COUNTER 0 reset out = T) /\
   (COUNTER (SUC m) reset out =
    ((m=0) \/
     ((out(SUC m) = ((reset m=0) => 0 | (out m)+1)) /\
      COUNTER m reset out)))");;

new_prim_rec_definition
 (`INIT`,
  "(INIT 0 reset p1 p2 = T) /\
   (INIT(SUC m) reset p1 p2 =
    (p2(SUC m) = ((reset(SUC m)=1) => 0 | p1(SUC m))) /\
    INIT m reset p1 p2)");;

new_prim_rec_definition
 (`INC`,
  "(INC 0 out p1 = T) /\
   (INC (SUC m) out p1 =
    (p1(SUC m) = out(SUC m)+1) /\
    INC m out p1)");;

new_prim_rec_definition
 (`DEL`,
  "(DEL 0 p2 (out:num->*) = T) /\
   (DEL (SUC m) p2 out =
    (m = 1) \/
    ((out(SUC m) = p2 m) /\
     DEL m p2 out))");;


let COUNTER = theorem `trace_counter` `COUNTER`
and INIT    = theorem `trace_counter` `INIT`
and INC     = theorem `trace_counter` `INC`
and DEL     = theorem `trace_counter` `DEL`;;

prove_thm
 (`Correctness`,
  "!m reset out p1 p2.
    INIT m reset p1 p2 /\
    DEL m p2 out       /\
    INC m out p1
    ==>
    COUNTER m reset out",
   INDUCT_TAC
    THEN REPEAT GEN_TAC
    THEN ASM_REWRITE_TAC[COUNTER;INIT;INC;DEL]);;


prove_thm
 (`Termination`,
  "!m. ?reset out p1 p2.
    INIT m reset p1 p2 /\
    DEL m p2 out       /\
    INC m out p1",
   INDUCT_TAC
    THEN REPEAT GEN_TAC
    THEN ASM_REWRITE_TAC[COUNTER;INIT;INC;DEL]);;
