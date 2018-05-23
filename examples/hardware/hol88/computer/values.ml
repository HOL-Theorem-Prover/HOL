%  MICROCODED COMPUTER PROOF : HOL                                      %
%                                                                       %
%  'values.ml'                                                          %
%                                                                       %
%  Description                                                          % 
%                                                                       %
%     This theory defines word widths, dimensions of memories, some     %
%  constants, definitions, and axioms common to both the host level     %
%  and target level specifications.                                     %
%                                                                       %
%  Author:  Jeff Joyce                                                  %
%  Date:    August 4, 1985                                              %

new_theory `values`;;

% Word Widths                                                           %
%                  2 - MEM and ALU control lines                        %
%                  3 - microcode test field, opcode                     %
%                  5 - microcode addresses                              %
%                 13 - main memory addresses                            %
%                 16 - main memory words and data paths                 %
%                 30 - microinstruction words                           %

declare_word_widths [2;3;5;13;16;30];;

% Memories                                                              %
%          5-bit address space, width 30 - microinstruction (ROM)       %
%         13-bit address space, width 16 - main memory (RAM)            %

declare_memories [(5,30);(13,16)];;

% Constants for various operations                                      %

new_constant (`INC16`   ,":word16 -> word16");;
new_constant (`ADD16`   ,":word16 -> word16 -> word16");;
new_constant (`SUB16`   ,":word16 -> word16 -> word16");;
new_constant (`PAD13_16`,":word13 -> word16");;
new_constant (`CUT16_13`,":word16 -> word13");;
new_constant (`ISZERO16`,":word16 -> bool");;
new_constant (`INC13`   ,":word13 -> word13");;
new_constant (`OPCODE`  ,":word16 -> word3");;

% Word axioms that should eventually appear in a theory about words     %

new_axiom
(
 `CUT_PAD`,
  "!w:word13. CUT16_13(PAD13_16 w) = w"
);;

new_axiom
(
 `CUT_INC_PAD`,
  "!w:word13. CUT16_13(INC16(PAD13_16 w)) = INC13 w"
);;

new_axiom
(
 `word2_CASES`,
  "!w:word2.
   (w = #00) \/ (w = #01) \/ (w = #10) \/ (w = #11)"
);;

new_axiom
(
 `word3_CASES`,
  "!w:word3.
   (w = #000) \/ (w = #001) \/ (w = #010) \/ (w = #011) \/
   (w = #100) \/ (w = #101) \/ (w = #110) \/ (w = #111)"
);;

new_axiom
(
 `word5_CASES`,
  "!w:word5.
  (w = #00000) \/ (w = #00001) \/ (w = #00010) \/ (w = #00011) \/
  (w = #00100) \/ (w = #00101) \/ (w = #00110) \/ (w = #00111) \/
  (w = #01000) \/ (w = #01001) \/ (w = #01010) \/ (w = #01011) \/
  (w = #01100) \/ (w = #01101) \/ (w = #01110) \/ (w = #01111) \/
  (w = #10000) \/ (w = #10001) \/ (w = #10010) \/ (w = #10011) \/
  (w = #10100) \/ (w = #10101) \/ (w = #10110) \/ (w = #10111) \/
  (w = #11000) \/ (w = #11001) \/ (w = #11010) \/ (w = #11011) \/
  (w = #11100) \/ (w = #11101) \/ (w = #11110) \/ (w = #11111)"
);;

% Often it is more convenient for the above word cases axioms to be     %
% stated in terms of possible number values instead of possible bit     %
% strings.  The following rules derive 'VAL' versions of the above      %
% axioms which are then saved as theorems.                              %

letrec prove_word_CASES n val_op tm =
 if n = 1 then (VAL_RULE (AP_TERM val_op (ASSUME tm)))
 else
  let th1 = (VAL_RULE (AP_TERM val_op (ASSUME (fst (dest_disj tm))))) in
  let th2 = (prove_word_CASES (n - 1) val_op (snd (dest_disj tm))) in
  let th3 = DISJ1 th1 (concl th2) in
  let th4 = DISJ2 (concl th1) th2 in
  DISJ_CASES (ASSUME tm) th3 th4;;

let convert_word_CASES n val_op thm =
  let var,body = dest_forall (concl thm) in
  (GEN var (MP (DISCH_ALL (prove_word_CASES n val_op body)) (SPEC var thm)));;

save_thm
(
 `VAL_word2_CASES`,
 (convert_word_CASES 4 "VAL2" (axiom `values` `word2_CASES`))
);;

save_thm
(
 `VAL_word3_CASES`,
 (convert_word_CASES 8 "VAL3" (axiom `values` `word3_CASES`))
);;

save_thm
(
 `VAL_word5_CASES`,
 (convert_word_CASES 32 "VAL5" (axiom `values` `word5_CASES`))
);;


% Define what is it is for a signal to be stable from times t1 to t2    %

new_definition
(
 `STABLE`,
  "STABLE (t1,t2) sig =
   !t. ((t1 < t) /\ (t < t2)) ==> (((sig t):*) = ((sig t1):*))"
);;

close_theory ();;
