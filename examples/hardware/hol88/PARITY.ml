%----------------------------------------------------------------------------%
% The parity checker example from the paper "HOL: A Proof Generating         %
% System for Higher-Order Logic" (which can be found on hol/doc/HOLSYS.tex). %
%                                                                            %
% For a more complicated parity checker see RESET_PARITY.ml.                 %
%----------------------------------------------------------------------------%

new_theory `PARITY`;;

let PARITY_DEF =
 new_prim_rec_definition
  (`PARITY_DEF`,
   "(PARITY 0 f = T) /\
    (PARITY(SUC n)f = (f(SUC n) => ~(PARITY n f) | PARITY n f))");;

let UNIQUENESS_LEMMA =
 prove_thm
  (`UNIQUENESS_LEMMA`,
   "!in out. 
     (out 0 = T) /\ (!t. out(SUC t) = (in(SUC t) => ~(out t) | out t))
     ==>
     (!t. out t = PARITY t in)",
   REPEAT GEN_TAC
    THEN STRIP_TAC
    THEN INDUCT_TAC
    THEN ASM_REWRITE_TAC[PARITY_DEF]);;

let ONE_DEF =
 new_definition
  (`ONE_DEF`, "ONE(out:num->bool) = !t. out t = T");;

let NOT_DEF =
 new_definition
  (`NOT_DEF`, "NOT(in,out:num->bool) = !t. out t = ~(in t)");;

let MUX_DEF =
 new_definition
  (`MUX_DEF`, 
   "MUX(sw,in1,in2,out:num->bool) = !t. out t = (sw t => in1 t | in2 t)");;

let REG_DEF =
 new_definition
  (`REG_DEF`, "REG(in,out:num->bool) = !t. out t = ((t=0) => F | in(t-1))");;

let PARITY_IMP_DEF =
 new_definition
  (`PARITY_IMP_DEF`,
   "PARITY_IMP(in,out) =
    ?l1 l2 l3 l4 l5. NOT(l2,l1)       /\
                     MUX(in,l1,l2,l3) /\
                     REG(out,l2)      /\
                     ONE l4           /\
                     REG(l4,l5)       /\
                     MUX(l5,l3,l4,out)");;

let lines tok t =
 (let x = (fst o dest_var o rator o lhs o snd o dest_forall) t
  in
  mem x (words tok)) ? false;;

let PARITY_LEMMA =
 prove_thm
  (`PARITY_LEMMA`,
   "!in out. 
     PARITY_IMP(in,out) ==> 
      (out 0 = T) /\ !t. out(SUC t) = (in(SUC t) => ~(out t) | out t)",
   PURE_REWRITE_TAC[PARITY_IMP_DEF;ONE_DEF;NOT_DEF;MUX_DEF;REG_DEF]
    THEN REPEAT STRIP_TAC
    THENL
     [FILTER_ASM_REWRITE_TAC(lines`out l4 l5`)[];ALL_TAC]
    THEN FIRST_ASSUM
          (\th. if lines`out`(concl th) 
                 then SUBST_TAC[SPEC "SUC t" th]
                 else NO_TAC)
    THEN FILTER_ASM_REWRITE_TAC(lines`l1 l3 l4 l5`)[]
    THEN FILTER_ASM_REWRITE_TAC(lines`l2`)[]
    THEN REWRITE_TAC[NOT_SUC;SUC_SUB1]);;

let PARITY_CORRECT =
 prove_thm
  (`PARITY_CORRECT`,
   "!in out. PARITY_IMP(in,out) ==> (!t. out t = PARITY t in)",
   REPEAT GEN_TAC
    THEN DISCH_TAC
    THEN IMP_RES_TAC PARITY_LEMMA
    THEN IMP_RES_TAC UNIQUENESS_LEMMA);;

