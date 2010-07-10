(*---------------------------------------------------------------------------
     This file needs to be processed with hol:
       hol < PARITY.sml
 ---------------------------------------------------------------------------*)

load "bossLib"; open bossLib;


val PARITY_def =
 Define
     `(PARITY 0 f  = T)
   /\ (PARITY (SUC n) f = if f (SUC n) then ~PARITY n f else PARITY n f)`;


val UNIQUENESS_LEMMA = prove(
  ``!inp out.
      (out 0 = T) /\
      (!t. out (SUC t) = if inp (SUC t) then ~out t else out t)
         ==>
      !t. out t = PARITY t inp``,
  REPEAT GEN_TAC THEN STRIP_TAC THEN Induct THENL [
    ASM_REWRITE_TAC [PARITY_def],
    ASM_REWRITE_TAC [PARITY_def]
  ]);


val ONE_def = Define `ONE(out:num->bool) = !t. out t = T`;

val NOT_def = Define `NOT(inp, out:num->bool) = !t. out t = ~inp t`;

val MUX_def = Define `MUX(sw,in1,in2,out:num->bool)
                       = !t. out t = if sw t then in1 t else in2 t`;

val REG_def = Define `REG(inp,out:num->bool)
                       = !t. out t = if (t=0) then F else inp(t-1)`;

val PARITY_IMP_def = Define
   `PARITY_IMP(inp,out) =
      ?l1 l2 l3 l4 l5.
        NOT(l2,l1)        /\
        MUX(inp,l1,l2,l3) /\
        REG(out,l2)       /\
        ONE l4            /\
        REG(l4,l5)        /\
        MUX(l5,l3,l4,out)`;


val PARITY_LEMMA = prove(
  ``!inp out.
        PARITY_IMP(inp,out)
           ==>
        (out 0 = T) /\
        !t. out(SUC t) = if inp(SUC t) then ~(out t) else out t``,
  PURE_REWRITE_TAC [PARITY_IMP_def, ONE_def, NOT_def, MUX_def, REG_def] THEN
  REPEAT STRIP_TAC THENL [
    PROVE_TAC [],
    PAT_ASSUM ``!t. out t = X t``
              (fn th => REWRITE_TAC [SPEC ``SUC t`` th]) THEN
    RW_TAC arith_ss []
  ]);


val PARITY_CORRECT = prove(
    ``!inp out. PARITY_IMP(inp,out)
                   ==>
                !t. out t = PARITY t inp``,
    RW_TAC std_ss []
      THEN MATCH_MP_TAC UNIQUENESS_LEMMA
      THEN PROVE_TAC [PARITY_LEMMA]);
