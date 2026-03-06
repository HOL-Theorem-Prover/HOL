(*---------------------------------------------------------------------------
     This file needs to be processed with Holmake

     Simply typing Holmake in this directory will build the files

       PARITYTheory.{sig,sml,uo,ui}

 ---------------------------------------------------------------------------*)
Theory PARITY


Definition PARITY_def:
      (PARITY 0 f  = T)
   /\ (PARITY (SUC n) f = if f (SUC n) then ~PARITY n f else PARITY n f)
End


Theorem UNIQUENESS_LEMMA:
    !inp out.
      (out 0 = T) /\
      (!t. out (SUC t) = if inp (SUC t) then ~out t else out t)
         ==>
      !t. out t = PARITY t inp
Proof
  REPEAT GEN_TAC THEN STRIP_TAC THEN Induct THENL [
    ASM_REWRITE_TAC [PARITY_def],
    ASM_REWRITE_TAC [PARITY_def]
  ]
QED


Definition ONE_def:   ONE(out:num->bool) = !t. out t = T
End

Definition NOT_def:   NOT(inp, out:num->bool) = !t. out t = ~inp t
End

Definition MUX_def:   MUX(sw,in1,in2,out:num->bool)
                       = !t. out t = if sw t then in1 t else in2 t
End

Definition REG_def:   REG(inp,out:num->bool)
                       = !t. out t = if (t=0) then F else inp(t-1)
End

Definition PARITY_IMP_def:
    PARITY_IMP(inp,out) =
      ?l1 l2 l3 l4 l5.
        NOT(l2,l1)        /\
        MUX(inp,l1,l2,l3) /\
        REG(out,l2)       /\
        ONE l4            /\
        REG(l4,l5)        /\
        MUX(l5,l3,l4,out)
End


val PARITY_LEMMA = prove(
  ``!inp out.
        PARITY_IMP(inp,out)
           ==>
        (out 0 = T) /\
        !t. out(SUC t) = if inp(SUC t) then ~(out t) else out t``,
  PURE_REWRITE_TAC [PARITY_IMP_def, ONE_def, NOT_def, MUX_def, REG_def] THEN
  REPEAT STRIP_TAC THENL [
    PROVE_TAC [],
    PAT_X_ASSUM ``!t. out t = X t``
              (fn th => REWRITE_TAC [SPEC ``SUC t`` th]) THEN
    RW_TAC arith_ss []
  ]);


Theorem PARITY_CORRECT:
      !inp out. PARITY_IMP(inp,out)
                   ==>
                !t. out t = PARITY t inp
Proof
    RW_TAC std_ss []
      THEN MATCH_MP_TAC UNIQUENESS_LEMMA
      THEN PROVE_TAC [PARITY_LEMMA]
QED

