%  MICROCODED COMPUTER PROOF : HOL                                      %
%                                                                       %
%  'next.ml'                                                            %
%                                                                       %
%  Description                                                          % 
%                                                                       %
%     This theory defines the 'NEXT' relation which relates a time      %
%  't2' to a earlier time 't1' as the next time the signal 'sig' is     %
%  is true after t1.                                                    %
%     The definition of NEXT and NEXT_INC_INTERVAL_LEMMA are taken      %
%  from Tom Melham's FACTORIAL example (slightly modified).             %
%                                                                       %
%  Author:  Jeff Joyce                                                  %
%  Date:    August 4, 1985                                              %

new_theory `next`;;

let NEXT = new_definition
(
 `NEXT`, 
  "NEXT (t1,t2) sig =
   (t1 < t2) /\ (sig t2)  /\ (!t. (t1 < t) /\ (t < t2) ==> ~sig t)"
);;

% Some preliminary lemmas %

let A_AND_NOT_A_LEMMA =
 TAC_PROOF
 (
  ([],"!t:bool. (t /\ ~t) = F"),
  GEN_TAC THEN (ASM_CASES_TAC "t:bool") THEN (ASM_REWRITE_TAC [])
 );;

let NOT_EQ_LEMMA =
 let lemma =
 (
  MP
   (SPEC_ALL LESS_CASES_IMP)
   (LIST_CONJ [(ASSUME "~(m < n)");(ASSUME "~(m = n)")])
 ) in
 TAC_PROOF
 (
  ([],"!m:num. !n:num. ~(m = n) ==> ((m < n) \/ (n < m))"),
  (REPEAT GEN_TAC) THEN
  (ASM_CASES_TAC "(m < n):bool") THENL
  [
   (STRIP_TAC THEN DISJ1_TAC THEN (ASM_REWRITE_TAC []));
   (STRIP_TAC THEN DISJ2_TAC THEN (ASM_REWRITE_TAC [lemma]))
  ]
 );;

%  NEXT (t1,t2) sig is true when t2 = (t1 + 1) and sig is true at t2.   %
%                                                                       %
%        |- !sig t1. sig(t1 + 1) ==> NEXT(t1,t1 + 1)sig                 %

let NEXT_INC_LEMMA =
 save_thm
 (
  `NEXT_INC_LEMMA`,
   TAC_PROOF
   (
    ([],"!sig:num->bool. !t1:num. (sig (t1 + 1) ==> NEXT (t1,(t1 + 1)) sig)"),
    (REPEAT GEN_TAC) THEN
    STRIP_TAC THEN
    (PURE_REWRITE_TAC [NEXT]) THEN
    CONJ_TAC THENL
    [
     (PURE_REWRITE_TAC [PURE_REWRITE_RULE [ADD1] LESS_SUC_REFL]);
     (
      CONJ_TAC THENL
      [
       (ASM_REWRITE_TAC []);
       (
        GEN_TAC THEN
        (REWRITE_TAC
         [SPECL ["t1:num";"t:num"] (PURE_REWRITE_RULE [ADD1] LESS_LESS_SUC)])
       )
      ]
     )
    ]));;

%  There is a unique time when sig is next true.                        %
%                                                                       %
%  |- !sig t1 t2 t2'. NEXT(t1,t2)sig /\ NEXT(t1,t2')sig ==> (t2 = t2')  %

let NEXT_IDENTITY_LEMMA =
 save_thm
 (
  `NEXT_IDENTITY_LEMMA`,
   let asm =
    PURE_REWRITE_RULE [NEXT]
      (ASSUME "NEXT (t1,t2) sig /\ NEXT (t1,t2') sig") in
   GENL ["sig";"t1"]
    (GENL ["t2";"t2'"]
     (DISCH_ALL
      (CCONTR "(t2 = t2')"
       (DISJ_CASES
        (MP (SPECL ["t2:num";"t2':num"] NOT_EQ_LEMMA) (ASSUME "~(t2 = t2')"))
         (
          SUBS
           [SPEC "(sig t2):bool" A_AND_NOT_A_LEMMA]
           (LIST_CONJ
            [
             (CONJUNCT1 (CONJUNCT2 (CONJUNCT1 asm)));
             (MP
              (SPEC "t2:num" (CONJUNCT2 (CONJUNCT2 (CONJUNCT2 asm))))
              (LIST_CONJ [CONJUNCT1 (CONJUNCT1 asm);(ASSUME "t2 < t2'")])
             )
            ]
           )
         )
         (
          SUBS
           [SPEC "(sig t2'):bool" A_AND_NOT_A_LEMMA]
           (LIST_CONJ
            [
             (CONJUNCT1 (CONJUNCT2 (CONJUNCT2 asm)));
             (MP
              (SPEC "t2':num" (CONJUNCT2 (CONJUNCT2 (CONJUNCT1 asm))))
              (LIST_CONJ [CONJUNCT1 (CONJUNCT2 asm);(ASSUME "t2' < t2")])
             )
            ]
           )
          ))))));;

%  Lemma for increasing the interval covered by NEXT.                   %
%                                                                       %
%  |- !sig t1 t2. ~sig(t1 + 1) /\ NEXT(t1 + 1,t2)sig ==> NEXT(t1,t2)sig %

let NEXT_INC_INTERVAL_LEMMA =
 save_thm
 (
  `NEXT_INC_INTERVAL_LEMMA`,
   TAC_PROOF
   (
    (
     [],
     "!sig t1 t2.
     ~(sig (t1 + 1)) /\ NEXT ((t1 + 1),t2) sig ==> NEXT (t1,t2) sig"
    ),
    (REWRITE_TAC [NEXT]) THEN
    (REPEAT STRIP_TAC) THEN
    (IMP_RES_TAC
     (REWRITE_RULE [LESS_OR_EQ] (PURE_REWRITE_RULE [ADD1] OR_LESS))) THEN
    (ASM_REWRITE_TAC []) THEN
    (DISJ_CASES_TAC
     (REWRITE_RULE [LESS_OR_EQ]
      (UNDISCH
       (SPECL ["t1";"t"]
        (PURE_REWRITE_RULE [ADD1] LESS_SUC_EQ))))) THEN
    (IMP_RES_TAC
     (DISCH_ALL
      (SUBS [SYM (ASSUME "(t1 + 1) = t")]
       (ASSUME "sig t:bool")))) THEN
    RES_TAC
   )
 );;

close_theory ();;
