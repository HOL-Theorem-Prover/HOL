signature PFTCandlePreamble = sig

  (* Emit a standalone Candle-ruleset PFT file containing:

     Defined constants and their equations (saved as candle$<name>_DEF):
       T_DEF:       |- T = ((\p. p) = (\p. p))
       AND_DEF:     |- /\ = \p q. (\f:bool->bool->bool. f p q) = (\f. f T T)
       IMP_DEF:     |- ==> = \p q. (p /\ q) = p
       FORALL_DEF:  |- ! = \P:A->bool. P = (\x. T)
       EXISTS_DEF:  |- ? = \P:A->bool. !q. (!x. P x ==> q) ==> q
       OR_DEF:      |- \/ = \p q. !r. (p ==> r) ==> (q ==> r) ==> r
       F_DEF:       |- F = !p. p
       NOT_DEF:     |- ~ = \p. p ==> F

     HOL4-variant definitions:
       EXISTS_DEF_HOL4: |- ? = \P. P(@ P)
       AND_DEF_HOL4:    |- /\ = \p q. !t. (p ==> q ==> t) ==> t

     Declared constant (no definition equation):
       @ : (A->bool)->A

     Axioms:
       SELECT_AX: |- !P:A->bool. !x:A. P x ==> P(@ P)
       ETA_AX:    |- !t:A->B. (\x. t x) = t

     Pro-forma theorems for derived rules (saved as candle$<name>):
       TRUTH:          |- T
       EQT_INTRO:      |- t = (t = T)
       CONJUNCT1:      p /\ q |- p
       CONJUNCT2:      p /\ q |- q
       CONJ:           p, q |- p /\ q
       MP:             p |- (p ==> q) = q
       DISCH:          |- ((p /\ q) = p) = (p ==> q)
       EQ_IMP_RULE1:   p = q |- p ==> q
       EQ_IMP_RULE2:   p = q |- q ==> p
       SPEC:           |- (!P) ==> P x
       GEN:            |- (P = \x. T) = !P
       EXISTS:         P x |- ?P
       CHOOSE:         |- (?P) ==> (!x. P x ==> Q) ==> Q
       DISJ1:          p |- p \/ q
       DISJ2:          q |- p \/ q
       DISJ_CASES:     p \/ q, p ==> r, q ==> r |- r
       CONTR:          F |- p
       NOT_ELIM:       ~p |- p ==> F
       NOT_INTRO:      p ==> F |- ~p
       SELECT_AX_SPEC: |- !x. P x ==> P(@ P)          (P : A->bool free)
       EXCLUDED_MIDDLE:|- !t. t \/ ~t
       CCONTR:         |- (~p ==> F) ==> p
       BOOL_CASES_AX:  |- !t. (t = T) \/ (t = F)

     All theorems and definition equations are SAVEd under "candle$<name>".
  *)
  val emit : {output: string, binary: bool} -> unit

end
