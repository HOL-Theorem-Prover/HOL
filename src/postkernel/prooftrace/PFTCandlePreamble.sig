signature PFTCandlePreamble = sig

  (* Emit a standalone Candle-ruleset PFT file containing:
     - Definitions of T, /\, ==>, !, ?, \/, F, ~ (HOL Light definitions)
     - Introduction of @ and axiom of choice
     - ETA_AX axiom
     - Pro-forma theorems for all HOL4 derived rules

     Variable names used in pro-formas (PFTEmit must construct matching
     variables for INST):
       p, q : bool     (for /\, ==>, \/, conjunction/implication rules)
       r    : bool     (for DISJ_CASES)
       t    : bool     (for EQT_INTRO, EXCLUDED_MIDDLE)
       Q    : bool     (for CHOOSE)
       P    : A->bool  (for !, ?, quantifier rules)
       x    : A        (for !, ?, quantifier rules)

     All theorems and definition equations are SAVEd under "candle$<name>".
  *)
  val emit : {output: string, binary: bool} -> unit

end
