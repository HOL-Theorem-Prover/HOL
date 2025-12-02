Theory plotkin4A_CBVPrelims

(* A translation of “Call-by-name, Call-by-value and the λ-Calculus” by
   Gordon Plotkin, Theoretical Computer Science 1 (1975), pp125–159.
   North Holland

   First part of Section 4 on the CBV equational theory, and its CR and
   standardisation results.  Independent of §3.
*)

Ancestors
  cterm nomset pred_set
Libs
  NEWLib

(* p134, λᵥ |- M = N, parameterised by function "Constapply" *)
Inductive lv:
[~I2:] lv capp (LAM x M @@ N) ([N/x] M)
[~I3:] capp a b = SOME t ⇒ lv capp (CONST a @@ CONST b) t
[~II1:] lv capp M M (* TYPO; original has M = N *)
[~II2:] lv capp M N ∧ lv capp N L ⇒ lv capp M L
[~II3:] lv capp M N ⇒ lv capp N M
[~III1a:] lv capp M N ⇒ lv capp (M @@ Z) (N @@ Z)
[~III1b:]  lv capp M N ⇒ lv capp (Z @@ M) (Z @@ N)
[~III2:] lv capp M N ⇒ lv capp (LAM x M) (LAM x N)
End

