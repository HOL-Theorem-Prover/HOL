
Theory jit_input
Ancestors
  pred_set arithmetic pair list words
Libs
  wordsLib

val RW = REWRITE_RULE;
val RW1 = ONCE_REWRITE_RULE;

(* abstract syntax *)

Datatype:
  input_type =
  (* no arguments, i.e. arguments are on the stack *)
    iSUB
  | iSWAP
  | iSTOP
  | iPOP
  (* one argument = immediate constant *)
  | iPUSH of word7
  (* one argument = jump target as offset from start of code *)
  | iJUMP of word7
  | iJEQ of word7    (* JEQ = jump if equal *)
  | iJLT of word7    (* JEQ = jump if less than *)
End

(* semantics *)

Definition iFETCH_def:
  (iFETCH n [] = NONE) /\
  (iFETCH n (x::xs) = if n = 0 then SOME x else iFETCH (n-1) xs)
End

val (iSTEP_rules,iSTEP_ind,iSTEP_cases) =
 Hol_reln
 `(!(p:num) xs l ns x (y:word32).
    (iFETCH p ns = SOME iSUB) ==>
    iSTEP (x::y::xs,l,p,ns) ((x-y)::y::xs,l,p+1,ns)) /\
  (!p xs l ns x y.
    (iFETCH p ns = SOME iSWAP) ==>
    iSTEP (x::y::xs,l,p,ns) (y::x::xs,l,p+1,ns)) /\
  (!(p:num) xs l ns x (y:word32).
    (iFETCH p ns = SOME iPOP) ==>
    iSTEP (x::y::xs,l,p,ns) (y::xs,l+1,p+1,ns)) /\
  (!(p:num) xs l ns w.
    (iFETCH p ns = SOME (iPUSH w)) ==>
    iSTEP (xs,l+1,p,ns) (w2w w::xs,l,p+1,ns)) /\
  (!p xs l ns w.
    (iFETCH p ns = SOME (iJUMP w)) ==>
    iSTEP (xs,l,p,ns) (xs,l,w2n w,ns)) /\
  (!p xs l ns x y w.
    (iFETCH p ns = SOME (iJEQ w)) /\ (x = y) ==>
    iSTEP (x::y::xs,l,p,ns) (x::y::xs,l,w2n w,ns)) /\
  (!p xs l ns x y w.
    (iFETCH p ns = SOME (iJEQ w)) /\ ~(x = y) ==>
    iSTEP (x::y::xs,l,p,ns) (x::y::xs,l,p+1,ns)) /\
  (!p xs l ns x y w.
    (iFETCH p ns = SOME (iJLT w)) /\ (x <+ y) ==>
    iSTEP (x::y::xs,l,p,ns) (x::y::xs,l,w2n w,ns)) /\
  (!p xs l ns x y w.
    (iFETCH p ns = SOME (iJLT w)) /\ ~(x <+ y) ==>
    iSTEP (x::y::xs,l,p,ns) (x::y::xs,l,p+1,ns))`

val (iEXEC_rules,iEXEC_ind,iEXEC_cases) =
 Hol_reln
 `(!p xs l ns.
    (iFETCH p ns = SOME iSTOP) ==>
    iEXEC (xs,l,p,ns) (xs,l,p,ns)) /\
  (!s t u.
    iSTEP s t /\ iEXEC t u ==> iEXEC s u)`

(* concrete syntax (string form) *)

Definition iIMM_def:
  iIMM i = [ CHR (ORD #"0" + w2n i) ]
End

Definition iENCODE1_def:
  (iENCODE1 iPOP  = "p") /\
  (iENCODE1 iSUB  = "-") /\
  (iENCODE1 iSWAP = "s") /\
  (iENCODE1 iSTOP = ".") /\
  (iENCODE1 (iPUSH i) = "c" ++ iIMM i) /\
  (iENCODE1 (iJUMP i) = "j" ++ iIMM i) /\
  (iENCODE1 (iJEQ i)  = "=" ++ iIMM i) /\
  (iENCODE1 (iJLT i)  = "<" ++ iIMM i)
End

Definition iENCODE_def:
  (iENCODE [] = "") /\
  (iENCODE (x::xs) = iENCODE1 x ++ iENCODE xs)
End

(* example:

  EVAL ``iENCODE [iSUB;iSTOP;iSWAP;iJLT 1w]``

*)
