Theory folMappingContext[bare]
Libs
  HolKernel Parse boolLib tautLib

(* ------------------------------------------------------------------------- *)
(* Worker theorems for first-order proof translation.  Formerly proved by    *)
(* folMapping.sml as it loaded.                                              *)
(* ------------------------------------------------------------------------- *)

Theorem HIDE_LITERAL:  !a. a ==> ~a ==> F
Proof tautLib.TAUT_TAC
QED

Theorem SHOW_LITERAL:  !x. (~x ==> F) ==> x
Proof tautLib.TAUT_TAC
QED

Theorem INITIALIZE_CLAUSE:  !a b. a \/ b ==> ~a ==> b
Proof tautLib.TAUT_TAC
QED

Theorem FINALIZE_CLAUSE:  !a b. (~a ==> b) ==> (a \/ b)
Proof tautLib.TAUT_TAC
QED

Theorem RESOLUTION:  !a. a /\ ~a ==> F
Proof tautLib.TAUT_TAC
QED

Theorem EQUAL_STEP:  !a b c. ((a ==> (b = c)) /\ b) ==> ~a \/ c
Proof tautLib.TAUT_TAC
QED

Theorem EXCLUDED_MIDDLE':  !t. ~t \/ t
Proof tautLib.TAUT_TAC
QED
