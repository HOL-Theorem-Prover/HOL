Theory refuteUnused
Ancestors
  refute
Libs
  bossLib

Theorem conjunctive_assumption:
  !b c : bool. (b /\ c) ==> b
Proof
  simp []
QED

Theorem incomparable_maximals:
  !b c d : bool. b ==> c ==> d ==> (b /\ c) \/ d
Proof
  simp []
QED

Theorem needed_assumption:
  !b : bool. b ==> b
Proof
  simp []
QED

Theorem no_assumptions:
  !b : bool. b = b
Proof
  simp []
QED

Theorem one_unused_assumption:
  !b c : bool. b ==> c ==> b
Proof
  simp []
QED

Theorem two_unused_assumptions:
  !b c : bool. b ==> c ==> T
Proof
  simp []
QED
