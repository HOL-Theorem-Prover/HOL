Theory caseEqAbbrev

Type foo = “:'a list”

Theorem bar:
  (case x of [] => 0 | h::t => 3) = 4 ==> x <> []
Proof
  simp[CaseEq"foo"]
QED

