Theory recordEnumSimpsB[bare]
Ancestors
  recordEnumSimpsA
Libs
  HolKernel Parse BasicProvers simpLib Datatype recordEnumSimpsLib

Theorem enum_lemma1:
   C2 <> C3
Proof
  simp_tac (srw_ss()) []
QED

Theorem enum_lemma2:
   D10 <> D11
Proof
  simp_tac (srw_ss()) []
QED

Theorem recd_lemma1:
   (r with fld1 := 3).fld1 = 3
Proof
  simp_tac (srw_ss()) []
QED

Theorem recd_lemma2:
   (r with fld1 := 3).fld2 = r.fld2
Proof
  simp_tac (srw_ss()) []
QED

Theorem normal_lemma:
   E1 n <> E3
Proof
  computeLib.EVAL_TAC
QED

Theorem fields_of_test:
  ^(#accessor (Lib.assoc "fld2" (TypeBase.fields_of “:'a Record”)))
    <| fld1 := 3; fld2 := K 3 : 'a -> num |>
=
  K 3
Proof
  simp_tac (srw_ss()) []
QED
