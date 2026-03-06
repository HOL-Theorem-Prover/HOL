Theory recordEnumSimpsA[bare]
Libs
  HolKernel Parse BasicProvers simpLib Datatype
  recordEnumSimpsLib

val _ = Datatype‘Enum1 = C1 | C2 | C3’;
val _ = Datatype‘Enum2 = D1 | D2 | D3 | D4 | D5 | D6 | D7 | D8 | D9 | D10
                       | D11 | D12 | D13 | D14 | D15 | D16
               ’;

val _ = Datatype‘Normal = E1 num | E2 bool | E3’;

val _ = Datatype‘Record = <| fld1 : num ; fld2 : 'a -> num |>’;

Theorem enum_lemma1:
   C1 <> C2
Proof
  simp_tac (srw_ss()) []
QED

Theorem enum_lemma2:
   D1 <> D2
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

