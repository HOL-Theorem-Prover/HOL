open HolKernel Parse BasicProvers simpLib Datatype

open recordEnumSimpsLib

val _ = new_theory "recordEnumSimpsA"

val _ = Datatype‘Enum1 = C1 | C2 | C3’;
val _ = Datatype‘Enum2 = D1 | D2 | D3 | D4 | D5 | D6 | D7 | D8 | D9 | D10
                       | D11 | D12 | D13 | D14 | D15 | D16
               ’;

val _ = Datatype‘Normal = E1 num | E2 bool | E3’;

val _ = Datatype‘Record = <| fld1 : num ; fld2 : 'a -> num |>’;

val enum_lemma1 = Q.store_thm("enum_lemma1",
  ‘C1 <> C2’,
  simp_tac (srw_ss()) []);

val enum_lemma2 = Q.store_thm("enum_lemma2",
  ‘D1 <> D2’,
  simp_tac (srw_ss()) []);

val recd_lemma1 = Q.store_thm("recd_lemma1",
  ‘(r with fld1 := 3).fld1 = 3’,
  simp_tac (srw_ss()) []);

val recd_lemma2 = Q.store_thm("recd_lemma2",
  ‘(r with fld1 := 3).fld2 = r.fld2’,
  simp_tac (srw_ss()) []);

val normal_lemma = Q.store_thm("normal_lemma",
  ‘E1 n <> E3’,
  computeLib.EVAL_TAC);

val _ = export_theory();
