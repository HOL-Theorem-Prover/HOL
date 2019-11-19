open HolKernel Parse BasicProvers simpLib Datatype

val _ = new_theory "recordEnumSimpsB"

local open recordEnumSimpsLib recordEnumSimpsATheory in end;

val enum_lemma1 = Q.store_thm("enum_lemma1",
  ‘C2 <> C3’,
  simp_tac (srw_ss()) []);

val enum_lemma2 = Q.store_thm("enum_lemma2",
  ‘D10 <> D11’,
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

Theorem fields_of_test:
  ^(#accessor (Lib.assoc "fld2" (TypeBase.fields_of “:'a Record”)))
    <| fld1 := 3; fld2 := K 3 : 'a -> num |>
=
  K 3
Proof
  simp_tac (srw_ss()) []
QED

val _ = export_theory();
