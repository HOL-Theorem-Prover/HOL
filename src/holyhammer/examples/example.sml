load "holyHammer";
open holyHammer;

(*--------------------------------------------------------------------------
  Example 1
  -------------------------------------------------------------------------- *)

val cj = ``a <= b ==> (g ** (b - a) * g ** a = g ** b)``  (* hh [] cj; *)
val lemmas = [fetch "arithmetic" "SUB_ADD", fetch "arithmetic" "EXP_ADD"];
val th = save_thm ("EXP_NEG",METIS_PROVE (lemmas) cj);

(*--------------------------------------------------------------------------
  Example 2
  -------------------------------------------------------------------------- *)

new_theory "zerok";

val BASE_DEF = new_definition ("BASE_DEF",``BASE = @(x:num). x >= 2``);
val th0 = INST_TYPE [alpha |-> ``:num``] SELECT_AX;
val th1 = save_thm ("hh0",SPECL [``\x.x>=(2:num)``,``2:num``] th0);
val cj = ``BASE>=2``; (* hh [th0,th1] cj; *)
val lemmas = [fetch "zerok" "BASE_DEF", fetch "numeral" "numeral_lte",
              fetch "arithmetic" "GREATER_EQ",
              fetch "arithmetic" "NUMERAL_DEF"];
val th = save_thm ("BASE_THM",METIS_PROVE ([th0,th1] @ lemmas) cj);

(*--------------------------------------------------------------------------
  Example 3
  -------------------------------------------------------------------------- *)

load "complexTheory";
val cj = ``i * i = -1``;
hh [] cj;
val lemmas = [fetch "real" "real_sub", fetch "real" "REAL_ADD_LID",
              fetch "real" "REAL_NEG_0", fetch "complex" "COMPLEX_1",
              fetch "real" "REAL_MUL_RZERO", fetch "complex" "complex_of_real",
              fetch "complex" "complex_neg", fetch "real" "REAL_MUL_RID",
              fetch "pair" "SND", fetch "complex" "i", fetch "pair" "FST",
              fetch "complex" "IM", fetch "complex" "RE",
              fetch "complex" "complex_mul"];
val th = METIS_PROVE lemmas cj;

(*--------------------------------------------------------------------------
  Example 4
  -------------------------------------------------------------------------- *)

load "complexTheory";
val cj = ``(1:complex) + 1 = 2``; (* hh [] cj; *)
val lemmas = [fetch "arithmetic" "TWO", fetch "complex" "COMPLEX_OF_REAL_ADD",
              fetch "real" "REAL", fetch "complex" "complex_of_num"];
val th = METIS_PROVE lemmas cj;
