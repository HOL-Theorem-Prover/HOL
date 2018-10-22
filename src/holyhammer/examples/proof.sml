load "holyHammer";
open holyHammer;
load "transcTheory";
set_timeout 60;


val cj = ``1 = cos x * cos x + sin x * sin x``;
(* holyhammer cj; proof found by eprover *)
val tactic = METIS_TAC [realTheory.REAL_NEGNEG, realTheory.REAL_NEG_RMUL, realTheory.REAL_SUB_REFL, realTheory.real_sub, transcTheory.COS_0, transcTheory.COS_ADD, transcTheory.COS_NEG, transcTheory.SIN_NEG];
val thm = store_thm ("LEM1", cj, tactic);

val cj = ``cos (2 * x) + 1 =
  cos x * cos x - sin x * sin x +
 (cos x * cos x + sin x * sin x)``;
(* holyhammer cj; proof found by eprover *)
val tactic = METIS_TAC [fetch "scratch" "LEM1", transcTheory.COS_ADD,
 realTheory.REAL_DOUBLE];
val thm = store_thm ("LEM2", cj, tactic);

val cj3 = ``((a:real) = b - c + (b + c)) ==>  (a = b + b)``;
(* holyhammer cj3; proof found by eprover *)
val tactic = METIS_TAC [realTheory.REAL_ADD2_SUB2, realTheory.REAL_ADD_RID, realTheory.REAL_SUB_ADD2, realTheory.real_sub];
val thm = store_thm ("LEM3", cj3, tactic);

val cj4 = ``cos (2 * x) = 2 * cos x pow 2 - 1``;
val cj5 = mk_imp (cj3,cj4);
(* holyhammer cj5;
   proof found by eprover
   but reconstruction failed *)
val lemmas = [fetch "scratch" "LEM2", fetch "real" "POW_2",
              fetch "real" "REAL_EQ_SUB_LADD", fetch "real" "REAL_DOUBLE"];
val thm = save_thm ("LEM4",METIS_PROVE (thm :: lemmas) cj4);

val cj = ``2 * cos x pow  2 = 1 + cos (2*x)``;
(* holyhammer cj; old proof found by vampire 2.6 *)
val lemmas = [fetch "scratch" "LEM4", fetch "real" "REAL_EQ_SUB_LADD",
              fetch "real" "REAL_ADD_SYM"];
val thm = save_thm ("LEM5",METIS_PROVE lemmas cj);

val cj = ``(2:real * a:real = b) ==> (a:real = b/2:real)``;
(* holyhammer cj; old proof found by vampire 2.6 *)
val lemmas = [fetch "real" "REAL_DOUBLE", fetch "real" "REAL_HALF_DOUBLE",
              fetch "real" "REAL_EQ_RDIV_EQ", fetch "real" "REAL_LT_HALF1",
              fetch "real" "REAL_HALF_BETWEEN", fetch "real" "REAL_DIV_REFL2"];
val thm = save_thm ("LEM6",METIS_PROVE lemmas cj);

val cj = ``cos x pow 2 = (1 + cos (2*x))/2``;
val lemmas = [fetch "scratch" "LEM6", fetch "scratch" "LEM5"];
val thm = save_thm ("LEM7",METIS_PROVE lemmas cj);
