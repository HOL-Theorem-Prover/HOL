load "holyHammer";
open holyHammer;
load "transcTheory";

val cj = ``1 = cos x * cos x + sin x * sin x``;
val lemmas = [fetch "real" "REAL_ADD_SYM", fetch "real" "POW_2",
              fetch "transc" "SIN_CIRCLE"];
val thm = save_thm ("LEM1",METIS_PROVE lemmas cj);

val cj = ``cos (2 * x) + 1 =
  cos x * cos x - sin x * sin x +
 (cos x * cos x + sin x * sin x)``;
val lemmas = [fetch "transc" "COS_ADD", fetch "scratch" "LEM1",
              fetch "real" "REAL_DOUBLE"];
val thm = save_thm ("LEM2",METIS_PROVE lemmas cj);

val cj = ``(a = b - c + (b + c)) ==>  (a = b + b)``;
val lemmas = [fetch "real" "REAL_ADD_SYM", fetch "real" "REAL_ADD_ASSOC",
              fetch "real" "REAL_EQ_SUB_LADD"];
val thm = save_thm ("LEM3",METIS_PROVE lemmas cj);

(* set_timeout 30; hh [thm] cj; (only Vampire finds a proof) *)
val cj = ``cos (2 * x) = 2 * cos x pow 2 - 1``;
val lemmas = [fetch "scratch" "LEM2", fetch "real" "POW_2",
              fetch "real" "REAL_EQ_SUB_LADD", fetch "real" "REAL_DOUBLE"];
val thm = save_thm ("LEM4",METIS_PROVE (thm :: lemmas) cj);

(* set_timeout 5; *)
val cj = ``2 * cos x pow  2 = 1 + cos (2*x)``;
val lemmas = [fetch "scratch" "LEM4", fetch "real" "REAL_EQ_SUB_LADD",
              fetch "real" "REAL_ADD_SYM"];
val thm = save_thm ("LEM5",METIS_PROVE lemmas cj);

(* set_predictors Mepo; *)
val cj = ``(2:real * a:real = b) ==> (a:real = b/2:real)``;
val lemmas = [fetch "real" "REAL_DOUBLE", fetch "real" "REAL_HALF_DOUBLE",
              fetch "real" "REAL_EQ_RDIV_EQ", fetch "real" "REAL_LT_HALF1",
              fetch "real" "REAL_HALF_BETWEEN", fetch "real" "REAL_DIV_REFL2"];
val thm = save_thm ("LEM6",METIS_PROVE lemmas cj);

val cj = ``cos x pow 2 = (1 + cos (2*x))/2``;
val lemmas = [fetch "scratch" "LEM6", fetch "scratch" "LEM5"];
val thm = save_thm ("LEM7",METIS_PROVE lemmas cj);
