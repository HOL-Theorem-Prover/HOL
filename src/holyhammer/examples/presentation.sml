load "holyHammer";
open holyHammer;

hh [] ``54 + 35 = 89``;

load "transcTheory";

val cj = ``1 = cos x * cos x + sin x * sin x``;
val lemmas = [fetch "real" "REAL_ADD_SYM", fetch "real" "POW_2",
              fetch "transc" "SIN_CIRCLE"];
val thm = save_thm ("LEM1",METIS_PROVE lemmas cj);

val cj = ``cos (2 * x) + 1 = 
  cos x * cos x - sin x * sin x + 
 (cos x * cos x + sin x * sin x)``;
val thm = save_thm ("LEM2",METIS_PROVE lemmas cj);

val cj = ``(a = b - c + (b + c)) ==>  (a = b + b)``;
val thm = save_thm ("LEM3",METIS_PROVE lemmas cj);

(* set_timeout 30; 
   Eprover alone doesn't find a proof even with Mepo predictions *)
val cj = ``cos (2 * x) = 2 * cos x pow 2 - 1``;
val thm = save_thm ("LEM4",METIS_PROVE (thm :: lemmas) cj);

(* set_timeout 5; *)
val cj = ``2 * cos x pow  2 = 1 + cos (2*x)``;
val thm = save_thm ("LEM5",METIS_PROVE lemmas cj);

val cj = ``(2:real * a:real = b) ==> (a:real = b/2:real)``;
set_predictors Mepo;
val thm = save_thm ("LEM6",METIS_PROVE lemmas cj);

val cj = ``cos x pow 2 = (1 + cos (2*x))/2``;
val thm = save_thm ("COS_LIN",METIS_PROVE lemmas cj);
