load "holyHammer";
open holyHammer;
load "transcTheory";

val cj = ``1 = cos x * cos x + sin x * sin x``; 
(* holyhammer cj; *)
val tactic = METIS_TAC [realTheory.REAL_ADD_SYM, realTheory.POW_2,
 transcTheory.SIN_CIRCLE];
val thm = store_thm ("LEM1", cj, tactic);

val cj = ``cos (2 * x) + 1 =
  cos x * cos x - sin x * sin x +
 (cos x * cos x + sin x * sin x)``;
(* holyhammer cj; *)
val tactic = METIS_TAC [fetch "scratch" "LEM1", transcTheory.COS_ADD,
 realTheory.REAL_DOUBLE];
val thm = store_thm ("LEM2", cj, tactic);

val cj3 = ``((a:real) = b - c + (b + c)) ==>  (a = b + b)``;
(* holyhammer cj3; *)
val tactic = METIS_TAC [realTheory.REAL_ADD_ASSOC, realTheory.REAL_SUB_ADD,
  realTheory.REAL_ADD_SYM];
val thm = store_thm ("LEM3", cj3, tactic);

val cj4 = ``cos (2 * x) = 2 * cos x pow 2 - 1``;
val cj5 = mk_imp (cj3,cj4);
(* set_timeout 30; holyhammer cj5; only Vampire finds a proof or tactictoe finds a proof *)
val lemmas = [fetch "scratch" "LEM2", fetch "real" "POW_2",
              fetch "real" "REAL_EQ_SUB_LADD", fetch "real" "REAL_DOUBLE"];
val thm = save_thm ("LEM4",METIS_PROVE (thm :: lemmas) cj4);

val cj = ``2 * cos x pow  2 = 1 + cos (2*x)``;
(* set_timeout 30; holyhammer cj; (* only Vampire finds a proof *) *)
val lemmas = [fetch "scratch" "LEM4", fetch "real" "REAL_EQ_SUB_LADD",
              fetch "real" "REAL_ADD_SYM"];
val thm = save_thm ("LEM5",METIS_PROVE lemmas cj);

val cj = ``(2:real * a:real = b) ==> (a:real = b/2:real)``;
(* set_timeout 30; holyhammer cj; *)
val lemmas = [fetch "real" "REAL_DOUBLE", fetch "real" "REAL_HALF_DOUBLE",
              fetch "real" "REAL_EQ_RDIV_EQ", fetch "real" "REAL_LT_HALF1",
              fetch "real" "REAL_HALF_BETWEEN", fetch "real" "REAL_DIV_REFL2"];
val thm = save_thm ("LEM6",METIS_PROVE lemmas cj);

val cj = ``cos x pow 2 = (1 + cos (2*x))/2``;
val lemmas = [fetch "scratch" "LEM6", fetch "scratch" "LEM5"];
val thm = save_thm ("LEM7",METIS_PROVE lemmas cj);


