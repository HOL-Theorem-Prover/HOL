(* proof of linearization of cosinus *)
load "holyHammer"; open holyHammer;
load "transcTheory"; open realTheory transcTheory;

val thm1 = holyhammer ``cos (2 * x) = cos (x + x)``;
val thm2 = TAC_PROOF (([],
  ``cos (x + x) = cos x * cos x - sin x * sin x``), hh);

val thm3_l0 = holyhammer ``cos x * cos x + sin x * sin x = 1``;
val thm3_l1 = holyhammer ``(a + b = 1) ==> (b = 1 - a)``;
val thm3 = METIS_PROVE [thm3_l0,thm3_l1]
  ``cos x * cos x - sin x * sin x = 
    cos x * cos x - (1 - cos x * cos x)``;

val thm4_l1 = holyhammer ``a - (1 - a) = a + a - 1``;
val thm4_l2 = holyhammer ``a - (1 - a) = 2 * a - 1``;
val thm4 = holyhammer
  ``cos x * cos x - (1 - cos x * cos x) = 
    2 * (cos x * cos x) - 1``;

val thm5 = holyhammer ``cos (2 * x) = 2 * (cos x * cos x) - 1``;
val thm6_l1 = holyhammer ``a = b - 1 ==> a + 1 = b``;
val thm6_l2 = holyhammer ``a = 2 * b ==> b = a / 2``;
val thm6 = METIS_PROVE [thm5,thm6_l1,thm6_l2] 
  ``cos x * cos x = (cos (2 * x) + 1) / 2``;
