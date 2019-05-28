load "holyHammer"; open holyHammer;
load "transcTheory"; 

val thm1 = holyhammer ``cos (2 * x) = cos (x + x)``;
val thm2 = holyhammer ``cos (x + x) = cos x * cos x - sin x * sin x``;

val thm3_l0 = holyhammer ``cos x * cos x + sin x * sin x = 1``;
val thm3_l1 = holyhammer ``(a + b = 1) ==> (b = 1 - a)``;
val thm3 = METIS_PROVE [thm3_l0,thm3_l1]

val thm4_l1 = holyhammer ``a - (1 - a) = a + a - 1``;
val thm4_l2 = holyhammer ``a - (1 - a) = 2 * a - 1``;
val thm4 = holyhammer ``cos x * cos x - (1 - cos x * cos x) = 2 * (cos x * cos x) - 1``;

val thm5 = holyhammer ``cos (2 * x) = 2 * (cos x * cos x) - 1``;
