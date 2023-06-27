(* Testing the knumsLib.knum_conv conversion.
 *)

open HolKernel bossLib cv_numsLib;
open arithmeticTheory;

val _ = new_theory "cv_numsTest";

Theorem test1 = cv_num_conv ``3 ** 4 ** 5``;
Theorem test2 = cv_num_conv ``2 ** 5 DIV 2``;
Theorem test3 = cv_num_conv ``(123 + 456) * 3``;

val large =
  ``123456789123456781234567812345678912345678912345678912345678912345678999 *
    987654321585858858585882882827474747474771717171727272737373737455959595``;

Theorem test4 = time cv_num_conv large;
Theorem test5 = time EVAL large;

val _ = export_theory ();
