(*---------------------------------------------------------------------------*)
(*   Simple examples involving function calls                                *)
(*---------------------------------------------------------------------------*)



(*---------------------------------------------------------------------------*)
(*   This is the example 3 in the paper                                      *)
(*---------------------------------------------------------------------------*)

val def1 = Define `f1 (x:word32) = x + x + 1w`;
val spec1 = pp_compile def1 true;


val def2 = Define `f2 x = x * f1 x`;
val spec2 = pp_compile def2 false;


val def3 = Define `f3 x = x + f2 x`;
val spec3 = pp_compile def3 false;

val def4 = Define `f4(x:word32,y,z) = x + y + y + z`;
val spec4 = pp_compile def4 false;

val def5 = Define `f5(x:word32,y) = y + (f4 (x, f3 y, y)) + x`;
val spec5 = pp_compile def5 false;
