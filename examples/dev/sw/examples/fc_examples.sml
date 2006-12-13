loadPath := (concat Globals.HOLDIR "/examples/dev/sw") :: 
            !loadPath;

use (concat Globals.HOLDIR "/examples/dev/sw/compiler");

show_assums := true
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

val def5 = Define `f5(x:word32,y) = y + (f4 (x, f2 y, y)) + x`;
val spec5 = pp_compile def5 false;


val def6 = Define `f6(x:word32,y) = 
	let a = if (x >= y) then f2 y else x in
	(y + (f4 (x, a, y)) + x)`;

val spec6_pre = pp_compile def6 false;

(* set_goal___spec_assums  spec6_pre*)	
val spec6 = prove___spec_assums spec6_pre
(
REWRITE_TAC[FUN_EQ_THM] THEN
Cases_on `x` THEN 
SIMP_TAC std_ss [def6, def4, def2, def1, FUN_EQ_THM, LET_THM] THEN
Cases_on `q >= r` THEN (
	ASM_SIMP_TAC std_ss [WORD_ADD_ASSOC]
))


val def7 = Define `f7(x:word32,y) = 
	let a = y + (2w * x) in
	let b = 5w in
	let c = if (a <= b) then (f2 a) + b else b in
	let d = f4 (c, c, a) in
	(x + d + b)`;

val spec7 = pp_compile def7 false;


