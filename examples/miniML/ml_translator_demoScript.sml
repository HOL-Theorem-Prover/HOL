open HolKernel Parse boolLib bossLib; val _ = new_theory "ml_translator_demo";

open ml_translatorLib;

open arithmeticTheory listTheory combinTheory pairTheory;



(* ************************************************************************** *

   Notes

   Partial definitions, e.g. HD, TL and ZIP, cannot be translated.

   MiniML only allows equality tests over num and bool, e.g. this
   means that functions such as MEM can only be translated for
   specific types, num and bool. Should equality types be implemented
   in MiniML?

   Shuold words and string, i.e. lists of characters, be supported by
   default?

 * ************************************************************************** *)


(* examples from library *)

val res = translate MAP;
val res = translate FILTER;
val res = translate APPEND;
val res = translate REVERSE_DEF;
val res = translate LENGTH;
val res = translate FOLDR;
val res = translate FOLDL;
val res = translate sortingTheory.PART_DEF;
val res = translate sortingTheory.PARTITION_DEF;
val res = translate sortingTheory.QSORT_DEF;
val res = translate SUM;
val res = translate FST;
val res = translate SND;
val res = translate UNZIP;
val res = translate FLAT;
val res = translate TAKE_def;
val res = translate SNOC;
val res = translate REV_DEF;
val res = translate EVERY_DEF;
val res = translate EXISTS_DEF;
val res = translate GENLIST;
val res = translate o_DEF;
val res = translate K_DEF;
val res = translate W_DEF;
val res = translate C_DEF;
val res = translate S_DEF;
val res = translate I_DEF;
val res = translate FAIL_DEF;
val res = translate PAD_RIGHT;
val res = translate PAD_LEFT;
val res = translate (MEM |> INST_TYPE [alpha|->``:num``]);
val res = translate (ALL_DISTINCT |> INST_TYPE [alpha|->``:num``]);
val res = translate (isPREFIX |> INST_TYPE [alpha|->``:num``]);


(* some locally defined examples *)

val (def,res) = mlDefine `
  (fac 0 = 1) /\
  (fac (SUC n) = SUC n * fac n)`;

val (def,res) = mlDefine `
  gcd m n = if n = 0 then m else gcd n (m MOD n)`

val (def,res) = mlDefine `
  foo f x = f (f x (\x. x))`

val (def,res) = mlDefine `
  n_times n f x = if n = 0 then x else n_times (n-1) f (f x)`

val (def,res) = mlDefine `
  fac_gcd k m n = if k = 0 then k else fac_gcd (k-1) (fac (gcd m n)) n`

val (def,res) = mlDefine `
  nlist n = if n = 0 then [] else n :: nlist (n-1)`;

val (def,res) = mlDefine `
  rhs n = if n = 0 then INR n else INL n`;

val (def,res) = mlDefine `
  rhs_option n = if n = 0 then INL NONE else INR (SOME n)`;

val (def,res) = mlDefine `
  add ((x1,x2),(y1,y2)) = x1+x2+y1+y2:num`;

val (def,res) = mlDefine `
  (silly (x,INL y) = x + y) /\
  (silly (x,INR y) = x + y:num)`;

val (def,res) = mlDefine `
  (ODDS [] = []) /\
  (ODDS [x] = [x]) /\
  (ODDS (x::y::xs) = x :: ODDS xs)`;

val (def,res) = mlDefine `
  (EVENS [] ys = []) /\
  (EVENS [x] ys = [x]) /\
  (EVENS (x::y::xs) (z1::z2::ys) = x :: EVENS xs ys) /\
  (EVENS _ _ = [])`;

val (def,res) = mlDefine `
  (LIT_TEST [] ys = 0) /\
  (LIT_TEST (1::xs) ys = 1) /\
  (LIT_TEST (2::xs) ys = 2 + LIT_TEST xs ys) /\
  (LIT_TEST _ ys = LENGTH ys)`;

val _ = export_theory();

