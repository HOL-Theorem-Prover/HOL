open HolKernel Parse boolLib bossLib; val _ = new_theory "ml_translator_demo";

open ml_translatorLib ml_translatorTheory;

open arithmeticTheory listTheory combinTheory pairTheory;
open stringTheory;

infix \\ val op \\ = op THEN;


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
val res = translate MEM;
val res = translate ALL_DISTINCT;
val res = translate isPREFIX;
val res = translate HD;
val res = translate TL;
val res = translate ZIP;


(* some locally defined examples *)

val def = mlDefine `
  (fac 0 = 1) /\
  (fac (SUC n) = SUC n * fac n)`;

val def = mlDefine `
  gcd m n = if n = 0 then m else gcd n (m MOD n)`

val def = mlDefine `
  foo f x = f (f x (\x. x))`

val def = mlDefine `
  n_times n f x = if n = 0:num then x else n_times (n-1) f (f x)`

val def = mlDefine `
  fac_gcd k m n = if k = 0:num then k else fac_gcd (k-1) (fac (gcd m n)) n`

val def = mlDefine `
  nlist n = if n = 0:num then [] else n :: nlist (n-1)`;

val def = mlDefine `
  rhs n = if n = 0:num then INR n else INL n`;

val def = mlDefine `
  rhs_option n = if n = 0 then INL NONE else INR (SOME n)`;

val def = mlDefine `
  add ((x1,x2),(y1,y2)) = x1+x2+y1+y2:num`;

val def = mlDefine `
  (silly (x,INL y) = x + y) /\
  (silly (x,INR y) = x + y:num)`;

val def = mlDefine `
  (list_test1 [] = []) /\
  (list_test1 [x] = [x]) /\
  (list_test1 (x::y::xs) = x :: list_test1 xs)`;

val def = mlDefine `
  (list_test2 [] ys = []) /\
  (list_test2 [x] ys = [(x,x)]) /\
  (list_test2 (x::y::xs) (z1::z2::ys) = (x,z1) :: list_test2 xs ys) /\
  (list_test2 _ _ = [])`;

val def = mlDefine `
  (list_test3 [] ys = 0) /\
  (list_test3 ((1:num)::xs) ys = 1) /\
  (list_test3 (2::xs) ys = 2 + list_test3 xs ys) /\
  (list_test3 _ ys = LENGTH ys)`;


(* chars, finite_maps, sets and lazy lists... *)

(* teaching the translator about characters (represented as num) *)

val CHAR_def = Define `
  CHAR (c:char) = NUM (ORD c)`;

val _ = add_type_inv ``CHAR``

val EqualityType_CHAR = prove(
  ``EqualityType CHAR``,
  EVAL_TAC \\ SRW_TAC [] [] \\ EVAL_TAC)
  |> store_eq_thm;

val Eval_Val_CHAR = prove(
  ``n < 256 ==> Eval env (Val (Lit (IntLit (&n)))) (CHAR (CHR n))``,
  SIMP_TAC (srw_ss()) [Eval_Val_NUM,CHAR_def])
  |> store_eval_thm;

val Eval_ORD = prove(
  ``!v. ((NUM --> NUM) (\x.x)) v ==> ((CHAR --> NUM) ORD) v``,
  SIMP_TAC std_ss [Arrow_def,AppReturns_def,CHAR_def])
  |> MATCH_MP (MATCH_MP Eval_WEAKEN (hol2deep ``\x.x:num``))
  |> store_eval_thm;

val Eval_CHR = prove(
  ``!v. ((NUM --> NUM) (\n. n MOD 256)) v ==>
        ((NUM --> CHAR) (\n. CHR (n MOD 256))) v``,
  SIMP_TAC (srw_ss()) [Arrow_def,AppReturns_def,CHAR_def])
  |> MATCH_MP (MATCH_MP Eval_WEAKEN (hol2deep ``\n. n MOD 256``))
  |> store_eval_thm;

val Eval_CHAR_LT = prove(
  ``!v. ((NUM --> NUM --> BOOL) (\m n. m < n)) v ==>
        ((CHAR --> CHAR --> BOOL) char_lt) v``,
  SIMP_TAC (srw_ss()) [Arrow_def,AppReturns_def,CHAR_def,char_lt_def]
  \\ METIS_TAC [])
  |> MATCH_MP (MATCH_MP Eval_WEAKEN (hol2deep ``\m n. m < n:num``))
  |> store_eval_thm;

(* now we can translate e.g. less-than over strings *)

val res = translate string_lt_def

val def = mlDefine `
  hi n = if n = 0 then "!" else "hello " ++ hi (n-1:num)`


(* qsort expanded *)

val Eval_Var_lemma = prove(
  ``Eval env (Var name) P = ?x. (lookup name env = SOME x) /\ P x``,
  SIMP_TAC (srw_ss()) [Eval_def,Once MiniMLTheory.evaluate'_cases]);

val Eval_QSORT_EXPANDED = save_thm("Eval_QSORT_EXPANDED",let
  val qsort_eval = translate sortingTheory.QSORT_DEF;
  val th = MATCH_MP Eval_Arrow qsort_eval
  val th1 = ASSUME ``Eval env (Var "R") ((a --> a --> BOOL) R)``
  val th = MATCH_MP th th1
  val th = MATCH_MP Eval_Arrow th
  val th1 = ASSUME ``Eval env (Var "xs") ((list a) xs)``
  val th = MATCH_MP th th1
  val th = REWRITE_RULE [Eval_def] th
  val th = DISCH_ALL th
  val th = SIMP_RULE std_ss [Eval_Var_lemma] th
  val th = SIMP_RULE std_ss [PULL_EXISTS,PULL_FORALL] th
  in th end)

val ML_QSORT_CORRECT = store_thm ("ML_QSORT_CORRECT",
  ``!env a ord R l xs.
      (lookup "QSORT" env = SOME (Recclosure QSORT_env QSORT_ml "QSORT")) /\
      (lookup "PARTITION" QSORT_env = SOME (Closure PARTITION_env "P" PARTITION_ml)) /\
      (lookup "APPEND" QSORT_env = SOME (Recclosure APPEND_env APPEND_ml "APPEND")) /\
      (lookup "PART" PARTITION_env = SOME (Recclosure PART_env PART_ml "PART")) /\
      list a l xs /\ (lookup "xs" env = SOME xs) /\
      (a --> a --> BOOL) ord R /\ (lookup "R" env = SOME R) /\
      transitive ord /\ total ord
      ==>
      ?l' xs'.
        evaluate' env
            (App Opapp (App Opapp (Var "QSORT") (Var "R")) (Var "xs"))
            (Rval xs') /\
        (list a l' xs') /\ PERM l l' /\ SORTED ord l'``,
  REPEAT STRIP_TAC \\ IMP_RES_TAC Eval_QSORT_EXPANDED
  \\ Q.LIST_EXISTS_TAC [`QSORT ord l`,`res'''`]
  \\ FULL_SIMP_TAC std_ss [QSORT_PERM,QSORT_SORTED]);


val _ = export_theory();

