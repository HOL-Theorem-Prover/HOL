open HolKernel Parse boolLib bossLib; val _ = new_theory "std_prelude";

open arithmeticTheory listTheory combinTheory pairTheory sumTheory;
open optionTheory oneTheory bitTheory stringTheory;
open patriciaTheory finite_mapTheory pred_setTheory;

open ml_translatorLib ml_translatorTheory mini_preludeTheory;;

val _ = translation_extends "mini_prelude"; (* HD, TL, APPEND, REV, REVERSE *)


(* pair *)

val res = translate FST;
val res = translate SND;
val res = translate CURRY_DEF;
val res = translate UNCURRY;

(* combin *)

val res = translate o_DEF;
val res = translate I_THM;
val res = translate C_DEF;
val res = translate K_DEF;
val res = translate S_DEF;
val res = translate UPDATE_def;
val res = translate W_DEF;

(* one *)

val _ = register_type ``:one``

(* option *)

val res = translate THE_DEF;
val res = translate IS_NONE_DEF;
val res = translate IS_SOME_DEF;
val res = translate OPTION_MAP_DEF;
val res = translate OPTION_MAP2_DEF;

val THE_side_def = prove(
  ``THE_side = IS_SOME``,
  FULL_SIMP_TAC std_ss [FUN_EQ_THM] THEN Cases
  THEN FULL_SIMP_TAC (srw_ss()) [fetch "-" "THE_side_def"])
  |> update_precondition;

val OPTION_MAP2_side_def = prove(
  ``!f x y. OPTION_MAP2_side f x y = T``,
  FULL_SIMP_TAC (srw_ss()) [fetch "-" "OPTION_MAP2_side_def",THE_side_def])
  |> update_precondition;

(* sum *)

val res = translate ISL;
val res = translate ISR;
val res = translate OUTL;
val res = translate OUTR;
val res = translate SUM_MAP_def;

val OUTL_side_def = prove(
  ``OUTL_side = ISL``,
  FULL_SIMP_TAC std_ss [FUN_EQ_THM] THEN Cases
  THEN FULL_SIMP_TAC (srw_ss()) [fetch "-" "OUTL_side_def"])
  |> update_precondition;

val OUTR_side_def = prove(
  ``OUTR_side = ISR``,
  FULL_SIMP_TAC std_ss [FUN_EQ_THM] THEN Cases
  THEN FULL_SIMP_TAC (srw_ss()) [fetch "-" "OUTR_side_def"])
  |> update_precondition;

(* list *)

val LENGTH_AUX_def = Define `
  (LENGTH_AUX [] n = (n:num)) /\
  (LENGTH_AUX (x::xs) n = LENGTH_AUX xs (n+1))`;

val LENGTH_AUX_THM = prove(
  ``!xs n. LENGTH_AUX xs n = LENGTH xs + n``,
  Induct THEN ASM_SIMP_TAC std_ss [LENGTH_AUX_def,LENGTH,ADD1,AC ADD_COMM ADD_ASSOC])
  |> Q.SPECL [`xs`,`0`] |> GSYM |> SIMP_RULE std_ss [];

val res = translate LENGTH_AUX_def;
val res = translate LENGTH_AUX_THM;
val res = translate MAP;
val res = translate FILTER;
val res = translate FOLDR;
val res = translate FOLDL;
val res = translate SUM;
val res = translate UNZIP;
val res = translate FLAT;
val res = translate TAKE_def;
val res = translate DROP_def;
val res = translate SNOC;
val res = translate EVERY_DEF;
val res = translate EXISTS_DEF;
val res = translate GENLIST;
val res = translate PAD_RIGHT;
val res = translate PAD_LEFT;
val res = translate MEM;
val res = translate ALL_DISTINCT;
val res = translate isPREFIX;
val res = translate FRONT_DEF;
val res = translate ZIP;
val res = translate EL;

val FRONT_side_def = prove(
  ``!xs. FRONT_side xs = ~(xs = [])``,
  Induct THEN FULL_SIMP_TAC (srw_ss()) [fetch "-" "FRONT_side_def",CONTAINER_def])
  |> update_precondition;

val ZIP_side_def = prove(
  ``!x. ZIP_side x = (LENGTH (FST x) = LENGTH (SND x))``,
  Cases THEN Q.SPEC_TAC (`r`,`r`) THEN Induct_on `q` THEN Cases_on `r`
  THEN FULL_SIMP_TAC (srw_ss()) [fetch "-" "ZIP_side_def"])
  |> update_precondition;

val EL_side_def = prove(
  ``!n xs. EL_side n xs = n < LENGTH xs``,
  Induct THEN Cases_on `xs` THEN FULL_SIMP_TAC (srw_ss())
    [fetch "-" "EL_side_def",CONTAINER_def])
  |> update_precondition;

(* sorting *)

val res = translate sortingTheory.PART_DEF;
val res = translate sortingTheory.PARTITION_DEF;
val res = translate sortingTheory.QSORT_DEF;

(* arithmetic *)

val EXP_AUX_def = Define `
  EXP_AUX m n k = if n = 0 then k else EXP_AUX m (n-1:num) (m * k:num)`;

val EXP_AUX_THM = prove(
  ``!n k. EXP_AUX m n (m**k) = m**(k+n)``,
  Induct THEN SIMP_TAC std_ss [EXP,Once EXP_AUX_def,ADD1]
  THEN ASM_SIMP_TAC std_ss [GSYM EXP]
  THEN FULL_SIMP_TAC std_ss [ADD1,AC ADD_COMM ADD_ASSOC])
  |> Q.SPECL [`n`,`0`] |> SIMP_RULE std_ss [EXP] |> GSYM;

val res = translate EXP_AUX_def;
val res = translate EXP_AUX_THM; (* tailrec version of EXP *)
val res = translate MIN_DEF;
val res = translate MAX_DEF;
val res = translate EVEN_MOD2;
val res = translate (REWRITE_RULE [EVEN_MOD2,DECIDE ``~(n = 0) = 0 < n:num``] ODD_EVEN);
val res = translate FUNPOW;
val res = translate MOD_2EXP_def;
val res = translate DIV_2EXP_def;
val res = translate (DECIDE ``PRE n = n-1``);
val res = translate ABS_DIFF_def;
val res = translate DIV2_def;

(* string *)

val CHAR_def = Define `
  CHAR (c:char) = NUM (ORD c)`;

val _ = add_type_inv ``CHAR`` ``:num``

val EqualityType_CHAR = prove(
  ``EqualityType CHAR``,
  EVAL_TAC THEN SRW_TAC [] [] THEN EVAL_TAC)
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
  THEN METIS_TAC [])
  |> MATCH_MP (MATCH_MP Eval_WEAKEN (hol2deep ``\m n. m < n:num``))
  |> store_eval_thm;

val res = translate string_lt_def;
val res = translate string_le_def;
val res = translate string_gt_def;
val res = translate string_ge_def;

(* bit *)

val res = translate bitTheory.BITS_THM2;
val res = translate (SIMP_RULE std_ss [bitTheory.BITS_THM,DECIDE ``SUC n - n = 1``] bitTheory.BIT_def);
val res = translate bitTheory.SBIT_def;

(* patricia trees, i.e. num |-> 'a *)

val FMAP_EQ_PTREE_def = Define `
  FMAP_EQ_PTREE f p =
    (FDOM f = { n | IS_SOME (PEEK p n) }) /\
    FEVERY (\(n,x). PEEK p n = SOME x) f /\ IS_PTREE p`;

val FMAP_EQ_PTREE_FLOOKUP = prove(
  ``FMAP_EQ_PTREE f p ==> (FLOOKUP f = PEEK p)``,
  SIMP_TAC std_ss [FUN_EQ_THM]
  THEN SIMP_TAC std_ss [FMAP_EQ_PTREE_def,PEEK_ADD,FAPPLY_FUPDATE_THM,
    FDOM_FUPDATE,FEVERY_DEF,IN_INSERT,EXTENSION,FLOOKUP_DEF,GSPECIFICATION]
  THEN REPEAT STRIP_TAC THEN Cases_on `p ' x`
  THEN METIS_TAC [IS_SOME_DEF,SOME_11]);

val FMAP_EQ_PTREE_FUPDATE = prove(
  ``FMAP_EQ_PTREE f p ==>
    FMAP_EQ_PTREE (FUPDATE f (n,x)) (ADD p (n,x))``,
  SIMP_TAC std_ss [FMAP_EQ_PTREE_def,PEEK_ADD,FAPPLY_FUPDATE_THM,
    FDOM_FUPDATE,FEVERY_DEF,IN_INSERT,GSPECIFICATION,EXTENSION,ADD_IS_PTREE]
  THEN REPEAT STRIP_TAC THEN Cases_on `x' = n` THEN FULL_SIMP_TAC std_ss []);

val FMAP_EQ_PTREE_DOMSUB = prove(
  ``FMAP_EQ_PTREE f p ==>
    FMAP_EQ_PTREE (f \\ n) (REMOVE p n)``,
  SIMP_TAC (srw_ss()) [FMAP_EQ_PTREE_def,FEVERY_DEF,PEEK_def,
    IN_INSERT,GSPECIFICATION,EXTENSION,DOMSUB_FAPPLY,PEEK_REMOVE]
  THEN REPEAT STRIP_TAC THEN Cases_on `x = n`
  THEN FULL_SIMP_TAC std_ss [DOMSUB_FAPPLY_NEQ]);

val _ = register_type ``:'a ptree``;
val PTREE_TYPE_def = fetch "-" "PTREE_TYPE_def";

val FMAP_TYPE_def = Define `
  FMAP_TYPE a f = \v. ?p. PTREE_TYPE a p v /\ FMAP_EQ_PTREE f p`;

val _ = add_type_inv ``FMAP_TYPE (a:'a -> v -> bool)`` ``:'a ptree``;

val res = translate BRANCHING_BIT_def;
val PEEK_eval = translate PEEK_def;

val Eval_FLOOKUP = prove(
  ``!v. ((PTREE_TYPE a --> NUM --> OPTION_TYPE a) PEEK) v ==>
        ((FMAP_TYPE a --> NUM --> OPTION_TYPE a) FLOOKUP) v``,
  SIMP_TAC (srw_ss()) [Arrow_def,AppReturns_def,FMAP_TYPE_def,
    PULL_EXISTS] THEN METIS_TAC [FMAP_EQ_PTREE_FLOOKUP])
  |> MATCH_MP (MATCH_MP Eval_WEAKEN PEEK_eval)
  |> store_eval_thm;

val res = translate MOD_2EXP_EQ_def;
val res = translate JOIN_def;
val ADD_eval = translate ADD_def;

val Eval_FUPDATE = prove(
  ``!v. ((PTREE_TYPE a --> PAIR_TYPE NUM a --> PTREE_TYPE a) ADD) v ==>
        ((FMAP_TYPE a --> PAIR_TYPE NUM a --> FMAP_TYPE a) FUPDATE) v``,
  SIMP_TAC (srw_ss()) [Arrow_def,AppReturns_def,FMAP_TYPE_def]
  THEN METIS_TAC [FMAP_EQ_PTREE_FUPDATE,PAIR])
  |> MATCH_MP (MATCH_MP Eval_WEAKEN ADD_eval)
  |> store_eval_thm;

val res = translate BRANCH_def;
val REMOVE_eval = translate REMOVE_def;

val Eval_DOMSUB = prove(
  ``!v. ((PTREE_TYPE a --> NUM --> PTREE_TYPE a) REMOVE) v ==>
        ((FMAP_TYPE a --> NUM --> FMAP_TYPE a) $\\) v``,
  SIMP_TAC (srw_ss()) [Arrow_def,AppReturns_def,FMAP_TYPE_def]
  THEN METIS_TAC [FMAP_EQ_PTREE_DOMSUB,PAIR])
  |> MATCH_MP (MATCH_MP Eval_WEAKEN REMOVE_eval)
  |> store_eval_thm;

(*
  hol2deep ``(FLOOKUP ((f \\ 5 \\ 6) |+ (5:int,x)) n)``
*)

val _ = export_theory();

