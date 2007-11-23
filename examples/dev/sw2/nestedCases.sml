structure nestedCases (* :> nestedCases *) =
struct

open HolKernel Parse boolLib pairLib PairRules bossLib pairSyntax;

(*-----------------------------------------------------------------------------------------*)
(* This transformation deals with logical functions and case expressions written with      *)
(* patterns.                                                                               *)
(*-----------------------------------------------------------------------------------------*)

(*-----------------------------------------------------------------------------------------*)
(* Convert nested case expressions into conditional statements.                            *)
(*-----------------------------------------------------------------------------------------*)

(*-----------------------------------------------------------------------------------------*)
(* For num_case.                                                                           *)
(*-----------------------------------------------------------------------------------------*)

val is_0_def = Define `
  (is_0 0 = T) /\
  (is_0 _ = F)`;

val is_0_lem = Q.prove (
  `is_0 z = (z = 0)`,
  Cases_on `z` THEN
  RW_TAC std_ss [is_0_def]
  )

val is_suc_def = Define `
  (is_suc 0 = F) /\
  (is_suc _ = T)`;

val destruct_suc_def = Define `
  (destruct_suc (SUC x) = x)`;

val num_case_lem = Q.prove (
  `num_case b f2 z = 
     if is_0 z then b
     else let v = destruct_suc z in f2 v`,
  Cases_on `z` THEN
  RW_TAC std_ss [arithmeticTheory.num_case_compute, is_0_def, destruct_suc_def]
  );


(*-----------------------------------------------------------------------------------------*)
(* Conversion.                                                                             *)
(*-----------------------------------------------------------------------------------------*)

val lems = [pairTheory.FORALL_PROD, pairTheory.pair_case_thm, num_case_lem, is_0_lem];

fun elim_pattern_match defs = 
  List.map (SIMP_RULE std_ss lems) defs

(*-----------------------------------------------------------------------------------------*)
(* Example 1.                                                                              *)
(*-----------------------------------------------------------------------------------------*)

(*
val gcd_def = Define `
  (gcd (0, y) = y) /\
  (gcd (SUC x, 0) = SUC x) /\
  (gcd (SUC x, SUC y) = if y <= x then gcd (x - y, SUC y) else gcd (SUC x, y - x))`;

val gcd_lem = Q.prove (
  `!z. gcd z = pair_case (\v v1. num_case v1 (\v2. num_case (SUC v2)
             (\v3. if v3 <= v2 then gcd(v2 - v3, SUC v3) else gcd (SUC v2, v3 - v2)) v1) v) z`,
  SIMP_TAC std_ss [pairTheory.FORALL_PROD] THEN
  Cases_on `p_1` THEN Cases_on `p_2` THEN
  RW_TAC arith_ss [gcd_def]
  );

val results = elim_pattern_match [gcd_lem]

*)

(*-----------------------------------------------------------------------------------------*)

end (* struct *)