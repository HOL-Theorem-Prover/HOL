(* ========================================================================= *)
(* Create "extra_stringTheory" for toString automation and definitions       *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Load and open relevant theories                                           *)
(* (Comment out "load" and "loadPath"s for compilation)                      *)
(* ------------------------------------------------------------------------- *)
(*

app load ["bossLib", "metisLib", "arithmeticTheory",
    	  "listTheory", "HurdUseful", "combinTheory", "pairTheory",
	  "extra_boolTheory", "jrhUtils", "numTheory", "simpLib",
	  "stringTheory", "rich_listTheory",
	  "stringSimps", "listSimps", "extra_numTheory"];

*)

open HolKernel Parse boolLib bossLib

open metisLib simpLib stringSimps listSimps

open arithmeticTheory listTheory combinTheory pairTheory
     numTheory stringTheory rich_listTheory listSimps numposrepTheory
     logrootTheory


val _ = new_theory "ASCIInumbers";

(* ------------------------------------------------------------------------- *)
(* Helpful proof tools                                                       *)
(* ------------------------------------------------------------------------- *)

val REVERSE = Tactical.REVERSE;
val Suff = Q_TAC SUFF_TAC;


val POP_ORW = POP_ASSUM (fn thm => ONCE_REWRITE_TAC [thm]);

val safe_list_ss = (simpLib.++ (bool_ss, LIST_ss));

val safe_string_ss = (simpLib.++ (bool_ss, STRING_ss));

val arith_string_ss = (simpLib.++ (arith_ss, STRING_ss));

val string_ss = (simpLib.++ (list_ss, STRING_ss));

val s2n_def = Define `s2n b f (s:string) = l2n b (MAP f (REVERSE s))`;
val n2s_def = Define `n2s b f n : string = REVERSE (MAP f (n2l b n))`;

val s2n_compute = Q.store_thm(
  "s2n_compute",
  `s2n b f s = l2n b (MAP f (REVERSE (EXPLODE s)))`,
  SRW_TAC [][stringTheory.IMPLODE_EXPLODE_I, s2n_def])
val n2s_compute = Q.store_thm(
  "n2s_compute",
  `n2s b f n = IMPLODE (REVERSE (MAP f (n2l b n)))`,
  SRW_TAC [][stringTheory.IMPLODE_EXPLODE_I, n2s_def])

val HEX_def = Define`
  (HEX 0 = #"0") /\
  (HEX 1 = #"1") /\
  (HEX 2 = #"2") /\
  (HEX 3 = #"3") /\
  (HEX 4 = #"4") /\
  (HEX 5 = #"5") /\
  (HEX 6 = #"6") /\
  (HEX 7 = #"7") /\
  (HEX 8 = #"8") /\
  (HEX 9 = #"9") /\
  (HEX 10 = #"A") /\
  (HEX 11 = #"B") /\
  (HEX 12 = #"C") /\
  (HEX 13 = #"D") /\
  (HEX 14 = #"E") /\
  (HEX 15 = #"F")`;

val UNHEX_def = Define`
  (UNHEX #"0" = 0) /\
  (UNHEX #"1" = 1) /\
  (UNHEX #"2" = 2) /\
  (UNHEX #"3" = 3) /\
  (UNHEX #"4" = 4) /\
  (UNHEX #"5" = 5) /\
  (UNHEX #"6" = 6) /\
  (UNHEX #"7" = 7) /\
  (UNHEX #"8" = 8) /\
  (UNHEX #"9" = 9) /\
  (UNHEX #"a" = 10) /\
  (UNHEX #"b" = 11) /\
  (UNHEX #"c" = 12) /\
  (UNHEX #"d" = 13) /\
  (UNHEX #"e" = 14) /\
  (UNHEX #"f" = 15) /\
  (UNHEX #"A" = 10) /\
  (UNHEX #"B" = 11) /\
  (UNHEX #"C" = 12) /\
  (UNHEX #"D" = 13) /\
  (UNHEX #"E" = 14) /\
  (UNHEX #"F" = 15)`;

val LESS_THM =
  CONV_RULE numLib.SUC_TO_NUMERAL_DEFN_CONV prim_recTheory.LESS_THM;

infix \\ << >>

val op \\ = op THEN;
val op << = op THENL;
val op >> = op THEN1;

val UNHEX_HEX = store_thm("UNHEX_HEX",
  ``!n. n < 16 ==> (UNHEX (HEX n) = n)``, SRW_TAC [] [LESS_THM] \\ EVAL_TAC);

val HEX_UNHEX = store_thm("HEX_UNHEX",
  ``!c. isHexDigit c ==> (HEX (UNHEX c) = toUpper c)``,
  Cases \\ SRW_TAC [] [isHexDigit_def] \\ Q.PAT_ASSUM `n < 256` (K ALL_TAC)
    << [`n < 58` by DECIDE_TAC, `n < 103` by DECIDE_TAC,
        `n < 71` by DECIDE_TAC]
    \\ FULL_SIMP_TAC std_ss [LESS_THM]
    \\ FULL_SIMP_TAC arith_ss []
    \\ EVAL_TAC);

val DEC_UNDEC = store_thm("DEC_UNDEC",
  ``!c. isDigit c ==> (HEX (UNHEX c) = c)``,
  Cases \\ SRW_TAC [] [isDigit_def] \\ Q.PAT_ASSUM `n < 256` (K ALL_TAC)
    \\ `n < 58` by DECIDE_TAC
    \\ FULL_SIMP_TAC std_ss [LESS_THM]
    \\ FULL_SIMP_TAC arith_ss []
    \\ EVAL_TAC);

val num_from_bin_string_def = Define `num_from_bin_string = s2n 2 UNHEX`;
val num_from_oct_string_def = Define `num_from_oct_string = s2n 8 UNHEX`;
val num_from_dec_string_def = Define `num_from_dec_string = s2n 10 UNHEX`;
val num_from_hex_string_def = Define `num_from_hex_string = s2n 16 UNHEX`;

val num_to_bin_string_def = Define `num_to_bin_string = n2s 2 HEX`;
val num_to_oct_string_def = Define `num_to_oct_string = n2s 8 HEX`;
val num_to_dec_string_def = Define `num_to_dec_string = n2s 10 HEX`;
val num_to_hex_string_def = Define `num_to_hex_string = n2s 16 HEX`;

val MAP_ID = Q.prove(
  `!l. EVERY (\x. f x = x) l ==> (MAP f l = l)`,
  Induct \\ SRW_TAC [] []);

val s2n_n2s = Q.store_thm("s2n_n2s",
  `!c2n n2c b n. 1 < b /\ (!x. x < b ==> (c2n (n2c x) = x)) ==>
      (s2n b c2n (n2s b n2c n) = n)`,
  SRW_TAC [] [s2n_def, n2s_def, MAP_MAP_o]
    \\ `MAP (c2n o n2c) (n2l b n) = n2l b n`
    by MATCH_MP_TAC MAP_ID
    \\ SRW_TAC [ARITH_ss] [l2n_n2l]
    \\ `!x. ($> b) x ==> (\x. c2n (n2c x) = x) x` by METIS_TAC [GREATER_DEF]
    \\ IMP_RES_TAC EVERY_MONOTONIC
    \\ POP_ASSUM MATCH_MP_TAC
    \\ METIS_TAC [n2l_BOUND, DECIDE ``1 < b ==> 0 < b``]);

(* ......................................................................... *)

val MAP_TAKE = Q.prove(
  `!f n l. MAP f (TAKE n l) = TAKE n (MAP f l)`,
  Induct_on `l` \\ SRW_TAC [] []);

val REVERSE_LASTN = Q.prove(
  `!n l. n <= LENGTH l ==> (LASTN n l = REVERSE (TAKE n (REVERSE l)))`,
  SRW_TAC [] [FIRSTN_REVERSE]);

val n2s_s2n = Q.store_thm("n2s_s2n",
  `!c2n n2c b s.
     1 < b /\ EVERY ($> b o c2n) s ==>
     (n2s b n2c (s2n b c2n s) =
       if s2n b c2n s = 0 then STRING (n2c 0) ""
       else MAP (n2c o c2n) (LASTN (SUC (LOG b (s2n b c2n s))) s))`,
  SRW_TAC [] [s2n_def, n2s_def]
    >> SRW_TAC [ARITH_ss] [l2n_def, Once n2l_def]
    \\ Q.ABBREV_TAC `l = MAP c2n (REVERSE s)`
    \\ `~(l = [])` by (STRIP_TAC \\ FULL_SIMP_TAC std_ss [l2n_def])
    \\ `EVERY ($> b) l` by (Q.UNABBREV_TAC `l`
          \\ SRW_TAC [] [EVERY_MAP, ALL_EL_REVERSE,
                         simpLib.SIMP_PROVE std_ss [FUN_EQ_THM]
                           ``(\x:char. b:num > c2n x) = ($> b o c2n)``])
    \\ SRW_TAC [] [n2l_l2n]
    \\ IMP_RES_TAC LENGTH_l2n
    \\ `SUC (LOG b (l2n b l)) <= LENGTH s`
    by METIS_TAC [LENGTH_MAP, LENGTH_REVERSE]
    \\ Q.UNABBREV_TAC `l`
    \\ SRW_TAC [] [GSYM MAP_REVERSE, REVERSE_LASTN, GSYM MAP_TAKE, MAP_MAP_o]);

(* ----------------------------------------------------------------------
    toString and toNum as overloads for the above (decimal notation)
   ---------------------------------------------------------------------- *)

val _ = overload_on ("toString", ``num_to_dec_string``)
val _ = overload_on ("toNum", ``num_from_dec_string``)

val toNum_toString = store_thm(
  "toNum_toString",
  ``!n. toNum (toString n) = n``,
  STRIP_TAC THEN
  SRW_TAC [][num_to_dec_string_def, num_from_dec_string_def] THEN
  MATCH_MP_TAC s2n_n2s THEN SIMP_TAC (srw_ss()) [] THEN
  Q.X_GEN_TAC `n` THEN STRIP_TAC THEN
  `(n = 0) \/ (n = 1) \/ (n = 2) \/ (n = 3) \/ (n = 4) \/
   (n = 5) \/ (n = 6) \/ (n = 7) \/ (n = 8) \/ (n = 9)` by DECIDE_TAC THEN
  SRW_TAC [][HEX_def, UNHEX_def]);
val toString_toNum_cancel = save_thm("toString_toNum_cancel", toNum_toString)

val toString_inj = store_thm(
  "toString_inj",
   ``!n m. (toString n = toString m) = (n = m)``,
   METIS_TAC [toNum_toString])
val toString_11 = save_thm("toString_11", toString_inj)
val _ = export_rewrites ["toString_inj"]

val STRCAT_toString_inj = store_thm
  ("STRCAT_toString_inj",
   ``!n m s. (STRCAT s (toString n) = STRCAT s (toString m)) = (n = m)``,
   SRW_TAC [] []);


val _ = export_theory ();
