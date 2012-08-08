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

open HolKernel Parse boolLib bossLib metisLib arithmeticTheory
     listTheory combinTheory pairTheory
     numTheory simpLib
     stringTheory rich_listTheory stringSimps
     listSimps

open logrootTheory


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

val l2n_def = Define`
  (l2n b [] = 0) /\
  (l2n b (h::t) = h MOD b + b * l2n b t)`;

val n2l_def = Define`
  n2l b n = if n < b \/ b < 2 then [n MOD b] else n MOD b :: n2l b (n DIV b)`;

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

val num_from_bin_list_def = Define `num_from_bin_list = l2n 2`;
val num_from_oct_list_def = Define `num_from_oct_list = l2n 8`;
val num_from_dec_list_def = Define `num_from_dec_list = l2n 10`;
val num_from_hex_list_def = Define `num_from_hex_list = l2n 16`;

val num_to_bin_list_def = Define `num_to_bin_list = n2l 2`;
val num_to_oct_list_def = Define `num_to_oct_list = n2l 8`;
val num_to_dec_list_def = Define `num_to_dec_list = n2l 10`;
val num_to_hex_list_def = Define `num_to_hex_list = n2l 16`;

val num_from_bin_string_def = Define `num_from_bin_string = s2n 2 UNHEX`;
val num_from_oct_string_def = Define `num_from_oct_string = s2n 8 UNHEX`;
val num_from_dec_string_def = Define `num_from_dec_string = s2n 10 UNHEX`;
val num_from_hex_string_def = Define `num_from_hex_string = s2n 16 UNHEX`;

val num_to_bin_string_def = Define `num_to_bin_string = n2s 2 HEX`;
val num_to_oct_string_def = Define `num_to_oct_string = n2s 8 HEX`;
val num_to_dec_string_def = Define `num_to_dec_string = n2s 10 HEX`;
val num_to_hex_string_def = Define `num_to_hex_string = n2s 16 HEX`;

infix \\ << >>

val op \\ = op THEN;
val op << = op THENL;
val op >> = op THEN1;

val LENGTH_n2l = Q.store_thm("LENGTH_n2l",
  `!b n. 1 < b ==> (LENGTH (n2l b n) = if n = 0 then 1 else SUC (LOG b n))`,
  completeInduct_on `LOG b n`
    \\ SRW_TAC [ARITH_ss] [Once n2l_def, LOG_RWT]
    \\ SRW_TAC [ARITH_ss] [LOG_RWT]
    \\ `0 < n DIV b` by SRW_TAC [ARITH_ss] [X_LT_DIV]
    \\ DECIDE_TAC);

val LOG_DIV_LESS = Q.prove(
  `!b n. b <= n /\ 1 < b ==> LOG b (n DIV b) < LOG b n`,
  SRW_TAC [] [] \\ IMP_RES_TAC LOG_DIV \\ DECIDE_TAC);

val l2n_n2l = Q.store_thm("l2n_n2l",
  `!b n. 1 < b ==> (l2n b (n2l b n) = n)`,
  completeInduct_on `LOG b n`
    \\ SRW_TAC [ARITH_ss] [Once n2l_def, l2n_def]
    \\ `LOG b (n DIV b) < LOG b n` by SRW_TAC [ARITH_ss] [LOG_DIV_LESS]
    \\ SRW_TAC [ARITH_ss] [(GSYM o ONCE_REWRITE_RULE [MULT_COMM]) DIVISION]);

val l2n_lt = Q.store_thm("l2n_lt",
  `!l b. 0 < b ==> l2n b l < b ** LENGTH l`,
  Induct \\ SRW_TAC [] [l2n_def, arithmeticTheory.EXP]
  \\ RES_TAC
  \\ IMP_RES_TAC arithmeticTheory.LESS_ADD_1
  \\ POP_ASSUM (K ALL_TAC)
  \\ POP_ASSUM SUBST1_TAC
  \\ SRW_TAC [] [arithmeticTheory.LEFT_ADD_DISTRIB]
  \\ SRW_TAC [ARITH_ss]
       [arithmeticTheory.MOD_LESS, DECIDE ``a < b:num ==> (a < b + c)``])

(* ......................................................................... *)

val LENGTH_l2n = Q.store_thm("LENGTH_l2n",
  `!b l. 1 < b /\ EVERY ($> b) l /\ ~(l2n b l = 0) ==>
     (SUC (LOG b (l2n b l)) <= LENGTH l)`,
  Induct_on `l` \\ SRW_TAC [ARITH_ss] [l2n_def, GREATER_DEF]
    << [ALL_TAC, `~(h = 0)` by (`0 < b` by DECIDE_TAC \\ STRIP_TAC
          \\ IMP_RES_TAC ZERO_MOD \\ FULL_SIMP_TAC arith_ss [])]
    \\ `0 < h + b * l2n b l`
    by (IMP_RES_TAC (simpLib.SIMP_PROVE arith_ss [LESS_MULT2]
         ``1 < b /\ ~(c = 0) ==> 0 < b * c``) \\ SRW_TAC [ARITH_ss] [])
    \\ SRW_TAC [ARITH_ss] [LOG_RWT, LESS_DIV_EQ_ZERO,
         SIMP_RULE arith_ss [] ADD_DIV_ADD_DIV]
    << [Cases_on `l` \\ FULL_SIMP_TAC (arith_ss++listSimps.LIST_ss) [l2n_def],
        SRW_TAC [ARITH_ss] [(GSYM o REWRITE_RULE [GSYM SUC_ONE_ADD]) LOG_DIV],
        `~(l2n b l = 0)` by (STRIP_TAC \\ FULL_SIMP_TAC arith_ss [])
          \\ SRW_TAC [] []]);

val EL_TAKE = Q.store_thm("EL_TAKE",
  `!x n l. x < n /\ n <= LENGTH l ==> (EL x (TAKE n l) = EL x l)`,
  Induct_on `l` \\ Cases_on `x` \\ SRW_TAC [ARITH_ss] []);

val l2n_DIGIT = Q.store_thm("l2n_DIGIT",
  `!b l x. 1 < b /\ EVERY ($> b) l /\ x < LENGTH l ==>
      ((l2n b l DIV b ** x) MOD b = EL x l)`,
  Induct_on `l` \\ SRW_TAC [ARITH_ss] [l2n_def, GREATER_DEF]
    \\ Cases_on `x`
    \\ SRW_TAC [ARITH_ss]
        [EXP, GSYM DIV_DIV_DIV_MULT, ZERO_LT_EXP, LESS_DIV_EQ_ZERO,
         SIMP_RULE arith_ss [] (CONJ MOD_TIMES ADD_DIV_ADD_DIV)]);

val DIV_0_IMP_LT = Q.store_thm("DIV_0_IMP_LT",
  `!b n. 1 < b /\ (n DIV b = 0) ==> n < b`,
  REPEAT STRIP_TAC \\ SPOSE_NOT_THEN ASSUME_TAC
    \\ FULL_SIMP_TAC std_ss [NOT_LESS]
    \\ IMP_RES_TAC LESS_EQUAL_ADD
    \\ `0 < b` by DECIDE_TAC
    \\ IMP_RES_TAC ADD_DIV_ADD_DIV
    \\ POP_ASSUM (Q.SPECL_THEN [`1`,`p`] (ASSUME_TAC o SIMP_RULE std_ss []))
    \\ FULL_SIMP_TAC arith_ss []);

val lem = Q.prove(
  `!b n. 1 < b ==> PRE (LENGTH (n2l b n)) <= LENGTH (n2l b (n DIV b))`,
  SRW_TAC [ARITH_ss] [LENGTH_n2l]
    << [
      `0 <= n DIV b /\ 0 < n` by DECIDE_TAC
        \\ IMP_RES_TAC DIV_0_IMP_LT
        \\ SRW_TAC [ARITH_ss] [LOG_RWT],
      IMP_RES_TAC (METIS_PROVE [LESS_DIV_EQ_ZERO,NOT_LESS_EQUAL]
         ``!b n. 1 < b /\ ~(n DIV b = 0) ==> b <= n``)
        \\ SRW_TAC [ARITH_ss] [LOG_DIV]]);

val EL_n2l = Q.store_thm("EL_n2l",
  `!b x n. 1 < b /\ x < LENGTH (n2l b n) ==>
     (EL x (n2l b n) = (n DIV (b ** x)) MOD b)`,
  completeInduct_on `LOG b n`
    \\ SRW_TAC [] []
    \\ ONCE_REWRITE_TAC [n2l_def]
    \\ SRW_TAC [ARITH_ss] []
    << [
      IMP_RES_TAC LENGTH_n2l
        \\ Cases_on `n = 0`
        \\ FULL_SIMP_TAC arith_ss []
        << [ALL_TAC, `LOG b n = 0` by SRW_TAC [ARITH_ss] [LOG_RWT]]
        \\ `x = 0` by DECIDE_TAC \\ SRW_TAC [ARITH_ss] [EXP],
      Cases_on `x = 0`
        \\ SRW_TAC [ARITH_ss] [EXP, EL_CONS]
        \\ `LOG b (n DIV b) < LOG b n /\ PRE x < x /\ 0 < x`
        by SRW_TAC [ARITH_ss] [LOG_DIV_LESS]
        \\ `PRE x < LENGTH (n2l b (n DIV b))`
        by METIS_TAC [lem, INV_PRE_LESS, LESS_LESS_EQ_TRANS]
        \\ RES_TAC
        \\ POP_ASSUM (Q.SPECL_THEN [`n DIV b`,`b`]
             (ASSUME_TAC o SIMP_RULE std_ss []))
        \\ POP_ASSUM (Q.SPEC_THEN `PRE x` IMP_RES_TAC)
        \\ SRW_TAC [ARITH_ss] [GSYM EXP, DIV_DIV_DIV_MULT,
             DECIDE ``!n. 0 < n ==> (SUC (PRE n) = n)``]]);

val LIST_EQ = Q.prove(
  `!a b. (LENGTH a = LENGTH b) /\
         (!x. x < LENGTH a ==> (EL x a = EL x b)) ==>
         (a = b)`,
  Induct_on `a` \\ Induct_on `b` \\ SRW_TAC [] []
    \\ METIS_TAC [prim_recTheory.LESS_0, LESS_MONO_EQ, EL, HD, TL]);

val n2l_l2n = Q.prove(
  `!b n l. 1 < b /\ EVERY ($> b) l /\ (n = l2n b l) ==>
      (n2l b n = if n = 0 then [0] else TAKE (SUC (LOG b n)) l)`,
  SRW_TAC [] [] >> SRW_TAC [ARITH_ss] [Once n2l_def]
    \\ MATCH_MP_TAC LIST_EQ \\ IMP_RES_TAC LENGTH_l2n
    \\ SRW_TAC [ARITH_ss] [LENGTH_n2l,LENGTH_TAKE,EL_TAKE,EL_n2l,l2n_DIGIT]);

val n2l_l2n = save_thm("n2l_l2n",
  n2l_l2n |> Q.SPECL [`b`,`l2n b l`,`l`]
          |> REWRITE_RULE []
          |> Q.GEN `l` |> Q.GEN `b`);

(* ------------------------------------------------------------------------- *)

val MAP_ID = Q.prove(
  `!l. EVERY (\x. f x = x) l ==> (MAP f l = l)`,
  Induct \\ SRW_TAC [] []);

val n2l_BOUND = Q.store_thm("n2l_BOUND",
  `!b n. 0 < b ==> EVERY ($> b) (n2l b n)`,
  NTAC 2 STRIP_TAC \\ completeInduct_on `LOG b n`
    \\ SRW_TAC [ARITH_ss] [Once n2l_def, GREATER_DEF]
    \\ `LOG b (n DIV b) < LOG b n` by SRW_TAC [ARITH_ss] [LOG_DIV_LESS]
    \\ SRW_TAC [ARITH_ss] []);

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

(* ------------------------------------------------------------------------- *)
(* ------------------------------------------------------------------------- *)

val rec_toString_def = Define
  `(rec_toString (0:num) = []) /\
   (rec_toString (SUC n) =
	(rec_toString ((SUC n) DIV 10)) ++ [CHR (48 + ((SUC n) MOD 10))])`;

val toString_def = Define
   `toString n = if (n = 0) then "0" else rec_toString n`;

val rec_toNum_def = Define
  `(rec_toNum [] n = 0:num) /\
   (rec_toNum (c::cs) n = (10**n) * ((ORD c) - 48) + rec_toNum cs (SUC n))`;

val toNum_def = Define `toNum s = rec_toNum (REVERSE s) 0`;

(* ------------------------------------------------------------------------- *)
(* ------------------------------------------------------------------------- *)

val op++ = Tactical.THEN
val op>> = Tactical.THEN1

val append_neq_lem = prove
  (``!m l. (~(l = [])) ==> (~(l ++ m = m))``,
   REPEAT STRIP_TAC
   ++ `LENGTH m = LENGTH (l ++ m)` by RW_TAC std_ss []
   ++ Cases_on `m` >> FULL_SIMP_TAC list_ss [APPEND_NIL]
   ++ Q.PAT_ASSUM `l ++ h::t = h::t` (K ALL_TAC)
   ++ FULL_SIMP_TAC arith_ss [LENGTH_APPEND, LENGTH, GSYM LENGTH_NIL]);

val append_sing_eq_lem = prove
  (``!l l' x x'. (l ++ [x] = l' ++ [x']) = ((l = l') /\ (x = x'))``,
   RW_TAC std_ss [GSYM SNOC_APPEND, SNOC_11] ++ DECIDE_TAC);

val STRCAT_NEQ = store_thm
  ("STRCAT_NEQ",
   ``!s1 s1'.
	~(s1 = "") /\ ~ (s1' = "") /\
	~IS_PREFIX s1 s1' /\ ~IS_PREFIX s1' s1 ==>
	!s2 s2'. ~(STRCAT s1 s2 = STRCAT s1' s2')``,
  Induct THEN1 SIMP_TAC (srw_ss()) [] THEN
  REPEAT GEN_TAC THEN Cases_on `s1'` THEN SIMP_TAC (srw_ss()) [] THEN
  Cases_on `h = h'` THEN ASM_SIMP_TAC (srw_ss()) [] THEN
  MAP_EVERY Cases_on [`s1 = ""`, `t = ""`] THEN ASM_SIMP_TAC (srw_ss()) []);

(* ------------------------------------------------------------------------- *)
(* ------------------------------------------------------------------------- *)

val toString_inj = store_thm
  ("toString_inj",
   ``!n m. (toString n = toString m) = (n = m)``,
   completeInduct_on `n`
   ++ REPEAT STRIP_TAC
   ++ Cases_on `n`
   >> (Cases_on `m` ++ RW_TAC arith_ss []
       ++ RW_TAC std_ss [toString_def]
       ++ SRW_TAC [] [rec_toString_def]
       ++ Cases_on `SUC n MOD 10 = 0`
       >> (SRW_TAC [] []
	   ++ Cases_on `SUC n DIV 10`
	   >> (METIS_TAC [SUC_NOT,MULT_EQ_0, ADD_0, ADD_COMM,
	      		  MATCH_MP DIVISION (DECIDE ``0:num < 10:num``)])
	   ++ RW_TAC string_ss [rec_toString_def,IMPLODE_EQ_THM]
	   ++ MATCH_MP_TAC append_neq_lem
	   ++ RW_TAC list_ss [])
       ++ Cases_on `rec_toString (SUC n DIV 10)`
       >> (SRW_TAC [] [CHAR_EQ_THM]
	   ++ `ORD (CHR (48 + SUC n MOD 10)) = 48 + SUC n MOD 10`
		by (RW_TAC std_ss [GSYM ORD_CHR]
		    ++ MATCH_MP_TAC LESS_LESS_EQ_TRANS ++ Q.EXISTS_TAC `48 + 10:num`
		    ++ RW_TAC arith_ss [LT_ADD_LCANCEL,
		       	      	        MATCH_MP DIVISION (DECIDE ``0:num < 10:num``)])
	   ++ RW_TAC arith_ss [])
       ++ RW_TAC string_ss [rec_toString_def,IMPLODE_EQ_THM])
   ++ Cases_on `m`
   >> (RW_TAC std_ss [toString_def]
       ++ RW_TAC string_ss [rec_toString_def,IMPLODE_EQ_THM]
       ++ Cases_on `SUC n' MOD 10 = 0`
       >> (SRW_TAC [] []
	   ++ Cases_on `SUC n' DIV 10`
	   >> (METIS_TAC [SUC_NOT,MULT_EQ_0, ADD_0, ADD_COMM,
	      		  MATCH_MP DIVISION (DECIDE ``0:num < 10:num``)])
	   ++ SRW_TAC [] [rec_toString_def] ++ MATCH_MP_TAC append_neq_lem
	   ++ RW_TAC list_ss [])
       ++ Cases_on `rec_toString (SUC n' DIV 10)`
       >> (SRW_TAC [] [CHAR_EQ_THM]
	   ++ `ORD (CHR (48 + SUC n' MOD 10)) = 48 + SUC n' MOD 10`
		by (RW_TAC std_ss [GSYM ORD_CHR]
		    ++ MATCH_MP_TAC LESS_LESS_EQ_TRANS ++ Q.EXISTS_TAC `48 + 10:num`
		    ++ RW_TAC arith_ss [LT_ADD_LCANCEL,
		       	      	        MATCH_MP DIVISION (DECIDE ``0:num < 10:num``)])
           ++ ONCE_REWRITE_TAC [ADD_COMM]
	   ++ RW_TAC arith_ss [])
       ++ SPOSE_NOT_THEN STRIP_ASSUME_TAC
       ++ `LENGTH (h::t ++ [CHR (SUC n' MOD 10 + 48)]) = LENGTH [#"0"]`
		by ASM_SIMP_TAC bool_ss []
       ++ Q.PAT_ASSUM `h::t ++ [CHR (SUC n' MOD 10 + 48)] = [#"0"]` (K ALL_TAC)
       ++ FULL_SIMP_TAC arith_ss [LENGTH_APPEND, LENGTH, GSYM LENGTH_NIL])
   ++ EQ_TAC
   >> (RW_TAC std_ss [toString_def, rec_toString_def, IMPLODE_11]
       ++ ONCE_REWRITE_TAC [DECIDE ``(n' = n) = (SUC n' = SUC n)``]
       ++ `(SUC n' = SUC n) =
       	   ((SUC n') DIV 10 * 10 + (SUC n') MOD 10 = (SUC n) DIV 10 * 10 + (SUC n) MOD 10)`
		by METIS_TAC [MATCH_MP DIVISION (DECIDE ``0:num < 10:num``)]
       ++ POP_ORW
       ++ FULL_SIMP_TAC std_ss [append_sing_eq_lem]
       ++ (MP_TAC o Q.SPECL [`48 + SUC n' MOD 10`, `48 + SUC n MOD 10`]) CHR_11
       ++ `!n. 48 + SUC n MOD 10 < 256`
		by (STRIP_TAC ++ MATCH_MP_TAC LESS_LESS_EQ_TRANS
		    ++ Q.EXISTS_TAC `48 + 10:num`
		    ++ RW_TAC arith_ss [LT_ADD_LCANCEL, MATCH_MP
       		       	      	        DIVISION (DECIDE ``0:num < 10:num``)])
       ++ RW_TAC arith_ss [EQ_MULT_LCANCEL]
       ++ Cases_on `SUC n' DIV 10`
       >> (Cases_on `SUC n DIV 10` ++ RW_TAC arith_ss []
	   ++ FULL_SIMP_TAC std_ss [rec_toString_def]
	   ++ `LENGTH ([]:char list) = LENGTH (rec_toString (SUC n'' DIV 10)
						++ [CHR (48 + SUC n'' MOD 10)])`
		by METIS_TAC []
	   ++ Q.PAT_ASSUM `[] = rec_toString (SUC n'' DIV 10)
	      		      	++ [CHR (48 + SUC n'' MOD 10)]` (K ALL_TAC)
	   ++ FULL_SIMP_TAC arith_ss [LENGTH_APPEND, LENGTH, GSYM LENGTH_NIL])
       ++ Cases_on `SUC n DIV 10`
       >> (RW_TAC arith_ss []
	   ++ FULL_SIMP_TAC std_ss [rec_toString_def]
	   ++ `LENGTH ([]:char list) =
	       LENGTH (rec_toString (SUC n'' DIV 10) ++ [CHR (48 + SUC n'' MOD 10)])`
		by METIS_TAC []
	   ++ Q.PAT_ASSUM `rec_toString (SUC n'' DIV 10)
	      		   ++ [CHR (48 + SUC n'' MOD 10)] = []` (K ALL_TAC)
	   ++ FULL_SIMP_TAC arith_ss [LENGTH_APPEND, LENGTH, GSYM LENGTH_NIL])
       ++ `SUC n' DIV 10 < SUC n'`
		by (MATCH_MP_TAC DIV_LESS ++ RW_TAC arith_ss [])
       ++ Suff `toString (SUC n'') = toString (SUC n''')` >> METIS_TAC []
       ++ SIMP_TAC arith_ss [toString_def, IMPLODE_11]
       ++ ASM_REWRITE_TAC [])
   ++ RW_TAC std_ss []);

val STRCAT_toString_inj = store_thm
  ("STRCAT_toString_inj",
   ``!n m s. (STRCAT s (toString n) = STRCAT s (toString m)) = (n = m)``,
   SRW_TAC [] [toString_inj]);

(* ------------------------------------------------------------------------- *)
(* ------------------------------------------------------------------------- *)

val toString_toNum_cancel = store_thm
  ("toString_toNum_cancel",
   ``!n. toNum(toString n) = n``,
   completeInduct_on `n`
   ++ Cases_on `n`
   >> (SRW_TAC [] [toString_def, toNum_def, rec_toNum_def])
   ++ SRW_TAC [] [toString_def, rec_toString_def, toNum_def, rec_toNum_def,
  		 GSYM SNOC_APPEND, REVERSE_SNOC]
   ++ Q.SPECL_THEN  [`48 + SUC n' MOD 10`] MP_TAC ORD_CHR
   ++ `!n. 48 + SUC n MOD 10 < 256`
	by (STRIP_TAC ++ MATCH_MP_TAC LESS_LESS_EQ_TRANS ++ Q.EXISTS_TAC `48 + 10:num`
	    ++ RW_TAC arith_ss [LT_ADD_LCANCEL, MATCH_MP
	       	      	        DIVISION (DECIDE ``0:num < 10:num``)])
   ++ RW_TAC arith_ss []
   ++ Suff `SUC n' MOD 10 + rec_toNum (REVERSE (rec_toString (SUC n' DIV 10))) 1 =
		SUC n' MOD 10 + (SUC n' DIV 10) * 10`
   >> METIS_TAC [ADD_COMM, MATCH_MP DIVISION (DECIDE ``0:num < 10:num``)]
   ++ SRW_TAC [][]
   ++ `SUC n' DIV 10 < SUC n'`
		by (MATCH_MP_TAC DIV_LESS ++ RW_TAC arith_ss [])
   ++ Suff `rec_toNum (REVERSE (rec_toString (SUC n' DIV 10))) 1 =
		10 * (toNum (toString (SUC n' DIV 10)))`
   >> METIS_TAC [MULT_COMM]
   ++ POP_ASSUM (K ALL_TAC)
   ++ POP_ASSUM (K ALL_TAC)
   ++ POP_ASSUM (K ALL_TAC)
   ++ Cases_on `SUC n' DIV 10`
   >> SRW_TAC [] [toString_def, toNum_def, rec_toNum_def, rec_toString_def]
   ++ Q.ABBREV_TAC `Q = rec_toNum (REVERSE (rec_toString (SUC n))) 1`
   ++ SRW_TAC [] [toString_def, toNum_def]
   ++ Q.UNABBREV_TAC `Q`
   ++ POP_ASSUM (K ALL_TAC)
   ++ Suff `!n m. rec_toNum (REVERSE (rec_toString (SUC n))) (SUC m) =
		      10 * rec_toNum (REVERSE (rec_toString (SUC n))) m`
   >> METIS_TAC [ONE]
   ++ completeInduct_on `SUC n`
   ++ SRW_TAC [] [toString_def, rec_toString_def, toNum_def, rec_toNum_def,
   		  GSYM SNOC_APPEND, REVERSE_SNOC, LEFT_ADD_DISTRIB]
   ++ ONCE_REWRITE_TAC [EXP]
   ++ RW_TAC arith_ss [EQ_ADD_LCANCEL]
   ++ `SUC n DIV 10 < SUC n`
   	by (MATCH_MP_TAC DIV_LESS ++ RW_TAC arith_ss [])
   ++ Cases_on `SUC n DIV 10`
   >> SRW_TAC [] [toString_def, toNum_def, rec_toNum_def, rec_toString_def]
   ++ Q.PAT_ASSUM `!m. m < SUC n ==> !n. b` (MP_TAC o Q.SPECL [`SUC n''`])
   ++ RW_TAC std_ss []);

(* ------------------------------------------------------------------------- *)
(* ------------------------------------------------------------------------- *)

val _ = export_theory ();
