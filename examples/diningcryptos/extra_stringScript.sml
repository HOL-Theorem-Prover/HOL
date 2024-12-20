(* ========================================================================= *)
(* Create "extra_stringTheory" for toString automation and definitions       *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Load and open relevant theories                                           *)
(* (Comment out "load" and "loadPath"s for compilation)                      *)
(* ------------------------------------------------------------------------- *)
(*

app load ["bossLib", "metisLib", "arithmeticTheory",
          "listTheory", "hurdUtils", "combinTheory", "pairTheory",
          "extra_boolTheory", "jrhUtils", "numTheory", "simpLib",
          "stringTheory", "rich_listTheory",
          "stringSimps", "listSimps", "extra_numTheory"];

*)

open HolKernel Parse boolLib bossLib metisLib arithmeticTheory
     listTheory hurdUtils extra_numTheory combinTheory pairTheory
     extra_boolTheory jrhUtils numTheory simpLib
     stringTheory rich_listTheory stringSimps
     listSimps;

(* ------------------------------------------------------------------------- *)
(* Start a new theory called "information"                                   *)
(* ------------------------------------------------------------------------- *)

val _ = new_theory "extra_string";

(* ------------------------------------------------------------------------- *)
(* Helpful proof tools                                                       *)
(* ------------------------------------------------------------------------- *)

val REVERSE = Tactical.REVERSE;
val Suff = PARSE_TAC SUFF_TAC;


val POP_ORW = POP_ASSUM (fn thm => ONCE_REWRITE_TAC [thm]);

val safe_list_ss = (simpLib.++ (bool_ss, LIST_ss));

val safe_string_ss = (simpLib.++ (bool_ss, STRING_ss));

val arith_string_ss = (simpLib.++ (arith_ss, STRING_ss));

val string_ss = (simpLib.++ (list_ss, STRING_ss));

(* ------------------------------------------------------------------------- *)
(* ------------------------------------------------------------------------- *)

val rec_toString_def = Define
  `(rec_toString (0:num) = []) /\
   (rec_toString (SUC n) =
        (rec_toString ((SUC n) DIV 10)) ++ [CHR (48 + ((SUC n) MOD 10))])`;

val toString_def = Define
   `toString n = if (n = 0) then "0" else IMPLODE (rec_toString n)`;

val rec_toNum_def = Define
  `(rec_toNum [] n = 0:num) /\
   (rec_toNum (c::cs) n = (10**n) * ((ORD c) - 48) + rec_toNum cs (SUC n))`;

val toNum_def = Define
   `toNum s = rec_toNum (REVERSE (EXPLODE s)) 0`;

(* ------------------------------------------------------------------------- *)
(* ------------------------------------------------------------------------- *)

val STRCAT1 = store_thm
  ("STRCAT1",
   ``!s1 s2. STRCAT s1 s2 = IMPLODE (EXPLODE s1 ++ EXPLODE s2)``,
   Induct_on `s1` THEN SRW_TAC [][STRCAT_def]);

val append_neq_lem = prove
  (``!m l. (~(l = [])) ==> (~(l ++ m = m))``,
   REPEAT STRIP_TAC
   >> `LENGTH m = LENGTH (l ++ m)` by RW_TAC std_ss []
   >> Cases_on `m` >- FULL_SIMP_TAC list_ss [APPEND_NIL]
   >> Q.PAT_ASSUM `l ++ h::t = h::t` (K ALL_TAC)
   >> FULL_SIMP_TAC arith_ss [LENGTH_APPEND, LENGTH, GSYM LENGTH_NIL]);

val append_sing_eq_lem = prove
  (``!l l' x x'. (l ++ [x] = l' ++ [x']) = ((l = l') /\ (x = x'))``,
   RW_TAC std_ss [GSYM SNOC_APPEND, SNOC_11] >> DECIDE_TAC);

val IMPLODE_APPEND_EQ = store_thm
  ("IMPLODE_APPEND_EQ",
   ``!s1 s2 s1' s2'.
        (IMPLODE (s1 ++ s2) = IMPLODE (s1' ++ s2')) =
        (s1 ++ s2 = s1' ++ s2')``,
   Induct
   >- (Induct >- (RW_TAC std_ss [APPEND_NIL, IMPLODE_EQ_EMPTYSTRING, IMPLODE_EQNS]
                  >> RW_TAC bool_ss [EQ_SYM_EQ])
       >> FULL_SIMP_TAC std_ss [APPEND_NIL, IMPLODE_EQNS, IMPLODE_EQ_THM, EXPLODE_IMPLODE]
       >> RW_TAC bool_ss [EQ_SYM_EQ])
   >> FULL_SIMP_TAC std_ss [APPEND, IMPLODE_EQNS, IMPLODE_EQ_THM, EXPLODE_IMPLODE]
   >> RW_TAC bool_ss [EQ_SYM_EQ]);

val STRCAT_NEQ = store_thm
  ("STRCAT_NEQ",
   ``!s1 s1'.
        (~ (s1 = "")) /\ (~ (s1' = "")) /\
        (~ (IS_PREFIX (EXPLODE s1) (EXPLODE s1'))) /\
        (~ (IS_PREFIX (EXPLODE s1') (EXPLODE s1))) ==>
        (!s2 s2'. ~(STRCAT s1 s2 = STRCAT s1' s2'))``,
   STRIP_TAC >> STRIP_TAC
   >> (ASSUME_TAC o Q.SPEC `s1`) IMPLODE_ONTO
   >> FULL_SIMP_TAC std_ss [] >> POP_ASSUM (K ALL_TAC)
   >> (ASSUME_TAC o Q.SPEC `s1'`) IMPLODE_ONTO
   >> FULL_SIMP_TAC std_ss [] >> POP_ASSUM (K ALL_TAC)
   >> RW_TAC std_ss [EXPLODE_IMPLODE, IMPLODE_EQ_EMPTYSTRING]
   >> (ASSUME_TAC o Q.SPEC `s2`) IMPLODE_ONTO
   >> FULL_SIMP_TAC std_ss [] >> POP_ASSUM (K ALL_TAC)
   >> (ASSUME_TAC o Q.SPEC `s2'`) IMPLODE_ONTO
   >> FULL_SIMP_TAC std_ss [] >> POP_ASSUM (K ALL_TAC)
   >> RW_TAC std_ss [EXPLODE_IMPLODE, Once STRCAT1, IMPLODE_APPEND_EQ]
   >> Q.ABBREV_TAC `foo = IMPLODE (STRCAT cs cs'')`
   >> RW_TAC std_ss [EXPLODE_IMPLODE, Once STRCAT1, IMPLODE_APPEND_EQ]
   >> Q.UNABBREV_TAC `foo`
   >> RW_TAC std_ss [EXPLODE_IMPLODE, IMPLODE_APPEND_EQ]
   >> SPOSE_NOT_THEN STRIP_ASSUME_TAC
   >> (ASSUME_TAC o Q.ISPECL [`LENGTH (cs:char list)`,
                              `LENGTH (cs':char list)`]) LESS_EQ_CASES
   >> FULL_SIMP_TAC std_ss []
   >- ((ASSUME_TAC o Q.ISPEC `(cs''':char list)` o
        UNDISCH o Q.ISPECL [`LENGTH (cs:char list)`,`(cs':char list)`])
        FIRSTN_APPEND1
       >> `FIRSTN (LENGTH (cs:char list)) (cs':char list) = cs`
          by METIS_TAC [FIRSTN_APPEND1, LESS_EQ_REFL, FIRSTN_LENGTH_ID]
       >> FULL_SIMP_TAC std_ss [LESS_EQ_EXISTS]
       >> (ASSUME_TAC o UNDISCH o REWRITE_RULE [Once EQ_SYM_EQ, Once ADD_COMM]
           o Q.ISPECL [`p:num`, `LENGTH (cs:char list)`,`(cs':char list)`] )
           APPEND_FIRSTN_LASTN
       >> FULL_SIMP_TAC std_ss [IS_PREFIX_APPEND]
       >> METIS_TAC [])
   >> (ASSUME_TAC o Q.ISPEC `(cs'':char list)` o
       UNDISCH o Q.ISPECL [`LENGTH (cs':char list)`,`(cs:char list)`]) FIRSTN_APPEND1
   >> `FIRSTN (LENGTH (cs':char list)) (cs:char list) = cs'`
      by METIS_TAC [FIRSTN_APPEND1, LESS_EQ_REFL, FIRSTN_LENGTH_ID]
   >> FULL_SIMP_TAC std_ss [LESS_EQ_EXISTS]
   >> (ASSUME_TAC o UNDISCH o REWRITE_RULE [Once EQ_SYM_EQ, Once ADD_COMM]
           o Q.ISPECL [`p:num`, `LENGTH (cs':char list)`,`(cs:char list)`])
       APPEND_FIRSTN_LASTN
   >> FULL_SIMP_TAC std_ss [IS_PREFIX_APPEND]
   >> METIS_TAC []);


(* ------------------------------------------------------------------------- *)
(* ------------------------------------------------------------------------- *)

val toString_inj = store_thm
  ("toString_inj",
   ``!n m. (toString n = toString m) = (n = m)``,
   completeInduct_on `n`
   >> REPEAT STRIP_TAC
   >> Cases_on `n`
   >- (Cases_on `m` >> RW_TAC arith_ss []
       >> RW_TAC std_ss [toString_def]
       >> SRW_TAC [] [rec_toString_def]
       >> Cases_on `SUC n MOD 10 = 0`
       >- (SRW_TAC [] []
           >> Cases_on `SUC n DIV 10`
           >- (METIS_TAC [SUC_NOT,MULT_EQ_0, ADD_0, ADD_COMM,
                          MATCH_MP DIVISION (DECIDE ``0:num < 10:num``)])
           >> RW_TAC string_ss [rec_toString_def,IMPLODE_EQ_THM]
           >> MATCH_MP_TAC append_neq_lem
           >> RW_TAC list_ss [])
       >> Cases_on `rec_toString (SUC n DIV 10)`
       >- (SRW_TAC [] [CHAR_EQ_THM]
           >> `ORD (CHR (48 + SUC n MOD 10)) = 48 + SUC n MOD 10`
                by (RW_TAC std_ss [GSYM ORD_CHR]
                    >> MATCH_MP_TAC LESS_LESS_EQ_TRANS >> Q.EXISTS_TAC `48 + 10:num`
                    >> RW_TAC arith_ss [LT_ADD_LCANCEL,
                                        MATCH_MP DIVISION (DECIDE ``0:num < 10:num``)])
           >> RW_TAC arith_ss [])
       >> RW_TAC string_ss [rec_toString_def,IMPLODE_EQ_THM])
   >> Cases_on `m`
   >- (RW_TAC std_ss [toString_def]
       >> RW_TAC string_ss [rec_toString_def,IMPLODE_EQ_THM]
       >> Cases_on `SUC n' MOD 10 = 0`
       >- (SRW_TAC [] []
           >> Cases_on `SUC n' DIV 10`
           >- (METIS_TAC [SUC_NOT,MULT_EQ_0, ADD_0, ADD_COMM,
                          MATCH_MP DIVISION (DECIDE ``0:num < 10:num``)])
           >> SRW_TAC [] [rec_toString_def] >> MATCH_MP_TAC append_neq_lem
           >> RW_TAC list_ss [])
       >> Cases_on `rec_toString (SUC n' DIV 10)`
       >- (SRW_TAC [] [CHAR_EQ_THM]
           >> `ORD (CHR (48 + SUC n' MOD 10)) = 48 + SUC n' MOD 10`
                by (RW_TAC std_ss [GSYM ORD_CHR]
                    >> MATCH_MP_TAC LESS_LESS_EQ_TRANS >> Q.EXISTS_TAC `48 + 10:num`
                    >> RW_TAC arith_ss [LT_ADD_LCANCEL,
                                        MATCH_MP DIVISION (DECIDE ``0:num < 10:num``)])
           >> ONCE_REWRITE_TAC [ADD_COMM]
           >> RW_TAC arith_ss [])
       >> SPOSE_NOT_THEN STRIP_ASSUME_TAC
       >> `LENGTH (h::t ++ [CHR (SUC n' MOD 10 + 48)]) = LENGTH [#"0"]`
                by ASM_SIMP_TAC bool_ss []
       >> Q.PAT_ASSUM `h::t ++ [CHR (SUC n' MOD 10 + 48)] = [#"0"]` (K ALL_TAC)
       >> FULL_SIMP_TAC arith_ss [LENGTH_APPEND, LENGTH, GSYM LENGTH_NIL])
   >> EQ_TAC
   >- (RW_TAC std_ss [toString_def, rec_toString_def, IMPLODE_11]
       >> ONCE_REWRITE_TAC [DECIDE ``(n' = n) = (SUC n' = SUC n)``]
       >> `(SUC n' = SUC n) =
           ((SUC n') DIV 10 * 10 + (SUC n') MOD 10 = (SUC n) DIV 10 * 10 + (SUC n) MOD 10)`
                by METIS_TAC [MATCH_MP DIVISION (DECIDE ``0:num < 10:num``)]
       >> POP_ORW
       >> FULL_SIMP_TAC std_ss [append_sing_eq_lem]
       >> (MP_TAC o Q.SPECL [`48 + SUC n' MOD 10`, `48 + SUC n MOD 10`]) CHR_11
       >> `!n. 48 + SUC n MOD 10 < 256`
                by (STRIP_TAC >> MATCH_MP_TAC LESS_LESS_EQ_TRANS
                    >> Q.EXISTS_TAC `48 + 10:num`
                    >> RW_TAC arith_ss [LT_ADD_LCANCEL, MATCH_MP
                                        DIVISION (DECIDE ``0:num < 10:num``)])
       >> RW_TAC arith_ss [EQ_MULT_LCANCEL]
       >> Cases_on `SUC n' DIV 10`
       >- (Cases_on `SUC n DIV 10` >> RW_TAC arith_ss []
           >> FULL_SIMP_TAC std_ss [rec_toString_def]
           >> `LENGTH ([]:char list) = LENGTH (rec_toString (SUC n'' DIV 10)
                                                ++ [CHR (48 + SUC n'' MOD 10)])`
                by METIS_TAC []
           >> Q.PAT_ASSUM `[] = rec_toString (SUC n'' DIV 10)
                                ++ [CHR (48 + SUC n'' MOD 10)]` (K ALL_TAC)
           >> FULL_SIMP_TAC arith_ss [LENGTH_APPEND, LENGTH, GSYM LENGTH_NIL])
       >> Cases_on `SUC n DIV 10`
       >- (RW_TAC arith_ss []
           >> FULL_SIMP_TAC std_ss [rec_toString_def]
           >> `LENGTH ([]:char list) =
               LENGTH (rec_toString (SUC n'' DIV 10) ++ [CHR (48 + SUC n'' MOD 10)])`
                by METIS_TAC []
           >> Q.PAT_ASSUM `rec_toString (SUC n'' DIV 10)
                           ++ [CHR (48 + SUC n'' MOD 10)] = []` (K ALL_TAC)
           >> FULL_SIMP_TAC arith_ss [LENGTH_APPEND, LENGTH, GSYM LENGTH_NIL])
       >> `SUC n' DIV 10 < SUC n'`
                by (MATCH_MP_TAC DIV_LESS >> RW_TAC arith_ss [])
       >> Suff `toString (SUC n'') = toString (SUC n''')` >- METIS_TAC []
       >> SIMP_TAC arith_ss [toString_def, IMPLODE_11]
       >> ASM_REWRITE_TAC [])
   >> RW_TAC std_ss []);

val STRCAT_toString_inj = store_thm
  ("STRCAT_toString_inj",
   ``!n m s. (STRCAT s (toString n) = STRCAT s (toString m)) = (n = m)``,
   SRW_TAC [] [STRCAT1, toString_inj]);

(* ------------------------------------------------------------------------- *)
(* ------------------------------------------------------------------------- *)

val toString_toNum_cancel = store_thm
  ("toString_toNum_cancel",
   ``!n. toNum(toString n) = n``,
   completeInduct_on `n`
   >> Cases_on `n`
   >- (SRW_TAC [] [toString_def, toNum_def, rec_toNum_def])
   >> SRW_TAC [] [toString_def, rec_toString_def, toNum_def, rec_toNum_def,
                 GSYM SNOC_APPEND, REVERSE_SNOC]
   >> (MP_TAC o Q.SPECL [`48 + SUC n' MOD 10`]) ORD_CHR
   >> `!n. 48 + SUC n MOD 10 < 256`
        by (STRIP_TAC >> MATCH_MP_TAC LESS_LESS_EQ_TRANS >> Q.EXISTS_TAC `48 + 10:num`
            >> RW_TAC arith_ss [LT_ADD_LCANCEL, MATCH_MP
                                DIVISION (DECIDE ``0:num < 10:num``)])
   >> RW_TAC arith_ss []
   >> Suff `SUC n' MOD 10 + rec_toNum (REVERSE (rec_toString (SUC n' DIV 10))) 1 =
                SUC n' MOD 10 + (SUC n' DIV 10) * 10`
   >- METIS_TAC [ADD_COMM, MATCH_MP DIVISION (DECIDE ``0:num < 10:num``)]
   >> RW_TAC arith_ss [EQ_ADD_RCANCEL]
   >> `SUC n' DIV 10 < SUC n'`
                by (MATCH_MP_TAC DIV_LESS >> RW_TAC arith_ss [])
   >> Suff `rec_toNum (REVERSE (rec_toString (SUC n' DIV 10))) 1 =
                10 * (toNum (toString (SUC n' DIV 10)))`
   >- METIS_TAC []
   >> POP_ASSUM (K ALL_TAC)
   >> POP_ASSUM (K ALL_TAC)
   >> POP_ASSUM (K ALL_TAC)
   >> Cases_on `SUC n' DIV 10`
   >- SRW_TAC [] [toString_def, toNum_def, rec_toNum_def, rec_toString_def]
   >> Q.ABBREV_TAC `Q = rec_toNum (REVERSE (rec_toString (SUC n))) 1`
   >> SRW_TAC [] [toString_def, toNum_def]
   >> Q.UNABBREV_TAC `Q`
   >> POP_ASSUM (K ALL_TAC)
   >> Suff `!n m. rec_toNum (REVERSE (rec_toString (SUC n))) (SUC m) =
                      10 * rec_toNum (REVERSE (rec_toString (SUC n))) m`
   >- METIS_TAC [SUC_0]
   >> completeInduct_on `SUC n`
   >> SRW_TAC [] [toString_def, rec_toString_def, toNum_def, rec_toNum_def,
                  GSYM SNOC_APPEND, REVERSE_SNOC, LEFT_ADD_DISTRIB]
   >> ONCE_REWRITE_TAC [EXP]
   >> RW_TAC arith_ss [EQ_ADD_LCANCEL]
   >> `SUC n DIV 10 < SUC n`
        by (MATCH_MP_TAC DIV_LESS >> RW_TAC arith_ss [])
   >> Cases_on `SUC n DIV 10`
   >- SRW_TAC [] [toString_def, toNum_def, rec_toNum_def, rec_toString_def]
   >> Q.PAT_ASSUM `!m. m < SUC n ==> !n. b` (MP_TAC o Q.SPECL [`SUC n''`])
   >> RW_TAC std_ss []);

(* ------------------------------------------------------------------------- *)
(* ------------------------------------------------------------------------- *)

val _ = export_theory ();
