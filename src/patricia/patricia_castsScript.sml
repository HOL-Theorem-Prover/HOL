(* ========================================================================= *)
(* FILE         : patricia_castsScript.sml                                   *)
(* DESCRIPTION  : Support for maps 'a word |-> 'b and string |-> 'a          *)
(* ========================================================================= *)

(* interactive use:
  app load ["patriciaTheory", "stringTheory", "wordsLib"];
*)

open HolKernel Parse boolLib bossLib Q arithmeticTheory listTheory
     rich_listTheory pred_setTheory bitTheory wordsTheory patriciaTheory;

val _ = new_theory "patricia_casts";

(* ------------------------------------------------------------------------- *)

infix \\ << >>

val op \\ = op THEN;
val op << = op THENL;
val op >> = op THEN1;

val m = apropos;

val _ = wordsLib.deprecate_word();

(* ------------------------------------------------------------------------- *)

val _ = set_fixity "IN_PTREEw" (Infix (NONASSOC, 425));
val _ = set_fixity "IN_PTREEs" (Infix (NONASSOC, 425));
val _ = set_fixity "INSERT_PTREEw" (Infixr 490);
val _ = set_fixity "INSERT_PTREEs" (Infixr 490);
val _ = set_fixity "UNION_PTREEw" (Infixl 500);
val _ = set_fixity "UNION_PTREEs" (Infixl 500);

val SKIP1_def = Define `SKIP1 (STRING c s) = s`;

val string_to_num_def = Define`
  string_to_num s = s2n 256 ORD (STRING (CHR 1) s)`;

val num_to_string_def = Define `num_to_string n = SKIP1 (n2s 256 CHR n)`;

val PEEKs_def     = Define `PEEKs t w = PEEK t (string_to_num w)`;
val FINDs_def     = Define `FINDs t w = THE (PEEKs t w)`;
val ADDs_def      = Define `ADDs t (w,d) = ADD t (string_to_num w,d)`;
val ADD_LISTs_def = Define `ADD_LISTs = FOLDL ADDs`;
val REMOVEs_def   = Define `REMOVEs t w = REMOVE t (string_to_num w)`;

val _ = overload_on ("'", Term`$PEEKs`);
val _ = overload_on ("|+", Term`$ADDs`);
val _ = overload_on ("|++", Term`$ADD_LISTs`);
val _ = overload_on ("\\\\", Term`$REMOVEs`);

val TRAVERSEs_def = Define
  `TRAVERSEs t = MAP num_to_string (TRAVERSE t)`;

val KEYSs_def = Define `KEYSs t = QSORT $< (TRAVERSEs t)`;

val IN_PTREEs_def = Define
  `$IN_PTREEs w t = (string_to_num w) IN_PTREE t`

val INSERT_PTREEs_def = Define
  `$INSERT_PTREEs w t = (string_to_num w) INSERT_PTREE t`;

val STRINGSET_OF_PTREE_def = Define`
  STRINGSET_OF_PTREE (t:unit ptree) = LIST_TO_SET (TRAVERSEs t)`;

val PTREE_OF_STRINGSET_def = Define`
  PTREE_OF_STRINGSET t s = PTREE_OF_NUMSET t (IMAGE string_to_num s)`;

(* ......................................................................... *)

val _ = Hol_datatype `word_ptree = Word_ptree of ('a -> unit) => 'b ptree`;

val _ = type_abbrev("word_ptreeset", ``:('a, unit) word_ptree``);

val THE_PTREE_def  = Define `THE_PTREE (Word_ptree a t) = t`;

val SOME_PTREE_def = zDefine `SOME_PTREE t = Word_ptree (K ()) t`;

val WordEmpty_def  = Define `WordEmpty = SOME_PTREE Empty`;

val _ = export_rewrites ["THE_PTREE_def"];

val PEEKw_def = Define`
  PEEKw (t:('a,'b) word_ptree) (w:'a word) = PEEK (THE_PTREE t) (w2n w)`;

val FINDw_def = Define `FINDw t w = THE (PEEKw t w)`;

val ADDw_def = Define`
  ADDw (t:('a,'b) word_ptree) (w:'a word,d) =
  SOME_PTREE (ADD (THE_PTREE t) (w2n w,d)) : ('a,'b) word_ptree`;

val ADD_LISTw_def = Define `ADD_LISTw = FOLDL ADDw`;

val REMOVEw_def = Define`
  REMOVEw (t:('a,'b) word_ptree) (w:'a word) =
  SOME_PTREE (REMOVE (THE_PTREE t) (w2n w)) : ('a,'b) word_ptree`;

val _ = overload_on ("'", Term`$PEEKw`);
val _ = overload_on ("|+", Term`$ADDw`);
val _ = overload_on ("|++", Term`$ADD_LISTw`);
val _ = overload_on ("\\\\", Term`$REMOVEw`);

val TRAVERSEw_def = Define`
  TRAVERSEw (t:('a, 'b) word_ptree) =
  MAP (n2w:num->'a word) (TRAVERSE (THE_PTREE t))`;

val KEYSw_def = Define `KEYSw t = QSORT $<+ (TRAVERSEw t)`;

val TRANSFORMw_def = Define`
  TRANSFORMw (f:'a->'b) (t:('c,'a) word_ptree) =
  SOME_PTREE (TRANSFORM f (THE_PTREE t)) : ('c,'b) word_ptree`;

val EVERY_LEAFw_def = Define`
  EVERY_LEAFw P (t:('a, 'b) word_ptree) =
  EVERY_LEAF (\k d. P (n2w k : 'a word) d) (THE_PTREE t)`;

val EXISTS_LEAFw_def = Define`
  EXISTS_LEAFw P (t:('a, 'b) word_ptree) =
  EXISTS_LEAF (\k d. P (n2w k : 'a word) d) (THE_PTREE t)`;

val SIZEw_def  = Define `SIZEw t = SIZE (THE_PTREE t)`;
val DEPTHw_def = Define `DEPTHw t = DEPTH (THE_PTREE t)`;

val IN_PTREEw_def = Define
  `$IN_PTREEw (w:'a word) (t:('a,unit) word_ptree) =
   (w2n w) IN_PTREE (THE_PTREE t)`;

val INSERT_PTREEw_def = Define
  `$INSERT_PTREEw (w:'a word) (t:('a,unit) word_ptree) =
   SOME_PTREE ((w2n w) INSERT_PTREE (THE_PTREE t)) : ('a,unit) word_ptree`;

val WORDSET_OF_PTREE_def = Define`
  WORDSET_OF_PTREE (t:('a,unit) word_ptree) = LIST_TO_SET (TRAVERSEw t)`;

val UNION_PTREEw_def = Define`
  $UNION_PTREEw t1 t2 =
  SOME_PTREE ($UNION_PTREE (THE_PTREE t1) (THE_PTREE t2))`;

val PTREE_OF_WORDSET_def = Define`
  PTREE_OF_WORDSET (t:('a, unit) word_ptree) (s:'a word set) =
  SOME_PTREE (PTREE_OF_NUMSET (THE_PTREE t) (IMAGE w2n s))
  : ('a, unit) word_ptree`;

val _ = overload_on ("|++", Term`$PTREE_OF_WORDSET`);
val _ = overload_on ("|++", Term`$PTREE_OF_STRINGSET`);

(* ------------------------------------------------------------------------- *)

val ADD_INSERT_STRING = save_thm("ADD_INSERT_STRING",
  (GEN_ALL o SIMP_CONV (srw_ss()) [GSYM INSERT_PTREEs_def, oneTheory.one])
  ``ADDs t (w,v:unit)``);

(*
val PTREE_OF_STRINGSET_EMPTY = store_thm("PTREE_OF_STRINGSET_EMPTY",
  `PTREE_OF_STRINGSET t {} = t`,
  SRW_TAC [] [PTREE_OF_STRINGSET_def, PTREE_OF_NUMSET_EMPTY]);

val PTREE_OF_STRINGSET_INSERT = store_thm("PTREE_OF_STRINGSET_INSERT",
  `!t s. IS_PTREE t /\ FINITE s ==>
         (PTREE_OF_STRINGSET t (x INSERT s) =
          x INSERT_PTREEs (PTREE_OF_STRINGSET t s))`,
  SRW_TAC [] [PTREE_OF_STRINGSET_def, INSERT_PTREEs_def, PTREE_OF_NUMSET_INSERT]
);
*)

val l2n_APPEND = store_thm("l2n_APPEND",
  `!b l1 l2. l2n b (l1 ++ l2) = l2n b l1 + b ** (LENGTH l1) * l2n b l2`,
  Induct_on `l1` \\ SRW_TAC [ARITH_ss] [EXP, l2n_def]);

val EXP_MONO = prove(
  `!b m n x. 1 < b /\ m < n /\ x < b ** m ==> (b ** m + x < b ** n)`,
  Induct_on `n`
    \\ SRW_TAC [ARITH_ss] [EXP]
    \\ Cases_on `m = n`
    \\ SRW_TAC [ARITH_ss] []
    << [
      `?p. b ** m = p + x` by METIS_TAC [LESS_ADD]
         \\ `?q. b = 1 + (q + 1)` by METIS_TAC [LESS_ADD_1]
         \\ FULL_SIMP_TAC arith_ss [LEFT_ADD_DISTRIB],
      `m < n` by DECIDE_TAC \\ RES_TAC
        \\ `b ** n < b * b ** n` by SRW_TAC [ARITH_ss] []
        \\ DECIDE_TAC]);

val l2n_LENGTH = store_thm("l2n_LENGTH",
  `!b l. 1 < b ==> l2n b l < b ** LENGTH l`,
  Induct_on `l` \\ SRW_TAC [ARITH_ss] [EXP, l2n_def]
    \\ RES_TAC \\ IMP_RES_TAC LESS_ADD_1
    \\ POP_ASSUM (K ALL_TAC) \\ POP_ASSUM SUBST1_TAC
    \\ SRW_TAC [ARITH_ss] [LEFT_ADD_DISTRIB, MOD_LESS,
          DECIDE ``a < b ==> (x + a < b + (y + x))``]);

val l2n_b_1 = prove(
  `!b. 1 < b ==> (l2n b [1] = 1)`,
  SRW_TAC [] [l2n_def]);

val l2n_11 = store_thm("l2n_11",
  `!b l1 l2.
      1 < b /\ EVERY ($> b) l1 /\ EVERY ($> b) l2 ==>
      ((l2n b (l1 ++ [1]) = l2n b (l2 ++ [1])) = (l1 = l2))`,
  REPEAT STRIP_TAC \\ EQ_TAC \\ SRW_TAC [] []
    \\ MATCH_MP_TAC LIST_EQ
    \\ `LENGTH l1 = LENGTH l2` by ALL_TAC
    \\ SRW_TAC [] []
    << [
      SPOSE_NOT_THEN STRIP_ASSUME_TAC
        \\ PAT_ASSUM `l2n b x = l2n b y` MP_TAC
        \\ ASM_SIMP_TAC (srw_ss()++ARITH_ss) [l2n_APPEND, l2n_b_1]
        \\ `(LENGTH l1 < LENGTH l2) \/ (LENGTH l2 < LENGTH l1)`
        by METIS_TAC [LESS_LESS_CASES]
        << [MATCH_MP_TAC (DECIDE ``a < b ==> ~(a = b + x)``),
            MATCH_MP_TAC (DECIDE ``b < a ==> ~(a + x = b)``)]
        \\ MATCH_MP_TAC EXP_MONO
        \\ SRW_TAC [] [l2n_LENGTH],
      `x < LENGTH l1` by DECIDE_TAC
        \\ IMP_RES_TAC (GSYM l2n_DIGIT)
        \\ NTAC 2 (POP_ASSUM SUBST1_TAC)
        \\ FULL_SIMP_TAC (srw_ss()) [l2n_APPEND]]);

val EVERY_MAP_ORD = store_thm("EVERY_MAP_ORD",
  `!l. EVERY ($> 256) (MAP ORD l)`,
  Induct \\ SRW_TAC [] [GREATER_DEF, stringTheory.ORD_BOUND]);

val MAP_11 = store_thm("MAP_11",
  `!f l1 l2.
       (!x y. (f x = f y) = (x = y)) ==>
       ((MAP f l1 = MAP f l2) = (l1 = l2))`,
  Induct_on `l1` \\ Induct_on `l2` \\ SRW_TAC [] []);

val REVERSE_11 = store_thm("REVERSE_11",
  `!l1 l2. ((REVERSE l1 = REVERSE l2) = (l1 = l2))`,
  Induct_on `l1` \\ Induct_on `l2` 
     \\ SRW_TAC [] [] \\ PROVE_TAC []);

val string_to_num_11 = store_thm("string_to_num_11",
  `!s t. (string_to_num s = string_to_num t) = (s = t)`,
  REPEAT STRIP_TAC \\ EQ_TAC
    \\ SRW_TAC [] [string_to_num_def, s2n_def]
    \\ SPECL_THEN [`256`, `MAP ORD (REVERSE s)`,
                          `MAP ORD (REVERSE t)`]
         (IMP_RES_TAC o SIMP_RULE (srw_ss()) [EVERY_MAP_ORD]) l2n_11
    \\ FULL_SIMP_TAC (srw_ss()) [REVERSE_11,
         (SIMP_RULE (srw_ss()) [stringTheory.ORD_11] o ISPEC `ORD`) MAP_11]);

val n2l_NOT_NULL = prove( `!b n. ~(n2l b n = [])`, SRW_TAC [] [Once n2l_def]);

val STRING_SKIP1 = prove(
  `!l c. EVERY ($> 256) l ==>
         ((STRING c (SKIP1 (MAP CHR l)) = MAP CHR l) =
         ~(l = []) /\ (l = ORD c::TL l))`,
  Induct \\ SRW_TAC [] [SKIP1_def]
    \\ Cases_on `c` \\ SRW_TAC [ARITH_ss] [stringTheory.CHR_11]);

val EVERY_CHR_LT_256 = prove(
  `!n. EVERY ($> 256) (REVERSE (n2l 256 n))`,
  SRW_TAC [] [ALL_EL_REVERSE, n2l_BOUND]);

val TL_APPEND = prove(
  `!l1 l2. ~(l1 = []) ==> (TL (l1 ++ l2) = TL l1 ++ l2)`,
  Induct \\ SRW_TAC [] []);

val TL_REVERSE = prove(
  `!l. ~(l = []) ==> (TL (REVERSE l) = REVERSE (FRONT l))`,
  Induct \\ SRW_TAC [] [Once FRONT_DEF, TL_APPEND, REVERSE_EQ_NIL]);

val TL_REVERSE_LAST = prove(
  `!l h. ~(l = []) ==> ((REVERSE l = h :: TL (REVERSE l)) = (h = LAST l))`,
  Induct \\ SRW_TAC [] [LAST_DEF] >> METIS_TAC []
    \\ PAT_ASSUM `!h. P` IMP_RES_TAC
    \\ NTAC 2 (POP_ASSUM (K ALL_TAC))
    \\ POP_ASSUM (SPEC_THEN `h'` (SUBST1_TAC o SYM))
    \\ SRW_TAC [] [TL_REVERSE, TL_APPEND, REVERSE_EQ_NIL]
    \\ METIS_TAC [APPEND, APPEND_11]);

val LENGTH_n2l_256 = prove(
  `!n. 0 < LENGTH (n2l 256 n)`, SRW_TAC [] [LENGTH_n2l]);

val LOG_ADD_COMM = ONCE_REWRITE_RULE [ADD_COMM] logrootTheory.LOG_ADD;

val STRING1_SKIP1 = prove(
  `!n. 256 <= n /\ (n DIV 256 ** LOG 256 n = 1) ==>
       (STRING (CHR 1) (SKIP1 (n2s 256 CHR n)) = n2s 256 CHR n)`,
  REPEAT STRIP_TAC
    \\ `n = (n DIV (256 ** LOG 256 n)) * (256 ** LOG 256 n) +
             n MOD (256 ** LOG 256 n)`
    by METIS_TAC [DECIDE ``0 < 256``, DIVISION, ZERO_LT_EXP]
    \\ POP_ASSUM SUBST1_TAC
    \\ SRW_TAC [] [GSYM MAP_REVERSE, REVERSE_EQ_NIL, n2l_NOT_NULL, n2s_def,
                   STRING_SKIP1, EVERY_CHR_LT_256, TL_REVERSE_LAST]
    \\ SRW_TAC [] [DECIDE ``0 < n ==> PRE n < n``, n2l_NOT_NULL,
         GSYM EL_PRE_LENGTH, LENGTH_n2l_256, EL_n2l]
    \\ SRW_TAC [ARITH_ss] [LENGTH_n2l, DIV_MULT_1, LOG_ADD_COMM]);

val string_to_num_num_to_string = prove(
  `!n. (n = 1) \/ (256 <= n) /\ (n DIV 256 ** LOG 256 n = 1) ==>
       (string_to_num (num_to_string n) = n)`,
  SRW_TAC [] [string_to_num_def, num_to_string_def] >> EVAL_TAC
    \\ SRW_TAC [] [STRING1_SKIP1, stringTheory.ORD_CHR_RWT, s2n_n2s]);

val s2n_STRING_STRING = prove(
  `!f b c1 c2 s.
       1 < b /\ 0 < (f c1 MOD b) ==>
       b <= s2n b f (STRING c1 (STRING c2 s))`,
  SRW_TAC [ARITH_ss] [EXP_ADD, s2n_def, EVAL ``l2n b [c]``, Once l2n_APPEND]
    \\ MATCH_MP_TAC (DECIDE ``a <= b ==> a <= b + c``)
    \\ REWRITE_TAC [GSYM MULT_ASSOC]
    \\ SRW_TAC [ARITH_ss] [ZERO_LESS_MULT, ZERO_LT_EXP]);

val s2n_STRING_STRING1 =
 (SIMP_RULE (srw_ss()) [EVAL ``ORD (CHR 1)``] o
  SPECL [`ORD`,`256`,`CHR 1`]) s2n_STRING_STRING;

val IMAGE_string_to_num = store_thm("IMAGE_string_to_num",
  `!n. (n = 1) \/ (256 <= n) /\ (n DIV 256 ** LOG 256 n = 1) =
       n IN IMAGE string_to_num UNIV`,
  SRW_TAC [] [IN_IMAGE] \\ EQ_TAC \\ SRW_TAC [] []
    << [EXISTS_TAC `""` \\ EVAL_TAC,
        METIS_TAC [string_to_num_num_to_string],
        `(x = "") \/ ?c s. x = STRING c s`
            by METIS_TAC [TypeBase.nchotomy_of ``:string``]
          \\ SRW_TAC [] [string_to_num_def, s2n_STRING_STRING1]
          >> EVAL_TAC \\ DISJ2_TAC
          \\ `LENGTH (MAP ORD (REVERSE s) ++ [ORD c]) =
              LENGTH s + 1`
          by SRW_TAC [] []
          \\ `l2n 256 (MAP ORD (REVERSE s) ++ [ORD c]) <
              256 ** (LENGTH s + 1)`
          by METIS_TAC [l2n_LENGTH, DECIDE ``1 < 256``]
          \\ SRW_TAC [ARITH_ss] [s2n_def, LOG_ADD_COMM, DIV_MULT_1,
               SPECL [`256`, `a ++ b`] l2n_APPEND]]);

val string_to_num_num_to_string = save_thm("string_to_num_num_to_string",
  REWRITE_RULE [IMAGE_string_to_num] string_to_num_num_to_string);

val num_to_string_string_to_num = store_thm("num_to_string_string_to_num",
  `!s. num_to_string (string_to_num s) = s`,
  SRW_TAC [] [GSYM string_to_num_11, string_to_num_num_to_string, IMAGE_IN]);

(* ------------------------------------------------------------------------- *)

val ADD_INSERT_WORD = save_thm("ADD_INSERT_WORD",
  (GEN_ALL o SIMP_CONV (srw_ss()) [GSYM INSERT_PTREEw_def, oneTheory.one])
  ``ADDw t (w,v:unit)``);

val THE_PTREE_SOME_PTREE = store_thm("THE_PTREE_SOME_PTREE",
  `!t. THE_PTREE (SOME_PTREE t) = t`,
  SRW_TAC [] [SOME_PTREE_def]);

val _ = export_rewrites ["THE_PTREE_SOME_PTREE"];

(*
val PTREE_OF_WORDSET_EMPTY = store_thm("PTREE_OF_WORDSET_EMPTY",
  `PTREE_OF_WORDSET (SOME_PTREE t) {} = SOME_PTREE t`,
  SRW_TAC [] [PTREE_OF_WORDSET_def, PTREE_OF_NUMSET_EMPTY]);

val PTREE_OF_WORDSET_INSERT = store_thm("PTREE_OF_WORDSET_INSERT",
  `!t s. IS_PTREE (THE_PTREE t) /\ FINITE s ==>
         (PTREE_OF_WORDSET t (x INSERT s) =
          x INSERT_PTREEw (PTREE_OF_WORDSET t s))`,
  SRW_TAC [] [PTREE_OF_WORDSET_def, INSERT_PTREEw_def, PTREE_OF_NUMSET_INSERT]);

val PTREE_OF_WORDSET_UNION = store_thm("PTREE_OF_WORDSET_UNION",
  `!t s1 s2. IS_PTREE (THE_PTREE t) /\ FINITE s1 /\ FINITE s2 ==>
         (PTREE_OF_WORDSET t (s1 UNION s2) =
          PTREE_OF_WORDSET (PTREE_OF_WORDSET t s1) s2)`,
  SRW_TAC [] [PTREE_OF_WORDSET_def, UNION_PTREEw_def, PTREE_OF_NUMSET_UNION]);
*)

(* ------------------------------------------------------------------------- *)

val _ = add_listform {leftdelim = [TOK "+{"], rightdelim = [TOK "}+"],
                      separator = [TOK ";", BreakSpace(1,0)],
                      cons = "INSERT_PTREEw", nilstr = "WordEmpty",
                      block_info = (PP.INCONSISTENT, 0)};

val _ = add_listform {leftdelim = [TOK "-{"], rightdelim = [TOK "}-"],
                      separator = [TOK ";", BreakSpace(1,0)],
                      cons = "INSERT_PTREEs", nilstr = "Empty",
                      block_info = (PP.INCONSISTENT, 0)};

val _ = computeLib.add_persistent_funs
  [("pred_setTheory.IMAGE_EMPTY", pred_setTheory.IMAGE_EMPTY),
   ("pred_setTheory.IMAGE_INSERT", pred_setTheory.IMAGE_INSERT),
   ("pred_setTheory.IMAGE_UNION", pred_setTheory.IMAGE_UNION),
   ("ADD_INSERT_WORD", ADD_INSERT_WORD),
   ("ADD_INSERT_STRING", ADD_INSERT_STRING),
   ("THE_PTREE_SOME_PTREE", THE_PTREE_SOME_PTREE)];

(* ------------------------------------------------------------------------- *)

val _ = export_theory();
