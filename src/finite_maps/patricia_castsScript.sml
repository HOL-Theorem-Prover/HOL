(* ========================================================================= *)
(* FILE         : patricia_castsScript.sml                                   *)
(* DESCRIPTION  : Support for maps 'a word |-> 'b and string |-> 'a          *)
(* ========================================================================= *)
Theory patricia_casts
Ancestors
  arithmetic list rich_list pred_set bit words patricia numposrep
  ASCIInumbers
Libs
  Q wordsLib


val _ = wordsLib.deprecate_word();
val _ = ParseExtras.temp_loose_equality()

(* ------------------------------------------------------------------------- *)

val _ = set_fixity "IN_PTREEw" (Infix (NONASSOC, 425));
val _ = set_fixity "IN_PTREEs" (Infix (NONASSOC, 425));
val _ = set_fixity "INSERT_PTREEw" (Infixr 490);
val _ = set_fixity "INSERT_PTREEs" (Infixr 490);
val _ = set_fixity "UNION_PTREEw" (Infixl 500);
val _ = set_fixity "UNION_PTREEs" (Infixl 500);

Definition SKIP1_def:   SKIP1 (STRING c s) = s
End

Definition string_to_num_def:
  string_to_num s = s2n 256 ORD (STRING (CHR 1) s)
End

Definition num_to_string_def:   num_to_string n = SKIP1 (n2s 256 CHR n)
End

Definition PEEKs_def:       PEEKs t w = PEEK t (string_to_num w)
End
Definition FINDs_def:       FINDs t w = THE (PEEKs t w)
End
Definition ADDs_def:        ADDs t (w,d) = ADD t (string_to_num w,d)
End
Definition ADD_LISTs_def:   ADD_LISTs = FOLDL ADDs
End
Definition REMOVEs_def:     REMOVEs t w = REMOVE t (string_to_num w)
End

val _ = overload_on ("'", Term`$PEEKs`);
val _ = overload_on ("|+", Term`$ADDs`);
val _ = overload_on ("|++", Term`$ADD_LISTs`);
val _ = overload_on ("\\\\", Term`$REMOVEs`);

Definition TRAVERSEs_def:
   TRAVERSEs t = MAP num_to_string (TRAVERSE t)
End

Definition KEYSs_def:   KEYSs t = QSORT $< (TRAVERSEs t)
End

Definition IN_PTREEs_def:
   $IN_PTREEs w t = (string_to_num w) IN_PTREE t
End

Definition INSERT_PTREEs_def:
   $INSERT_PTREEs w t = (string_to_num w) INSERT_PTREE t
End

Definition STRINGSET_OF_PTREE_def:
  STRINGSET_OF_PTREE (t:unit ptree) = LIST_TO_SET (TRAVERSEs t)
End

Definition PTREE_OF_STRINGSET_def:
  PTREE_OF_STRINGSET t s = PTREE_OF_NUMSET t (IMAGE string_to_num s)
End

(* ......................................................................... *)

val _ = Datatype `word_ptree = Word_ptree ('a -> unit) ('b ptree)`;

val _ = type_abbrev("word_ptreeset", ``:('a, unit) word_ptree``);

Definition THE_PTREE_def:    THE_PTREE (Word_ptree a t) = t
End

Definition SOME_PTREE_def[nocompute]:   SOME_PTREE t = Word_ptree (K ()) t
End

Definition WordEmpty_def:    WordEmpty = SOME_PTREE Empty
End

val _ = export_rewrites ["THE_PTREE_def"];

Definition PEEKw_def:
  PEEKw (t:('a,'b) word_ptree) (w:'a word) = PEEK (THE_PTREE t) (w2n w)
End

Definition FINDw_def:   FINDw t w = THE (PEEKw t w)
End

Definition ADDw_def:
  ADDw (t:('a,'b) word_ptree) (w:'a word,d) =
  SOME_PTREE (ADD (THE_PTREE t) (w2n w,d)) : ('a,'b) word_ptree
End

Definition ADD_LISTw_def:   ADD_LISTw = FOLDL ADDw
End

Definition REMOVEw_def:
  REMOVEw (t:('a,'b) word_ptree) (w:'a word) =
  SOME_PTREE (REMOVE (THE_PTREE t) (w2n w)) : ('a,'b) word_ptree
End

val _ = overload_on ("'", Term`$PEEKw`);
val _ = overload_on ("|+", Term`$ADDw`);
val _ = overload_on ("|++", Term`$ADD_LISTw`);
val _ = overload_on ("\\\\", Term`$REMOVEw`);

Definition TRAVERSEw_def:
  TRAVERSEw (t:('a, 'b) word_ptree) =
  MAP (n2w:num->'a word) (TRAVERSE (THE_PTREE t))
End

Definition KEYSw_def:   KEYSw t = QSORT $<+ (TRAVERSEw t)
End

Definition TRANSFORMw_def:
  TRANSFORMw (f:'a->'b) (t:('c,'a) word_ptree) =
  SOME_PTREE (TRANSFORM f (THE_PTREE t)) : ('c,'b) word_ptree
End

Definition EVERY_LEAFw_def:
  EVERY_LEAFw P (t:('a, 'b) word_ptree) =
  EVERY_LEAF (\k d. P (n2w k : 'a word) d) (THE_PTREE t)
End

Definition EXISTS_LEAFw_def:
  EXISTS_LEAFw P (t:('a, 'b) word_ptree) =
  EXISTS_LEAF (\k d. P (n2w k : 'a word) d) (THE_PTREE t)
End

Definition SIZEw_def:    SIZEw t = SIZE (THE_PTREE t)
End
Definition DEPTHw_def:   DEPTHw t = DEPTH (THE_PTREE t)
End

Definition IN_PTREEw_def:
   $IN_PTREEw (w:'a word) (t:('a,unit) word_ptree) =
   (w2n w) IN_PTREE (THE_PTREE t)
End

Definition INSERT_PTREEw_def:
   $INSERT_PTREEw (w:'a word) (t:('a,unit) word_ptree) =
   SOME_PTREE ((w2n w) INSERT_PTREE (THE_PTREE t)) : ('a,unit) word_ptree
End

Definition WORDSET_OF_PTREE_def:
  WORDSET_OF_PTREE (t:('a,unit) word_ptree) = LIST_TO_SET (TRAVERSEw t)
End

Definition UNION_PTREEw_def:
  $UNION_PTREEw t1 t2 =
  SOME_PTREE ($UNION_PTREE (THE_PTREE t1) (THE_PTREE t2))
End

Definition PTREE_OF_WORDSET_def:
  PTREE_OF_WORDSET (t:('a, unit) word_ptree) (s:'a word set) =
  SOME_PTREE (PTREE_OF_NUMSET (THE_PTREE t) (IMAGE w2n s))
  : ('a, unit) word_ptree
End

val _ = overload_on ("|++", Term`$PTREE_OF_WORDSET`);
val _ = overload_on ("|++", Term`$PTREE_OF_STRINGSET`);

(* ------------------------------------------------------------------------- *)

Theorem ADD_INSERT_STRING =
  (GEN_ALL o SIMP_CONV (srw_ss()) [GSYM INSERT_PTREEs_def, oneTheory.one])
  ``ADDs t (w,v:unit)``;

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

Theorem EVERY_MAP_ORD:
   !l. EVERY ($> 256) (MAP ORD l)
Proof
  Induct \\ SRW_TAC [] [GREATER_DEF, stringTheory.ORD_BOUND]
QED

Theorem MAP_11:
   !f l1 l2.
       (!x y. (f x = f y) = (x = y)) ==>
       ((MAP f l1 = MAP f l2) = (l1 = l2))
Proof
  Induct_on `l1` \\ Induct_on `l2` \\ SRW_TAC [] []
QED

Theorem REVERSE_11:
   !l1 l2. ((REVERSE l1 = REVERSE l2) = (l1 = l2))
Proof
  Induct_on `l1` \\ Induct_on `l2`
     \\ SRW_TAC [] [] \\ PROVE_TAC []
QED

Theorem string_to_num_11:
   !s t. (string_to_num s = string_to_num t) = (s = t)
Proof
  REPEAT STRIP_TAC \\ EQ_TAC
    \\ SRW_TAC [] [string_to_num_def, s2n_def]
    \\ SPECL_THEN [`256`, `MAP ORD (REVERSE s)`,
                          `MAP ORD (REVERSE t)`]
         (IMP_RES_TAC o SIMP_RULE (srw_ss()) [EVERY_MAP_ORD]) l2n_11
    \\ FULL_SIMP_TAC (srw_ss()) [REVERSE_11,
         (SIMP_RULE (srw_ss()) [stringTheory.ORD_11] o ISPEC `ORD`) MAP_11]
QED

Theorem n2l_NOT_NULL[local]:
   !b n. ~(n2l b n = [])
Proof SRW_TAC [] [Once n2l_def]
QED

Theorem STRING_SKIP1[local]:
   !l c. EVERY ($> 256) l ==>
         ((STRING c (SKIP1 (MAP CHR l)) = MAP CHR l) =
         ~(l = []) /\ (l = ORD c::TL l))
Proof
  Induct \\ SRW_TAC [] [SKIP1_def]
    \\ Cases_on `c` \\ SRW_TAC [ARITH_ss] [stringTheory.CHR_11]
QED

Theorem EVERY_CHR_LT_256[local]:
   !n. EVERY ($> 256) (REVERSE (n2l 256 n))
Proof
  SRW_TAC [] [ALL_EL_REVERSE, n2l_BOUND]
QED

Theorem TL_APPEND[local]:
   !l1 l2. ~(l1 = []) ==> (TL (l1 ++ l2) = TL l1 ++ l2)
Proof
  Induct \\ SRW_TAC [] []
QED

Theorem TL_REVERSE[local]:
   !l. ~(l = []) ==> (TL (REVERSE l) = REVERSE (FRONT l))
Proof
  Induct \\ SRW_TAC [] [Once FRONT_DEF, TL_APPEND, REVERSE_EQ_NIL]
QED

Theorem TL_REVERSE_LAST[local]:
   !l h. ~(l = []) ==> ((REVERSE l = h :: TL (REVERSE l)) = (h = LAST l))
Proof
  Induct \\ SRW_TAC [] [LAST_DEF] >- METIS_TAC []
    \\ PAT_X_ASSUM `!h. P` IMP_RES_TAC
    \\ NTAC 2 (POP_ASSUM (K ALL_TAC))
    \\ POP_ASSUM (SPEC_THEN `h'` (SUBST1_TAC o SYM))
    \\ SRW_TAC [] [TL_REVERSE, TL_APPEND, REVERSE_EQ_NIL]
    \\ METIS_TAC [APPEND, APPEND_11]
QED

Theorem LENGTH_n2l_256[local]:
   !n. 0 < LENGTH (n2l 256 n)
Proof SRW_TAC [] [LENGTH_n2l]
QED

val LOG_ADD_COMM = ONCE_REWRITE_RULE [ADD_COMM] logrootTheory.LOG_ADD;

Theorem STRING1_SKIP1[local]:
   !n. 256 <= n /\ (n DIV 256 ** LOG 256 n = 1) ==>
       (STRING (CHR 1) (SKIP1 (n2s 256 CHR n)) = n2s 256 CHR n)
Proof
  REPEAT STRIP_TAC
    \\ `n = (n DIV (256 ** LOG 256 n)) * (256 ** LOG 256 n) +
             n MOD (256 ** LOG 256 n)`
    by METIS_TAC [DECIDE ``0 < 256``, DIVISION, ZERO_LT_EXP]
    \\ POP_ASSUM SUBST1_TAC
    \\ SRW_TAC [] [GSYM MAP_REVERSE, REVERSE_EQ_NIL, n2l_NOT_NULL, n2s_def,
                   STRING_SKIP1, EVERY_CHR_LT_256, TL_REVERSE_LAST]
    \\ SRW_TAC [] [DECIDE ``0 < n ==> PRE n < n``, n2l_NOT_NULL,
         GSYM EL_PRE_LENGTH, LENGTH_n2l_256, EL_n2l]
    \\ SRW_TAC [ARITH_ss] [LENGTH_n2l, DIV_MULT_1, LOG_ADD_COMM]
QED

Theorem string_to_num_num_to_string[local]:
   !n. (n = 1) \/ (256 <= n) /\ (n DIV 256 ** LOG 256 n = 1) ==>
       (string_to_num (num_to_string n) = n)
Proof
  SRW_TAC [] [string_to_num_def, num_to_string_def] >- EVAL_TAC
    \\ SRW_TAC [] [STRING1_SKIP1, stringTheory.ORD_CHR_RWT, s2n_n2s]
QED

Theorem s2n_STRING_STRING[local]:
   !f b c1 c2 s.
       1 < b /\ 0 < (f c1 MOD b) ==>
       b <= s2n b f (STRING c1 (STRING c2 s))
Proof
  SRW_TAC [ARITH_ss] [EXP_ADD, s2n_def, l2n_def, Once l2n_APPEND]
    \\ MATCH_MP_TAC (DECIDE ``a <= b ==> a <= b + c``)
    \\ REWRITE_TAC [GSYM MULT_ASSOC]
    \\ SRW_TAC [ARITH_ss] [ZERO_LESS_MULT, ZERO_LT_EXP]
QED

val s2n_STRING_STRING1 =
 (SIMP_RULE (srw_ss()) [EVAL ``ORD (CHR 1)``] o
  SPECL [`ORD`,`256`,`CHR 1`]) s2n_STRING_STRING;

Theorem IMAGE_string_to_num:
   !n. (n = 1) \/ (256 <= n) /\ (n DIV 256 ** LOG 256 n = 1) =
       n IN IMAGE string_to_num UNIV
Proof
  SRW_TAC [] [IN_IMAGE] \\ EQ_TAC \\ SRW_TAC [] []
    >| [
       EXISTS_TAC `""` \\ EVAL_TAC,
       METIS_TAC [string_to_num_num_to_string],
       `(x = "") \/ ?c s. x = STRING c s`
       by METIS_TAC [TypeBase.nchotomy_of ``:string``]
       \\ SRW_TAC [] [string_to_num_def, s2n_STRING_STRING1]
       >- EVAL_TAC
       \\ DISJ2_TAC
       \\ `LENGTH (MAP ORD (REVERSE s) ++ [ORD c]) = LENGTH s + 1`
       by SRW_TAC [] []
       \\ `l2n 256 (MAP ORD (REVERSE s) ++ [ORD c]) < 256 ** (LENGTH s + 1)`
       by METIS_TAC [l2n_lt, DECIDE ``0 < 256``]
       \\ SRW_TAC [ARITH_ss] [s2n_def, LOG_ADD_COMM, DIV_MULT_1,
                              SPECL [`256`, `a ++ b`] l2n_APPEND]
    ]
QED

Theorem string_to_num_num_to_string =
  REWRITE_RULE [IMAGE_string_to_num] string_to_num_num_to_string;

Theorem num_to_string_string_to_num:
   !s. num_to_string (string_to_num s) = s
Proof
  SRW_TAC [] [GSYM string_to_num_11, string_to_num_num_to_string, IMAGE_IN]
QED

(* ------------------------------------------------------------------------- *)

Theorem ADD_INSERT_WORD =
  (GEN_ALL o SIMP_CONV (srw_ss()) [GSYM INSERT_PTREEw_def, oneTheory.one])
  ``ADDw t (w,v:unit)``;

Theorem THE_PTREE_SOME_PTREE:
   !t. THE_PTREE (SOME_PTREE t) = t
Proof
  SRW_TAC [] [SOME_PTREE_def]
QED

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
  ["pred_set.IMAGE_EMPTY",
   "pred_set.IMAGE_INSERT",
   "pred_set.IMAGE_UNION",
   "ADD_INSERT_WORD",
   "ADD_INSERT_STRING",
   "THE_PTREE_SOME_PTREE"];

(* ------------------------------------------------------------------------- *)

