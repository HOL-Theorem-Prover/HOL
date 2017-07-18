open HolKernel Parse boolLib bossLib wordsLib;
open arithmeticTheory listTheory optionTheory rich_listTheory
     pairTheory comparisonTheory stringTheory;

local open numSyntax Regexp_Type in end;
val comparison_distinct = TypeBase.distinct_of ``:ordering``

val _ = new_theory "charset";

(*---------------------------------------------------------------------------*)
(* Alphabet of regexps and DFAs (typically size 128 or 256). Set in          *)
(* Regexp_Type.sml.                                                          *)
(*---------------------------------------------------------------------------*)

val alphabet_size_def =
 Define
   `alphabet_size = ^(numSyntax.term_of_int Regexp_Type.alphabet_size)`;

val ALPHABET_def =
 Define
  `ALPHABET = ^(rhs (concl (EVAL ``GENLIST I alphabet_size``)))`;

val mem_alphabet = Q.store_thm
("mem_alphabet",
 `!c. MEM c ALPHABET ==> c < alphabet_size`,
 rw_tac std_ss [ALPHABET_def,alphabet_size_def,MEM] >> EVAL_TAC);

val alphabet_mem = Q.store_thm
("alphabet_mem",
 `!c. c < alphabet_size ==> MEM c ALPHABET`,
 simp_tac bool_ss [alphabet_size_def]
  >> CONV_TAC (REPEATC (numLib.BOUNDED_FORALL_CONV EVAL))
  >> rw []);

val mem_alphabet_iff = Q.store_thm
("mem_alphabet_iff",
 `!c. MEM c ALPHABET <=> c < alphabet_size`,
 metis_tac [mem_alphabet,alphabet_mem]);

val ORD_CHR_lem = Q.store_thm
("ORD_CHR_lem",
 `!c. c < alphabet_size ==> (ORD(CHR c) = c)`,
 rw[alphabet_size_def,GSYM ORD_CHR] >> decide_tac);


(*---------------------------------------------------------------------------*)
(* Charsets are represented by :word64#word64#word64#word64                  *)
(*---------------------------------------------------------------------------*)

val _ = Hol_datatype
         `charset = Charset of word64 => word64 => word64 => word64`;

(*---------------------------------------------------------------------------*)
(* Character sets.                                                           *)
(*---------------------------------------------------------------------------*)

val charset_empty_def =
 Define
   `charset_empty = Charset 0w 0w 0w 0w`;

val charset_full_def =
 Define
  `charset_full = Charset (~0w) (~0w) (~0w) (~0w)`;

(*---------------------------------------------------------------------------*)
(*   |- charset_full =                                                       *)
(*        Charset                                                            *)
(*         0xFFFFFFFFFFFFFFFFw 0xFFFFFFFFFFFFFFFFw                           *)
(*         0xFFFFFFFFFFFFFFFFw 0xFFFFFFFFFFFFFFFFw                           *)
(*---------------------------------------------------------------------------*)

val charset_full_thm = save_thm
("charset_full_thm",
 CONV_RULE (RHS_CONV EVAL) charset_full_def);

val words4_bit_def =
 Define
   `words4_bit c (Charset w1 w2 w3 w4) =
       if c < 64 then word_bit c w1 else
       if c < 128 then word_bit (c-64) w2 else
       if c < 192 then word_bit (c-128) w3
       else word_bit (c-192) w4`
;

val charset_mem_def =
 Define
  `charset_mem c (cs:charset) = c < alphabet_size /\ words4_bit c cs`;

val charset_union_def =
 Define
  `charset_union (cs1:charset) (cs2:charset) =
    if cs1 = cs2 then cs1 else
    if cs1 = charset_empty then cs2 else
    if cs2 = charset_empty then cs1
    else
    case (cs1,cs2)
     of (Charset u1 u2 u3 u4, Charset v1 v2 v3 v4)
        => Charset (word_or u1 v1)
                   (word_or u2 v2)
                   (word_or u3 v3)
                   (word_or u4 v4)`
;

val charset_sing_def =
 Define
  `charset_sing c =
     let n = ORD c
     in if n < 64  then Charset (1w << n) 0w 0w 0w else
        if n < 128 then Charset 0w (1w << (n-64)) 0w 0w else
        if n < 192 then Charset 0w 0w (1w << (n-128)) 0w
        else Charset 0w 0w 0w (1w << (n-192))`
;

val charset_insert_def =
 Define
   `charset_insert c cset = charset_union (charset_sing c) cset`;

(*

val sanity_check = Q.prove
(`!c cset. charset_mem (ORD c) (charset_insert c cset)`,
 rw_tac list_ss [charset_mem_def,charset_insert_def, charset_sing_def,
                 alphabet_size_def,ORD_BOUND,LET_THM]
 >> Cases_on `cset`
 >> rw_tac list_ss [charset_union_def, words4_bit_def]
 >> ASSUME_TAC (SPEC_ALL ORD_BOUND)
 >> full_simp_tac list_ss [charset_empty_def]
 >> rw_tac list_ss []
 >> rpt (pop_assum mp_tac)
 >> srw_tac [WORD_ss, WORD_EXTRACT_ss, WORD_BIT_EQ_ss] [])

*)


val charset_cmp_def =
 Define
  `charset_cmp (Charset u1 u2 u3 u4) (Charset v1 v2 v3 v4) =
    case num_cmp (w2n u1) (w2n v1)
      of Less => Less
       | Greater => Greater
       | Equal =>
    case num_cmp (w2n u2) (w2n v2)
      of Less => Less
       | Greater => Greater
       | Equal =>
    case num_cmp (w2n u3) (w2n v3)
      of Less => Less
       | Greater => Greater
       | Equal =>
    num_cmp (w2n u4) (w2n v4)`
;

(*---------------------------------------------------------------------------*)
(* Charset theorems                                                          *)
(*---------------------------------------------------------------------------*)

val charset_mem_empty = Q.store_thm
("charset_mem_empty",
 `!c. ~charset_mem c charset_empty`,
  rw_tac list_ss [charset_mem_def,charset_empty_def,words4_bit_def,
               alphabet_size_def,GSYM IMP_DISJ_THM,wordsTheory.word_bit_0]);

val charset_mem_union = Q.store_thm
("charset_mem_union",
 `!c cs1 cs2.
    charset_mem c (charset_union cs1 cs2) <=> charset_mem c cs1 \/ charset_mem c cs2`,
 rw_tac list_ss [charset_mem_empty, charset_union_def,EQ_IMP_THM]
  >> REPEAT (WEAKEN_TAC is_neg)
  >> BasicProvers.EVERY_CASE_TAC
  >> full_simp_tac list_ss [charset_mem_def,words4_bit_def,alphabet_size_def]
  >> rw_tac arith_ss []
  >> full_simp_tac arith_ss []
  >> qpat_x_assum `word_bit _ __` mp_tac
  >> srw_tac [WORD_ss, WORD_EXTRACT_ss, WORD_BIT_EQ_ss] []
);

val num_cmp_eq = Q.store_thm
("num_cmp_eq",
 `!k. num_cmp k k = Equal`,
 rw_tac std_ss [comparisonTheory.num_cmp_def]);

val charset_cmp_id = Q.store_thm
("charset_cmp_id",
 `!cs. charset_cmp (cs:charset) cs = Equal`,
 Cases >> rw_tac std_ss [charset_cmp_def,num_cmp_eq]);

val charset_cmp_eq = Q.store_thm
("charset_cmp_eq",
 `!cs1 cs2. (charset_cmp cs1 cs2 = Equal) <=> (cs1 = cs2)`,
 Cases
  >> Cases
  >> rw_tac std_ss [charset_cmp_def]
  >> BasicProvers.EVERY_CASE_TAC
  >> rw_tac std_ss [GSYM IMP_DISJ_THM]
  >> full_simp_tac std_ss [num_cmp_eq]
  >> rw_tac arith_ss []
  >> rpt (pop_assum mp_tac)
  >> rw_tac arith_ss [num_cmp_def,wordsTheory.w2n_11]);

val charset_cmp_less = Q.prove
(`!u1 u2 u3 u4 v1 v2 v3 v4.
    (charset_cmp (Charset u1 u2 u3 u4) (Charset v1 v2 v3 v4) = Less)
   <=>
    w2n u1 < w2n v1
    \/ (w2n u1 = w2n v1) /\ w2n u2 < w2n v2
    \/ (w2n u1 = w2n v1) /\ (w2n u2 = w2n v2) /\ w2n u3 < w2n v3
    \/ (w2n u1 = w2n v1) /\ (w2n u2 = w2n v2) /\ (w2n u3 = w2n v3) /\ w2n u4 < w2n v4`,
  rw_tac std_ss [charset_cmp_def]
  >> BasicProvers.EVERY_CASE_TAC
  >> full_simp_tac std_ss [num_cmp_eq]
  >> rpt (pop_assum mp_tac)
  >> rw_tac arith_ss [num_cmp_def,wordsTheory.w2n_11]);

val charset_cmp_strict = Q.store_thm
("charset_cmp_strict",
 `!cs1 cs2. (charset_cmp cs1 cs2 = Less) <=> (charset_cmp cs2 cs1 = Greater)`,
 Cases
 >> Cases
 >> rw_tac std_ss [charset_cmp_def]
 >> BasicProvers.EVERY_CASE_TAC
 >> metis_tac [num_cmp_good,good_cmp_thm,comparison_distinct])
;

val charset_cmp_trans = Q.store_thm
("charset_cmp_trans",
 `!cs1 cs2 cs3.
      (charset_cmp cs1 cs2 = Less) /\
      (charset_cmp cs2 cs3 = Less)
      ==>
      (charset_cmp cs1 cs3 = Less)`,
  Cases
  >> Cases
  >> Cases
  >> rw_tac arith_ss [charset_cmp_less]);

val charset_string_def =
 Define
  `charset_string s =
      FOLDL (\a c. charset_union a (charset_sing c))
            charset_empty
            s`
;

val _ = export_theory();
