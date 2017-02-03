open HolKernel Parse boolLib bossLib wordsLib lcsymtacs;
open arithmeticTheory listTheory optionTheory rich_listTheory
     pairTheory comparisonTheory stringTheory;
 
local open numSyntax Regexp_Type in end;

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
(* Charsets are represented by bool[n], from wordsLib.                       *)
(*---------------------------------------------------------------------------*)

val _ = 
  type_abbrev("charset", 
              wordsSyntax.mk_int_word_type Regexp_Type.alphabet_size);

(*---------------------------------------------------------------------------*)
(* Character sets.                                                           *)
(*---------------------------------------------------------------------------*)

val charset_empty_def = 
 Define 
   `charset_empty:charset = 0w`;

val charset_full_def = 
  let val num_of = Vector.foldr(fn (b,n) => if b then  2 * n + 1 else 2 * n) 0 
      val full_num = num_of (Vector.tabulate (Regexp_Type.alphabet_size, K true))
  in
    Define
      `charset_full:charset = 
         ^(wordsSyntax.mk_wordii(full_num,Regexp_Type.alphabet_size))`
  end;

val charset_mem_def = 
 Define 
  `charset_mem c (cs:charset) = c < alphabet_size /\ word_bit c cs`;

val charset_union_def = 
 Define 
  `charset_union (cs1:charset) (cs2:charset) = 
    if cs1 = cs2 then cs1 else 
    if cs1 = charset_empty then cs2 else
    if cs2 = charset_empty then cs1 
    else word_or cs1 cs2`;

val charset_sing_def = 
 Define 
  `charset_sing c = (1w << ORD c):charset`;

val charset_cmp_def = 
 Define
  `charset_cmp (cs1:charset) cs2 = num_cmp (w2n cs1) (w2n cs2)`;

(*---------------------------------------------------------------------------*)
(* Charset theorems                                                          *)
(*---------------------------------------------------------------------------*)

val charset_mem_empty = Q.store_thm 
("charset_mem_empty",
 `!c. ~charset_mem c charset_empty`,
  simp_tac list_ss [charset_mem_def,charset_empty_def,wordsTheory.word_bit_0]);

val charset_mem_union = Q.store_thm ("charset_mem_union",
`!c cs1 cs2.
  charset_mem c (charset_union cs1 cs2) ⇔ charset_mem c cs1 ∨ charset_mem c cs2`, 
 rw [charset_mem_def, charset_union_def,charset_empty_def, 
     wordsTheory.word_bit_0, alphabet_size_def,EQ_IMP_THM]
  >> pop_assum mp_tac
  >> srw_tac [WORD_ss, WORD_EXTRACT_ss, WORD_BIT_EQ_ss] []);

val num_cmp_eq = Q.store_thm
("num_cmp_eq",
 `!k. num_cmp k k = Equal`,
 RW_TAC std_ss [comparisonTheory.num_cmp_def]);

val charset_cmp_eq = Q.store_thm
("charset_cmp_eq",
 `!cs. charset_cmp (cs:charset) cs = Equal`,
 RW_TAC std_ss [charset_cmp_def,num_cmp_eq]);

val charset_cmp_eq = Q.store_thm 
("charset_cmp_eq",
 `!cs1 cs2. (charset_cmp cs1 cs2 = Equal) <=> (cs1 = cs2)`,
 rw [charset_cmp_def,num_cmp_def])

val charset_cmp_strict = Q.store_thm 
("charset_cmp_strict",
 `!cs1 cs2. (charset_cmp cs1 cs2 = Less) <=> (charset_cmp cs2 cs1 = Greater)`,
 metis_tac [charset_cmp_def,num_cmp_good,good_cmp_thm]);

val charset_cmp_trans = Q.store_thm 
("charset_cmp_trans",
 `!cs1 cs2 cs3. 
      (charset_cmp cs1 cs2 = Less) /\ 
      (charset_cmp cs2 cs3 = Less)
      ==> 
      (charset_cmp cs1 cs3 = Less)`,
 metis_tac [charset_cmp_def,num_cmp_good,good_cmp_thm]);

val _ = export_theory();
