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

Definition alphabet_size_def :
  alphabet_size = ^(numSyntax.term_of_int Regexp_Type.alphabet_size)
End

Definition ALPHABET_def :
  ALPHABET = ^(rhs (concl (EVAL ``GENLIST I alphabet_size``)))
End

Theorem mem_alphabet :
 !c. MEM c ALPHABET ==> c < alphabet_size
Proof
 rw_tac std_ss [ALPHABET_def,alphabet_size_def,MEM] >> EVAL_TAC
QED

Theorem alphabet_mem[local] :
 !c. c < alphabet_size ==> MEM c ALPHABET
Proof
 simp_tac bool_ss [alphabet_size_def]
  >> CONV_TAC (REPEATC (numLib.BOUNDED_FORALL_CONV EVAL))
  >> rw []
QED

Theorem mem_alphabet_iff :
 !c. MEM c ALPHABET <=> c < alphabet_size
Proof
 metis_tac [mem_alphabet,alphabet_mem]
QED

Theorem ORD_CHR_lem :
 !c. c < alphabet_size ==> (ORD(CHR c) = c)
Proof
 rw[alphabet_size_def,GSYM ORD_CHR] >> decide_tac
QED


(*---------------------------------------------------------------------------*)
(* Character sets are represented by 4-tuples of word64                      *)
(*---------------------------------------------------------------------------*)

val _ = Hol_datatype
         `charset = Charset of word64 => word64 => word64 => word64`;

Definition charset_empty_def :
  charset_empty = Charset 0w 0w 0w 0w
End

Definition charset_full_def :
   charset_full = Charset (~0w) (~0w) (~0w) (~0w)
End


(*---------------------------------------------------------------------------*)
(*   |- charset_full =                                                       *)
(*        Charset                                                            *)
(*         0xFFFFFFFFFFFFFFFFw 0xFFFFFFFFFFFFFFFFw                           *)
(*         0xFFFFFFFFFFFFFFFFw 0xFFFFFFFFFFFFFFFFw                           *)
(*---------------------------------------------------------------------------*)

Theorem charset_full_thm = CONV_RULE (RHS_CONV EVAL) charset_full_def;

Definition words4_bit_def :
  words4_bit c (Charset w1 w2 w3 w4) =
     if c < 128 then
       (if c < 64 then word_bit c w1 else word_bit (c-64) w2)
     else
       (if c < 192 then word_bit (c-128) w3 else word_bit (c-192) w4)
End

Definition charset_mem_def :
   charset_mem c (cs:charset) <=> c < alphabet_size /\ words4_bit c cs
End


Definition charset_union_def :
   charset_union (cs1:charset) (cs2:charset) =
    if cs1 = cs2 then cs1 else
    if cs1 = charset_empty then cs2 else
    if cs2 = charset_empty then cs1
    else
    case (cs1,cs2)
     of (Charset u1 u2 u3 u4, Charset v1 v2 v3 v4)
        => Charset (word_or u1 v1)
                   (word_or u2 v2)
                   (word_or u3 v3)
                   (word_or u4 v4)
End

Definition charset_sing_def :
   charset_sing c =
     let n = ORD c
     in if n < 64  then Charset (1w << n) 0w 0w 0w else
        if n < 128 then Charset 0w (1w << (n-64)) 0w 0w else
        if n < 192 then Charset 0w 0w (1w << (n-128)) 0w
        else Charset 0w 0w 0w (1w << (n-192))
End


Definition charset_insert_def :
    charset_insert c cset = charset_union (charset_sing c) cset
End


(*
Theorem sanity_check[local] :
 !c cset. charset_mem (ORD c) (charset_insert c cset)
Proof
 rw_tac list_ss [charset_mem_def,charset_insert_def, charset_sing_def,
                 alphabet_size_def,ORD_BOUND,LET_THM]
 >> Cases_on `cset`
 >> rw_tac list_ss [charset_union_def, words4_bit_def]
 >> ASSUME_TAC (SPEC_ALL ORD_BOUND)
 >> full_simp_tac list_ss [charset_empty_def]
 >> rw_tac list_ss []
 >> rpt (pop_assum mp_tac)
 >> srw_tac [WORD_ss, WORD_EXTRACT_ss, WORD_BIT_EQ_ss] []

QED
*)


Definition charset_cmp_def :
   charset_cmp (Charset u1 u2 u3 u4) (Charset v1 v2 v3 v4) =
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
    num_cmp (w2n u4) (w2n v4)
End


(*---------------------------------------------------------------------------*)
(* Charset theorems                                                          *)
(*---------------------------------------------------------------------------*)

Theorem charset_mem_empty :
 !c.
   ~charset_mem c charset_empty
Proof
  rw_tac list_ss [charset_mem_def,charset_empty_def,words4_bit_def,
               alphabet_size_def,GSYM IMP_DISJ_THM,wordsTheory.word_bit_0]
QED

Theorem charset_mem_union :
 !c cs1 cs2.
    charset_mem c (charset_union cs1 cs2) <=> charset_mem c cs1 \/ charset_mem c cs2
Proof
 rw_tac list_ss [charset_mem_empty, charset_union_def,EQ_IMP_THM]
  >> REPEAT (WEAKEN_TAC is_neg)
  >> BasicProvers.EVERY_CASE_TAC
  >> full_simp_tac list_ss [charset_mem_def,words4_bit_def,alphabet_size_def]
  >> rw_tac arith_ss []
  >> full_simp_tac arith_ss []
  >> qpat_x_assum `word_bit _ __` mp_tac
  >> srw_tac [WORD_ss, WORD_EXTRACT_ss, WORD_BIT_EQ_ss] []
QED

Theorem num_cmp_eq :
 !k1 k2.
   (num_cmp k1 k2 = Equal) <=> (k1 = k2)
Proof
 rw_tac std_ss [comparisonTheory.num_cmp_def]
QED

Theorem charset_cmp_eq :
 !cs1 cs2.
   (charset_cmp cs1 cs2 = Equal) <=> (cs1 = cs2)
Proof
 Cases
  >> Cases
  >> rw_tac std_ss [charset_cmp_def]
  >> BasicProvers.EVERY_CASE_TAC
  >> rw_tac std_ss [GSYM IMP_DISJ_THM]
  >> full_simp_tac std_ss [num_cmp_eq]
  >> rw_tac arith_ss []
  >> rpt (pop_assum mp_tac)
  >> rw_tac arith_ss [num_cmp_def,wordsTheory.w2n_11]
QED

Theorem charset_cmp_less[local] :
 !u1 u2 u3 u4 v1 v2 v3 v4.
    (charset_cmp (Charset u1 u2 u3 u4) (Charset v1 v2 v3 v4) = Less)
   <=>
    w2n u1 < w2n v1
    \/ (w2n u1 = w2n v1) /\ w2n u2 < w2n v2
    \/ (w2n u1 = w2n v1) /\ (w2n u2 = w2n v2) /\ w2n u3 < w2n v3
    \/ (w2n u1 = w2n v1) /\ (w2n u2 = w2n v2) /\ (w2n u3 = w2n v3) /\ w2n u4 < w2n v4
Proof
  rw_tac std_ss [charset_cmp_def]
  >> BasicProvers.EVERY_CASE_TAC
  >> full_simp_tac std_ss [num_cmp_eq]
  >> rpt (pop_assum mp_tac)
  >> rw_tac arith_ss [num_cmp_def,wordsTheory.w2n_11]
QED

Theorem charset_cmp_strict :
 !cs1 cs2.
   (charset_cmp cs1 cs2 = Less) <=> (charset_cmp cs2 cs1 = Greater)
Proof
 Cases >> Cases
 >> rw_tac std_ss [charset_cmp_def]
 >> BasicProvers.EVERY_CASE_TAC
 >> metis_tac [num_cmp_good,good_cmp_thm,comparison_distinct])
;

Theorem charset_cmp_trans :
 !cs1 cs2 cs3.
      (charset_cmp cs1 cs2 = Less) /\
      (charset_cmp cs2 cs3 = Less)
      ==>
      (charset_cmp cs1 cs3 = Less)
Proof
  Cases >> Cases >> Cases
  >> rw_tac arith_ss [charset_cmp_less]
QED

Definition charset_string_def :
   charset_string s =
      FOLDL (\a c. charset_union a (charset_sing c))
            charset_empty
            s
End

val _ = export_theory();
