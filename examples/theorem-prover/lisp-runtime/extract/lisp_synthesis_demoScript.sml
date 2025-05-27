
open HolKernel Parse boolLib bossLib; val _ = new_theory "lisp_synthesis_demo";

open arithmeticTheory listTheory pairTheory lisp_sexpTheory lisp_synthesisLib;

(* we start by proving a lemma which helps with termination proofs *)

val term_lemma = prove(
  ``!x. isDot x ==> LSIZE (CAR x) < LSIZE x /\ LSIZE (CDR x) < LSIZE x``,
  Cases \\ EVAL_TAC \\ DECIDE_TAC);


(* we define a few shallow embeddings *)

val append_def = lisp_tDefine "append" `
  append x y = if isDot x then Dot (CAR x) (append (CDR x) y) else y`
  (WF_REL_TAC `measure (LSIZE o FST)` \\ SIMP_TAC std_ss [term_lemma]);

val rev_def = lisp_tDefine "rev" `
  rev x = if isDot x then append (rev (CDR x)) (Dot (CAR x) (Sym "NIL")) else x`
  (WF_REL_TAC `measure (LSIZE)` \\ SIMP_TAC std_ss [term_lemma]);

val len_def = lisp_tDefine "len" `
  len x = if isDot x then LISP_ADD (len (CDR x)) (Val 1) else Val 0`
  (WF_REL_TAC `measure (LSIZE)` \\ SIMP_TAC std_ss [term_lemma]);

val part_def = lisp_tDefine "part" `
  part pivot x res1 res2 =
    if isDot x then
      if isTrue (LISP_LESS (CAR x) pivot)
      then part pivot (CDR x) (Dot (CAR x) res1) res2
      else part pivot (CDR x) res1 (Dot (CAR x) res2)
    else Dot res1 res2`
  (WF_REL_TAC `measure (LSIZE o FST o SND)` \\ SIMP_TAC std_ss [term_lemma]);

val LIZE_EQ_SUC = prove(
  ``!x. (LSIZE x = SUC n) ==> LSIZE (CAR x) <= n /\ LSIZE (CDR x) <= n``,
  Cases \\ EVAL_TAC \\ DECIDE_TAC);

val part_LSIZE = prove(
  ``!y x x1 x2.
      LSIZE (part x y x1 x2) = SUC (LSIZE y + LSIZE x1 + LSIZE x2)``,
  REVERSE Induct \\ ONCE_REWRITE_TAC [part_def]
  \\ SIMP_TAC std_ss [isDot_def,LSIZE_def,CAR_def,CDR_def]
  \\ SRW_TAC [] [] \\ FULL_SIMP_TAC std_ss [LSIZE_def] \\ DECIDE_TAC)
  |> Q.SPECL [`b`,`a`,`Sym "NIL"`,`Sym "NIL"`] |> MATCH_MP LIZE_EQ_SUC
  |> REWRITE_RULE [ADD_0,LSIZE_def];

val NOT_LISP_LESS_TWO = prove(
  ``!x. ~isTrue (LISP_LESS (len x) (Val 2)) ==> isDot x``,
  Cases \\ ONCE_REWRITE_TAC [len_def] \\ SIMP_TAC std_ss [isDot_def] \\ EVAL_TAC);

val qsort_def = lisp_tDefine "qsort" `
  qsort x =
    if isTrue (LISP_LESS (len x) (Val 2)) then x else
      let pivot = CAR x in
      let res = part pivot (CDR x) (Sym "NIL") (Sym "NIL") in
        append (qsort (CAR res)) (Dot pivot (qsort (CDR res)))`
 (WF_REL_TAC `measure LSIZE` \\ REPEAT STRIP_TAC
  \\ IMP_RES_TAC NOT_LISP_LESS_TWO
  \\ FULL_SIMP_TAC std_ss [isDot_thm,LSIZE_def,CAR_def,CDR_def]
  \\ STRIP_ASSUME_TAC part_LSIZE \\ DECIDE_TAC)


(* we use our tool to derive corresponding deep embeddings *)

val thms = synthesise_deep_embeddings ()

val _ = export_theory();
