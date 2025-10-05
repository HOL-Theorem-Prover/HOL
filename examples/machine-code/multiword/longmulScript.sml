(*
  Multiplication of two 64-bit words results in numbers that need
  128-bit words to not truncate the result. This script shows how
  one can use only operations over 64-bit words and still compute
  the complete 128-bit result (as two 64-bit words).

  Main definition: longmul64_def
  Main theorem:    longmul64_thm (but see also longmul64_parts)
*)
Theory longmul
Ancestors
  multiword words arithmetic list pair
Libs
  wordsLib blastLib dep_rewrite

(*-------------------------------------------------------------------------*
   Implementation
 *-------------------------------------------------------------------------*)

Definition chop64_def:
  chop64 (a:word64) = (a && 0xFFFFFFFFw, a >>> 32)
End

Definition glue64_def:
  glue64 (w1:word64) (w2:word64) = (w2 << 32) + w1
End

Definition longmul64_def:
  longmul64 (a:word64) (b:word64) =
    let (a1,a2) = chop64 a in
    let (b1,b2) = chop64 b in
    let (a1b1,k1) = chop64 (a1 * b1) in
    let (a1b2,k1) = chop64 (a1 * b2 + k1) in
    let (a2b1,k2) = chop64 (a2 * b1 + a1b2) in
    let lower = glue64 a1b1 a2b1 in (* or just a * b but that's one more mult *)
    let upper = a2 * b2 + k2 + k1 in
      ((lower:word64), (upper:word64))
End

(*-------------------------------------------------------------------------*
   Correctness proof
 *-------------------------------------------------------------------------*)

Definition split64_def:
  split64 (w:word64) = [w2w w; w2w (w >>> 32)] : word32 list
End

Triviality mw_mul_expand:
  mw_mul [a1;a2] [b1;b2] [0w;0w:word32] =
    let (a1b1,k1) = single_mul_add a1 b1 0w 0w in
    let (a1b2,k1) = single_mul_add a1 b2 k1 0w in
    let (a2b1,k2) = single_mul_add a2 b1 0w a1b2 in
    let (a2b2,k3) = single_mul_add a2 b2 k2 k1 in
      [a1b1;a2b1;a2b2;k3]
Proof
  simp [mw_mul_def,mw_mul_pass_def]
  \\ rpt (pairarg_tac \\ gvs [])
QED

Triviality length_split64:
  LENGTH (split64 b) = 2
Proof
  simp [split64_def]
QED

Triviality mw2n_split64:
  mw2n (split64 a) = w2n a
Proof
  simp [split64_def,mw2n_def,w2w_def,w2n_lsr]
  \\ Cases_on ‘a’ \\ fs []
  \\ simp [DIV_MOD_MOD_DIV]
  \\ ‘0n < 4294967296’ by fs[]
  \\ drule DIVISION
  \\ disch_then $ qspec_then ‘n’ $ mp_tac o GSYM
  \\ simp []
QED

Triviality chop64_alt:
  chop64 (a:word64) = (w2w ((w2w a):word32), w2w ((w2w (a >>> 32)) :word32))
Proof
  simp [chop64_def] \\ BBLAST_TAC
QED

Triviality single_mul_add_eq_chop64:
  single_mul_add (a:word32) b k s = (r1,r2) ⇒
  chop64 (w2w a * w2w b + w2w k + w2w s) = (w2w r1, w2w r2)
Proof
  strip_tac
  \\ dxrule single_mul_add_thm \\ strip_tac
  \\ Cases_on ‘a’ \\ gvs []
  \\ Cases_on ‘b’ \\ gvs []
  \\ Cases_on ‘s’ \\ gvs []
  \\ Cases_on ‘k’ \\ gvs []
  \\ Cases_on ‘r1’ \\ gvs []
  \\ Cases_on ‘r2’ \\ gvs [w2w_def]
  \\ fs [word_add_n2w,word_mul_n2w]
  \\ last_x_assum $ rewrite_tac o single o GSYM
  \\ rewrite_tac [chop64_alt,w2w_def,w2n_lsr] \\ simp []
  \\ DEP_REWRITE_TAC [LESS_DIV_EQ_ZERO] \\ simp []
QED

Triviality w2w_glue64:
  w2w (glue64 (w2w x) (w2w y)) = (x:word32) ∧
  w2w (glue64 (w2w x) (w2w y) >>> 32) = (y:word32)
Proof
  simp [glue64_def] \\ BBLAST_TAC
QED

Triviality chop64_eq_w2w:
  chop64 w = (w2w (a:word32), w2w (b:word32)) ⇒
  a = w2w w ∧ b = w2w (w >>> 32)
Proof
  simp [chop64_def] \\ BBLAST_TAC
QED

Triviality mw_mul_longmul64:
  mw_mul (split64 a) (split64 b) [0w; 0w] =
    let (w1,w2) = longmul64 a b in
      split64 w1 ++ split64 w2
Proof
  simp [split64_def,mw_mul_expand,longmul64_def]
  \\ rpt (pairarg_tac \\ gvs [])
  \\ rpt $ dxrule single_mul_add_eq_chop64
  \\ rpt disch_tac
  \\ gvs [EVAL “w2w 0w”]
  \\ qpat_x_assum ‘chop64 a = _’ mp_tac
  \\ qpat_x_assum ‘chop64 b = _’ mp_tac
  \\ simp [chop64_alt]
  \\ rpt disch_tac
  \\ gvs [w2w_glue64]
  \\ dxrule chop64_eq_w2w \\ fs []
QED

Triviality longmul64_lemma =
  mw_mul_thm
  |> INST_TYPE [alpha |-> “:32”]
  |> Q.SPECL [‘split64 a’, ‘split64 b’, ‘[0w;0w]’]
  |> SRULE [length_split64,mw2n_split64]
  |> SRULE [mw2n_def]
  |> SRULE [mw_mul_longmul64,LET_THM,pairTheory.UNCURRY,mw2n_APPEND,
            length_split64,mw2n_split64,dimwords_def];

Theorem longmul64_thm:
  longmul64 a b = (lower, upper)
  ⇒
  w2n a * w2n b = 2 ** 64 * w2n upper + w2n lower
Proof
  simp [GSYM longmul64_lemma]
QED

Theorem longmul64_parts:
  longmul64 a b = (lower, upper)
  ⇒
  lower = a * b ∧
  upper = n2w ((w2n a * w2n b) DIV 2 ** 64)
Proof
  rw [] \\ imp_res_tac longmul64_thm
  \\ Cases_on ‘a’ \\ Cases_on ‘b’ \\ gvs [word_mul_n2w]
  \\ gvs [GSYM word_add_n2w, GSYM word_mul_n2w]
  >- BBLAST_TAC
  \\ DEP_REWRITE_TAC [LESS_DIV_EQ_ZERO] \\ simp []
  \\ irule LESS_LESS_EQ_TRANS
  \\ irule_at Any w2n_lt \\ simp []
QED
