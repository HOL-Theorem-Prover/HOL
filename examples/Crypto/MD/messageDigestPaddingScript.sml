open HolKernel boolLib bossLib Parse wordsLib
     arithmeticTheory numposrepTheory listTheory rich_listTheory
     bitTheory wordsTheory byteTheory logrootTheory dividesTheory
     cv_stdTheory cv_transLib

val () = new_theory "messageDigestPadding";

val () = cv_auto_trans n2l_n2lA;

Definition pad_message_def:
  pad_message bits =
  let l = LENGTH bits in
  let n = (l + 1) MOD 512 in
  let k = if n <= 448 then 448 - n else 512 + 448 - n in
  let lb = PAD_LEFT 0 64 $ (if l = 0 then [] else REVERSE $ n2l 2 l) in
  bits ++ 1 :: REPLICATE k 0 ++ lb
End

val () = cv_auto_trans pad_message_def;

Theorem pad_message_length_multiple:
  LENGTH bs < 2 ** 64 ==>
  divides 512 $ LENGTH (pad_message bs)
Proof
  rewrite_tac[pad_message_def, PAD_LEFT, ADD1]
  \\ strip_tac
  \\ BasicProvers.LET_ELIM_TAC
  \\ Cases_on`l = 0` \\ gs[Abbr`n`, Abbr`lb`, Abbr`k`]
  \\ simp[LENGTH_n2l, ADD1, LOG2_def]
  \\ `LOG2 l < 64`
  by ( qspecl_then[`l`,`64`]mp_tac LT_TWOEXP \\ simp[] )
  \\ gs[LOG2_def]
  \\ qspec_then `512` mp_tac DIVISION
  \\ impl_tac >- rw[]
  \\ disch_then(qspec_then`l + 1`mp_tac)
  \\ strip_tac
  \\ qpat_x_assum`l + 1 = _`(assume_tac o SYM)
  \\ `(l + 1) MOD 512 = l + 1 - (l + 1) DIV 512 * 512` by simp[]
  \\ pop_assum SUBST1_TAC
  \\ IF_CASES_TAC
  \\ simp[]
  \\ irule DIVIDES_ADD_1
  \\ simp[]
  \\ simp[divides_def]
QED

Definition parse_block_def:
  parse_block acc bits =
  if NULL bits then REVERSE acc : word32 list
  else parse_block
      ((word_from_bin_list $ REVERSE $ TAKE 32 bits)::acc)
      (DROP 32 bits)
Termination
  WF_REL_TAC`measure (LENGTH o SND)` \\ Cases \\ rw[]
End

val () = cv_auto_trans parse_block_def;

Definition parse_message_def:
  parse_message acc bits =
  if NULL bits then REVERSE acc else
  parse_message (parse_block [] (TAKE 512 bits) :: acc) (DROP 512 bits)
Termination
  WF_REL_TAC`measure (LENGTH o SND)` \\ Cases \\ rw[]
End

val () = cv_auto_trans parse_message_def;

val () = export_theory();
