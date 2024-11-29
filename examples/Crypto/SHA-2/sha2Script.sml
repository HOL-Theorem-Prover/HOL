open HolKernel boolLib bossLib Parse
     listTheory rich_listTheory arithmeticTheory logrootTheory
     bitTheory wordsTheory numposrepTheory byteTheory wordsLib
     dividesTheory cv_transLib cv_stdTheory

(* The SHA-2 Standard: https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.180-4.pdf *)
(* SHA-256 in particular (i.e. Section 6.2) *)

val _ = new_theory"sha2";

(* TODO: move *)
Definition bool_to_bit_def:
  bool_to_bit b = if b then 1 else 0n
End

val () = cv_auto_trans bool_to_bit_def;

(* TODO: move *)
val () = cv_auto_trans numposrepTheory.n2l_n2lA;

Definition pad_message_def:
  pad_message bs =
  let l = LENGTH bs in
  let n = (l + 1) MOD 512 in
  let k = if n <= 448 then 448 - n else 512 + 448 - n in
  let lb = PAD_LEFT 0 64 $ (if l = 0 then [] else REVERSE $ n2l 2 l) in
  let bits = MAP bool_to_bit bs in
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
  \\ rw[Abbr`bits`]
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
  else parse_block ((word_from_bin_list (TAKE 32 bits))::acc) (DROP 32 bits)
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

Definition initial_hash_value_def:
  initial_hash_value : word32 list = [
    0x6a09e667w;
    0xbb67ae85w;
    0x3c6ef372w;
    0xa54ff53aw;
    0x510e527fw;
    0x9b05688cw;
    0x1f83d9abw;
    0x5be0cd19w
  ]
End

val () = cv_trans_deep_embedding EVAL initial_hash_value_def;

Definition rotr_def:
  rotr n (x: 'a word) = x >>> n || x << (dimindex(:'a) - n)
End

val () = cv_auto_trans (INST_TYPE[alpha |-> ``:32``] rotr_def);

Definition sigma0_def:
  sigma0 (x: word32) = rotr 7 x ?? rotr 18 x ?? x >>> 3
End

Definition sigma1_def:
  sigma1 (x: word32) = rotr 17 x ?? rotr 19 x ?? x >>> 10
End

val () = cv_auto_trans sigma0_def;
val () = cv_auto_trans sigma1_def;

Definition initial_schedule_loop_def:
  initial_schedule_loop Ws t =
  if t ≥ 64 ∨ t < 16 ∨ LENGTH Ws < t then
    REVERSE Ws
  else let
    Wt2  = EL  1 Ws;
    Wt7  = EL  6 Ws;
    Wt15 = EL 14 Ws;
    Wt16 = EL 15 Ws;
    Wt = sigma1 Wt2 + Wt7 + sigma0 Wt15 + Wt16
  in
    initial_schedule_loop (Wt::Ws) (SUC t)
Termination
  WF_REL_TAC`measure (λx. 64 - SND x)`
End

val initial_schedule_loop_pre_def = cv_auto_trans_pre initial_schedule_loop_def;

Theorem initial_schedule_loop_pre[cv_pre]:
  ∀Ws t. initial_schedule_loop_pre Ws t
Proof
  ho_match_mp_tac initial_schedule_loop_ind
  \\ rw[initial_schedule_loop_def]
  \\ rw[Once initial_schedule_loop_pre_def]
QED

Definition initial_schedule_def:
  initial_schedule block =
  initial_schedule_loop block 16
End

val () = cv_auto_trans initial_schedule_def;

(*
Definition process_block_def:
  process_block block
*)

(*
cv_eval``parse_message [] (pad_message [
  F;T;T;F;F;F;F;T; F;T;T;F;F;F;T;F; F;T;T;F;F;F;T;T
])``
*)

val _ = export_theory();
