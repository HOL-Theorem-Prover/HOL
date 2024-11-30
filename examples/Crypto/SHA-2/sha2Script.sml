open HolKernel boolLib bossLib Parse
     listTheory rich_listTheory arithmeticTheory logrootTheory
     bitTheory wordsTheory numposrepTheory byteTheory wordsLib
     dividesTheory cv_transLib cv_stdTheory

(* The SHA-2 Standard: https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.180-4.pdf *)
(* SHA-256 in particular (i.e. Section 6.2) *)

val _ = new_theory"sha2";

(* TODO: move *)
val () = cv_auto_trans numposrepTheory.n2l_n2lA;

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

Definition initial_hash_value_def:
  initial_hash_value = (
    0x6a09e667w : word32,
    0xbb67ae85w : word32,
    0x3c6ef372w : word32,
    0xa54ff53aw : word32,
    0x510e527fw : word32,
    0x9b05688cw : word32,
    0x1f83d9abw : word32,
    0x5be0cd19w : word32
  )
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

Definition Sigma0_def:
  Sigma0 (x: word32) = rotr 2 x ?? rotr 13 x ?? rotr 22 x
End

Definition Sigma1_def:
  Sigma1 (x: word32) = rotr 6 x ?? rotr 11 x ?? rotr 25 x
End

val () = cv_auto_trans Sigma0_def;
val () = cv_auto_trans Sigma1_def;

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
  initial_schedule_loop (REVERSE block) 16
End

val () = cv_auto_trans initial_schedule_def;

Definition K_def:
  K: word32 list = [
    0x428a2f98w; 0x71374491w; 0xb5c0fbcfw; 0xe9b5dba5w; 0x3956c25bw; 0x59f111f1w; 0x923f82a4w; 0xab1c5ed5w;
    0xd807aa98w; 0x12835b01w; 0x243185bew; 0x550c7dc3w; 0x72be5d74w; 0x80deb1few; 0x9bdc06a7w; 0xc19bf174w;
    0xe49b69c1w; 0xefbe4786w; 0x0fc19dc6w; 0x240ca1ccw; 0x2de92c6fw; 0x4a7484aaw; 0x5cb0a9dcw; 0x76f988daw;
    0x983e5152w; 0xa831c66dw; 0xb00327c8w; 0xbf597fc7w; 0xc6e00bf3w; 0xd5a79147w; 0x06ca6351w; 0x14292967w;
    0x27b70a85w; 0x2e1b2138w; 0x4d2c6dfcw; 0x53380d13w; 0x650a7354w; 0x766a0abbw; 0x81c2c92ew; 0x92722c85w;
    0xa2bfe8a1w; 0xa81a664bw; 0xc24b8b70w; 0xc76c51a3w; 0xd192e819w; 0xd6990624w; 0xf40e3585w; 0x106aa070w;
    0x19a4c116w; 0x1e376c08w; 0x2748774cw; 0x34b0bcb5w; 0x391c0cb3w; 0x4ed8aa4aw; 0x5b9cca4fw; 0x682e6ff3w;
    0x748f82eew; 0x78a5636fw; 0x84c87814w; 0x8cc70208w; 0x90befffaw; 0xa4506cebw; 0xbef9a3f7w; 0xc67178f2w;
  ]
End

val () = cv_trans_deep_embedding EVAL K_def;

Definition Ch_def:
  Ch (x:word32) y z = (x && y) ?? (¬x && z)
End

val () = cv_auto_trans Ch_def;

Definition Maj_def:
  Maj (x:word32) y z = (x && y) ?? (x && z) ?? (y && z)
End

val () = cv_auto_trans Maj_def;

Definition step3_def:
  step3 Ws (t, (a, b, c, d, e, f, g, h)) = let
    t1 = h + Sigma1 e + Ch e f g +
         (if t < 64 then EL t K else 0w) +
         (if t < LENGTH Ws then EL t Ws else 0w);
    t2 = Sigma0 a + Maj a b c;
    h = g;
    g = f;
    f = e;
    e = d + t1;
    d = c;
    c = b;
    b = a;
    a = t1 + t2 in
  (SUC t, (a, b, c, d, e, f, g, h))
End

val step3_pre_def = cv_auto_trans_pre step3_def;

Theorem step3_pre[cv_pre]:
  step3_pre Ws v
Proof
  rw[step3_pre_def, K_def]
QED

Definition process_block_def:
  process_block hash block = let
    Ws = initial_schedule block;
    hs = FUNPOW (step3 Ws) 64 (0, hash);
  in case (hash, hs) of ((a0,b0,c0,d0,e0,f0,g0,h0),(_,(a,b,c,d,e,f,g,h)))
  => (a0+a, b0+b, c0+c, d0+d, e0+e, f0+f, g0+g, h0+h)
End

val () = cv_auto_trans process_block_def;

Definition process_blocks_def:
  process_blocks bs = FOLDL process_block initial_hash_value bs
End

val () = cv_auto_trans process_blocks_def;

Definition SHA_256_def:
  SHA_256 m : 256 word = let
    p = pad_message m;
    blocks = parse_message [] p
  in
    case process_blocks blocks of
         (a, b, c, d, e, f, g, h)
  => concat_word_list [h; g; f; e; d; c; b; a]
End

val () = cv_auto_trans SHA_256_def;

Definition SHA_256_bytes_def:
  SHA_256_bytes (bs: word8 list) =
  SHA_256 $ FLAT $
    MAP (REVERSE o PAD_RIGHT 0 8 o word_to_bin_list) bs
End

val () = cv_auto_trans SHA_256_bytes_def;

Theorem SHA_256_bytes_abc:
  SHA_256_bytes (MAP (n2w o ORD) "abc") =
  0xBA7816BF8F01CFEA414140DE5DAE2223B00361A396177A9CB410FF61F20015ADw
Proof
  CONV_TAC(PATH_CONV"lrr"EVAL)
  \\ (fn g => (g |> #2 |> lhs |> cv_eval |> ACCEPT_TAC) g)
QED

Theorem SHA_256_bytes_two_blocks:
  SHA_256_bytes (MAP (n2w o ORD)
    "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq") =
  0x248D6A61D20638B8E5C026930C3E6039A33CE45964FF2167F6ECEDD419DB06C1w
Proof
  CONV_TAC(PATH_CONV"lrr"EVAL)
  \\ (fn g => (g |> #2 |> lhs |> cv_eval |> ACCEPT_TAC) g)
QED

val _ = export_theory();
