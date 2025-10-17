Theory ripemd160
Ancestors
  list rich_list arithmetic logroot numposrep byte words cv_std
Libs
  wordsLib cv_transLib intLib

(* The RIPEMD-160 Specification: https://homes.esat.kuleuven.be/~bosselae/ripemd160/pdf/AB-9601/AB-9601.pdf *)
(* See Appendix A for Pseudo-code for RIPEMD-160 *)

(* auxiliary function used in chg_end_def *)
Definition chg_end_acc_def:
  chg_end_acc acc bits =
  if NULL bits then acc
  else chg_end_acc (TAKE 8 bits ++ acc) (DROP 8 bits)
Termination
  WF_REL_TAC`measure (LENGTH o SND)` \\ Cases \\ rw[]
End

Theorem chg_end_acc_sum_length:
  ∀acc bits. LENGTH $ chg_end_acc acc bits = LENGTH acc + LENGTH bits
Proof
  ho_match_mp_tac chg_end_acc_ind>>
  rw[]>>
  rw[Once chg_end_acc_def]>>
  fs[NULL_EQ]>>
  simp[LENGTH_TAKE_EQ]
QED

(* change bits in little-endian to that in big-endian or vice versa, padding 0s to the left of bits when necessary to make the length of bits a multiple of 8 *)
Definition chg_end_def:
  chg_end bits: num list =
  let
    l = LENGTH bits;
    n = l MOD 8;
    k = (8 - n) MOD 8
  in
    chg_end_acc [] $ (REPLICATE k 0 ++ bits)
End

Theorem chg_end_length_multiple:
  divides 8 $ LENGTH (chg_end bits)
Proof
  simp[chg_end_def,chg_end_acc_sum_length,dividesTheory.DIVIDES_MOD_0]>>
  Cases_on ‘LENGTH bits MOD 8’>>
  simp[Once $ GSYM MOD_PLUS]>>
  intLib.ARITH_TAC
QED

(* if the length of bits is a multiple of 8, then chg_end bits has the same length; otherwise, chg_end is (8 - LENGTH bits MOD 8) bits longer than bits *)
Theorem chg_end_length:
  LENGTH (chg_end bits) = LENGTH bits + (8 − LENGTH bits MOD 8) MOD 8
Proof
  rw[chg_end_def,chg_end_acc_sum_length]
QED

Definition pad_message_def:
  pad_message bits =
  let
    l  = LENGTH bits;
    n  = (l + 1) MOD 512;
    k  = if n ≤ 448 then 448 - n else 512 + 448 - n;
    lb = chg_end $ PAD_LEFT 0 64 (if l = 0 then [] else REVERSE $ n2l 2 l)
  in
    bits ++ (1 :: REPLICATE k 0) ++ lb
End

val () = cv_auto_trans n2l_n2lA;
val () = cv_auto_trans pad_message_def;

Theorem pad_message_length_multiple:
  LENGTH bits < 2 ** 64 ⇒ divides 512 $ LENGTH (pad_message bits)
Proof
  strip_tac>>
  ‘LENGTH (n2l 2 (LENGTH bits)) ≤ 64’ by (
    ‘LENGTH bits ≤ 2 ** 64 - 1’ by decide_tac>>
    Cases_on ‘LENGTH bits’>>
    simp[LENGTH_n2l]>>
    ‘0 < SUC n’ by simp[]>>
    drule_then assume_tac logrootTheory.LOG2_LE_MONO>>
    pop_assum $ drule_then assume_tac>>
    gvs[])>>
  rw[pad_message_def]>>
  gvs[]>>
  simp[chg_end_length,bitstringTheory.length_pad_left,ADD1]>>
  Cases_on ‘LENGTH (n2l 2 (LENGTH bits)) = 64’>>
  simp[dividesTheory.DIVIDES_MOD_0]>>
  intLib.ARITH_TAC
QED

Definition parse_block_def:
  parse_block acc bits: word32 list =
  if NULL bits then REVERSE acc
  else
    parse_block
      ((word_from_bin_list $ REVERSE $ chg_end $ TAKE 32 bits)::acc)
      (DROP 32 bits)
Termination
  WF_REL_TAC`measure (LENGTH o SND)` \\ Cases \\ rw[]
End

(* parse bits (assumed to have length that is a multiple of 512) into blocks, each of which is a schedule consisting of 16 words of 32 bits *)
Definition parse_message_def:
  parse_message acc bits =
  if NULL bits then REVERSE acc
  else parse_message (parse_block [] (TAKE 512 bits) :: acc) (DROP 512 bits)
Termination
  WF_REL_TAC`measure (LENGTH o SND)` \\ Cases \\ rw[]
End

val () = cv_auto_trans parse_message_def;

Theorem parse_block_size:
  ∀n acc bits.
    LENGTH bits = 32 * n ⇒ LENGTH $ parse_block acc bits = LENGTH acc + n
Proof
  Induct
  >-rw[Once parse_block_def]
  >-(
    rw[ADD1]>>
    Cases_on ‘NULL bits’
    >-fs[NULL_LENGTH]
    >-simp[Once parse_block_def])
QED

Theorem parse_message_size:
  ∀acc bits.
    divides 512 $ LENGTH bits ∧ EVERY (λe. LENGTH e = 16) acc ⇒
    EVERY (λe. LENGTH e = 16) $ parse_message acc bits
Proof
  ho_match_mp_tac parse_message_ind>>
  rw[]>>
  rw[Once parse_message_def]>>
  gvs[]>>
  last_x_assum irule>>
  CONJ_TAC>>
  fs[dividesTheory.divides_def,NULL_LENGTH,GSYM LENGTH_NON_NIL]
  >-(
    ‘512 ≤ LENGTH bits’ by simp[]>>
    drule_then assume_tac LENGTH_TAKE>>
    ‘LENGTH $ TAKE 512 bits = 32 * 16’ by simp[]>>
    drule parse_block_size>>
    simp[])
  >-intLib.ARITH_TAC
QED

Theorem parse_message_block_size:
  LENGTH m < 2 ** 64 ⇒ EVERY (λe. LENGTH e = 16) $ parse_message [] $ pad_message m
Proof
  strip_tac>>
  drule_then assume_tac pad_message_length_multiple>>
  drule_then assume_tac parse_message_size>>
  simp[]
QED

(* dummy final else-branch added to make f well-defined in all cases *)
Definition f_def:
  f (j: num) x y z: word32 =
  if 0 ≤ j ∧ j ≤ 15 then x ?? y ?? z
  else if 16 ≤ j ∧ j ≤ 31 then (x && y) || (¬x && z)
  else if 32 ≤ j ∧ j ≤ 47 then (x || ¬y) ?? z
  else if 48 ≤ j ∧ j ≤ 63 then (x && z) || (y && ¬z)
  else if 64 ≤ j ∧ j ≤ 79 then x ?? (y || ¬z)
  else 0w
End

val () = cv_auto_trans f_def;

(* dummy final else-branch added to make K well-defined in all cases *)
Definition K_def:
  K (j: num): word32 =
  if 0 ≤ j ∧ j ≤ 15 then 0x00000000w
  else if 16 ≤ j ∧ j ≤ 31 then 0x5A827999w
  else if 32 ≤ j ∧ j ≤ 47 then 0x6ED9EBA1w
  else if 48 ≤ j ∧ j ≤ 63 then 0x8F1BBCDCw
  else if 64 ≤ j ∧ j ≤ 79 then 0xA953FD4Ew
  else 0w
End

val () = cv_auto_trans K_def;

(* dummy final else-branch added to make K' well-defined in all cases *)
Definition K'_def:
  K' (j: num): word32 =
  if 0 ≤ j ∧ j ≤ 15 then 0x50A28BE6w
  else if 16 ≤ j ∧ j ≤ 31 then 0x5C4DD124w
  else if 32 ≤ j ∧ j ≤ 47 then 0x6D703EF3w
  else if 48 ≤ j ∧ j ≤ 63 then 0x7A6D76E9w
  else if 64 ≤ j ∧ j ≤ 79 then 0x00000000w
  else 0w
End

val () = cv_auto_trans K'_def;

Definition rho_def:
  rho n: num = EL n [7;4;13;1;10;6;15;3;12;0;9;5;2;14;11;8]
End

val rho_pre_def = cv_trans_pre "rho_pre" rho_def;

Theorem rho_pre[cv_pre]:
  n < 16 ⇒ rho_pre n
Proof
  simp[rho_pre_def]
QED

Definition rho_alt_def:
  rho_alt n: num =
  if n < 16 then EL n [7;4;13;1;10;6;15;3;12;0;9;5;2;14;11;8]
  else 0
End

val rho_alt_pre_def = cv_trans_pre "rho_alt_pre" rho_alt_def;

Theorem rho_alt_pre[cv_pre]:
  rho_alt_pre n
Proof
  simp[rho_alt_pre_def]
QED

Theorem rho_eq_rho_alt_lt_16:
  n < 16 ⇒ rho n = rho_alt n
Proof
  rw[rho_def,rho_alt_def]
QED

Triviality suc_help = CONV_RULE numLib.SUC_TO_NUMERAL_DEFN_CONV prim_recTheory.LESS_THM;

Theorem rho_preserves_lt_16:
  n < 16 ⇒ rho n < 16
Proof
  rw[rho_def]>>
  pop_assum (fn thm => strip_assume_tac $ SRULE [suc_help] thm)>>
  fs[]
QED

Theorem funpow_rho_preserves_lt_16:
  ∀n m. m < 16 ⇒ FUNPOW rho n m < 16
Proof
  Induct>>
  rw[FUNPOW]>>
  last_x_assum irule>>
  simp[rho_preserves_lt_16]
QED

Theorem rho_eq_rho_alt_lt_16_funpow:
  m < 16 ⇒ FUNPOW rho n m = FUNPOW rho_alt n m
Proof
  strip_tac>>
  irule FUNPOW_CONG>>
  rw[]>>
  irule rho_eq_rho_alt_lt_16>>
  simp[funpow_rho_preserves_lt_16]
QED

Definition pi_def:
  pi i = (9 * i + 5) MOD 16
End

val () = cv_trans pi_def;

Definition r_def:
  r j =
  let
    qt = j DIV 16;
    rm = j MOD 16
  in
    FUNPOW rho qt rm
End

Theorem r_alt_cv:
  r j =
  let
    qt = j DIV 16;
    rm = j MOD 16
  in
    FUNPOW rho_alt qt rm
Proof
  rw[r_def,rho_def,rho_alt_def,rho_eq_rho_alt_lt_16_funpow]
QED

val () = cv_auto_trans r_alt_cv;

Theorem r_lt_16:
  r j < 16
Proof
  simp[r_def]>>
  irule funpow_rho_preserves_lt_16>>
  intLib.ARITH_TAC
QED

Definition r'_def:
  r' j =
  let
    qt = j DIV 16;
    rm = pi (j MOD 16)
  in
    FUNPOW rho qt rm
End

Theorem r'_alt_cv:
  r' j =
  let
    qt = j DIV 16;
    rm = pi (j MOD 16)
  in
    FUNPOW rho_alt qt rm
Proof
  rw[r'_def,rho_def,rho_alt_def,pi_def,rho_eq_rho_alt_lt_16_funpow]
QED

val () = cv_auto_trans r'_alt_cv;

Theorem r'_lt_16:
  r' j < 16
Proof
  simp[r'_def,pi_def]>>
  irule funpow_rho_preserves_lt_16>>
  intLib.ARITH_TAC
QED

Definition shift_lookup_table_def:
  shift_lookup_table: num list list = [
    [11;14;15;12;5;8;7;9;11;13;14;15;6;7;9;8];
    [12;13;11;15;6;9;9;7;12;15;11;13;7;8;7;7];
    [13;15;14;11;7;7;6;8;13;14;13;12;5;5;6;9];
    [14;11;12;14;8;6;5;5;15;12;15;14;9;9;8;6];
    [15;12;13;13;9;5;8;6;14;11;12;11;8;6;5;5]]
End

val () = cv_trans_deep_embedding EVAL shift_lookup_table_def;

Definition s_def:
  s j =
  let
    row = j DIV 16;
    col = r j
  in
    EL col (EL row shift_lookup_table)
End

val s_pre_def = cv_trans_pre "s_pre" s_def;

Theorem s_pre[cv_pre]:
  s_pre j ⇔ j < 80
Proof
  simp[s_pre_def]>>
  iff_tac>>
  strip_tac>>
  ‘LENGTH shift_lookup_table = 5’ by EVAL_TAC>>
  rw[]
  >-intLib.ARITH_TAC
  >-intLib.ARITH_TAC
  >-(
    last_x_assum (fn thm => strip_assume_tac $ SRULE [suc_help] thm)>>
    simp[]>>
    EVAL_TAC)
QED

Definition s'_def:
  s' j =
  let
    row = j DIV 16;
    col = r' j
  in
    EL col (EL row shift_lookup_table)
End

val s'_pre_def = cv_trans_pre "s'_pre" s'_def;

Theorem s'_pre[cv_pre]:
  s'_pre j ⇔ j < 80
Proof
  simp[s'_pre_def]>>
  iff_tac>>
  strip_tac>>
  ‘LENGTH shift_lookup_table = 5’ by EVAL_TAC>>
  rw[]
  >-intLib.ARITH_TAC
  >-intLib.ARITH_TAC
  >-(
    last_x_assum (fn thm => strip_assume_tac $ SRULE [suc_help] thm)>>
    simp[]>>
    EVAL_TAC)
QED

Definition initial_value_def:
  initial_value: word32 # word32 # word32 # word32 # word32 =
  (0x67452301w,0xEFCDAB89w,0x98BADCFEw,0x10325476w,0xC3D2E1F0w)
End

val () = cv_trans_deep_embedding EVAL initial_value_def;

Definition rol_def:
  rol n x: 'a word = (x << n) || (x >>> (dimindex(:'a) - n))
End

val () = cv_auto_trans (INST_TYPE[alpha |-> ``:32``] rol_def);

Definition inner_for_loop_def:
  inner_for_loop block (j,(A,B,C,D,E),(A',B',C',D',E')) =
  let
    T1 = rol (s  j) (A  + f j        B  C  D  + EL (r  j) block + K  j) + E;
    T2 = rol (s' j) (A' + f (79 - j) B' C' D' + EL (r' j) block + K' j) + E'
  in
    (SUC j,(E,T1,B,rol 10 C,D),(E',T2,B',rol 10 C',D'))
End

Definition inner_for_loop_alt_def:
  inner_for_loop_alt block (j,(A,B,C,D,E),(A',B',C',D',E')) =
  if j < 80 ∧ LENGTH block = 16 then
    let
      T1 = rol (s  j) (A  + f j        B  C  D  + EL (r  j) block + K  j) + E;
      T2 = rol (s' j) (A' + f (79 - j) B' C' D' + EL (r' j) block + K' j) + E'
    in
      (SUC j,(E,T1,B,rol 10 C,D),(E',T2,B',rol 10 C',D'))
  else
    (0,(0w,0w,0w,0w,0w),(0w,0w,0w,0w,0w))
End

val inner_for_loop_alt_pre_def = cv_trans_pre "inner_for_loop_alt_pre"
                                              inner_for_loop_alt_def;

Theorem inner_for_loop_alt_pre[cv_pre]:
  inner_for_loop_alt_pre block v
Proof
  simp[inner_for_loop_alt_pre_def]>>
  rw[r_lt_16,r'_lt_16]
QED

Theorem inner_for_loop_eq_alt:
  j < 80 ∧ LENGTH block = 16 ⇒
  inner_for_loop block (j,v) = inner_for_loop_alt block (j,v)
Proof
  PairCases_on ‘v’>>
  rw[inner_for_loop_def,inner_for_loop_alt_def]
QED

(* the body of the outer for-loop *)
Definition process_block_def:
  process_block (h0,h1,h2,h3,h4) block =
  let
    hs = FUNPOW (inner_for_loop block) 80 (0,(h0,h1,h2,h3,h4),(h0,h1,h2,h3,h4))
  in
    case hs of
      (_,(A,B,C,D,E),(A',B',C',D',E')) =>
        (h1 + C + D',h2 + D + E',h3 + E + A',h4 + A + B',h0 + B + C')
End

Definition process_block_alt_def:
  process_block_alt (h0,h1,h2,h3,h4) block =
  let
    hs = FUNPOW (inner_for_loop_alt block) 80 (0,(h0,h1,h2,h3,h4),(h0,h1,h2,h3,h4))
  in
    case hs of
      (_,(A,B,C,D,E),(A',B',C',D',E')) =>
        (h1 + C + D',h2 + D + E',h3 + E + A',h4 + A + B',h0 + B + C')
End

val () = cv_auto_trans process_block_alt_def;

Theorem FUNPOW_inner_for_loop_index:
  ∀m v. FUNPOW (inner_for_loop block) m v = (x,y) ⇒ x = m + FST v
Proof
  Induct>>
  simp[FUNPOW]>>
  rw[]>>
  last_x_assum drule>>
  PairCases_on ‘v’>>
  simp[inner_for_loop_def]
QED

Theorem process_block_eq_alt:
  LENGTH block = 16 ⇒ process_block v block = process_block_alt v block
Proof
  PairCases_on ‘v’>>
  rw[process_block_def,process_block_alt_def,inner_for_loop_eq_alt]>>
  AP_THM_TAC>>
  AP_TERM_TAC>>
  irule FUNPOW_CONG>>
  rw[]>>
  qmatch_goalsub_abbrev_tac ‘(FUNPOW (inner_for_loop block) m vv)’>>
  Cases_on ‘(FUNPOW (inner_for_loop block) m vv)’>>
  irule inner_for_loop_eq_alt>>
  simp[]>>
  drule FUNPOW_inner_for_loop_index>>
  simp[Abbr ‘vv’]
QED

Definition outer_for_loop_def:
  outer_for_loop blocks = FOLDL process_block initial_value blocks
End

Definition outer_for_loop_alt_def:
  outer_for_loop_alt blocks = FOLDL process_block_alt initial_value blocks
End

val () = cv_auto_trans outer_for_loop_alt_def;

Theorem outer_for_loop_alt_cv:
  EVERY (λe. LENGTH e = 16) blocks ⇒
  outer_for_loop blocks = outer_for_loop_alt blocks
Proof
  rw[outer_for_loop_def,outer_for_loop_alt_def]>>
  irule FOLDL_CONG>>
  rw[]>>
  imp_res_tac EVERY_MEM>>
  fs[]>>
  simp[process_block_eq_alt]
QED

(* change w (a word of 32 bits) in little-endian to that in big-endian or vice versa *)
Definition word32_chg_end_def:
  word32_chg_end (w: word32): word32 =
  word_from_bin_list $ REVERSE $ chg_end $ REVERSE $ word_to_bin_list w
End

val () = cv_auto_trans word32_chg_end_def;

Definition RIPEMD_160_def:
  RIPEMD_160 m: 160 word option =
  if LENGTH m < 2 ** 64 then
    let
      p      = pad_message m;
      blocks = parse_message [] p
    in
      case outer_for_loop blocks of
        (h0,h1,h2,h3,h4) =>
          SOME $ concat_word_list [
              (word32_chg_end h4);
              (word32_chg_end h3);
              (word32_chg_end h2);
              (word32_chg_end h1);
              (word32_chg_end h0)]
  else NONE
End

Theorem RIPEMD_160_alt_cv:
  RIPEMD_160 m =
  if LENGTH m < 2 ** 64 then
    let
      p      = pad_message m;
      blocks = parse_message [] p
    in
      case outer_for_loop_alt blocks of
        (h0,h1,h2,h3,h4) =>
          SOME $ concat_word_list [
              (word32_chg_end h4);
              (word32_chg_end h3);
              (word32_chg_end h2);
              (word32_chg_end h1);
              (word32_chg_end h0)]
  else NONE
Proof
  rw[RIPEMD_160_def]>>
  assume_tac parse_message_block_size>>
  rfs[]>>
  drule_then assume_tac outer_for_loop_alt_cv>>
  rw[]
QED

val () = cv_auto_trans RIPEMD_160_alt_cv;

Definition RIPEMD_160_bytes_def:
  RIPEMD_160_bytes (bs: word8 list) =
  RIPEMD_160 $ FLAT $
    MAP (REVERSE o PAD_RIGHT 0 8 o word_to_bin_list) bs
End

val () = cv_auto_trans RIPEMD_160_bytes_def;

Theorem RIPEMD_160_bytes_abc:
  RIPEMD_160_bytes (MAP (n2w o ORD) "abc") =
  SOME 0x8EB208F7E05D987A9B044A8E98C6B087F15A0BFCw
Proof
  CONV_TAC(PATH_CONV"lrr"EVAL)>>
  (fn g => (g |> #2 |> lhs |> cv_eval |> assume_tac>>simp[]) g)
QED

Theorem RIPEMD_160_bytes_two_blocks:
  RIPEMD_160_bytes (MAP (n2w o ORD)
    "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq") =
  SOME 0x12A053384A9C0C88E405A06C27DCF49ADA62EB2Bw
Proof
  CONV_TAC(PATH_CONV"lrr"EVAL)>>
  (fn g => (g |> #2 |> lhs |> cv_eval |> assume_tac>>simp[]) g)
QED

